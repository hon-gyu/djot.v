(* ai-disclosure: autonomous *)

(* The inline layer: the parser's pass over a paragraph's text, and the
   canonical (renderable) view it inverts.

   The same two-sided shape as the block layer, one level down.  There,
   `Line.v` classifies a line and `Step.v` folds lines into blocks, while
   `Render.v`'s `cblock` describes the parser's image by the source data
   that determines it.  Here `para_inlines` is the pass, `cinline` is the
   image, and the two meet in `para_inlines_ci_para`.

   The pass currently recognizes escapes and verbatim spans.  The same
   state and canonical view are the extension points for the delimiter
   table and brackets in `.project/260811.inline-parser.md`.

   The scan threads through line breaks rather than restarting at each
   one, because a span may cross a break.  The canonical view stays
   line-local, `cblock` describing a paragraph as a list of lines, and
   `iscan_cis_closed` is what reconciles the two: a canonical line always
   leaves the scan owing nothing to the next.

   Parser and renderer share the file because at this size a split would
   be three files of twenty lines.  It splits the way the block parser
   did once a side outgrows the other. *)

From Stdlib Require Import String Ascii List Bool Lia.
From DjotV Require Import Strings Ast.
Import ListNotations.

Local Open Scope string_scope.

(*
Escapes
=======

A backslash escape is not a construct: `\*` and a bare `*` in a position
where nothing opens both parse to `Str "*"`, so the AST cannot tell them
apart and `cinline` gains no constructor.  What an escape is, is the
*spelling* a `CIStr` needs so that its text comes back unchanged, which
makes this a pair of string functions and one theorem relating them. *)

(* djot.js `pattPunctuation` (inline.ts:84): the ASCII punctuation
   blocks.  This is the set a backslash may escape, and it is deliberately
   wider than the set that ever *needs* escaping. *)
Definition is_punct (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((Nat.leb 33 n && Nat.leb n 47) || (Nat.leb 58 n && Nat.leb n 64)
   || (Nat.leb 91 n && Nat.leb n 96) || (Nat.leb 123 n && Nat.leb n 126))%bool.

(* The characters a `CIStr` must escape to survive reparsing.  Today only
   the backslash: nothing else has inline meaning yet.  Every construct
   that claims a delimiter character adds it here, and the two
   obligations below are what it has to keep true.

   The alternative, escaping every punctuation character unconditionally,
   would keep this constant and needs no obligation, at the cost of
   rendering `a, b` as `a\, b`.  djot.js escapes selectively (it renders
   `\,` back as a bare `,`), and matching that costs only the two lemmas. *)
Definition tick : ascii := "`"%char.
Definition is_tick (c : ascii) : bool := Ascii.eqb c tick.

(* The escape character itself, as opposed to the set of characters that
   need escaping.  The scanner must test *this* to detect a pending
   escape: `needs_escape` contains the backtick, and testing it here
   would make a bare backtick set the escape flag instead of opening a
   verbatim span. *)
Definition bslash : ascii := "\"%char.
Definition is_bslash (c : ascii) : bool := Ascii.eqb c bslash.

Lemma is_tick_bslash : is_tick bslash = false.
Proof. reflexivity. Qed.

Lemma is_bslash_bslash : is_bslash bslash = true.
Proof. reflexivity. Qed.

(*
The delimiter table
-------------------

djot.js instantiates one function, `betweenMatched(c, annotation,
defaultmatch, opentest)` (`inline.ts:103`), at nine characters, so the
table is a transcription rather than a generalization of ours.  It is a
table and not nine branches for the reason
`.project/project-engineering-lessons.md` gives under "A hanging `Qed`":
the scanner must keep one recursive call and decide what to do by lookup,
or a general lemma about it becomes unprovable while every `Compute`
stays fast.

Six rows here.  The hyphen and the two quote characters are also
`betweenMatched` rows upstream, but each carries a second construct on
the same character (smart dashes, smart quotes), and adding a row is
cheap where adding a construct is not. *)

Inductive dstyle : Type :=
  | DEmph | DStrong | DSuper | DSub | DMark | DInsert.

Definition dchar (k : dstyle) : ascii :=
  match k with
  | DEmph => "_"%char | DStrong => "*"%char
  | DSuper => "^"%char | DSub => "~"%char
  | DMark => "="%char | DInsert => "+"%char
  end.

(* Whether an unbraced delimiter may open a span at all: djot.js's
   `opentest`, `alwaysTrue` for the emphasis four and `hasBrace` for the
   two that exist only in braced form (`{= =}`, `{+ +}`). *)
Definition dbare (k : dstyle) : bool :=
  match k with DMark | DInsert => false | _ => true end.

Definition dnode (k : dstyle) (ns : inlines) : inline :=
  match k with
  | DEmph => Emph ns | DStrong => Strong ns
  | DSuper => Superscript ns | DSub => Subscript ns
  | DMark => Highlight ns | DInsert => Insert ns
  end.

Definition dstyle_of (c : ascii) : option dstyle :=
  if Ascii.eqb c "_" then Some DEmph
  else if Ascii.eqb c "*" then Some DStrong
  else if Ascii.eqb c "^" then Some DSuper
  else if Ascii.eqb c "~" then Some DSub
  else if Ascii.eqb c "=" then Some DMark
  else if Ascii.eqb c "+" then Some DInsert
  else None.

Definition is_delim (c : ascii) : bool :=
  match dstyle_of c with Some _ => true | None => false end.

(* The table's coherence obligation, alongside the `needs_escape` ones
   below: a row's character must look the row up again.  A new row that
   reuses a character silently shadows an old one without it. *)
Lemma dstyle_of_dchar : forall k, dstyle_of (dchar k) = Some k.
Proof. intros []; reflexivity. Qed.

(* The braces that force a delimiter open or closed.  `{` also begins an
   attribute, which is not implemented; until it is, a `{` that is not an
   open marker is literal text, matching what the scanner did before. *)
Definition lbrace : ascii := "{"%char.
Definition rbrace : ascii := "}"%char.

Definition needs_escape (c : ascii) : bool :=
  (is_bslash c || is_tick c || is_delim c
   || Ascii.eqb c lbrace || Ascii.eqb c rbrace)%bool.

(* Obligation 1: an escaped character must be one the decoder accepts. *)
Lemma needs_escape_punct : forall c, needs_escape c = true -> is_punct c = true.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7] H.
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    vm_compute in H |- *; first [reflexivity | discriminate].
Qed.

(* Obligation 2: the escape character escapes itself, or a text ending in
   a backslash would decode as an escape of whatever followed. *)
Lemma needs_escape_backslash : needs_escape "\"%char = true.
Proof. reflexivity. Qed.

(* Obligation 3: a backtick in a `Str` must not reach the scanner bare,
   or it would open a verbatim span instead of standing for itself.  This
   is the obligation every delimiter character will add. *)
Lemma needs_escape_tick : forall c, is_tick c = true -> needs_escape c = true.
Proof.
  intros c H. unfold needs_escape. rewrite H.
  rewrite orb_true_r. reflexivity.
Qed.

(* Obligation 4, the same for every delimiter the table claims, and for
   the braces that force one open or closed. *)
Lemma needs_escape_delim : forall c, is_delim c = true -> needs_escape c = true.
Proof.
  intros c H. unfold needs_escape. rewrite H.
  rewrite orb_true_r. reflexivity.
Qed.

Lemma needs_escape_lbrace : needs_escape lbrace = true.
Proof. reflexivity. Qed.

Lemma needs_escape_rbrace : needs_escape rbrace = true.
Proof. reflexivity. Qed.

Fixpoint escape_str (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if needs_escape c
      then String "\"%char (String c (escape_str rest))
      else String c (escape_str rest)
  end.

(* Verbatim delimiters use the least positive backtick-run length that
   does not occur in the content, matching djot.js `verbatimDelim`. *)
Fixpoint tick_runs_from (run : nat) (s : string) : list nat :=
  match s with
  | EmptyString => if Nat.eqb run 0 then [] else [run]
  | String c rest =>
      if is_tick c then tick_runs_from (S run) rest
      else if Nat.eqb run 0
           then tick_runs_from 0 rest
           else run :: tick_runs_from 0 rest
  end.

Definition tick_runs (s : string) : list nat := tick_runs_from 0 s.

Fixpoint first_missing (fuel candidate : nat) (runs : list nat) : nat :=
  match fuel with
  | 0 => candidate
  | S fuel' =>
      if existsb (Nat.eqb candidate) runs
      then first_missing fuel' (S candidate) runs
      else candidate
  end.

Definition verb_ticks (s : string) : nat :=
  first_missing (S (String.length s)) 1 (tick_runs s).

Lemma first_missing_nonzero :
  forall fuel n runs, n <> 0 -> first_missing fuel n runs <> 0.
Proof.
  induction fuel as [|fuel IH]; intros n runs Hn; cbn [first_missing].
  - exact Hn.
  - destruct (existsb (Nat.eqb n) runs); [apply IH; discriminate|exact Hn].
Qed.

Lemma verb_ticks_nonzero : forall s, verb_ticks s <> 0.
Proof. intros s. unfold verb_ticks. apply first_missing_nonzero. discriminate. Qed.

Definition starts_tick (s : string) : bool :=
  match s with String c _ => is_tick c | _ => false end.

Definition ends_tick (s : string) : bool := starts_tick (rev_string s).

Lemma starts_tick_app_l :
  forall a b, nonempty_str a = true -> starts_tick (a ++ b) = starts_tick a.
Proof. intros [|c a] b H; [discriminate|reflexivity]. Qed.

Lemma rev_nonempty_str :
  forall s, nonempty_str (rev_string s) = nonempty_str s.
Proof.
  intros [|c s]; [reflexivity|].
  rewrite rev_string_cons. destruct (rev_string s); reflexivity.
Qed.

Lemma ends_tick_cons_nonempty :
  forall c d s, ends_tick (String c (String d s)) = ends_tick (String d s).
Proof.
  intros c d s. unfold ends_tick. rewrite rev_string_cons.
  apply starts_tick_app_l. rewrite rev_nonempty_str. reflexivity.
Qed.

Lemma ends_tick_app_r :
  forall a b, nonempty_str b = true -> ends_tick (a ++ b) = ends_tick b.
Proof.
  intros a b Hb. unfold ends_tick. rewrite rev_string_app.
  apply starts_tick_app_l. rewrite rev_nonempty_str. exact Hb.
Qed.

Definition pad_verb (s : string) : string :=
  let left := if starts_tick s then " " else EmptyString in
  let right := if ends_tick s then " " else EmptyString in
  (left ++ s ++ right)%string.

Lemma pad_verb_nonempty :
  forall s, nonempty_str s = true -> nonempty_str (pad_verb s) = true.
Proof.
  intros s H. unfold pad_verb. destruct (starts_tick s); cbn [append];
    [reflexivity|]. destruct s; [discriminate|reflexivity].
Qed.

Lemma pad_verb_starts_nontick :
  forall s, nonempty_str s = true -> starts_tick (pad_verb s) = false.
Proof.
  intros s H. unfold pad_verb. destruct (starts_tick s) eqn:Hs;
    destruct (ends_tick s); cbn [append starts_tick]; try reflexivity.
  all: rewrite starts_tick_app_l by exact H; exact Hs.
Qed.

Lemma pad_verb_ends_nontick :
  forall s, nonempty_str s = true -> ends_tick (pad_verb s) = false.
Proof.
  intros s H. unfold pad_verb. destruct (starts_tick s);
    destruct (ends_tick s) eqn:He; cbn [append].
  - change (ends_tick (" " ++ (s ++ " ")) = false).
    rewrite ends_tick_app_r by (destruct s; [discriminate|reflexivity]).
    rewrite ends_tick_app_r by reflexivity. reflexivity.
  - rewrite append_empty_r. change (ends_tick (" " ++ s) = false).
    rewrite ends_tick_app_r by exact H. exact He.
  - rewrite ends_tick_app_r by reflexivity. reflexivity.
  - rewrite append_empty_r. exact He.
Qed.

Fixpoint ticks (n : nat) : string :=
  match n with 0 => EmptyString | S k => String tick (ticks k) end.

Lemma ticks_succ_r :
  forall n, ticks (S n) = (ticks n ++ String tick EmptyString)%string.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [ticks append]. rewrite <- IH. reflexivity.
Qed.

Definition verb_text (s : string) : string :=
  let d := ticks (verb_ticks s) in (d ++ pad_verb s ++ d)%string.

Fixpoint verb_safe_from (n run : nat) (s : string) : bool :=
  match s with
  | EmptyString => negb (Nat.eqb run n)
  | String c rest =>
      if is_tick c then verb_safe_from n (S run) rest
      else (negb (Nat.eqb run n) && verb_safe_from n 0 rest)%bool
  end.

Definition verb_safe (n : nat) (s : string) : bool :=
  verb_safe_from n 0 s.

Definition starts_space_tick (s : string) : bool :=
  match s with
  | String c (String d _) => (Ascii.eqb c " "%char && is_tick d)%bool
  | _ => false
  end.

(* Exactly the strings `trim_verb` can emit. *)
Definition verb_content_ok (s : string) : bool :=
  (no_nl s && negb (starts_space_tick s)
   && negb (starts_space_tick (rev_string s))
   && verb_safe (verb_ticks s) (pad_verb s))%bool.

(*
Canonical inlines
=================
*)

(* One line's inline content, described by the source that determines it.
   One constructor per inline construct the roundtrip covers, exactly as
   `cblock` carries one per block construct. *)
Inductive cinline : Type :=
  | CIStr (s : string)
  | CIVerb (s : string).

(* The last byte of `s`, or `prev` when `s` is empty. *)
Fixpoint str_last (s : string) (prev : option ascii) : option ascii :=
  match s with
  | EmptyString => prev
  | String c rest => str_last rest (Some c)
  end.

(* Source text, threading the byte to the left of what is being emitted
   (`None` at the start of a line).

   Not `concat (map ...)`: a delimiter's spelling depends on its
   neighbours, so `Emph [CIStr "b"]` renders `_b_` at a line start but
   `{_b_}` inside `a_b_c`, and a context-free per-element function
   cannot say which.  One byte on each side is the whole of the context
   any djot rule consults, since `can_open` and `can_close` each test a
   single neighbouring character (djot.js `inline.ts:110-112`); the byte
   to the right is available from the unconsumed tail. *)
Fixpoint ci_text (prev : option ascii) (cis : list cinline) : string :=
  match cis with
  | [] => EmptyString
  | CIStr s :: rest =>
      let e := escape_str s in e ++ ci_text (str_last e prev) rest
  | CIVerb s :: rest =>
      let v := verb_text s in v ++ ci_text (str_last v prev) rest
  end.

Definition ci_line (cis : list cinline) : string := ci_text None cis.

Lemma ci_text_prev :
  forall cis p q, ci_text p cis = ci_text q cis.
Proof.
  induction cis as [|c rest IH]; intros p q; [reflexivity|].
  destruct c; cbn [ci_text]; f_equal; apply IH.
Qed.

(* ...and the AST the parser builds from that text. *)
Definition ci_ast (ci : cinline) : node inline :=
  match ci with
  | CIStr s => mk (Str s)
  | CIVerb s => mk (Verbatim s)
  end.

Definition ci_inlines (cis : list cinline) : inlines := map ci_ast cis.

Lemma ci_line_nil : ci_line [] = EmptyString.
Proof. reflexivity. Qed.

Lemma ci_line_str : forall s, ci_line [CIStr s] = escape_str s.
Proof. intros s. unfold ci_line. cbn [ci_text]. apply append_empty_r. Qed.

(*
Renderability
-------------
*)

(* A `Str` carrying no text would not have been emitted, and one carrying
   a newline is not within-line content.

   An *empty* verbatim is excluded outright, which narrows the view by a
   document the parser can reach.  Its canonical source is two adjacent
   delimiter runs and nothing between, so it is closed only by what
   follows it: at the end of a paragraph the scan closes it, and anywhere
   else the runs merge and swallow the next byte -- across a line break
   included, since spans cross breaks.  Representing it would take a
   condition on the *paragraph*, which is one level above anything
   `cinline` knows about.  `Verbatim ""` in a one-line paragraph does
   round-trip; it is simply outside the view. *)
Definition ci_ok (ci : cinline) : bool :=
  match ci with
  | CIStr s => nonempty_str s && no_nl s
  | CIVerb s => nonempty_str s && verb_content_ok s
  end.

(* Pairwise source separation: adjacent strings merge, and adjacent
   verbatim spans merge their delimiter runs. *)
Definition ci_pair_ok (a b : cinline) : bool :=
  match a, b with
  | CIStr _, CIStr _ => false
  | CIVerb _, CIVerb _ => false
  | _, _ => true
  end.

Fixpoint ci_sep_ok (cis : list cinline) : bool :=
  match cis with
  | a :: ((b :: _) as rest) => ci_pair_ok a b && ci_sep_ok rest
  | _ => true
  end.

Definition cis_ok (cis : list cinline) : bool :=
  forallb ci_ok cis && ci_sep_ok cis.

(* Nonemptiness of a line's content is not a separate obligation: the
   block layer already asks that a paragraph's rendered lines are
   nonblank, and only `[]` renders blank. *)
Lemma cis_nonempty_of_line :
  forall cis, nonempty_str (ci_line cis) = true -> nonempty cis = true.
Proof.
  intros [|c rest] H; [rewrite ci_line_nil in H; discriminate | reflexivity].
Qed.

(* The form the block layer supplies it in: `para_ok` and `heading_ok`
   both carry `forallb line_ok` over the rendered lines. *)
Lemma cis_nonempty_of_lines :
  forall lss,
    forallb line_ok (map ci_line lss) = true ->
    forallb nonempty lss = true.
Proof.
  induction lss as [|cis rest IH]; [reflexivity|].
  cbn [map forallb]. intros H. apply andb_true_iff in H as [Hl Hr].
  rewrite (cis_nonempty_of_line cis
             (nonblank_nonempty _ (line_ok_nonblank _ Hl))).
  exact (IH Hr).
Qed.

(*
The inline pass
===============
*)

(* Verbatim content is trimmed of one padding space at each end, but only
   where it sits against a backtick (djot.js `trimVerbatim`, parse.ts:57).
   A space not adjacent to a backtick is content: `` ` a ` `` really is
   " a ".  Reversed, "ends with a backtick then a space" is "starts with a
   space then a backtick", so one function does both ends. *)

Definition strip_pad (s : string) : string :=
  match s with
  | String c rest =>
      if (Ascii.eqb c " "%char && starts_tick rest)%bool then rest else s
  | EmptyString => s
  end.

Definition trim_verb (s : string) : string :=
  rev_string (strip_pad (rev_string (strip_pad s))).

Lemma strip_pad_added :
  forall s, starts_tick s = true -> strip_pad (" " ++ s) = s.
Proof.
  intros [|c s] H; [discriminate|].
  cbn [starts_tick] in H. cbn [strip_pad append starts_tick].
  rewrite H. reflexivity.
Qed.

Lemma strip_pad_stable :
  forall s, negb (starts_space_tick s) = true -> strip_pad s = s.
Proof.
  intros [|c s] H; [reflexivity|]. destruct s as [|d s].
  - cbn [strip_pad starts_tick]. destruct (Ascii.eqb c " "%char); reflexivity.
  - cbn [starts_space_tick strip_pad] in H |- *.
    destruct (Ascii.eqb c " "%char) eqn:Hc; [|reflexivity].
    destruct (is_tick d) eqn:Hd; [discriminate|].
    cbn [starts_tick]. rewrite Hd. reflexivity.
Qed.

Lemma strip_pad_pad_verb :
  forall s, negb (starts_space_tick s) = true ->
    strip_pad (pad_verb s)
    = (s ++ if ends_tick s then " " else EmptyString)%string.
Proof.
  intros [|c [|d s]] H; unfold pad_verb;
    cbn [starts_tick starts_space_tick append] in H |- *.
  - reflexivity.
  - destruct (is_tick c) eqn:Hc;
      destruct (ends_tick (String c EmptyString)) eqn:He;
      cbn [append strip_pad starts_tick].
    + rewrite Hc. reflexivity.
    + rewrite Hc. reflexivity.
    + unfold ends_tick, rev_string, starts_tick in He.
      cbn [rev_string_aux] in He. rewrite Hc in He. discriminate.
    + destruct (Ascii.eqb c " "%char); reflexivity.
  - destruct (is_tick c) eqn:Hc;
      destruct (ends_tick (String c (String d s))) eqn:He;
      cbn [append strip_pad starts_tick].
    + rewrite Hc. reflexivity.
    + rewrite Hc. reflexivity.
    + apply negb_true_iff in H. rewrite H. reflexivity.
    + apply negb_true_iff in H. rewrite H. reflexivity.
Qed.

Lemma trim_verb_pad :
  forall s, verb_content_ok s = true -> trim_verb (pad_verb s) = s.
Proof.
  intros s H. unfold verb_content_ok in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[Hnl Hleft] Hright] Hsafe].
  unfold trim_verb. rewrite strip_pad_pad_verb by exact Hleft.
  destruct (ends_tick s) eqn:He.
  - rewrite rev_string_app. cbn [rev_string rev_string_aux append].
    change (rev_string (strip_pad (" " ++ rev_string s)) = s).
    rewrite strip_pad_added.
    + apply rev_string_involutive.
    + exact He.
  - rewrite append_empty_r. rewrite strip_pad_stable by exact Hright.
    apply rev_string_involutive.
Qed.

(*
The scanner
-----------

One character at a time, structurally recursive on the remaining input.
That is not an accident of style: it is what makes "the scanner never
revisits a position" definitional rather than a theorem, which is the
`no-backtracking` half of Phase 3 obtained for free (see
`.project/260811.inline-parser.md` §2.4).  It also matches djot.js's
`feed`, which is a position-at-a-time loop over a mode flag.

A verbatim closer is a run of *exactly* the opening width, so a run
cannot be resolved until the character after it arrives; that is why
`IVerb` carries a pending run count rather than closing eagerly.  A run
of the wrong width is content, which is how `` ` `` ` `` holds two
backticks inside a one-backtick fence. *)

Definition one (c : ascii) : string := String c EmptyString.

Lemma nat_eqb_refl : forall n, Nat.eqb n n = true.
Proof. induction n; [reflexivity|exact IHn]. Qed.

(* djot.js `pattNonspace` (inline.ts:80).  `can_open` and `can_close` are
   each one test of one neighbouring byte against this. *)
Definition is_space (c : ascii) : bool :=
  (Ascii.eqb c " "%char || Ascii.eqb c "009"%char
   || Ascii.eqb c "013"%char || Ascii.eqb c "010"%char)%bool.

Definition nonspace_at (p : option ascii) : bool :=
  match p with None => false | Some c => negb (is_space c) end.

(*
The scope stack
---------------

djot.js keeps a flat event list and rewrites it: an opener leaves a
placeholder `str` match, closing splices the real annotation over it, and
`clearOpeners` discards the openers a completed match spanned.  We keep a
stack of open scopes instead, each carrying its own accumulated inlines.
The two are equivalent -- probed against djot.js over the corpus and
~580k generated strings before any of this was written, see
`.project/260811.inline-parser.md` §2.2 -- and the stack is what the
proofs can induct on.

Three dispositions, of the four the probe found.  *Close* pops the
scope and emits its node.  *Abandon* replaces a scope by literal text:
its opener's spelling, then its content, spliced into the level below,
which is what `clearOpeners` plus the placeholder amount to.  The
remaining two, *discard* and closing below the top, belong to brackets
and are not reachable from this table. *)

Record frame : Type := Frame {
  fr_style : dstyle;
  fr_marked : bool;          (* opened as `{d`, so only `d}` closes it *)
  fr_out : inlines           (* this scope's inlines, reversed *)
}.

(* The opener's source text, which is what it decays to when abandoned. *)
Definition fr_src (f : frame) : string :=
  if fr_marked f then String lbrace (one (dchar (fr_style f)))
  else one (dchar (fr_style f)).

Record ostate : Type := OState {
  os_out : inlines;          (* the outermost scope, reversed *)
  os_stk : list frame        (* open scopes, innermost first *)
}.

Definition ostart : ostate := OState [] [].

Definition dstyle_eqb (a b : dstyle) : bool :=
  match a, b with
  | DEmph, DEmph | DStrong, DStrong | DSuper, DSuper
  | DSub, DSub | DMark, DMark | DInsert, DInsert => true
  | _, _ => false
  end.

(* A closer matches an opener when the character *and* the marking agree:
   djot.js keys its opener map by `{d` or `d`, so `{_a_` does not close
   and neither does `_a_}`. *)
Definition dmatch (k : dstyle) (m : bool) (f : frame) : bool :=
  (dstyle_eqb k (fr_style f) && Bool.eqb m (fr_marked f))%bool.

(* Reversed-list splices that merge a `Str` seam, so `no_adjacent_str`
   survives an abandoned opener becoming text next to its neighbours. *)
Definition osnoc (n : node inline) (out : inlines) : inlines :=
  match out, n with
  | Node p [] (Str t) :: rest, Node _ [] (Str s) =>
      (Node p [] (Str (t ++ s)) :: rest)%list
  | _, _ => (n :: out)%list
  end.

(* Whether the seam could merge: exactly `Wf.plain_str` of the head, and
   the same notion `no_adjacent_str` is stated over.  A `Str` carrying
   attributes is a node in its own right and never merges. *)
Definition starts_str (out : inlines) : bool :=
  match out with Node _ [] (Str _) :: _ => true | _ => false end.

Fixpoint oapp (cur out : inlines) : inlines :=
  match cur with
  | [] => out
  | [n] => osnoc n out
  | n :: rest => n :: oapp rest out
  end.

Definition oemit (n : node inline) (o : ostate) : ostate :=
  match os_stk o with
  | [] => OState (n :: os_out o) []
  | f :: rest =>
      OState (os_out o) (Frame (fr_style f) (fr_marked f) (n :: fr_out f) :: rest)
  end.

Definition flush_text (txt : string) (o : ostate) : ostate :=
  if nonempty_str txt then oemit (mk (Str txt)) o else o.

Definition opush (k : dstyle) (m : bool) (o : ostate) : ostate :=
  OState (os_out o) (Frame k m [] :: os_stk o).

(* Walk out through the open scopes looking for one this closer matches,
   abandoning each scope it passes.  `pend` carries what those abandoned
   scopes contributed, ready to splice into the next level down.

   `nonempty content` is djot.js's exclusion of the empty span
   (`opener.endpos !== pos - 1`, inline.ts:148): `{__}` is literal. *)
Fixpoint oclose_go (k : dstyle) (m : bool) (pend : inlines) (stk : list frame)
  : option (inlines * list frame) :=
  match stk with
  | [] => None
  | f :: rest =>
      let content := oapp pend (fr_out f) in
      if (dmatch k m f && nonempty content)%bool
      then Some (content, rest)
      else oclose_go k m (oapp content [mk (Str (fr_src f))]) rest
  end.

Definition oclose (k : dstyle) (m : bool) (o : ostate) : option ostate :=
  match oclose_go k m [] (os_stk o) with
  | None => None
  | Some (content, rest) =>
      Some (oemit (mk (dnode k (List.rev content))) (OState (os_out o) rest))
  end.

(* Everything still open when the paragraph ends is abandoned. *)
Fixpoint oflatten (pend : inlines) (stk : list frame) (bottom : inlines)
  : inlines :=
  match stk with
  | [] => oapp pend bottom
  | f :: rest =>
      oflatten (oapp (oapp pend (fr_out f)) [mk (Str (fr_src f))]) rest bottom
  end.

Definition ofinish (o : ostate) : inlines :=
  oflatten [] (os_stk o) (os_out o).

Inductive iscan : Type :=
  (* accumulating literal text; `esc` is a pending backslash, and `prev`
     is the byte before `txt` (`None` at the start of a paragraph or of a
     line), which is what `can_close` consults when `txt` is empty *)
  | IText (esc : bool) (txt : string) (prev : option ascii) (o : ostate)
  (* a `{` whose role the next byte decides: open marker, or text *)
  | IBrace (txt : string) (prev : option ascii) (o : ostate)
  (* an unbraced delimiter whose role the next byte decides; `canclose`
     was computed from the byte before it *)
  | IDelim (k : dstyle) (txt : string) (canclose : bool) (o : ostate)
  (* counting an opening backtick run *)
  | IOpen (n : nat) (o : ostate)
  (* inside a width-`n` verbatim, with `run` unresolved trailing ticks *)
  | IVerb (n run : nat) (txt : string) (o : ostate).

(* One byte in text mode.  The delimiter arm is a lookup, not six
   branches, for the reason the table's own comment gives. *)
Definition ilead (c : ascii) (txt : string) (prev : option ascii) (o : ostate)
  : iscan :=
  if is_bslash c then IText true txt prev o
  else if is_tick c then IOpen 1 (flush_text txt o)
  else if Ascii.eqb c lbrace then IBrace txt prev o
  else match dstyle_of c with
       | Some k => IDelim k txt (nonspace_at (str_last txt prev)) o
       | None => IText false (txt ++ one c)%string prev o
       end.

(* Resolving a `{`: an open marker if a delimiter follows, text
   otherwise.  A marked delimiter needs no further lookahead -- djot.js
   forces `can_open` and blocks `can_close` for it -- so it opens here.

   An attribute also begins with `{`, and is not implemented; until it is,
   every other `{` is text, which is what the scanner did before. *)
Definition ibrace_step (c : ascii) (txt : string) (prev : option ascii)
  (o : ostate) : iscan :=
  match dstyle_of c with
  | Some k =>
      IText false EmptyString (Some (dchar k)) (opush k true (flush_text txt o))
  | None => ilead c (txt ++ one lbrace)%string prev o
  end.

(* Resolving an unbraced delimiter, once the byte after it has arrived
   (or not, at the end of a line: `inone`).  Closing wins over opening,
   as in djot.js, and a `}` immediately after forces the close. *)
Definition idelim_lit (k : dstyle) (txt : string) (marker : bool) : string :=
  (txt ++ one (dchar k) ++ if marker then one rbrace else EmptyString)%string.

Definition idelim_done (k : dstyle) (txt : string) (marker : bool)
  (next : option ascii) (o : ostate) : iscan :=
  if (dbare k && negb marker && nonspace_at next)%bool
  then IText false EmptyString (Some (dchar k)) (opush k false (flush_text txt o))
  else IText false (idelim_lit k txt marker) None o.

Definition idelim_resolve (k : dstyle) (txt : string) (canclose marker : bool)
  (next : option ascii) (o : ostate) : iscan :=
  if (canclose || marker)%bool
  then match oclose k marker (flush_text txt o) with
       | Some o' =>
           IText false EmptyString
             (Some (if marker then rbrace else dchar k)) o'
       | None => idelim_done k txt marker next o
       end
  else idelim_done k txt marker next o.

(* No byte follows: the end of a line or of the paragraph.  `IBrace` and
   `IDelim` are the only states this changes, and after it neither
   remains, which is what lets `ibreak` and `ifinish` match on the rest. *)
Definition iresolve (st : iscan) : iscan :=
  match st with
  | IBrace txt prev o => IText false (txt ++ one lbrace)%string prev o
  | IDelim k txt canclose o => idelim_resolve k txt canclose false None o
  | _ => st
  end.

Definition istep (c : ascii) (st : iscan) : iscan :=
  match st with
  | IText true txt prev o =>
      IText false (txt ++ (if is_punct c then one c
                           else String "\"%char (one c)))%string prev o
  | IText false txt prev o => ilead c txt prev o
  | IBrace txt prev o => ibrace_step c txt prev o
  | IDelim k txt canclose o =>
      let marker := Ascii.eqb c rbrace in
      let st' := idelim_resolve k txt canclose marker (Some c) o in
      (* the `}` of a close marker is consumed with the delimiter; any
         other byte still has to be dispatched *)
      if marker then st'
      else match st' with
           | IText false txt' prev' o' => ilead c txt' prev' o'
           | other => other
           end
  | IOpen n o =>
      if is_tick c then IOpen (S n) o else IVerb n 0 (one c) o
  | IVerb n run txt o =>
      if is_tick c then IVerb n (S run) txt o
      else if Nat.eqb run n
      then ilead c EmptyString (Some tick)
             (oemit (mk (Verbatim (trim_verb txt))) o)
      else IVerb n 0 (txt ++ ticks run ++ one c)%string o
  end.

(* End of line.  An unclosed verbatim closes here, as djot.js does in
   `getMatches`.  A pending backslash is a literal backslash, which is
   djoths's reading; djot.js makes it a hard break, an already-logged
   disagreement (`escapes.test:30`).  Neither can arise from a canonical
   rendering, since `escape_str` never emits a bare backslash. *)
Definition ifinish_ostate (st : iscan) : ostate :=
  match iresolve st with
  | IText true txt _ o => flush_text (txt ++ one bslash)%string o
  | IText false txt _ o => flush_text txt o
  | IOpen _ o => oemit (mk (Verbatim EmptyString)) o
  | IVerb n run txt o =>
      oemit (mk (Verbatim (trim_verb
                   (if Nat.eqb run n then txt else txt ++ ticks run)%string))) o
  (* unreachable: `iresolve` leaves no `IBrace` and no `IDelim` *)
  | IBrace _ _ o | IDelim _ _ _ o => o
  end.

Definition ifinish_rev (st : iscan) : inlines := ofinish (ifinish_ostate st).

Definition ifinish (st : iscan) : inlines := List.rev (ifinish_rev st).

(* A line boundary inside a paragraph.
   djot.js scans the newline as an ordinary character of the subject, and
   tests it *before* the verbatim mode (`inline.ts:832`), so a span may
   cross a break: `` `a `` / `` b` `` is one code span containing a
   newline, and the same will hold of the delimiter family.  A paragraph
   is therefore one scan with this between its lines, not a scan per
   line.

   Only `IText` ends the line.  Inside a verbatim the newline is content,
   which is why it arrives here as `one nl` rather than closing anything;
   a resolved closing run (`run = n`) is the one case where the span ends
   *at* the break and the newline is the soft break after it. *)
Definition ibreak (st : iscan) : iscan :=
  match iresolve st with
  | IText true txt _ o =>
      IText false EmptyString None
        (oemit (mk SoftBreak) (flush_text (txt ++ one bslash)%string o))
  | IText false txt _ o =>
      IText false EmptyString None (oemit (mk SoftBreak) (flush_text txt o))
  | IOpen n o => IVerb n 0 nl o
  | IVerb n run txt o =>
      if Nat.eqb run n
      then IText false EmptyString None
             (oemit (mk SoftBreak) (oemit (mk (Verbatim (trim_verb txt))) o))
      else IVerb n 0 (txt ++ ticks run ++ nl)%string o
  (* unreachable, as in `ifinish_ostate` *)
  | (IBrace _ _ _ | IDelim _ _ _ _) as st' => st'
  end.

Definition null {A} (l : list A) : bool :=
  match l with [] => true | _ => false end.

(* A state that owes nothing to the next line: every construct it has
   seen is resolved, so the boundary just ends the line and `ibreak`
   agrees with `ifinish` on what was emitted.  What fails it is a span
   still open across the break -- an unterminated backtick run, a
   verbatim whose closer has not arrived, or any open scope. *)
Definition iscan_closed (st : iscan) : bool :=
  match iresolve st with
  | IText _ _ _ o => null (os_stk o)
  | IOpen _ _ => false
  | IVerb n run _ o => (Nat.eqb run n && null (os_stk o))%bool
  | IBrace _ _ _ | IDelim _ _ _ _ => false
  end.

Lemma ibreak_closed :
  forall st,
    iscan_closed st = true ->
    ibreak st = IText false EmptyString None
                  (OState (mk SoftBreak :: ifinish_rev st) []).
Proof.
  intros st H. unfold iscan_closed, ibreak, ifinish_rev, ifinish_ostate in *.
  destruct (iresolve st) as [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o];
    try discriminate.
  - destruct o as [out [|f stk]]; [|discriminate].
    unfold flush_text, oemit, ofinish; cbn [os_stk os_out oflatten oapp].
    destruct (nonempty_str (txt ++ one bslash)); reflexivity.
  - destruct o as [out [|f stk]]; [|discriminate].
    unfold flush_text, oemit, ofinish; cbn [os_stk os_out oflatten oapp].
    destruct (nonempty_str txt); reflexivity.
  - apply andb_true_iff in H as [Hr Hs]. rewrite Hr.
    destruct o as [out [|f stk]]; [|discriminate].
    unfold oemit, ofinish; cbn [os_stk os_out oflatten oapp]. reflexivity.
Qed.

Fixpoint iscan_str (s : string) (st : iscan) : iscan :=
  match s with
  | EmptyString => st
  | String c rest => iscan_str rest (istep c st)
  end.

(* A paragraph's lines, in order.  Trailing whitespace is stripped from
   the last line only -- djot.js's `getMatches` drops the final soft
   break and the spaces before it, and does so whatever state the scan is
   in, so `` `a  `` closes on the trimmed content.  Interior lines keep
   their trailing spaces, which is observable inside a verbatim. *)
Fixpoint iscan_lines (l : list string) (st : iscan) : iscan :=
  match l with
  | [] => st
  | [x] => iscan_str (strip_trailing_ws x) st
  | x :: rest => iscan_lines rest (ibreak (iscan_str x st))
  end.

Lemma iscan_str_app :
  forall a b st, iscan_str (a ++ b) st = iscan_str b (iscan_str a st).
Proof.
  induction a as [|c a IH]; intros b st; cbn [iscan_str]; [reflexivity|].
  apply IH.
Qed.

Lemma iscan_open_ticks_more :
  forall k n out,
    iscan_str (ticks k) (IOpen n out) = IOpen (n + k) out.
Proof.
  induction k as [|k IH]; intros n out.
  - cbn [ticks iscan_str]. f_equal. lia.
  - cbn [ticks iscan_str istep]. change
      (iscan_str (ticks k) (IOpen (S n) out) = IOpen (n + S k) out).
    rewrite IH. f_equal. lia.
Qed.

Lemma iscan_open_ticks :
  forall k txt prev o,
    iscan_str (ticks (S k)) (IText false txt prev o)
    = IOpen (S k) (flush_text txt o).
Proof.
  intros k txt prev o. cbn [ticks iscan_str istep ilead]. change
    (iscan_str (ticks k) (IOpen 1 (flush_text txt o))
     = IOpen (S k) (flush_text txt o)).
  rewrite iscan_open_ticks_more. f_equal.
Qed.

Lemma iscan_verb_ticks_more :
  forall k n run txt out,
    iscan_str (ticks k) (IVerb n run txt out) = IVerb n (run + k) txt out.
Proof.
  induction k as [|k IH]; intros n run txt out.
  - cbn [ticks iscan_str]. f_equal. lia.
  - cbn [ticks iscan_str istep]. change
      (iscan_str (ticks k) (IVerb n (S run) txt out)
       = IVerb n (run + S k) txt out).
    rewrite IH. f_equal. lia.
Qed.

Lemma iscan_open_body :
  forall s n out,
    nonempty_str s = true -> starts_tick s = false -> n <> 0 ->
    iscan_str s (IOpen n out) = iscan_str s (IVerb n 0 EmptyString out).
Proof.
  intros [|c s] n out Hne Hstart Hn; [discriminate|].
  cbn [starts_tick] in Hstart. cbn [iscan_str istep]. rewrite Hstart.
  replace (Nat.eqb 0 n) with false.
  - reflexivity.
  - destruct n; [contradiction|reflexivity].
Qed.

Lemma iscan_verb_safe_nonempty :
  forall s n run txt out,
    nonempty_str s = true -> ends_tick s = false ->
    verb_safe_from n run s = true ->
    iscan_str s (IVerb n run txt out)
    = IVerb n 0 (txt ++ ticks run ++ s) out.
Proof.
  induction s as [|c rest IH]; intros n run txt out Hne Hend Hsafe;
    [discriminate|].
  cbn [iscan_str verb_safe_from] in Hsafe |- *.
  destruct (is_tick c) eqn:Hc.
  - cbn [istep]. rewrite Hc. destruct rest as [|d rest'].
    + unfold ends_tick, starts_tick, rev_string in Hend.
      cbn [rev_string_aux] in Hend. rewrite Hc in Hend. discriminate.
    + rewrite ends_tick_cons_nonempty in Hend.
      rewrite (IH n (S run) txt out eq_refl Hend Hsafe).
      apply Ascii.eqb_eq in Hc. subst c. f_equal.
      rewrite ticks_succ_r, !append_assoc. reflexivity.
  - apply andb_true_iff in Hsafe as [Hrun Hsafe].
    apply negb_true_iff in Hrun. cbn [istep]. rewrite Hc, Hrun.
    destruct rest as [|d rest'].
    + cbn [iscan_str]. f_equal.
    + rewrite ends_tick_cons_nonempty in Hend.
      rewrite (IH n 0 (txt ++ ticks run ++ one c) out eq_refl Hend Hsafe).
      f_equal. cbn [ticks one]. rewrite !append_assoc. reflexivity.
Qed.

Lemma iscan_verb_text_nonempty :
  forall s txt prev o,
    nonempty_str s = true ->
    verb_safe (verb_ticks s) (pad_verb s) = true ->
    iscan_str (verb_text s) (IText false txt prev o)
    = IVerb (verb_ticks s) (verb_ticks s) (pad_verb s) (flush_text txt o).
Proof.
  intros s txt prev o Hne Hsafe. unfold verb_text.
  rewrite !iscan_str_app.
  destruct (verb_ticks s) as [|k] eqn:Hn;
    [exfalso; apply (verb_ticks_nonzero s); exact Hn|].
  rewrite iscan_open_ticks.
  unfold verb_safe in Hsafe.
  rewrite (iscan_open_body (pad_verb s) (S k) (flush_text txt o)
             (pad_verb_nonempty s Hne) (pad_verb_starts_nontick s Hne))
    by discriminate.
  rewrite (iscan_verb_safe_nonempty (pad_verb s) (S k) 0 EmptyString
             (flush_text txt o) (pad_verb_nonempty s Hne)
             (pad_verb_ends_nontick s Hne) Hsafe).
  change (iscan_str (ticks (S k))
            (IVerb (S k) 0 (pad_verb s) (flush_text txt o))
          = IVerb (S k) (S k) (pad_verb s) (flush_text txt o)).
  rewrite iscan_verb_ticks_more. f_equal.
Qed.

(*
The output frame
----------------

Every state carries the inlines emitted so far, in reverse, and every
transition only ever conses onto them.  So a fixed suffix rides through
the whole scan untouched, and `ifinish` reverses it out at the front.
This is what lets a paragraph be assembled one line at a time from a
scan that does not restart: the lines after the first run against a
suffix holding the lines before it. *)

Definition istart : iscan := IText false EmptyString None ostart.

(* Appending at the *bottom* -- `os_out`, the outermost scope -- is what
   makes this commute with every transition: pushing and popping scopes
   only ever touch `os_stk`, so the suffix is out of their reach. *)
Definition oout_app (base : inlines) (o : ostate) : ostate :=
  OState (os_out o ++ base)%list (os_stk o).

Definition iout_app (base : inlines) (st : iscan) : iscan :=
  match st with
  | IText esc txt prev o => IText esc txt prev (oout_app base o)
  | IBrace txt prev o => IBrace txt prev (oout_app base o)
  | IDelim k txt cc o => IDelim k txt cc (oout_app base o)
  | IOpen n o => IOpen n (oout_app base o)
  | IVerb n run txt o => IVerb n run txt (oout_app base o)
  end.

Lemma oemit_app :
  forall n o base,
    oemit n (oout_app base o) = oout_app base (oemit n o).
Proof.
  intros n [out [|f stk]] base; reflexivity.
Qed.

Lemma flush_text_app :
  forall txt o base,
    flush_text txt (oout_app base o) = oout_app base (flush_text txt o).
Proof.
  intros txt o base. unfold flush_text.
  destruct (nonempty_str txt); [apply oemit_app | reflexivity].
Qed.

Lemma opush_app :
  forall k m o base,
    opush k m (oout_app base o) = oout_app base (opush k m o).
Proof. intros k m o base. reflexivity. Qed.

Lemma oclose_app :
  forall k m o base,
    oclose k m (oout_app base o)
    = option_map (oout_app base) (oclose k m o).
Proof.
  intros k m o base. unfold oclose. cbn [oout_app os_stk os_out].
  destruct (oclose_go k m [] (os_stk o)) as [[content rest]|]; [|reflexivity].
  cbn [option_map].
  rewrite <- (oemit_app (mk (dnode k (List.rev content)))
                (OState (os_out o) rest) base).
  reflexivity.
Qed.

Lemma ilead_app :
  forall c txt prev o base,
    ilead c txt prev (oout_app base o) = iout_app base (ilead c txt prev o).
Proof.
  intros c txt prev o base. unfold ilead.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c); [cbn [iout_app]; rewrite flush_text_app; reflexivity|].
  destruct (Ascii.eqb c lbrace); [reflexivity|].
  destruct (dstyle_of c); reflexivity.
Qed.

Lemma idelim_resolve_app :
  forall k txt cc marker next o base,
    idelim_resolve k txt cc marker next (oout_app base o)
    = iout_app base (idelim_resolve k txt cc marker next o).
Proof.
  intros k txt cc marker next o base.
  assert (Hdone : forall o', idelim_done k txt marker next (oout_app base o')
                             = iout_app base (idelim_done k txt marker next o')).
  { intros o'. unfold idelim_done.
    destruct (dbare k && negb marker && nonspace_at next)%bool;
      [cbn [iout_app]; rewrite flush_text_app, opush_app|]; reflexivity. }
  unfold idelim_resolve. destruct (cc || marker)%bool; [|apply Hdone].
  rewrite flush_text_app, oclose_app.
  destruct (oclose k marker (flush_text txt o)); [reflexivity | apply Hdone].
Qed.

Lemma iresolve_app :
  forall base st, iresolve (iout_app base st) = iout_app base (iresolve st).
Proof.
  intros base [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o];
    try reflexivity.
  apply idelim_resolve_app.
Qed.

Lemma istep_out_app :
  forall c base st, istep c (iout_app base st) = iout_app base (istep c st).
Proof.
  intros c base [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o];
    cbn [iout_app istep].
  - reflexivity.
  - apply ilead_app.
  - unfold ibrace_step. destruct (dstyle_of c);
      [cbn [iout_app]; rewrite flush_text_app, opush_app; reflexivity
      |apply ilead_app].
  - rewrite idelim_resolve_app. destruct (Ascii.eqb c rbrace); [reflexivity|].
    destruct (idelim_resolve k txt cc false (Some c) o)
      as [[] txt' prev' o'|? ? ?|? ? ? ?|? ?|? ? ? ?]; cbn [iout_app];
      try reflexivity.
    apply ilead_app.
  - destruct (is_tick c); reflexivity.
  - destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); [|reflexivity].
    rewrite (oemit_app (mk (Verbatim (trim_verb txt))) o base).
    apply ilead_app.
Qed.

Lemma iscan_str_out_app :
  forall s base st,
    iscan_str s (iout_app base st) = iout_app base (iscan_str s st).
Proof.
  induction s as [|c s IH]; intros base st; cbn [iscan_str]; [reflexivity|].
  rewrite istep_out_app. apply IH.
Qed.

Lemma ibreak_out_app :
  forall base st, ibreak (iout_app base st) = iout_app base (ibreak st).
Proof.
  intros base st. unfold ibreak. rewrite iresolve_app.
  destruct (iresolve st) as [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o];
    cbn [iout_app]; try reflexivity.
  1,2: rewrite flush_text_app, oemit_app; reflexivity.
  destruct (Nat.eqb run n); [|reflexivity].
  rewrite !oemit_app. reflexivity.
Qed.

Lemma iscan_lines_cons2 :
  forall x y rest st,
    iscan_lines (x :: y :: rest) st
    = iscan_lines (y :: rest) (ibreak (iscan_str x st)).
Proof. reflexivity. Qed.

Lemma iscan_lines_out_app :
  forall l base st,
    iscan_lines l (iout_app base st) = iout_app base (iscan_lines l st).
Proof.
  induction l as [|x [|y rest] IH]; intros base st; cbn [iscan_lines].
  - reflexivity.
  - apply iscan_str_out_app.
  - rewrite iscan_str_out_app, ibreak_out_app. apply IH.
Qed.

(* The one place the suffix is not entirely inert: flattening an
   abandoned scope merges a `Str` seam, and if the suffix began with a
   `Str` the merge would reach across into it.  It never does -- the
   suffix is always a previous line, whose most recent node is the
   `SoftBreak` that ended it -- so the hypothesis is discharged by
   construction rather than carried. *)
Lemma osnoc_nonstr :
  forall n out, starts_str out = false -> osnoc n out = (n :: out)%list.
Proof.
  intros n [|[a [|x xs] i] out'] H; try reflexivity.
  cbn [starts_str] in H. destruct n as [c [|y ys] j]; destruct i;
    try reflexivity; discriminate.
Qed.

Lemma oapp_one : forall n out, oapp [n] out = osnoc n out.
Proof. reflexivity. Qed.

Lemma oapp_cons2 :
  forall n m rest out, oapp (n :: m :: rest) out = (n :: oapp (m :: rest) out)%list.
Proof. reflexivity. Qed.

Lemma oapp_app :
  forall cur out base,
    starts_str base = false ->
    oapp cur (out ++ base)%list = (oapp cur out ++ base)%list.
Proof.
  induction cur as [|n cur IH]; intros out base Hb; [reflexivity|].
  destruct cur as [|m cur'].
  - rewrite !oapp_one. destruct out as [|x out']; cbn [app].
    + rewrite (osnoc_nonstr n base Hb). reflexivity.
    + destruct x as [a [|p ps] i]; [|reflexivity].
      destruct i; try reflexivity.
      destruct n as [c [|q qs] j]; [|reflexivity]. destruct j; reflexivity.
  - rewrite !oapp_cons2. cbn [app]. f_equal. apply (IH out base Hb).
Qed.

Lemma oflatten_app :
  forall stk pend bottom base,
    starts_str base = false ->
    oflatten pend stk (bottom ++ base)%list
    = (oflatten pend stk bottom ++ base)%list.
Proof.
  induction stk as [|f stk IH]; intros pend bottom base Hb;
    cbn [oflatten]; [apply oapp_app, Hb | apply IH, Hb].
Qed.

Lemma ofinish_out_app :
  forall base o,
    starts_str base = false ->
    ofinish (oout_app base o) = (ofinish o ++ base)%list.
Proof.
  intros base o Hb. unfold ofinish, oout_app; cbn [os_out os_stk].
  apply oflatten_app, Hb.
Qed.

Lemma ifinish_rev_out_app :
  forall base st,
    starts_str base = false ->
    ifinish_rev (iout_app base st) = (ifinish_rev st ++ base)%list.
Proof.
  intros base st Hb. unfold ifinish_rev, ifinish_ostate.
  rewrite iresolve_app.
  destruct (iresolve st) as [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o];
    cbn [iout_app].
  1,2: rewrite flush_text_app; apply ofinish_out_app, Hb.
  1,2: apply ofinish_out_app, Hb.
  - rewrite oemit_app. apply ofinish_out_app, Hb.
  - rewrite oemit_app. apply ofinish_out_app, Hb.
Qed.

Lemma ifinish_out_app :
  forall base st,
    starts_str base = false ->
    ifinish (iout_app base st) = (List.rev base ++ ifinish st)%list.
Proof.
  intros base st Hb. unfold ifinish.
  rewrite ifinish_rev_out_app by exact Hb.
  rewrite List.rev_app_distr. reflexivity.
Qed.

(* Parse one line's inline content.  Every construct of
   `.project/260811.inline-parser.md` lands here. *)
Definition parse_inline_line (s : string) : inlines := ifinish (iscan_str s istart).

Definition text_sep_ok (txt : string) (cis : list cinline) : bool :=
  match txt, cis with
  | String _ _, CIStr _ :: _ => false
  | _, _ => true
  end.

Lemma ifinish_text :
  forall txt prev out,
    ifinish (IText false txt prev (OState out []))
    = List.rev (os_out (flush_text txt (OState out []))).
Proof.
  intros txt prev out. unfold ifinish, ifinish_rev, ifinish_ostate, iresolve.
  unfold flush_text, oemit; cbn [os_stk os_out].
  destruct (nonempty_str txt); reflexivity.
Qed.

(* Canonical text never opens a verbatim: `needs_escape` claims the
   backtick, so `escape_str` emits none bare.  The scanner therefore
   stays in `IText` throughout, and this is the whole of what the
   roundtrip needs from it today. *)
Lemma ilead_plain :
  forall c txt prev o,
    needs_escape c = false ->
    ilead c txt prev o = IText false (txt ++ one c)%string prev o.
Proof.
  intros c txt prev o Hc. unfold needs_escape in Hc.
  apply orb_false_iff in Hc as [Hc Hrb].
  apply orb_false_iff in Hc as [Hc Hlb].
  apply orb_false_iff in Hc as [Hc Hdl].
  apply orb_false_iff in Hc as [Hbs Htk].
  unfold ilead. rewrite Hbs, Htk, Hlb.
  destruct (dstyle_of c) eqn:Hd; [|reflexivity].
  unfold is_delim in Hdl. rewrite Hd in Hdl. discriminate.
Qed.

(* Canonical text never leaves `IText`: `needs_escape` claims every
   character the scanner dispatches on -- the backslash, the backtick,
   the six delimiters and the two braces -- so `escape_str` emits none of
   them bare.  This is the whole of what the roundtrip needs from the
   scanner, and it is why adding a table row costs an escape and not a
   proof. *)
Lemma iscan_escape :
  forall s txt prev o,
    iscan_str (escape_str s) (IText false txt prev o)
    = IText false (txt ++ s)%string prev o.
Proof.
  induction s as [|c rest IH]; intros txt prev o.
  - cbn [escape_str iscan_str]. rewrite append_empty_r. reflexivity.
  - cbn [escape_str]. destruct (needs_escape c) eqn:Hc.
    + cbn [iscan_str istep]. unfold ilead.
      change (is_bslash "\"%char) with true. cbn [iscan_str istep].
      rewrite (needs_escape_punct c Hc).
      rewrite IH, append_assoc. reflexivity.
    + cbn [iscan_str istep]. rewrite (ilead_plain c txt prev o Hc).
      rewrite IH, append_assoc. reflexivity.
Qed.

Lemma iscan_escape_after_verb :
  forall s n body o,
    nonempty_str s = true ->
    iscan_str (escape_str s) (IVerb n n body o)
    = IText false s (Some tick) (oemit (mk (Verbatim (trim_verb body))) o).
Proof.
  intros [|c rest] n body o Hne; [discriminate|].
  cbn [escape_str]. destruct (needs_escape c) eqn:Hc.
  - cbn [iscan_str istep].
    change (is_tick "\"%char) with false. rewrite nat_eqb_refl.
    unfold ilead at 1. change (is_bslash "\"%char) with true.
    cbn [iscan_str istep]. rewrite (needs_escape_punct c Hc), iscan_escape.
    cbn [append one]. reflexivity.
  - cbn [iscan_str istep].
    replace (is_tick c) with false
      by (destruct (is_tick c) eqn:Ht;
          [rewrite (needs_escape_tick c Ht) in Hc; discriminate|reflexivity]).
    rewrite nat_eqb_refl, (ilead_plain c EmptyString (Some tick) _ Hc).
    rewrite iscan_escape. cbn [one append]. reflexivity.
Qed.

Lemma cis_ok_tail :
  forall c rest, cis_ok (c :: rest) = true -> cis_ok rest = true.
Proof.
  intros c rest H. unfold cis_ok in *. apply andb_true_iff in H as [Ha Hs].
  apply andb_true_iff. split.
  - cbn [forallb] in Ha. apply andb_true_iff in Ha as [_ Ha]. exact Ha.
  - destruct rest as [|r rest']; [reflexivity|].
    cbn [ci_sep_ok] in Hs. apply andb_true_iff in Hs as [_ Hs]. exact Hs.
Qed.

Lemma cis_ok_head :
  forall c rest, cis_ok (c :: rest) = true -> ci_ok c = true.
Proof.
  intros c rest H. unfold cis_ok in H. apply andb_true_iff in H as [H _].
  cbn [forallb] in H. apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma ci_str_tail_sep :
  forall s rest,
    cis_ok (CIStr s :: rest) = true -> nonempty_str s = true ->
    text_sep_ok s rest = true.
Proof.
  intros s [|r rest] H Hs; [unfold text_sep_ok; destruct s; reflexivity|].
  destruct r as [t|v]; [|unfold text_sep_ok; destruct s; reflexivity].
  unfold cis_ok in H. cbn [ci_sep_ok ci_pair_ok] in H.
  repeat rewrite andb_false_r in H. discriminate.
Qed.

Lemma ci_verb_next_str :
  forall v c rest,
    cis_ok (CIVerb v :: c :: rest) = true ->
    exists s, c = CIStr s.
Proof.
  intros v [s|w] rest H; [exists s; reflexivity|].
  unfold cis_ok in H. apply andb_true_iff in H as [_ H].
  cbn [ci_sep_ok ci_pair_ok] in H.
  apply andb_true_iff in H as [H _]. destruct v; discriminate.
Qed.

Lemma ci_verb_nonempty :
  forall v rest, cis_ok (CIVerb v :: rest) = true -> nonempty_str v = true.
Proof.
  intros v rest H. pose proof (cis_ok_head (CIVerb v) rest H) as Hv.
  cbn [ci_ok] in Hv. apply andb_true_iff in Hv as [Hv _]. exact Hv.
Qed.

Lemma ci_verb_content_ok :
  forall v rest, cis_ok (CIVerb v :: rest) = true -> verb_content_ok v = true.
Proof.
  intros v rest H. pose proof (cis_ok_head (CIVerb v) rest H) as Hv.
  cbn [ci_ok] in Hv. apply andb_true_iff in Hv as [_ Hv]. exact Hv.
Qed.

Lemma verb_content_safe :
  forall v, verb_content_ok v = true -> verb_safe (verb_ticks v) (pad_verb v) = true.
Proof.
  intros v H. unfold verb_content_ok in H.
  repeat rewrite andb_true_iff in H. destruct H as [[[_ _] _] H]. exact H.
Qed.

(* The canonical view has no delimiter yet, so a canonical line's scan
   never pushes a scope: these three run over `OState out []` and the
   stack plays no part.  When `cinline` gains a delimiter this is where
   the nesting induction goes. *)
Definition flush_out (txt : string) (out : inlines) : inlines :=
  if nonempty_str txt then mk (Str txt) :: out else out.

Lemma flush_text_flat :
  forall txt out, flush_text txt (OState out []) = OState (flush_out txt out) [].
Proof.
  intros txt out. unfold flush_text, flush_out, oemit; cbn [os_stk].
  destruct (nonempty_str txt); reflexivity.
Qed.

Lemma iscan_ci_after_verb :
  forall s rest prev n body out,
    nonempty_str s = true ->
    iscan_str (ci_text prev (CIStr s :: rest))
      (IVerb n n body (OState out []))
    = iscan_str (ci_text prev (CIStr s :: rest))
        (IText false EmptyString (Some tick)
           (OState (mk (Verbatim (trim_verb body)) :: out) [])).
Proof.
  intros s rest prev n body out Hs. cbn [ci_text].
  rewrite !iscan_str_app, iscan_escape_after_verb by exact Hs.
  rewrite iscan_escape. reflexivity.
Qed.

Lemma iscan_cis :
  forall cis prev prev' txt out,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    ifinish (iscan_str (ci_text prev cis)
               (IText false txt prev' (OState out [])))
    = (List.rev (flush_out txt out) ++ ci_inlines cis)%list.
Proof.
  induction cis as [|c rest IH]; intros prev prev' txt out Hok Hsep.
  - cbn [ci_text ci_inlines iscan_str]. rewrite app_nil_r.
    rewrite ifinish_text, flush_text_flat. reflexivity.
  - destruct c as [s|v].
    + destruct txt as [|x txt']; [|discriminate].
      cbn [ci_text]. rewrite iscan_str_app, iscan_escape.
      cbn [ci_inlines map append]. rewrite IH.
      * pose proof (cis_ok_head (CIStr s) rest Hok) as Hs.
        cbn [ci_ok] in Hs. apply andb_true_iff in Hs as [Hs _].
        unfold flush_out. rewrite Hs.
        cbn [List.rev nonempty_str ci_ast map].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * apply ci_str_tail_sep; [exact Hok|].
        pose proof (cis_ok_head (CIStr s) rest Hok) as Hs.
        cbn [ci_ok] in Hs. apply andb_true_iff in Hs as [Hs _]. exact Hs.
    + pose proof (ci_verb_nonempty v rest Hok) as Hvne.
      pose proof (ci_verb_content_ok v rest Hok) as Hvok.
      destruct rest as [|r rest'].
      * cbn [ci_text]. rewrite append_empty_r.
        unfold ci_inlines. cbn [map].
        rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
        rewrite flush_text_flat.
        unfold ifinish, ifinish_rev, ifinish_ostate, iresolve.
        rewrite nat_eqb_refl, trim_verb_pad by exact Hvok.
        unfold oemit, ofinish; cbn [os_stk os_out oflatten oapp].
        cbn [List.rev ci_ast]. reflexivity.
      * destruct (ci_verb_next_str v r rest' Hok) as [s Hr]. subst r.
        pose proof (cis_ok_head (CIStr s) rest'
                      (cis_ok_tail _ _ Hok)) as Hsok.
        cbn [ci_ok] in Hsok.
        apply andb_true_iff in Hsok as [Hs _].
        cbn [ci_text]. rewrite iscan_str_app.
        rewrite iscan_verb_text_nonempty
          by auto using verb_content_safe.
        rewrite flush_text_flat.
        change
          (ifinish
             (iscan_str
                (ci_text (str_last (verb_text v) prev) (CIStr s :: rest'))
                (IVerb (verb_ticks v) (verb_ticks v) (pad_verb v)
                   (OState (flush_out txt out) [])))
           = (List.rev (flush_out txt out)
              ++ ci_inlines (CIVerb v :: CIStr s :: rest'))%list).
        rewrite iscan_ci_after_verb by exact Hs.
        rewrite trim_verb_pad by exact Hvok.
        rewrite IH.
        -- unfold flush_out at 1. cbn [nonempty_str].
           cbn [ci_inlines map ci_ast List.rev].
           rewrite <- List.app_assoc. reflexivity.
        -- exact (cis_ok_tail _ _ Hok).
        -- reflexivity.
Qed.

(* The other half of what a canonical line owes the paragraph: it leaves
   the scan owing nothing to the next line.  Every canonical constituent
   either stays in `IText` (a string) or resolves its closing run before
   the line ends (a verbatim), which is exactly why the empty verbatim
   had to go: two adjacent runs leave `IOpen`. *)
Lemma iscan_cis_closed :
  forall cis prev prev' txt out,
    cis_ok cis = true ->
    iscan_closed (iscan_str (ci_text prev cis)
                    (IText false txt prev' (OState out []))) = true.
Proof.
  induction cis as [|c rest IH]; intros prev prev' txt out Hok; [reflexivity|].
  destruct c as [s|v].
  - cbn [ci_text]. rewrite iscan_str_app, iscan_escape.
    apply IH, (cis_ok_tail _ _ Hok).
  - pose proof (ci_verb_nonempty v rest Hok) as Hvne.
    pose proof (ci_verb_content_ok v rest Hok) as Hvok.
    cbn [ci_text]. rewrite iscan_str_app.
    rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
    rewrite flush_text_flat.
    destruct rest as [|r rest'].
    + cbn [ci_text iscan_str iscan_closed iresolve os_stk null].
      rewrite nat_eqb_refl. reflexivity.
    + destruct (ci_verb_next_str v r rest' Hok) as [s Hr]. subst r.
      pose proof (cis_ok_head (CIStr s) rest'
                    (cis_ok_tail _ _ Hok)) as Hsok.
      cbn [ci_ok] in Hsok. apply andb_true_iff in Hsok as [Hs _].
      rewrite iscan_ci_after_verb by exact Hs.
      apply IH, (cis_ok_tail _ _ Hok).
Qed.

(*
The scan is productive
----------------------

`Wf.v` needs that a nonempty line yields at least one inline, which the
old one-`Str`-per-line parser had by construction and a scanner does not.
The initial state is deliberately *un*productive, since empty input must
give no inlines; one character suffices. *)

(* Productive means: whatever follows, at least one inline comes out.
   `IText` with nothing pending and nothing emitted is the one state
   that fails it -- which is the start state, as it must be, since empty
   input yields no inlines.  An open scope counts as productive: it is
   abandoned at the end, and its opener becomes text. *)
Definition ostate_nonempty (o : ostate) : bool :=
  (nonempty (os_out o) || negb (null (os_stk o)))%bool.

Definition iscan_productive (st : iscan) : bool :=
  match st with
  | IText false txt _ o => (nonempty_str txt || ostate_nonempty o)%bool
  | _ => true
  end.

Lemma nonempty_str_app_l :
  forall a b, nonempty_str b = true -> nonempty_str (a ++ b)%string = true.
Proof. intros [|x a] b H; [exact H | reflexivity]. Qed.

Lemma nonempty_rev : forall (l : inlines), nonempty (List.rev l) = nonempty l.
Proof.
  intros [|n l]; [reflexivity|].
  cbn [List.rev nonempty]. destruct (List.rev l ++ [n])%list eqn:E; [|reflexivity].
  destruct (List.rev l); discriminate.
Qed.

Lemma ostate_nonempty_emit :
  forall n o, ostate_nonempty (oemit n o) = true.
Proof.
  intros n [out [|f stk]]; [reflexivity|].
  unfold ostate_nonempty, oemit; cbn [os_out os_stk null negb].
  apply orb_true_r.
Qed.

Lemma ostate_nonempty_flush :
  forall txt o,
    ostate_nonempty o = true -> ostate_nonempty (flush_text txt o) = true.
Proof.
  intros txt o H. unfold flush_text.
  destruct (nonempty_str txt); [apply ostate_nonempty_emit | exact H].
Qed.

Lemma ostate_nonempty_flush_str :
  forall txt o,
    nonempty_str txt = true -> ostate_nonempty (flush_text txt o) = true.
Proof.
  intros txt o H. unfold flush_text. rewrite H. apply ostate_nonempty_emit.
Qed.

Lemma ostate_nonempty_push :
  forall k m o, ostate_nonempty (opush k m o) = true.
Proof.
  intros k m o. unfold ostate_nonempty, opush; cbn [os_stk].
  rewrite orb_true_r. reflexivity.
Qed.

Lemma iscan_productive_lead :
  forall c txt prev o,
    (nonempty_str txt || ostate_nonempty o)%bool = true ->
    iscan_productive (ilead c txt prev o) = true.
Proof.
  intros c txt prev o H. unfold ilead.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c); [reflexivity|].
  destruct (Ascii.eqb c lbrace); [reflexivity|].
  destruct (dstyle_of c); [reflexivity|].
  cbn [iscan_productive]. apply orb_true_iff. left.
  apply nonempty_str_app_l. reflexivity.
Qed.

Lemma idelim_done_productive :
  forall k txt marker next o,
    iscan_productive (idelim_done k txt marker next o) = true
    /\ forall txt' prev' o',
         idelim_done k txt marker next o = IText false txt' prev' o' ->
         (nonempty_str txt' || ostate_nonempty o')%bool = true.
Proof.
  intros k txt marker next o. unfold idelim_done.
  destruct (dbare k && negb marker && nonspace_at next)%bool.
  - split.
    + cbn [iscan_productive]. rewrite ostate_nonempty_push. apply orb_true_r.
    + intros txt' prev' o' E. injection E as E1 E2. subst txt' o'.
      rewrite ostate_nonempty_push. apply orb_true_r.
  - assert (Hlit : nonempty_str (idelim_lit k txt marker) = true)
      by (unfold idelim_lit; apply nonempty_str_app_l; reflexivity).
    split.
    + cbn [iscan_productive]. rewrite Hlit. reflexivity.
    + intros txt' prev' o' E. injection E as E1 E2 E3. subst txt' o'.
      rewrite Hlit. reflexivity.
Qed.

Lemma idelim_resolve_productive :
  forall k txt cc marker next o,
    iscan_productive (idelim_resolve k txt cc marker next o) = true
    /\ forall txt' prev' o',
         idelim_resolve k txt cc marker next o = IText false txt' prev' o' ->
         (nonempty_str txt' || ostate_nonempty o')%bool = true.
Proof.
  intros k txt cc marker next o. unfold idelim_resolve.
  destruct (cc || marker)%bool; [|apply idelim_done_productive].
  destruct (oclose k marker (flush_text txt o)) as [o'|] eqn:Ec;
    [|apply idelim_done_productive].
  assert (Hne : ostate_nonempty o' = true).
  { unfold oclose in Ec.
    destruct (oclose_go k marker [] (os_stk (flush_text txt o)))
      as [[content rest]|]; [|discriminate].
    injection Ec as <-. apply ostate_nonempty_emit. }
  split.
  - cbn [iscan_productive]. rewrite Hne. apply orb_true_r.
  - intros txt' prev' o'' E. injection E as E1 E2. subst txt' o''.
    rewrite Hne. apply orb_true_r.
Qed.

(* Every way a pending delimiter can resolve lands back in text mode:
   closing, opening and decaying to literal text all do.  So after
   `iresolve` there is no `IBrace` and no `IDelim` left, which is what
   makes the catch-all arms of `ibreak` and `ifinish_ostate` dead. *)
Lemma idelim_done_text :
  forall k txt marker next o,
    exists txt' prev' o',
      idelim_done k txt marker next o = IText false txt' prev' o'.
Proof.
  intros k txt marker next o. unfold idelim_done.
  destruct (dbare k && negb marker && nonspace_at next)%bool; eauto.
Qed.

Lemma idelim_resolve_text :
  forall k txt cc marker next o,
    exists txt' prev' o',
      idelim_resolve k txt cc marker next o = IText false txt' prev' o'.
Proof.
  intros k txt cc marker next o. unfold idelim_resolve.
  destruct (cc || marker)%bool; [|apply idelim_done_text].
  destruct (oclose k marker (flush_text txt o));
    [eauto | apply idelim_done_text].
Qed.

Lemma iresolve_resolved :
  forall st,
    match iresolve st with
    | IBrace _ _ _ | IDelim _ _ _ _ => False
    | _ => True
    end.
Proof.
  intros [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o];
    cbn [iresolve]; try exact I.
  destruct (idelim_resolve_text k txt cc false None o) as [txt' [prev' [o' E]]].
  rewrite E. exact I.
Qed.

Lemma iscan_productive_resolve :
  forall st, iscan_productive st = true -> iscan_productive (iresolve st) = true.
Proof.
  intros [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o] H;
    cbn [iresolve]; try exact H; [|apply idelim_resolve_productive].
  cbn [iscan_productive]. apply orb_true_iff. left.
  apply nonempty_str_app_l. reflexivity.
Qed.

Lemma iscan_productive_step :
  forall c st, iscan_productive st = true -> iscan_productive (istep c st) = true.
Proof.
  intros c [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o] H;
    cbn [istep].
  - cbn [iscan_productive]. apply orb_true_iff. left.
    apply nonempty_str_app_l. destruct (is_punct c); reflexivity.
  - apply iscan_productive_lead, H.
  - unfold ibrace_step. destruct (dstyle_of c).
    + cbn [iscan_productive]. rewrite ostate_nonempty_push.
      apply orb_true_r.
    + apply iscan_productive_lead. apply orb_true_iff. left.
      apply nonempty_str_app_l. reflexivity.
  - (* whichever way the pending delimiter resolves, something is owed:
       either a scope is open, or its spelling is in the text buffer *)
    destruct (Ascii.eqb c rbrace);
      [apply (idelim_resolve_productive k txt cc true (Some c) o)|].
    destruct (idelim_resolve_productive k txt cc false (Some c) o) as [_ Ht].
    destruct (idelim_resolve_text k txt cc false (Some c) o)
      as [txt' [prev' [o' E]]].
    rewrite E. apply iscan_productive_lead, (Ht txt' prev' o' E).
  - destruct (is_tick c); reflexivity.
  - destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); [|reflexivity].
    apply iscan_productive_lead.
    rewrite ostate_nonempty_emit. apply orb_true_r.
Qed.

Lemma iscan_productive_str :
  forall s st, iscan_productive st = true ->
  iscan_productive (iscan_str s st) = true.
Proof.
  induction s as [|c rest IH]; intros st H; [exact H|].
  cbn [iscan_str]. apply IH, iscan_productive_step, H.
Qed.

(* Unconditional: a boundary either pushes a `SoftBreak` or leaves a
   state that is productive by construction, so every paragraph of two
   or more lines is productive whatever its first line held. *)
Lemma iscan_productive_break :
  forall st, iscan_productive (ibreak st) = true.
Proof.
  intros st. unfold ibreak.
  destruct (iresolve st) as [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o];
    cbn [iscan_productive]; try reflexivity.
  1,2: rewrite ostate_nonempty_emit; apply orb_true_r.
  destruct (Nat.eqb run n); cbn [iscan_productive]; [|reflexivity].
  rewrite ostate_nonempty_emit. apply orb_true_r.
Qed.

Lemma iscan_productive_lines :
  forall l st, iscan_productive st = true ->
  iscan_productive (iscan_lines l st) = true.
Proof.
  induction l as [|x [|y rest] IH]; intros st H; cbn [iscan_lines].
  - exact H.
  - apply iscan_productive_str, H.
  - apply IH, iscan_productive_break.
Qed.

Lemma nonempty_oapp :
  forall cur out, nonempty out = true -> nonempty (oapp cur out) = true.
Proof.
  induction cur as [|n cur IH]; intros out H; [exact H|].
  destruct cur as [|m cur']; [|rewrite oapp_cons2; reflexivity].
  rewrite oapp_one. destruct out as [|[a [|p ps] i] out']; [discriminate| |].
  - unfold osnoc. destruct i; try reflexivity.
    destruct n as [c [|q qs] j]; [|reflexivity]. destruct j; reflexivity.
  - unfold osnoc. destruct n as [c d j]; reflexivity.
Qed.

Lemma nonempty_oapp_l :
  forall cur out, nonempty cur = true -> nonempty (oapp cur out) = true.
Proof.
  intros [|x [|y cur']] out H; [discriminate| |rewrite oapp_cons2; reflexivity].
  rewrite oapp_one. destruct out as [|[a [|p ps] i] out']; try reflexivity.
  unfold osnoc. destruct i; try reflexivity.
  destruct x as [c [|q qs] j]; [|reflexivity]. destruct j; reflexivity.
Qed.

Lemma nonempty_oapp_snoc :
  forall cur n, nonempty (oapp cur [n]) = true.
Proof.
  intros cur n. destruct cur as [|x cur']; [reflexivity|].
  apply nonempty_oapp_l. reflexivity.
Qed.

(* Something comes out if anything is owed: content below, an open scope
   whose opener will decay to text, or a pending splice. *)
Lemma nonempty_oflatten :
  forall stk pend bottom,
    (nonempty bottom || negb (null stk) || nonempty pend)%bool = true ->
    nonempty (oflatten pend stk bottom) = true.
Proof.
  induction stk as [|f stk IH]; intros pend bottom H; cbn [oflatten].
  - cbn [null negb] in H. rewrite orb_false_r in H.
    apply orb_true_iff in H as [H|H];
      [apply nonempty_oapp, H | apply nonempty_oapp_l, H].
  - apply IH. rewrite nonempty_oapp_snoc, orb_true_r. reflexivity.
Qed.

Lemma nonempty_ofinish :
  forall o, ostate_nonempty o = true -> nonempty (ofinish o) = true.
Proof.
  intros o H. unfold ofinish. apply nonempty_oflatten.
  unfold ostate_nonempty in H. rewrite H. reflexivity.
Qed.

Lemma iscan_productive_finish :
  forall st, iscan_productive st = true -> nonempty (ifinish st) = true.
Proof.
  intros st H. unfold ifinish. rewrite nonempty_rev.
  unfold ifinish_rev, ifinish_ostate.
  pose proof (iscan_productive_resolve st H) as Hres.
  pose proof (iresolve_resolved st) as Hno.
  destruct (iresolve st) as
    [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o];
    try contradiction; apply nonempty_ofinish.
  - apply ostate_nonempty_flush_str, nonempty_str_app_l. reflexivity.
  - cbn [iscan_productive] in Hres.
    apply orb_true_iff in Hres as [Hres|Hres];
      [apply ostate_nonempty_flush_str, Hres
      |apply ostate_nonempty_flush, Hres].
  - apply ostate_nonempty_emit.
  - apply ostate_nonempty_emit.
Qed.

Lemma iscan_productive_first :
  forall c, iscan_productive (istep c istart) = true.
Proof.
  intros c. unfold istart. cbn [istep]. unfold ilead.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c); [reflexivity|].
  destruct (Ascii.eqb c lbrace); [reflexivity|].
  destruct (dstyle_of c); reflexivity.
Qed.

Lemma parse_inline_line_nonempty :
  forall s, nonempty_str s = true -> nonempty (parse_inline_line s) = true.
Proof.
  intros [|c rest] H; [discriminate|].
  unfold parse_inline_line. cbn [iscan_str].
  apply iscan_productive_finish, iscan_productive_str, iscan_productive_first.
Qed.

Lemma parse_inline_line_escape :
  forall s, nonempty_str s = true ->
  parse_inline_line (escape_str s) = [mk (Str s)].
Proof.
  intros s H. unfold parse_inline_line, istart. rewrite iscan_escape.
  change (EmptyString ++ s)%string with s.
  unfold ifinish, ifinish_rev, ifinish_ostate, iresolve, flush_text.
  rewrite H. reflexivity.
Qed.

(* A paragraph's lines, in order, into inlines: one scan, with `ibreak`
   between lines.  It was a scan per line joined by `SoftBreak` until
   spans were allowed to cross a break; the two agree exactly when no
   line leaves the scan mid-span, which is what the canonical view
   guarantees and `para_inlines_cons2_closed` states. *)
Definition para_inlines (l : list string) : inlines :=
  ifinish (iscan_lines l istart).

Lemma para_inlines_one :
  forall x, para_inlines [x] = parse_inline_line (strip_trailing_ws x).
Proof. reflexivity. Qed.

(* The old defining equation, now conditional: a line that leaves the
   scan mid-span does not contribute a separable run of inlines, because
   the span it opened is finished by a later line. *)
Lemma para_inlines_cons2_closed :
  forall x y rest,
    iscan_closed (iscan_str x istart) = true ->
    para_inlines (x :: y :: rest) =
    (parse_inline_line x ++ mk SoftBreak :: para_inlines (y :: rest))%list.
Proof.
  intros x y rest Hcl. unfold para_inlines, parse_inline_line.
  rewrite iscan_lines_cons2, (ibreak_closed _ Hcl).
  change (IText false EmptyString None
            (OState (mk SoftBreak :: ifinish_rev (iscan_str x istart)) []))
    with (iout_app (mk SoftBreak :: ifinish_rev (iscan_str x istart)) istart).
  rewrite iscan_lines_out_app, ifinish_out_app by reflexivity.
  cbn [List.rev]. rewrite <- List.app_assoc. reflexivity.
Qed.

(* The canonical view's paragraph, laid out the same way. *)
Fixpoint ci_para (lss : list (list cinline)) : inlines :=
  match lss with
  | [] => []
  | [cis] => ci_inlines cis
  | cis :: rest => (ci_inlines cis ++ mk SoftBreak :: ci_para rest)%list
  end.

Lemma ci_para_one : forall cis, ci_para [cis] = ci_inlines cis.
Proof. reflexivity. Qed.

Lemma ci_para_cons2 :
  forall cis cis2 rest,
    ci_para (cis :: cis2 :: rest)
    = (ci_inlines cis ++ mk SoftBreak :: ci_para (cis2 :: rest))%list.
Proof. reflexivity. Qed.

(*
The pass inverts the view
=========================
*)

(** Parsing a canonical line's text gives back its inlines. *)
Lemma parse_inline_line_ci :
  forall cis, cis_ok cis = true -> nonempty cis = true ->
  parse_inline_line (ci_line cis) = ci_inlines cis.
Proof.
  intros cis Hok Hne.
  unfold parse_inline_line, istart, ostart, ci_line.
  rewrite (iscan_cis cis None None EmptyString []).
  - reflexivity.
  - exact Hok.
  - reflexivity.
Qed.

(** The same, a paragraph at a time.  The last hypothesis is `para_ok`'s
    trailing-whitespace conjunct: `para_inlines` strips the final line,
    so the two agree exactly when there is nothing to strip. *)
Lemma para_inlines_ci_para :
  forall lss,
    forallb cis_ok lss = true ->
    forallb nonempty lss = true ->
    strip_trailing_ws (last (map ci_line lss) EmptyString)
      = last (map ci_line lss) EmptyString ->
    para_inlines (map ci_line lss) = ci_para lss.
Proof.
  induction lss as [|cis rest IH]; intros Hok Hne Hlast; [reflexivity|].
  cbn [forallb] in Hok, Hne.
  apply andb_true_iff in Hok as [Hc Hr].
  apply andb_true_iff in Hne as [Hn Hnr].
  destruct rest as [|cis2 rest'].
  - cbn [map last] in Hlast |- *.
    rewrite para_inlines_one, Hlast.
    change (parse_inline_line (ci_line cis) = ci_para [cis]).
    rewrite ci_para_one. apply parse_inline_line_ci; assumption.
  - cbn [map] in *.
    rewrite para_inlines_cons2_closed
      by (unfold ci_line, istart; apply iscan_cis_closed, Hc).
    rewrite ci_para_cons2, (parse_inline_line_ci cis Hc Hn).
    f_equal. f_equal.
    apply IH; [exact Hr | exact Hnr |].
    rewrite last_cons_nonnil in Hlast by discriminate. exact Hlast.
Qed.

(*
The renderer
============
*)

(* Recover the lines of a paragraph from its inlines: `Str` extends the
   current line, `SoftBreak` ends it. *)
Fixpoint inline_lines (ils : inlines) (cur : string) : list string :=
  match ils with
  | [] => [cur]
  | Node _ _ (Str s) :: rest => inline_lines rest (cur ++ escape_str s)
  | Node _ _ (Verbatim s) :: rest => inline_lines rest (cur ++ verb_text s)
  | Node _ _ SoftBreak :: rest => cur :: inline_lines rest EmptyString
  | _ :: rest => inline_lines rest cur
  end.

Lemma inline_lines_softbreak :
  forall rest cur,
    inline_lines (mk SoftBreak :: rest) cur = cur :: inline_lines rest EmptyString.
Proof. reflexivity. Qed.

(** Rendering a canonical line's inlines appends its text and consumes
    nothing else, which is what makes the paragraph case an induction. *)
Lemma inline_lines_ci_inlines :
  forall cis cur rest,
    cis_ok cis = true -> nonempty cis = true ->
    inline_lines (ci_inlines cis ++ rest)%list cur
    = inline_lines rest (cur ++ ci_line cis).
Proof.
  intros cis cur rest Hok Hne. clear Hok Hne.
  induction cis as [|c cs IH] in cur |- *.
  - cbn [ci_inlines ci_line ci_text app inline_lines].
    rewrite append_empty_r. reflexivity.
  - destruct c as [s|v];
      cbn [ci_inlines ci_ast mk map app inline_lines ci_line ci_text].
    + rewrite IH.
      rewrite (ci_text_prev cs (str_last (escape_str s) None) None).
      unfold ci_line. rewrite append_assoc. reflexivity.
    + rewrite IH.
      rewrite (ci_text_prev cs (str_last (verb_text v) None) None).
      unfold ci_line. rewrite append_assoc. reflexivity.
Qed.

Lemma inline_lines_ci_para :
  forall rest cis cur,
    forallb cis_ok (cis :: rest) = true ->
    forallb nonempty (cis :: rest) = true ->
    inline_lines (ci_para (cis :: rest)) cur
    = (cur ++ ci_line cis) :: map ci_line rest.
Proof.
  induction rest as [|cis2 rest' IH]; intros cis cur Hok Hne;
    cbn [forallb] in Hok, Hne;
    apply andb_true_iff in Hok as [Hc Hr];
    apply andb_true_iff in Hne as [Hn Hnr].
  - rewrite ci_para_one. cbn [map].
    rewrite <- (app_nil_r (ci_inlines cis)).
    rewrite inline_lines_ci_inlines by assumption.
    reflexivity.
  - rewrite ci_para_cons2.
    rewrite inline_lines_ci_inlines by assumption.
    rewrite inline_lines_softbreak.
    rewrite IH by assumption.
    reflexivity.
Qed.

(** The renderer emits exactly the canonical lines. *)
Corollary inline_lines_ci :
  forall lss,
    forallb cis_ok lss = true -> forallb nonempty lss = true ->
    nonempty lss = true ->
    inline_lines (ci_para lss) EmptyString = map ci_line lss.
Proof.
  intros [|cis rest] Hok Hne Hlss; [discriminate|].
  rewrite inline_lines_ci_para by assumption. reflexivity.
Qed.

(*
Escapes, pinned
===============
*)

(* The scanner accepts any punctuation after a backslash... *)
Example escaped_punct_literal : parse_inline_line "\*" = [mk (Str "*")].
Proof. reflexivity. Qed.

(* ...and leaves a backslash before anything else alone. *)
Example escaped_nonpunct_literal : parse_inline_line "\a" = [mk (Str "\a")].
Proof. reflexivity. Qed.

(* A backtick in a `Str` is escaped, so it does not open a verbatim... *)
Example escaped_tick_literal : parse_inline_line "\`a\`" = [mk (Str "`a`")].
Proof. reflexivity. Qed.

(* ...while a bare one does, and a run of the wrong width is content. *)
Example verbatim_basic : parse_inline_line "`a`" = [mk (Verbatim "a")].
Proof. reflexivity. Qed.

Example verbatim_wrong_width_is_content :
  parse_inline_line "` `` `" = [mk (Verbatim "``")].
Proof. reflexivity. Qed.

Example verbatim_unclosed_closes_at_eol :
  parse_inline_line "`a" = [mk (Verbatim "a")].
Proof. reflexivity. Qed.

(* The encoder emits only what `needs_escape` names, which is why a
   comma renders bare where a backslash does not.  Matching djot.js,
   which renders `\,` back as `,`. *)
Example escape_backslash : escape_str "a\b" = "a\\b".
Proof. reflexivity. Qed.

Example escape_leaves_punct : escape_str "a,b" = "a,b".
Proof. reflexivity. Qed.

(* ...but a delimiter the table claims is escaped, like the backtick. *)
Example escape_delims : escape_str "a*b_c{d}" = "a\*b\_c\{d\}".
Proof. reflexivity. Qed.

(*
Canonical verbatim, pinned
==========================
*)

Example verb_ticks_examples :
  (verb_ticks "a", verb_ticks "`", verb_ticks "``", verb_ticks "` ``")
  = (1, 2, 1, 3).
Proof. vm_compute. reflexivity. Qed.

Example verbatim_render_tick : ci_line [CIVerb "`"] = "`` ` ``".
Proof. vm_compute. reflexivity. Qed.

Example verbatim_mixed_roundtrip :
  parse_inline_line (ci_line [CIStr "a"; CIVerb "`"; CIStr "*"])
  = ci_inlines [CIStr "a"; CIVerb "`"; CIStr "*"].
Proof. vm_compute. reflexivity. Qed.

(* The byte after a delayed closer is dispatched normally: here it is
   the backslash that protects a literal backtick. *)
Example verbatim_then_escaped_tick :
  parse_inline_line (ci_line [CIVerb "v"; CIStr "`"])
  = ci_inlines [CIVerb "v"; CIStr "`"].
Proof. vm_compute. reflexivity. Qed.

(* The empty verbatim is outside the view: its two runs are separated by
   nothing, so only the end of the paragraph closes it. *)
Example empty_verbatim_not_canonical : ci_ok (CIVerb EmptyString) = false.
Proof. reflexivity. Qed.

(*
Spans cross a line break
========================
*)

(* A verbatim opened on one line closes on the next, with the break as
   content -- matching djot.js, which scans the newline as an ordinary
   character.  It was two spans and a stray empty one before the scan was
   threaded through the paragraph. *)
Example verbatim_crosses_break :
  para_inlines ["`a"; "b`"] = [mk (Verbatim "a
b")].
Proof. vm_compute. reflexivity. Qed.

(* And the ordinary case still splits at the break. *)
Example text_breaks_at_line_end :
  para_inlines ["a"; "b"] = [mk (Str "a"); mk SoftBreak; mk (Str "b")].
Proof. vm_compute. reflexivity. Qed.

(* A delimiter span crosses one too. *)
Example emph_crosses_break :
  para_inlines ["_a"; "b_"]
  = [mk (Emph [mk (Str "a"); mk SoftBreak; mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

(*
The delimiter family, pinned
============================

Every one of these was checked against djot.js before it was written.
*)

(* Bare and braced spell the same span... *)
Example emph_bare : parse_inline_line "_a_" = [mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example emph_braced : parse_inline_line "{_a_}" = [mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

(* ...but the marking is part of the key, so a braced opener is not
   closed by a bare delimiter, and the whole thing decays to text. *)
Example emph_marked_needs_marked_closer :
  parse_inline_line "{_a_" = [mk (Str "{_a_")].
Proof. vm_compute. reflexivity. Qed.

(* `can_open` is a nonspace to the right, `can_close` a nonspace to the
   left, so a delimiter against a space is literal. *)
Example emph_open_needs_nonspace :
  parse_inline_line "_ a_" = [mk (Str "_ a_")].
Proof. vm_compute. reflexivity. Qed.

(* ...and the brace overrides both, which is the point of the marker. *)
Example braced_keeps_the_space :
  parse_inline_line "{_ a_}" = [mk (Emph [mk (Str " a")])].
Proof. vm_compute. reflexivity. Qed.

(* Doubling is nesting, not a second construct.  This is the fact that
   makes `__` for strong a *different table*, not an extension of this
   one (`.project/260811.inline-parser.md` §0.1). *)
Example doubled_is_nested :
  parse_inline_line "__a__" = [mk (Emph [mk (Emph [mk (Str "a")])])].
Proof. vm_compute. reflexivity. Qed.

(* An opener the closer spans is abandoned: its source becomes text, and
   its content splices into the scope that closed.  This is the stack's
   half of djot.js's `clearOpeners`. *)
Example abandoned_opener_becomes_text :
  parse_inline_line "_a*b_" = [mk (Emph [mk (Str "a*b")])].
Proof. vm_compute. reflexivity. Qed.

(* An opener that never closes decays the same way, merging with the text
   on both sides so no two `Str` nodes end up adjacent. *)
Example unclosed_opener_merges :
  parse_inline_line "a*b" = [mk (Str "a*b")].
Proof. vm_compute. reflexivity. Qed.

(* The two rows that only exist braced: a bare `=` or `+` is text. *)
Example mark_needs_braces :
  (parse_inline_line "=a=", parse_inline_line "{=a=}")
  = ([mk (Str "=a=")], [mk (Highlight [mk (Str "a")])]).
Proof. vm_compute. reflexivity. Qed.

(* An empty span is not a span: djot.js excludes a closer that sits
   immediately after its opener. *)
Example empty_span_is_text :
  parse_inline_line "{__}" = [mk (Str "{__}")].
Proof. vm_compute. reflexivity. Qed.

(* Verbatim is a mode, not a row: while one is open the table is
   suppressed entirely. *)
Example verbatim_suppresses_delimiters :
  parse_inline_line "`_a_`" = [mk (Verbatim "_a_")].
Proof. vm_compute. reflexivity. Qed.
