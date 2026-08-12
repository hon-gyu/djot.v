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

Definition needs_escape (c : ascii) : bool := (is_bslash c || is_tick c)%bool.

(* Obligation 1: an escaped character must be one the decoder accepts. *)
Lemma needs_escape_punct : forall c, needs_escape c = true -> is_punct c = true.
Proof.
  intros c H. unfold needs_escape, is_bslash, is_tick in H.
  apply orb_true_iff in H as [H|H]; apply Ascii.eqb_eq in H; subst; reflexivity.
Qed.

(* Obligation 2: the escape character escapes itself, or a text ending in
   a backslash would decode as an escape of whatever followed. *)
Lemma needs_escape_backslash : needs_escape "\"%char = true.
Proof. reflexivity. Qed.

(* Obligation 3: a backtick in a `Str` must not reach the scanner bare,
   or it would open a verbatim span instead of standing for itself.  This
   is the obligation every delimiter character will add. *)
Lemma needs_escape_tick : forall c, is_tick c = true -> needs_escape c = true.
Proof. intros c H. unfold needs_escape. rewrite H. apply orb_true_r. Qed.

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

Inductive iscan : Type :=
  (* accumulating literal text; `esc` is a pending backslash *)
  | IText (esc : bool) (txt : string) (out : inlines)
  (* counting an opening backtick run *)
  | IOpen (n : nat) (out : inlines)
  (* inside a width-`n` verbatim, with `run` unresolved trailing ticks *)
  | IVerb (n run : nat) (txt : string) (out : inlines).

Definition one (c : ascii) : string := String c EmptyString.

Lemma nat_eqb_refl : forall n, Nat.eqb n n = true.
Proof. induction n; [reflexivity|exact IHn]. Qed.

Definition flush_text (txt : string) (out : inlines) : inlines :=
  if nonempty_str txt then mk (Str txt) :: out else out.

Definition itext_step (c : ascii) (txt : string) (out : inlines) : iscan :=
  if is_bslash c then IText true txt out
  else if is_tick c then IOpen 1 (flush_text txt out)
  else IText false (txt ++ one c)%string out.

Definition istep (c : ascii) (st : iscan) : iscan :=
  match st with
  | IText true txt out =>
      IText false (txt ++ (if is_punct c then one c
                           else String "\"%char (one c)))%string out
  | IText false txt out => itext_step c txt out
  | IOpen n out =>
      if is_tick c then IOpen (S n) out else IVerb n 0 (one c) out
  | IVerb n run txt out =>
      if is_tick c then IVerb n (S run) txt out
      else if Nat.eqb run n
      then itext_step c EmptyString (mk (Verbatim (trim_verb txt)) :: out)
      else IVerb n 0 (txt ++ ticks run ++ one c)%string out
  end.

(* End of line.  An unclosed verbatim closes here, as djot.js does in
   `getMatches`.  A pending backslash is a literal backslash, which is
   djoths's reading; djot.js makes it a hard break, an already-logged
   disagreement (`escapes.test:30`).  Neither can arise from a canonical
   rendering, since `escape_str` never emits a bare backslash. *)
Definition ifinish_rev (st : iscan) : inlines :=
  match st with
  | IText true txt out =>
      flush_text (txt ++ String "\"%char EmptyString)%string out
  | IText false txt out => flush_text txt out
  | IOpen _ out => mk (Verbatim EmptyString) :: out
  | IVerb n run txt out =>
      if Nat.eqb run n
      then mk (Verbatim (trim_verb txt)) :: out
      else mk (Verbatim (trim_verb (txt ++ ticks run)%string)) :: out
  end.

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
  match st with
  | IText true txt out =>
      IText false EmptyString
        (mk SoftBreak :: flush_text (txt ++ one bslash)%string out)
  | IText false txt out =>
      IText false EmptyString (mk SoftBreak :: flush_text txt out)
  | IOpen n out => IVerb n 0 nl out
  | IVerb n run txt out =>
      if Nat.eqb run n
      then IText false EmptyString
             (mk SoftBreak :: mk (Verbatim (trim_verb txt)) :: out)
      else IVerb n 0 (txt ++ ticks run ++ nl)%string out
  end.

(* A state that owes nothing to the next line: every construct it has
   seen is resolved, so the boundary just ends the line and `ibreak`
   agrees with `ifinish` on what was emitted.  The two states that fail
   it are the ones a span crosses a break in: a backtick run still being
   counted, and a verbatim whose closer has not arrived. *)
Definition iscan_closed (st : iscan) : bool :=
  match st with
  | IText _ _ _ => true
  | IOpen _ _ => false
  | IVerb n run _ _ => Nat.eqb run n
  end.

Lemma ibreak_closed :
  forall st,
    iscan_closed st = true ->
    ibreak st = IText false EmptyString (mk SoftBreak :: ifinish_rev st).
Proof.
  intros [[] txt out|n out|n run txt out] H;
    cbn [ibreak ifinish_rev iscan_closed] in *; try reflexivity; [discriminate|].
  rewrite H. reflexivity.
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
  forall k txt out,
    iscan_str (ticks (S k)) (IText false txt out)
    = IOpen (S k) (flush_text txt out).
Proof.
  intros k txt out. cbn [ticks iscan_str istep]. change
    (iscan_str (ticks k) (IOpen 1 (flush_text txt out))
     = IOpen (S k) (flush_text txt out)).
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
  forall s txt out,
    nonempty_str s = true ->
    verb_safe (verb_ticks s) (pad_verb s) = true ->
    iscan_str (verb_text s) (IText false txt out)
    = IVerb (verb_ticks s) (verb_ticks s) (pad_verb s)
        (flush_text txt out).
Proof.
  intros s txt out Hne Hsafe. unfold verb_text.
  rewrite !iscan_str_app.
  destruct (verb_ticks s) as [|k] eqn:Hn;
    [exfalso; apply (verb_ticks_nonzero s); exact Hn|].
  rewrite iscan_open_ticks.
  unfold verb_safe in Hsafe.
  rewrite (iscan_open_body (pad_verb s) (S k) (flush_text txt out)
             (pad_verb_nonempty s Hne) (pad_verb_starts_nontick s Hne))
    by discriminate.
  rewrite (iscan_verb_safe_nonempty (pad_verb s) (S k) 0 EmptyString
             (flush_text txt out) (pad_verb_nonempty s Hne)
             (pad_verb_ends_nontick s Hne) Hsafe).
  change (iscan_str (ticks (S k))
            (IVerb (S k) 0 (pad_verb s) (flush_text txt out))
          = IVerb (S k) (S k) (pad_verb s) (flush_text txt out)).
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

Definition istart : iscan := IText false EmptyString [].

Definition iout_app (base : inlines) (st : iscan) : iscan :=
  match st with
  | IText esc txt out => IText esc txt (out ++ base)%list
  | IOpen n out => IOpen n (out ++ base)%list
  | IVerb n run txt out => IVerb n run txt (out ++ base)%list
  end.

Lemma flush_text_app :
  forall txt out base,
    flush_text txt (out ++ base)%list = (flush_text txt out ++ base)%list.
Proof.
  intros txt out base. unfold flush_text.
  destruct (nonempty_str txt); reflexivity.
Qed.

Lemma itext_step_out_app :
  forall c txt out base,
    itext_step c txt (out ++ base)%list = iout_app base (itext_step c txt out).
Proof.
  intros c txt out base. unfold itext_step.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c); cbn [iout_app]; [rewrite flush_text_app|]; reflexivity.
Qed.

Lemma istep_out_app :
  forall c base st, istep c (iout_app base st) = iout_app base (istep c st).
Proof.
  intros c base [[] txt out|n out|n run txt out]; cbn [iout_app istep].
  - reflexivity.
  - apply itext_step_out_app.
  - destruct (is_tick c); reflexivity.
  - destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); [|reflexivity].
    change (mk (Verbatim (trim_verb txt)) :: (out ++ base))%list
      with ((mk (Verbatim (trim_verb txt)) :: out) ++ base)%list.
    apply itext_step_out_app.
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
  intros base [[] txt out|n out|n run txt out]; cbn [iout_app ibreak].
  1,2: rewrite flush_text_app; reflexivity.
  - reflexivity.
  - destruct (Nat.eqb run n); reflexivity.
Qed.

Lemma iscan_lines_one :
  forall x st, iscan_lines [x] st = iscan_str (strip_trailing_ws x) st.
Proof. reflexivity. Qed.

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

Lemma ifinish_rev_out_app :
  forall base st,
    ifinish_rev (iout_app base st) = (ifinish_rev st ++ base)%list.
Proof.
  intros base [[] txt out|n out|n run txt out]; cbn [ifinish_rev iout_app].
  1,2: apply flush_text_app.
  - reflexivity.
  - destruct (Nat.eqb run n); reflexivity.
Qed.

Lemma ifinish_out_app :
  forall base st, ifinish (iout_app base st) = (List.rev base ++ ifinish st)%list.
Proof.
  intros base st. unfold ifinish.
  rewrite ifinish_rev_out_app, List.rev_app_distr. reflexivity.
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
  forall txt out,
    ifinish (IText false txt out) = List.rev (flush_text txt out).
Proof. reflexivity. Qed.

Lemma rev_flush_verb_str :
  forall s v txt out,
    nonempty_str s = true ->
    List.rev (flush_text s (mk (Verbatim v) :: flush_text txt out))
    = (List.rev (flush_text txt out) ++ [mk (Verbatim v); mk (Str s)])%list.
Proof.
  intros s v txt out Hs. unfold flush_text. rewrite Hs.
  destruct (nonempty_str txt); cbn [List.rev].
  all: rewrite <- List.app_assoc; reflexivity.
Qed.

(* Canonical text never opens a verbatim: `needs_escape` claims the
   backtick, so `escape_str` emits none bare.  The scanner therefore
   stays in `IText` throughout, and this is the whole of what the
   roundtrip needs from it today. *)
Lemma iscan_escape :
  forall s txt out,
    iscan_str (escape_str s) (IText false txt out)
    = IText false (txt ++ s)%string out.
Proof.
  induction s as [|c rest IH]; intros txt out.
  - cbn [escape_str iscan_str]. rewrite append_empty_r. reflexivity.
  - cbn [escape_str]. destruct (needs_escape c) eqn:Hc.
    + simpl. rewrite (needs_escape_punct c Hc).
      rewrite IH, append_assoc. reflexivity.
    + cbn [iscan_str istep itext_step].
      unfold itext_step.
      replace (is_bslash c) with false
        by (destruct (is_bslash c) eqn:Hb; [|reflexivity];
            unfold needs_escape in Hc; rewrite Hb in Hc; discriminate).
      replace (is_tick c) with false
        by (destruct (is_tick c) eqn:Ht;
            [rewrite (needs_escape_tick c Ht) in Hc; discriminate | reflexivity]).
      rewrite IH, append_assoc. reflexivity.
Qed.

Lemma iscan_escape_after_verb :
  forall s n body out,
    nonempty_str s = true ->
    iscan_str (escape_str s) (IVerb n n body out)
    = IText false s (mk (Verbatim (trim_verb body)) :: out).
Proof.
  intros [|c rest] n body out Hne; [discriminate|].
  cbn [escape_str]. destruct (needs_escape c) eqn:Hc.
  - cbn [iscan_str istep].
    replace (is_tick "\"%char) with false by reflexivity.
    rewrite nat_eqb_refl. unfold itext_step.
    replace (is_bslash "\"%char) with true by reflexivity.
    cbn [iscan_str istep]. rewrite (needs_escape_punct c Hc), iscan_escape.
    cbn [append one]. reflexivity.
  - cbn [iscan_str istep]. rewrite nat_eqb_refl. unfold itext_step.
    replace (is_bslash c) with false
      by (destruct (is_bslash c) eqn:Hb; [|reflexivity];
          unfold needs_escape in Hc; rewrite Hb in Hc; discriminate).
    replace (is_tick c) with false
      by (destruct (is_tick c) eqn:Ht;
          [rewrite (needs_escape_tick c Ht) in Hc; discriminate|reflexivity]).
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

Lemma iscan_ci_after_verb :
  forall s rest prev n body out,
    nonempty_str s = true ->
    iscan_str (ci_text prev (CIStr s :: rest)) (IVerb n n body out)
    = iscan_str (ci_text prev (CIStr s :: rest))
        (IText false EmptyString (mk (Verbatim (trim_verb body)) :: out)).
Proof.
  intros s rest prev n body out Hs. cbn [ci_text].
  rewrite !iscan_str_app, iscan_escape_after_verb by exact Hs.
  rewrite iscan_escape. reflexivity.
Qed.

Lemma iscan_cis :
  forall cis prev txt out,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    ifinish (iscan_str (ci_text prev cis) (IText false txt out))
    = (List.rev (flush_text txt out) ++ ci_inlines cis)%list.
Proof.
  induction cis as [|c rest IH]; intros prev txt out Hok Hsep.
  - cbn [ci_text ci_inlines iscan_str]. rewrite app_nil_r. reflexivity.
  - destruct c as [s|v].
    + destruct txt as [|x txt']; [|discriminate].
      cbn [ci_text]. rewrite iscan_str_app, iscan_escape.
      cbn [ci_inlines map append]. rewrite IH.
      * unfold flush_text.
        pose proof (cis_ok_head (CIStr s) rest Hok) as Hs.
        cbn [ci_ok] in Hs. apply andb_true_iff in Hs as [Hs _].
        rewrite Hs. cbn [List.rev nonempty_str ci_ast map flush_text].
        change (((List.rev out ++ [mk (Str s)]) ++ ci_inlines rest)%list
                = (List.rev out ++ ([mk (Str s)] ++ ci_inlines rest))%list).
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
        unfold ifinish, ifinish_rev.
        rewrite nat_eqb_refl, trim_verb_pad by exact Hvok.
        cbn [List.rev ci_ast]. reflexivity.
      * destruct (ci_verb_next_str v r rest' Hok) as [s Hr]. subst r.
        pose proof (cis_ok_head (CIStr s) rest'
                      (cis_ok_tail _ _ Hok)) as Hsok.
        cbn [ci_ok] in Hsok.
        apply andb_true_iff in Hsok as [Hs _].
        cbn [ci_text]. rewrite iscan_str_app.
        rewrite iscan_verb_text_nonempty.
        -- change
             (ifinish
                (iscan_str
                   (ci_text (str_last (verb_text v) prev) (CIStr s :: rest'))
                   (IVerb (verb_ticks v) (verb_ticks v) (pad_verb v)
                      (flush_text txt out)))
              = (List.rev (flush_text txt out)
                 ++ ci_inlines (CIVerb v :: CIStr s :: rest'))%list).
           rewrite iscan_ci_after_verb by exact Hs.
           rewrite trim_verb_pad by exact Hvok.
           rewrite IH.
           ++ cbn [flush_text nonempty_str ci_inlines map ci_ast List.rev].
              change
                (((List.rev (flush_text txt out) ++ [mk (Verbatim v)])
                   ++ (mk (Str s) :: map ci_ast rest'))%list
                 = (List.rev (flush_text txt out)
                    ++ ([mk (Verbatim v)]
                        ++ (mk (Str s) :: map ci_ast rest')))%list).
              rewrite <- List.app_assoc. reflexivity.
           ++ exact (cis_ok_tail _ _ Hok).
           ++ reflexivity.
        -- exact Hvne.
        -- exact (verb_content_safe v Hvok).
Qed.

(* The other half of what a canonical line owes the paragraph: it leaves
   the scan owing nothing to the next line.  Every canonical constituent
   either stays in `IText` (a string) or resolves its closing run before
   the line ends (a verbatim), which is exactly why the empty verbatim
   had to go: two adjacent runs leave `IOpen`. *)
Lemma iscan_cis_closed :
  forall cis prev txt out,
    cis_ok cis = true ->
    iscan_closed (iscan_str (ci_text prev cis) (IText false txt out)) = true.
Proof.
  induction cis as [|c rest IH]; intros prev txt out Hok; [reflexivity|].
  destruct c as [s|v].
  - cbn [ci_text]. rewrite iscan_str_app, iscan_escape.
    apply IH, (cis_ok_tail _ _ Hok).
  - pose proof (ci_verb_nonempty v rest Hok) as Hvne.
    pose proof (ci_verb_content_ok v rest Hok) as Hvok.
    cbn [ci_text]. rewrite iscan_str_app.
    rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
    destruct rest as [|r rest'].
    + cbn [ci_text iscan_str iscan_closed]. apply nat_eqb_refl.
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

Definition iscan_productive (st : iscan) : bool :=
  match st with
  | IText false txt out => (nonempty_str txt || nonempty out)%bool
  | _ => true
  end.

Lemma nonempty_rev : forall (l : inlines), nonempty (List.rev l) = nonempty l.
Proof.
  intros [|n l]; [reflexivity|].
  cbn [List.rev nonempty]. destruct (List.rev l ++ [n])%list eqn:E; [|reflexivity].
  destruct (List.rev l); discriminate.
Qed.

Lemma iscan_productive_step :
  forall c st, iscan_productive st = true -> iscan_productive (istep c st) = true.
Proof.
  intros c [[] txt out|n out|n run txt out] H;
    cbn [istep itext_step iscan_productive].
  - destruct (is_punct c); cbn [iscan_productive];
      rewrite ?nonempty_str_append_r; try reflexivity;
      apply orb_true_iff; left;
      destruct txt; reflexivity.
  - unfold itext_step. destruct (is_bslash c); [reflexivity|].
    destruct (is_tick c); [reflexivity|].
    cbn [iscan_productive]. apply orb_true_iff. left.
    destruct txt; reflexivity.
  - destruct (is_tick c); reflexivity.
  - destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); cbn [itext_step iscan_productive].
    + unfold itext_step. destruct (is_bslash c); [reflexivity|].
      destruct (is_tick c); [reflexivity|].
      apply orb_true_iff. left. reflexivity.
    + reflexivity.
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
  intros [[] txt out|n out|n run txt out]; cbn [ibreak]; try reflexivity.
  destruct (Nat.eqb run n); reflexivity.
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

Lemma iscan_productive_finish :
  forall st, iscan_productive st = true -> nonempty (ifinish st) = true.
Proof.
  intros [[] txt out|n out|n run txt out] H; unfold ifinish;
    rewrite nonempty_rev; cbn [ifinish_rev]; unfold flush_text.
  - destruct (nonempty_str (txt ++ String "\"%char EmptyString)) eqn:E;
      [reflexivity|].
    destruct txt; discriminate.
  - cbn [iscan_productive] in H. apply orb_true_iff in H as [H|H].
    + rewrite H. reflexivity.
    + destruct (nonempty_str txt); [reflexivity | exact H].
  - reflexivity.
  - destruct (Nat.eqb run n); reflexivity.
Qed.

Lemma iscan_productive_first :
  forall c, iscan_productive (istep c (IText false EmptyString [])) = true.
Proof.
  intros c. cbn [istep itext_step]. unfold itext_step.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c); reflexivity.
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
  unfold ifinish, ifinish_rev, flush_text. rewrite H. reflexivity.
Qed.

(* A paragraph's lines, in order, into inlines: one scan, with `ibreak`
   between lines.  It was a scan per line joined by `SoftBreak` until
   spans were allowed to cross a break; the two agree exactly when no
   line leaves the scan mid-span, which is what the canonical view
   guarantees and `para_inlines_cons2_clean` states. *)
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
  change (IText false EmptyString
            (mk SoftBreak :: ifinish_rev (iscan_str x istart)))
    with (iout_app (mk SoftBreak :: ifinish_rev (iscan_str x istart)) istart).
  rewrite iscan_lines_out_app, ifinish_out_app.
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
  unfold parse_inline_line, istart, ci_line. rewrite iscan_cis.
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

Example escape_leaves_punct : escape_str "a,*b" = "a,*b".
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
