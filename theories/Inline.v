(* ai-disclosure: autonomous *)

(* The inline layer: the parser's pass over a paragraph's text, and the
   canonical (renderable) view it inverts.

   The same two-sided shape as the block layer, one level down.  There,
   `Line.v` classifies a line and `Step.v` folds lines into blocks, while
   `Render.v`'s `cblock` describes the parser's image by the source data
   that determines it.  Here `para_inlines` is the pass, `cinline` is the
   image, and the two meet in `para_inlines_ci_para`.

   The pass recognizes escapes, verbatim spans, and the delimiter table
   in `.project/260811.inline-parser.md`.  Brackets remain the next
   extension point for the state and canonical view.

   The scan threads through line breaks rather than restarting at each
   one, because a span may cross a break.  The canonical view stays
   line-local, `cblock` describing a paragraph as a list of lines, and
   `iscan_cis_closed` is what reconciles the two: a canonical line always
   leaves the scan owing nothing to the next.

   Parser and renderer share the file because at this size a split would
   be three files of twenty lines.  It splits the way the block parser
   did once a side outgrows the other. *)

From Stdlib Require Import String Ascii List Bool Lia Wf_nat.
From DjotV Require Import Strings Ast Attributes.
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

(* The node a closed bracket builds, and the one place image-ness is
   consulted.  Kept beside `dnode` for the same reason: it is a lookup,
   not a branch in the scanner. *)
Definition bnode (image : bool) (ns : inlines) (tgt : target) : inline :=
  if image then Image ns tgt else Link ns tgt.

(* The label supplied by an empty reference (`[text][]`) is the string
   content of the first bracket.  This is djot.js's `getStringContent`,
   kept local to the inline layer so classification still does not consult
   either reference map. *)
Fixpoint reference_text (il : inline) : string :=
  let go :=
    fix go (ns : inlines) : string :=
      match ns with
      | [] => EmptyString
      | n :: rest => reference_text (node_contents n) ++ go rest
      end in
  match il with
  | Str s | Verbatim s | Math _ s | RawInline _ s => s
  | SoftBreak | HardBreak => nl
  | Emph ns | Strong ns | Highlight ns | Insert ns | Delete ns
  | Superscript ns | Subscript ns | Span ns | Link ns _ | Image ns _
  | Quoted _ ns => go ns
  | FootnoteReference _ | Symbol _ | UrlLink _ | EmailLink _
  | NonBreakingSpace => EmptyString
  end.

Definition reference_inlines_text (ns : inlines) : string :=
  String.concat EmptyString (map (fun n => reference_text (node_contents n)) ns).

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

(* The bracket family's characters.  The three the scanner dispatches on
   in text mode -- `!`, `[`, `]` -- are in `needs_escape`; the parens are
   dispatched only inside a destination, so they are claimed by
   `needs_escape_dest` instead. *)
Definition bang : ascii := "!"%char.
Definition lbrack : ascii := "["%char.
Definition rbrack : ascii := "]"%char.
Definition lparen : ascii := "("%char.
Definition rparen : ascii := ")"%char.

(* `ibreak` writes the break into a destination as `nl` and the
   reconstruction reads it back byte by byte, so the two spellings have
   to be the same character. *)
Definition nl_char : ascii := "010"%char.

Definition one (c : ascii) : string := String c EmptyString.

Lemma nl_one_char : nl = one nl_char.
Proof. reflexivity. Qed.

Definition needs_escape (c : ascii) : bool :=
  (is_bslash c || is_tick c || is_delim c
   || Ascii.eqb c lbrace || Ascii.eqb c rbrace
   || Ascii.eqb c lbrack || Ascii.eqb c rbrack
   || Ascii.eqb c bang)%bool.

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

(* And the same for the brackets, now that the scanner dispatches on
   them: a `[` in a `Str` would open a scope, and a `]` would close one
   that a later construct opened. *)
Lemma needs_escape_lbrack : needs_escape lbrack = true.
Proof. reflexivity. Qed.

Lemma needs_escape_rbrack : needs_escape rbrack = true.
Proof. reflexivity. Qed.

(* The `!` an image opens on.  Escaping it unconditionally is what lets a
   `Str` ending in `!` sit before a link without turning it into an
   image, which is exactly the reading djot.js gives `\![a](u)`. *)
Lemma needs_escape_bang : needs_escape bang = true.
Proof. reflexivity. Qed.

(* Inside a destination the scanner dispatches on two more characters,
   the parentheses that move its depth counter, and on none of the
   delimiters -- but escaping those too is harmless (an escape decodes to
   the character in either mode) and keeps one predicate ordered above
   the other. *)
Definition needs_escape_dest (c : ascii) : bool :=
  (needs_escape c || Ascii.eqb c lparen || Ascii.eqb c rparen)%bool.

Lemma needs_escape_dest_punct :
  forall c, needs_escape_dest c = true -> is_punct c = true.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7] H.
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    vm_compute in H |- *; first [reflexivity | discriminate].
Qed.

Fixpoint escape_str (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if needs_escape c
      then String "\"%char (String c (escape_str rest))
      else String c (escape_str rest)
  end.

Fixpoint escape_dest (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if needs_escape_dest c
      then String "\"%char (String c (escape_dest rest))
      else String c (escape_dest rest)
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

(* A bracket's own source: the `[`, with the `!` of an image.  Both the
   canonical rendering and the literal fallback put it back. *)
Definition bracket_open (image : bool) : string :=
  if image then String bang (one lbrack) else one lbrack.

(* A link's closing half: the `](`, the escaped destination, and the `)`,
   with whatever follows.  Written with a tail for the same reason
   `marked_close` is -- the scanner inversion needs to speak of the
   closer and its continuation as one string. *)
Definition link_close (dst tail : string) : string :=
  String rbrack (String lparen (escape_dest dst ++ String rparen tail)).

(* A reference link's closing half: the `]`, then `[`, the label and `]`.
   The label is not escaped -- the scanner's reference mode accumulates
   bytes literally until a `]` -- so `ci_ok` has to keep `]` out of it
   rather than escape it. *)
Definition ref_close (label tail : string) : string :=
  String rbrack (String lbrack (label ++ String rbrack tail)).

(* One line's inline content, described by the source that determines it.
   One constructor per inline construct the roundtrip covers, exactly as
   `cblock` carries one per block construct. *)
Inductive cinline : Type :=
  | CIStr (s : string)
  | CIVerb (s : string)
  | CIDelim (k : dstyle) (kids : list cinline)
  (* a direct link or image: its label, and the destination it resolves
     to.  The label may be empty -- `[](u)` is a link in djot -- which is
     the one way this differs from a delimiter. *)
  | CILink (img : bool) (kids : list cinline) (dst : string)
  (* a reference link or image: its text and the label it resolves
     against.  The explicit spelling `[text][label]` is the canonical one
     because it is context-free: the collapsed `[text][]` reads its label
     off the text, so it cannot express a label the text does not spell. *)
  | CIRef (img : bool) (kids : list cinline) (label : string).

Fixpoint ci_size (ci : cinline) : nat :=
  let go :=
    fix go (cis : list cinline) : nat :=
      match cis with
      | [] => 0
      | c :: rest => ci_size c + go rest
      end in
  match ci with
  | CIStr _ | CIVerb _ => 1
  | CIDelim _ kids | CILink _ kids _ | CIRef _ kids _ => S (go kids)
  end.

Fixpoint cis_size (cis : list cinline) : nat :=
  match cis with [] => 0 | c :: rest => ci_size c + cis_size rest end.

Lemma ci_size_delim :
  forall k kids, ci_size (CIDelim k kids) = S (cis_size kids).
Proof.
  intros k kids.
  assert (H : forall xs,
    (fix go (cis : list cinline) : nat :=
       match cis with
       | [] => 0
       | c :: rest => ci_size c + go rest
       end) xs = cis_size xs).
  { induction xs as [|c rest IH]; cbn [cis_size]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_size]. rewrite H. reflexivity.
Qed.

Lemma ci_size_link :
  forall img kids dst, ci_size (CILink img kids dst) = S (cis_size kids).
Proof.
  intros img kids dst. exact (ci_size_delim DEmph kids).
Qed.

Lemma ci_size_ref :
  forall img kids label, ci_size (CIRef img kids label) = S (cis_size kids).
Proof.
  intros img kids label. exact (ci_size_delim DEmph kids).
Qed.

Lemma ci_size_pos : forall ci, 0 < ci_size ci.
Proof.
  intros [s|s|k kids|img kids dst|img kids label]; cbn [ci_size]; lia.
Qed.

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
Fixpoint ci_src (ci : cinline) : string :=
  let go :=
    fix go (cis : list cinline) : string :=
      match cis with
      | [] => EmptyString
      | c :: rest => (ci_src c ++ go rest)%string
      end in
  match ci with
  | CIStr s => escape_str s
  | CIVerb s => verb_text s
  | CIDelim k kids =>
      String lbrace
        (String (dchar k) (go kids ++ String (dchar k) (one rbrace)))
  | CILink img kids dst =>
      (bracket_open img ++ (go kids ++ link_close dst EmptyString))%string
  | CIRef img kids label =>
      (bracket_open img ++ (go kids ++ ref_close label EmptyString))%string
  end.

Fixpoint ci_text (cis : list cinline) : string :=
  match cis with
  | [] => EmptyString
  | ci :: rest => (ci_src ci ++ ci_text rest)%string
  end.

Definition ci_line (cis : list cinline) : string := ci_text cis.

Lemma ci_src_delim :
  forall k kids,
    ci_src (CIDelim k kids)
    = String lbrace
        (String (dchar k) (ci_text kids ++ String (dchar k) (one rbrace))).
Proof.
  intros k kids.
  assert (H : forall xs,
    (fix go (cis : list cinline) : string :=
       match cis with
       | [] => EmptyString
       | c :: rest => (ci_src c ++ go rest)%string
       end) xs = ci_text xs).
  { induction xs as [|c rest IH]; cbn [ci_text]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_src]. rewrite H. reflexivity.
Qed.

Lemma ci_src_link :
  forall img kids dst,
    ci_src (CILink img kids dst)
    = (bracket_open img ++ (ci_text kids ++ link_close dst EmptyString))%string.
Proof.
  intros img kids dst.
  assert (H : forall xs,
    (fix go (cis : list cinline) : string :=
       match cis with
       | [] => EmptyString
       | c :: rest => (ci_src c ++ go rest)%string
       end) xs = ci_text xs).
  { induction xs as [|c rest IH]; cbn [ci_text]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_src]. rewrite H. reflexivity.
Qed.

Lemma ci_src_ref :
  forall img kids label,
    ci_src (CIRef img kids label)
    = (bracket_open img ++ (ci_text kids ++ ref_close label EmptyString))%string.
Proof.
  intros img kids label.
  assert (H : forall xs,
    (fix go (cis : list cinline) : string :=
       match cis with
       | [] => EmptyString
       | c :: rest => (ci_src c ++ go rest)%string
       end) xs = ci_text xs).
  { induction xs as [|c rest IH]; cbn [ci_text]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_src]. rewrite H. reflexivity.
Qed.

(* ...and the AST the parser builds from that text. *)
Fixpoint ci_ast (ci : cinline) : node inline :=
  let go :=
    fix go (cis : list cinline) : inlines :=
      match cis with
      | [] => []
      | c :: rest => ci_ast c :: go rest
      end in
  match ci with
  | CIStr s => mk (Str s)
  | CIVerb s => mk (Verbatim s)
  | CIDelim k kids => mk (dnode k (go kids))
  | CILink img kids dst => mk (bnode img (go kids) (Direct dst))
  | CIRef img kids label => mk (bnode img (go kids) (Reference label))
  end.

Definition ci_inlines (cis : list cinline) : inlines := map ci_ast cis.

Lemma ci_ast_delim :
  forall k kids, ci_ast (CIDelim k kids) = mk (dnode k (ci_inlines kids)).
Proof.
  intros k kids.
  assert (H : forall xs,
    (fix go (cis : list cinline) : inlines :=
       match cis with
       | [] => []
       | c :: rest => ci_ast c :: go rest
       end) xs = ci_inlines xs).
  { induction xs as [|c rest IH]; cbn [ci_inlines map]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_ast]. rewrite H. reflexivity.
Qed.

Lemma ci_ast_link :
  forall img kids dst,
    ci_ast (CILink img kids dst)
    = mk (bnode img (ci_inlines kids) (Direct dst)).
Proof.
  intros img kids dst.
  assert (H : forall xs,
    (fix go (cis : list cinline) : inlines :=
       match cis with
       | [] => []
       | c :: rest => ci_ast c :: go rest
       end) xs = ci_inlines xs).
  { induction xs as [|c rest IH]; cbn [ci_inlines map]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_ast]. rewrite H. reflexivity.
Qed.

Lemma ci_ast_ref :
  forall img kids label,
    ci_ast (CIRef img kids label)
    = mk (bnode img (ci_inlines kids) (Reference label)).
Proof.
  intros img kids label.
  assert (H : forall xs,
    (fix go (cis : list cinline) : inlines :=
       match cis with
       | [] => []
       | c :: rest => ci_ast c :: go rest
       end) xs = ci_inlines xs).
  { induction xs as [|c rest IH]; cbn [ci_inlines map]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_ast]. rewrite H. reflexivity.
Qed.

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
(* A `!` before a link's `[` would make it an image, and there is no
   pair rule for that: `needs_escape` claims the `!`, so a `Str` ending
   in one renders as `\!` and djot.js reads that as a link too. *)
Definition ci_pair_ok (a b : cinline) : bool :=
  match a, b with
  | CIStr _, CIStr _ => false
  | CIVerb _, CIVerb _ => false
  | _, _ => true
  end.

Fixpoint ci_ok (ci : cinline) : bool :=
  let go :=
    fix go (cis : list cinline) : bool :=
      match cis with
      | [] => true
      | c :: rest => (ci_ok c && go rest)%bool
      end in
  let sep :=
    fix sep (cis : list cinline) : bool :=
      match cis with
      | a :: ((b :: _) as rest) => ci_pair_ok a b && sep rest
      | _ => true
      end in
  match ci with
  | CIStr s => nonempty_str s && no_nl s
  | CIVerb s => nonempty_str s && verb_content_ok s
  | CIDelim _ kids => (nonempty kids && go kids && sep kids)%bool
  (* A destination holding a line break cannot round-trip: the scanner
     drops the break rather than recording it, so the rendering would
     come back shorter.  Everything else the scanner dispatches on is
     escaped by `escape_dest`. *)
  | CILink _ kids dst => (no_nl dst && go kids && sep kids)%bool
  (* A label reaches the AST normalized, so only an already-normalized one
     round-trips; `]` would end it early, and an empty one is the
     collapsed spelling, whose label comes from the text instead. *)
  | CIRef _ kids label =>
      (nonempty_str label && no_char rbrack label
       && String.eqb (normalize_label label) label
       && go kids && sep kids)%bool
  end.

(* Pairwise source separation: adjacent strings merge, and adjacent
   verbatim spans merge their delimiter runs. *)
Fixpoint ci_sep_ok (cis : list cinline) : bool :=
  match cis with
  | a :: ((b :: _) as rest) => ci_pair_ok a b && ci_sep_ok rest
  | _ => true
  end.

Definition cis_ok (cis : list cinline) : bool :=
  forallb ci_ok cis && ci_sep_ok cis.

Lemma ci_ok_delim :
  forall k kids,
    ci_ok (CIDelim k kids) = (nonempty kids && cis_ok kids)%bool.
Proof.
  intros k kids.
  assert (Hg : forall xs,
    (fix go (cis : list cinline) : bool :=
       match cis with
       | [] => true
       | c :: rest => (ci_ok c && go rest)%bool
       end) xs = forallb ci_ok xs).
  { induction xs as [|c rest IH]; cbn [forallb]; [reflexivity|].
    rewrite IH. reflexivity. }
  assert (Hs : forall xs,
    (fix sep (cis : list cinline) : bool :=
       match cis with
       | a :: ((b :: _) as rest) => ci_pair_ok a b && sep rest
       | _ => true
       end) xs = ci_sep_ok xs).
  { induction xs as [|a [|b rest] IH]; cbn [ci_sep_ok]; [reflexivity..|].
    rewrite IH. reflexivity. }
  cbn [ci_ok]. rewrite Hg, Hs. unfold cis_ok.
  repeat rewrite andb_assoc. reflexivity.
Qed.

Lemma ci_ok_link :
  forall img kids dst,
    ci_ok (CILink img kids dst) = (no_nl dst && cis_ok kids)%bool.
Proof.
  intros img kids dst.
  assert (Hg : forall xs,
    (fix go (cis : list cinline) : bool :=
       match cis with
       | [] => true
       | c :: rest => (ci_ok c && go rest)%bool
       end) xs = forallb ci_ok xs).
  { induction xs as [|c rest IH]; cbn [forallb]; [reflexivity|].
    rewrite IH. reflexivity. }
  assert (Hs : forall xs,
    (fix sep (cis : list cinline) : bool :=
       match cis with
       | a :: ((b :: _) as rest) => ci_pair_ok a b && sep rest
       | _ => true
       end) xs = ci_sep_ok xs).
  { induction xs as [|a [|b rest] IH]; cbn [ci_sep_ok]; [reflexivity..|].
    rewrite IH. reflexivity. }
  cbn [ci_ok]. rewrite Hg, Hs. unfold cis_ok.
  repeat rewrite andb_assoc. reflexivity.
Qed.

Lemma ci_ok_ref :
  forall img kids label,
    ci_ok (CIRef img kids label)
    = (nonempty_str label && no_char rbrack label
       && String.eqb (normalize_label label) label && cis_ok kids)%bool.
Proof.
  intros img kids label.
  assert (Hg : forall xs,
    (fix go (cis : list cinline) : bool :=
       match cis with
       | [] => true
       | c :: rest => (ci_ok c && go rest)%bool
       end) xs = forallb ci_ok xs).
  { induction xs as [|c rest IH]; cbn [forallb]; [reflexivity|].
    rewrite IH. reflexivity. }
  assert (Hs : forall xs,
    (fix sep (cis : list cinline) : bool :=
       match cis with
       | a :: ((b :: _) as rest) => ci_pair_ok a b && sep rest
       | _ => true
       end) xs = ci_sep_ok xs).
  { induction xs as [|a [|b rest] IH]; cbn [ci_sep_ok]; [reflexivity..|].
    rewrite IH. reflexivity. }
  cbn [ci_ok]. rewrite Hg, Hs. unfold cis_ok.
  repeat rewrite andb_assoc. reflexivity.
Qed.

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
That is not an accident of style: it makes "the scanner never re-feeds a
source position through tokenization" structural, which is the project's
precise no-backtracking claim (see `.project/260811.inline-parser.md`
§2.4).  It does not forbid retroactive scope-stack changes, and it is not
a linear-time claim: resolving one byte may still walk the opener stack.
It also matches djot.js's `feed`, which is a position-at-a-time loop over
a mode flag.

A verbatim closer is a run of *exactly* the opening width, so a run
cannot be resolved until the character after it arrives; that is why
`IVerb` carries a pending run count rather than closing eagerly.  A run
of the wrong width is content, which is how `` ` `` ` `` holds two
backticks inside a one-backtick fence. *)

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

Inductive frame_kind : Type :=
  | FKDelim (style : dstyle)
  (* `image` records the `!` before the `[`, which djot.js instead reads
     back off the subject at the close (`inline.ts:475`).  We cannot: the
     text before the bracket has been flushed by then, and an escaped
     `\!` is indistinguishable from a bare one once it is in the buffer. *)
  | FKBracket (image : bool).

Record frame : Type := Frame {
  fr_kind : frame_kind;
  fr_marked : bool;          (* delimiter opened as `{d`; false for `[` *)
  fr_out : inlines           (* this scope's inlines, reversed *)
}.

(* The opener's source text, which is what it decays to when abandoned. *)
Definition fr_src (f : frame) : string :=
  match fr_kind f with
  | FKDelim k =>
      if fr_marked f then String lbrace (one (dchar k)) else one (dchar k)
  | FKBracket image => bracket_open image
  end.

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
  match fr_kind f with
  | FKDelim k' => (dstyle_eqb k k' && Bool.eqb m (fr_marked f))%bool
  | FKBracket _ => false
  end.

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
      OState (os_out o) (Frame (fr_kind f) (fr_marked f) (n :: fr_out f) :: rest)
  end.

(* Emit in source order while merging a plain-`Str` seam.  Ordinary
   scanner emission keeps the seam obligation explicit in `iscan_wf`;
   reconstruction paths (abandoned frames and bracket literal fallback)
   already know they are splicing source fragments and need the merge by
   construction. *)
Definition oemit_merge (n : node inline) (o : ostate) : ostate :=
  match os_stk o with
  | [] => OState (osnoc n (os_out o)) []
  | f :: rest =>
      OState (os_out o)
        (Frame (fr_kind f) (fr_marked f) (osnoc n (fr_out f)) :: rest)
  end.

Fixpoint oemit_all_merge (ns : inlines) (o : ostate) : ostate :=
  match ns with
  | [] => o
  | n :: rest => oemit_all_merge rest (oemit_merge n o)
  end.

Fixpoint oemit_all (ns : inlines) (o : ostate) : ostate :=
  match ns with
  | [] => o
  | n :: rest => oemit_all rest (oemit n o)
  end.

Definition flush_text (txt : string) (o : ostate) : ostate :=
  if nonempty_str txt then oemit (mk (Str txt)) o else o.

Definition opush (k : dstyle) (m : bool) (o : ostate) : ostate :=
  OState (os_out o) (Frame (FKDelim k) m [] :: os_stk o).

Definition bpush (image : bool) (o : ostate) : ostate :=
  OState (os_out o) (Frame (FKBracket image) false [] :: os_stk o).

Lemma oemit_all_app :
  forall a b o, oemit_all (a ++ b)%list o = oemit_all b (oemit_all a o).
Proof.
  induction a as [|n a IH]; intros b o; cbn [oemit_all];
    [reflexivity|apply IH].
Qed.

Lemma oemit_all_frame :
  forall ns out kind m acc stk,
    oemit_all ns (OState out (Frame kind m acc :: stk))
    = OState out (Frame kind m (List.rev ns ++ acc)%list :: stk).
Proof.
  induction ns as [|n ns IH]; intros out kind m acc stk;
    cbn [oemit_all List.rev app]; [reflexivity|].
  change (oemit_all ns (OState out (Frame kind m (n :: acc) :: stk))
          = OState out
              (Frame kind m ((List.rev ns ++ [n]) ++ acc)%list :: stk)).
  rewrite IH, <- List.app_assoc. reflexivity.
Qed.

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

Lemma oclose_oemit_all_marked :
  forall k ns base,
    nonempty ns = true ->
    oclose k true (oemit_all ns (opush k true base))
    = Some (oemit (mk (dnode k ns)) base).
Proof.
  intros k ns [out stk] Hne. unfold opush. rewrite oemit_all_frame.
  unfold oclose. cbn [os_stk os_out oclose_go oapp dmatch fr_kind
    fr_marked fr_out]. rewrite !app_nil_r.
  assert (Hrev : nonempty (List.rev ns) = true).
  { destruct ns as [|n rest]; [discriminate|].
    cbn [List.rev]. destruct (List.rev rest); reflexivity. }
  rewrite Hrev. destruct k;
    cbn [dmatch dstyle_eqb fr_kind fr_marked andb_true_l].
  all: cbn; rewrite List.rev_involutive; reflexivity.
Qed.

(* Brackets share the ordered scope stack with delimiters.  Finding a
   bracket abandons any delimiter frames above it, just as djot.js closes
   the bracketed construct before `clearOpeners` removes openers inside
   it.  Unlike a delimiter close this only extracts the label content:
   the following byte still decides link, reference, span, or literal
   brackets. *)
Fixpoint bclose_go (pend : inlines) (stk : list frame)
  : option (inlines * bool * list frame) :=
  match stk with
  | [] => None
  | f :: rest =>
      let content := oapp pend (fr_out f) in
      match fr_kind f with
      | FKBracket image => Some (content, image, rest)
      | FKDelim _ =>
          bclose_go (oapp content [mk (Str (fr_src f))]) rest
      end
  end.

Definition bclose (o : ostate) : option (inlines * bool * ostate) :=
  match bclose_go [] (os_stk o) with
  | None => None
  | Some (content, image, rest) =>
      Some (List.rev content, image, OState (os_out o) rest)
  end.

Lemma bclose_oemit_all :
  forall ns image base,
    bclose (oemit_all ns (bpush image base)) = Some (ns, image, base).
Proof.
  intros ns image [out stk]. unfold bpush. rewrite oemit_all_frame.
  unfold bclose. cbn [os_stk os_out bclose_go fr_out fr_kind oapp].
  rewrite app_nil_r, List.rev_involutive. reflexivity.
Qed.

(*
Putting a bracket back as text
------------------------------

A bracket's role is decided long after its label is scanned, so the
literal fallback has to reconstruct source from children that are
already classified.  Three operations do it, and between them they keep
the two invariants the text states carry: pending text never sits on a
`Str`, and no two `Str` nodes are adjacent.

None of the three re-reads a byte.  They rewrite state that is already
built, which is the same family as abandoning a scope. *)

(* Undoing a flush.  The text before a `[` was flushed into the current
   scope when the bracket opened; if the bracket decays to text that
   `Str` has to come back out, or the reconstructed text would flush on
   top of it. *)
Definition opop_str (o : ostate) : string * ostate :=
  match os_stk o with
  | [] =>
      match os_out o with
      | Node _ [] (Str s) :: rest => (s, OState rest [])
      | _ => (EmptyString, o)
      end
  | f :: fs =>
      match fr_out f with
      | Node _ [] (Str s) :: rest =>
          (s, OState (os_out o) (Frame (fr_kind f) (fr_marked f) rest :: fs))
      | _ => (EmptyString, o)
      end
  end.

(* Children back into the buffer.  A plain `Str` child is text and joins
   it; anything else is emitted, flushing the buffer first.  So emissions
   alternate `Str` and non-`Str` and the seam obligation holds by
   construction -- this is why the fallback needs no merging emission. *)
Fixpoint bflat (kids : inlines) (txt : string) (o : ostate) : string * ostate :=
  match kids with
  | [] => (txt, o)
  | Node _ [] (Str s) :: rest => bflat rest (txt ++ s)%string o
  | n :: rest => bflat rest EmptyString (oemit n (flush_text txt o))
  end.

(* Text that spans a line break.  A `SoftBreak` is a node, so such text
   cannot go back into the buffer whole.  Only a destination needs this:
   it is the one buffer that survives `ibreak`. *)
Fixpoint bsplit_nl (s txt : string) (o : ostate) : string * ostate :=
  match s with
  | EmptyString => (txt, o)
  | String c rest =>
      if Ascii.eqb c nl_char
      then bsplit_nl rest EmptyString (oemit (mk SoftBreak) (flush_text txt o))
      else bsplit_nl rest (txt ++ one c)%string o
  end.

(* A closed bracket that turns out to be literal: `[`, the label, `]`. *)
Definition bclosed_lit (kids : inlines) (image : bool) (o : ostate)
  : string * ostate :=
  let '(pre, o1) := opop_str o in
  let '(txt, o2) := bflat kids (pre ++ bracket_open image)%string o1 in
  ((txt ++ one rbrack)%string, o2).

(* A span whose spec failed, or that ran out of line: the bracket's own
   literal text, then the `{` and everything the machine read. *)
Definition bspan_lit (kids : inlines) (image : bool) (src : string)
  (o : ostate) : string * ostate :=
  let '(txt, o') := bclosed_lit kids image o in
  ((txt ++ one lbrace ++ src)%string, o').

Definition bref_lit (kids : inlines) (image : bool) (label : string)
  (o : ostate) : string * ostate :=
  let '(txt, o') := bclosed_lit kids image o in
  ((txt ++ one lbrack ++ label)%string, o').

(* A destination that never closed: the above, then `(` and what the
   destination had accumulated, including the breaks it spanned. *)
Definition bdest_lit (kids : inlines) (image esc : bool) (dst : string)
  (o : ostate) : string * ostate :=
  let '(txt, o') := bclosed_lit kids image o in
  bsplit_nl (if esc then (dst ++ one bslash)%string else dst)
            (txt ++ one lparen)%string o'.

(* The destination itself drops the breaks (`parse.ts:612`), which is why
   they are kept as characters until it is known to close. *)
Fixpoint drop_nl (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if Ascii.eqb c nl_char then drop_nl rest else String c (drop_nl rest)
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
  | IVerb (n run : nat) (txt : string) (o : ostate)
  (* a `!` whose role the next byte decides: `[` opens an image, and
     anything else makes it text.  An *escaped* `!` never reaches here,
     which is what keeps `\![a](u)` a link. *)
  | IBang (txt : string) (prev : option ascii) (o : ostate)
  (* a `]` whose role the next byte decides: `(` enters a destination,
     anything else makes the brackets literal.  `kids` is the label,
     already classified and in source order, `image` is what its opener
     was, and `o` is the state the bracket opened in, restored by
     `bclose`. *)
  | IClosed (kids : inlines) (image : bool) (o : ostate)
  (* inside the second bracket of `[text][label]`.  The label is source
     text, not inline content: upstream's `strMatches` retroactively
     flattens everything in this region before building the reference. *)
  (* A closed bracket followed by `{`: a span, if the spec parses.  The
     spec is read with the same machine block attributes use, fed a byte
     at a time; `src` is what it has eaten, kept so the whole region can
     be put back as text when the machine fails.  `image` is carried only
     for that reconstruction -- a span ignores it, so `![x]{.a}` is a `!`
     followed by a span. *)
  | ISpan (kids : inlines) (image : bool) (p : aparser) (src : string)
          (o : ostate)
  (* An attribute spec, which attaches to whatever precedes it.  `txt` is
     the text pending when the `{` arrived: it is both the literal
     fallback and, on success, the thing the spec attaches to. *)
  | IAttr (p : aparser) (src : string) (txt : string) (prev : option ascii)
          (o : ostate)
  | IReference (kids : inlines) (image : bool) (label : string) (o : ostate)
  (* inside a `](`.  `depth` counts unclosed inner parentheses, `dst`
     accumulates the destination with its escapes decoded, and `esc` is a
     pending backslash, as in text mode.  A destination survives a line
     break, so this is the second state `ibreak` carries across one. *)
  | IDest (kids : inlines) (image esc : bool) (depth : nat) (dst : string)
          (o : ostate).

(* One byte in text mode.  The delimiter arm is a lookup, not six
   branches, for the reason the table's own comment gives. *)
Definition ilead (c : ascii) (txt : string) (prev : option ascii) (o : ostate)
  : iscan :=
  if is_bslash c then IText true txt prev o
  else if is_tick c then IOpen 1 (flush_text txt o)
  else if Ascii.eqb c lbrace then IBrace txt prev o
  (* A `[` opens a scope on the same stack the delimiters use, so their
     relative order is kept and the label needs no second parser.  A `]`
     closes the innermost bracket scope, abandoning any delimiter scopes
     opened inside it, and hands the label to `IClosed`; with no bracket
     open it is ordinary text. *)
  else if Ascii.eqb c bang then IBang txt prev o
  else if Ascii.eqb c lbrack
  then IText false EmptyString (Some lbrack) (bpush false (flush_text txt o))
  else if Ascii.eqb c rbrack
  then match bclose (flush_text txt o) with
       | Some (kids, image, o') => IClosed kids image o'
       | None => IText false (txt ++ one rbrack)%string prev o
       end
  else match dstyle_of c with
       | Some k => IDelim k txt (nonspace_at (str_last txt prev)) o
       | None => IText false (txt ++ one c)%string prev o
       end.

Definition null {A} (l : list A) : bool :=
  match l with [] => true | _ => false end.

(* Has the scan produced anything here?  An open scope counts: it is
   abandoned at the end and its opener becomes text. *)
Definition ostate_nonempty (o : ostate) : bool :=
  (nonempty (os_out o) || negb (null (os_stk o)))%bool.


(* The run an attribute spec attaches to when the thing before it is
   pending text: everything after the last whitespace.  djot.js attaches
   to the last *word*, so `foo bar{.a}` attributes only `bar` while
   `a-b{.a}` attributes all of `a-b` -- the split is on whitespace, not
   on word characters.  The result satisfies `s = pre ++ w` with `w`
   whitespace-free, which is why an attributed `Str` can never contain a
   space. *)
Fixpoint last_ws_split (s : string) : string * string :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c rest =>
      match last_ws_split rest with
      | (EmptyString, w) =>
          if is_ws c then (one c, w) else (EmptyString, String c w)
      | (pre, w) => (String c pre, w)
      end
  end.

(* Where a finished spec lands.  Pending text takes it on its last word,
   which is the only target implemented: a spec after a *node* -- `*e*{.a}`
   -- would decorate what the scan last emitted, and that reads the
   current scope, which `oout_app` perturbs.  See the note at
   `iattr_no_node_target` below.

   An empty spec attaches to nothing.  djot.js still cuts the text in two
   there (`foo{}bar` is two `str` nodes), but both are plain and the HTML
   is identical, so we keep one run and stay inside `no_adjacent_str`.
   Text ending in whitespace has no last word, so `foo {.a}` drops the
   spec and keeps accumulating -- which is djot.js's adjacency rule. *)
Definition iattr_attach (a : attr) (src txt : string) (prev : option ascii)
  (o : ostate) : iscan :=
  (* Nothing to attach to.  djot.js drops the spec; we do too when there
     is pending text, and otherwise keep its source.  Two reasons for the
     second half, and only the first is about fidelity: a spec that ate
     the whole scan would leave a paragraph or heading with no children,
     which `wf_block` excludes and `parse_inline_line_nonempty` denies.
     The other is that "has anything been emitted" is not a question this
     may ask -- `oout_app` appends a previous line's output underneath,
     so the answer is not stable under it, while pending text is.  The
     residue is `{#i} x` and `[l](u){}`, logged under ours. *)
  let drop :=
    if nonempty_str txt
    then IText false txt prev o
    else IText false (txt ++ one lbrace ++ src)%string prev o in
  match a with
  | [] => drop
  | _ =>
      let '(pre, w) := last_ws_split txt in
      if nonempty_str w
      then IText false EmptyString (Some rbrace)
             (oemit (Node NoPos a (Str w)) (flush_text pre o))
      else drop
  end.

(* One byte of an inline attribute spec, read with the machine block
   attributes use.  Failure hands the byte back to `ilead` with the text
   restored, as a span's does. *)
Definition iattr_feed (c : ascii) (p : aparser) (src txt : string)
  (prev : option ascii) (o : ostate) : iscan :=
  let p' := astep p c in
  if ap_failed p'
  then ilead c (txt ++ one lbrace ++ src)%string prev o
  else if ap_done p'
  then iattr_attach (ap_attrs p') (src ++ one c)%string txt prev o
  else IAttr p' (src ++ one c)%string txt prev o.

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
  | None => iattr_feed c ap_init EmptyString txt prev o
  end.

(* A span ignores the image marker: `![x]{.a}` is a literal `!` followed
   by a span.  The `!` was never flushed -- `IClosed` records it in a flag
   and `bclosed_lit` puts it back on the literal path -- so the span path
   has to emit it here, and it merges with any `Str` already at the tip
   the same way, since `flush_text` alone would leave two adjacent. *)
Definition ospan_bang (image : bool) (o : ostate) : ostate :=
  if image
  then let '(pre, o1) := opop_str o in flush_text (pre ++ one bang)%string o1
  else o.

(* One byte into an open span's spec.  `ADone` arrives on the `}`, so the
   node is built here with no byte left over.  On `AFail` the region up to
   but not including the failing byte becomes text and that byte is
   dispatched afresh: djot.js resumes its scan there, so `[s]{bad*x*y` is
   `[s]{bad`, a strong `x`, and `y`. *)
Definition ispan_feed (c : ascii) (kids : inlines) (image : bool)
  (p : aparser) (src : string) (o : ostate) : iscan :=
  let p' := astep p c in
  if ap_failed p'
  then let '(txt, o') := bspan_lit kids image src o in ilead c txt None o'
  else if ap_done p'
  then IText false EmptyString (Some rbrace)
         (oemit (Node NoPos (ap_attrs p') (Span kids)) (ospan_bang image o))
  else ISpan kids image p' (src ++ one c)%string o.

(* Resolving a `!`: an image opener if a `[` follows, text otherwise.
   The `!` is *not* flushed with the text before it -- it is the opener's
   own source, and `fr_src` puts it back if the bracket decays. *)
Definition ibang_step (c : ascii) (txt : string) (prev : option ascii)
  (o : ostate) : iscan :=
  if Ascii.eqb c lbrack
  then IText false EmptyString (Some lbrack) (bpush true (flush_text txt o))
  else ilead c (txt ++ one bang)%string prev o.

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
  | IAttr _ src txt prev o =>
      IText false (txt ++ one lbrace ++ src)%string prev o
  | IBang txt prev o => IText false (txt ++ one bang)%string prev o
  | IDelim k txt canclose o => idelim_resolve k txt canclose false None o
  (* `[a]` at the end of a line is literal: djot.js scans the newline as
     an ordinary byte, and a `(` after it is not a destination. *)
  | IClosed kids image o =>
      let '(txt, o') := bclosed_lit kids image o in IText false txt None o'
  | _ => st
  end.

Definition istep (c : ascii) (st : iscan) : iscan :=
  match st with
  | IText true txt prev o =>
      IText false (txt ++ (if is_punct c then one c
                           else String "\"%char (one c)))%string prev o
  | IText false txt prev o => ilead c txt prev o
  | IBrace txt prev o => ibrace_step c txt prev o
  | IBang txt prev o => ibang_step c txt prev o
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
  (* The two bracket modes.  Nothing enters them yet: `[` and `]` are not
     dispatched, so `bclose` has no caller and these arms are dead.  They
     are written first because every state-parametric invariant below
     must say what they do, and landing that separately from the dispatch
     is what keeps a missed case from hiding behind a behaviour diff. *)
  | IClosed kids image o =>
      if Ascii.eqb c lparen then IDest kids image false 0 EmptyString o
      else if Ascii.eqb c lbrack then IReference kids image EmptyString o
      else if Ascii.eqb c lbrace
      then ISpan kids image ap_init EmptyString o
      else let '(txt, o') := bclosed_lit kids image o in ilead c txt None o'
  | ISpan kids image p src o => ispan_feed c kids image p src o
  | IAttr p src txt prev o => iattr_feed c p src txt prev o
  | IReference kids image label o =>
      if Ascii.eqb c rbrack
      then let key := match label with
                      | EmptyString => reference_inlines_text kids
                      | _ => label
                      end in
           IText false EmptyString (Some rbrack)
             (oemit (mk (bnode image kids (Reference (normalize_label key)))) o)
      else IReference kids image (label ++ one c)%string o
  | IDest kids image true depth dst o =>
      IDest kids image false depth
        (dst ++ (if is_punct c then one c
                 else String bslash (one c)))%string o
  | IDest kids image false depth dst o =>
      if is_bslash c then IDest kids image true depth dst o
      else if Ascii.eqb c lparen
      then IDest kids image false (S depth) (dst ++ one lparen)%string o
      else if Ascii.eqb c rparen
      then match depth with
           | O =>
               (* the balanced close: the one byte that builds the node *)
               IText false EmptyString (Some rparen)
                 (oemit (mk (bnode image kids (Direct (drop_nl dst)))) o)
           | S d => IDest kids image false d (dst ++ one rparen)%string o
           end
      else IDest kids image false depth (dst ++ one c)%string o
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
  (* an unclosed destination is literal, breaks and all *)
  | IDest kids image esc _ dst o =>
      let '(txt, o') := bdest_lit kids image esc dst o in flush_text txt o'
  | IReference kids image label o =>
      let '(txt, o') := bref_lit kids image label o in flush_text txt o'
  (* an unclosed span is literal too: the scan does not cross the break,
     so a spec that would have continued on the next line never closes *)
  | ISpan kids image _ src o =>
      let '(txt, o') := bspan_lit kids image src o in flush_text txt o'
  (* unreachable: `iresolve` leaves no `IBrace`, `IAttr`, `IBang`,
     `IDelim` or `IClosed` *)
  | IBrace _ _ o | IAttr _ _ _ _ o | IBang _ _ o | IDelim _ _ _ o
  | IClosed _ _ o => o
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
  (* A destination crosses the break: djot.js keeps scanning and strips
     the newline from the destination text at the close, so the byte is
     accumulated and dropped later rather than dropped here -- the
     literal fallback still needs it if the destination never closes. *)
  | IDest kids image esc depth dst o =>
      IDest kids image false depth
        (dst ++ (if esc then one bslash else EmptyString) ++ nl)%string o
  | IReference kids image label o =>
      IReference kids image (label ++ nl)%string o
  (* A span's spec crosses the break too, and the newline is whitespace to
     the machine: `[s]{.a` / `.b}` is one span whose classes merge.  It is
     fed rather than accumulated because the machine is what decides
     whether the break separates two tokens. *)
  | ISpan kids image p src o => ispan_feed nl_char kids image p src o
  (* unreachable, as in `ifinish_ostate` *)
  | (IBrace _ _ _ | IAttr _ _ _ _ _ | IBang _ _ _ | IDelim _ _ _ _
    | IClosed _ _ _) as st' => st'
  end.

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
  (* an open destination owes the next line; `IClosed` cannot appear,
     since `iresolve` has just turned it into text *)
  | IBrace _ _ _ | IAttr _ _ _ _ _ | IBang _ _ _ | IDelim _ _ _ _
  | IClosed _ _ _ | ISpan _ _ _ _ _
  | IReference _ _ _ _ | IDest _ _ _ _ _ _ => false
  end.

Lemma ibreak_closed :
  forall st,
    iscan_closed st = true ->
    ibreak st = IText false EmptyString None
                  (OState (mk SoftBreak :: ifinish_rev st) []).
Proof.
  intros st H. unfold iscan_closed, ibreak, ifinish_rev, ifinish_ostate in *.
  destruct (iresolve st) as [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|kids img esc depth dst ob];
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

(* An executable certificate for the sense in which this scan does not
   backtrack.  One unit of fuel authorizes dispatching one source byte;
   state rewrites such as closing or abandoning a scope spend no source
   fuel and never feed that byte back to the scanner.  This deliberately
   says nothing about the internal cost of a dispatch -- `oclose` may walk
   the opener stack -- so it is not a linear-time theorem.  Bracket
   attribute reparse will be a separate, strictly decreasing call with
   attribute recognition disabled, rather than a relaxation of this
   contract. *)
Fixpoint iscan_str_fuel (fuel : nat) (s : string) (st : iscan)
  : option iscan :=
  match s with
  | EmptyString => Some st
  | String c rest =>
      match fuel with
      | O => None
      | S fuel' => iscan_str_fuel fuel' rest (istep c st)
      end
  end.

Lemma iscan_str_no_reread :
  forall s st,
    iscan_str_fuel (String.length s) s st = Some (iscan_str s st).
Proof.
  induction s as [|c rest IH]; intros st; cbn [String.length iscan_str_fuel
    iscan_str]; [reflexivity|apply IH].
Qed.

Lemma iscan_str_fuel_short :
  forall s fuel st,
    fuel < String.length s -> iscan_str_fuel fuel s st = None.
Proof.
  induction s as [|c rest IH]; intros fuel st Hlt.
  - cbn [String.length] in Hlt. lia.
  - destruct fuel as [|fuel']; [reflexivity|].
    cbn [String.length iscan_str_fuel] in Hlt |- *.
    apply IH. lia.
Qed.

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
  | IBang txt prev o => IBang txt prev (oout_app base o)
  | IClosed kids image o => IClosed kids image (oout_app base o)
  | ISpan kids image p src o => ISpan kids image p src (oout_app base o)
  | IAttr p src txt prev o => IAttr p src txt prev (oout_app base o)
  | IReference kids image label o =>
      IReference kids image label (oout_app base o)
  | IDest kids image esc depth dst o =>
      IDest kids image esc depth dst (oout_app base o)
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

Lemma bpush_app :
  forall image o base,
    bpush image (oout_app base o) = oout_app base (bpush image o).
Proof. intros image o base. reflexivity. Qed.

Lemma bclose_app :
  forall o base,
    bclose (oout_app base o)
    = option_map (fun p => (fst (fst p), snd (fst p),
                            oout_app base (snd p))) (bclose o).
Proof.
  intros o base. unfold bclose. cbn [oout_app os_stk os_out].
  destruct (bclose_go [] (os_stk o)) as [[[content image] rest]|]; reflexivity.
Qed.

(* The bracket reconstruction is the second place the suffix is not
   inert, and for the same reason as `oflatten`: `opop_str` reads the
   most recent node, and with nothing emitted yet that node comes from
   the suffix.  The hypothesis is the one `ofinish_out_app` already
   carries, and its single caller discharges it the same way -- the
   suffix is a previous line, ending in a `SoftBreak`. *)
Lemma opop_str_app :
  forall o base,
    starts_str base = false ->
    opop_str (oout_app base o)
    = (fst (opop_str o), oout_app base (snd (opop_str o))).
Proof.
  intros [out stk] base Hb. unfold opop_str, oout_app; cbn [os_out os_stk].
  destruct stk as [|f fs].
  - destruct out as [|n rest]; cbn [app].
    + destruct base as [|[a [|p ps] i] base']; try reflexivity.
      cbn [starts_str] in Hb. destruct i; try reflexivity. discriminate.
    + destruct n as [a [|p ps] i]; try reflexivity.
      destruct i; reflexivity.
  - destruct (fr_out f) as [|n rest]; [reflexivity|].
    destruct n as [a [|p ps] i]; try reflexivity.
    destruct i; reflexivity.
Qed.

Lemma bflat_app :
  forall kids txt o base,
    bflat kids txt (oout_app base o)
    = (fst (bflat kids txt o), oout_app base (snd (bflat kids txt o))).
Proof.
  induction kids as [|[a attrs i] kids IH]; intros txt o base; cbn [bflat].
  - reflexivity.
  - destruct attrs as [|p ps];
      [destruct i; try (rewrite flush_text_app, oemit_app; apply IH); apply IH
      |rewrite flush_text_app, oemit_app; apply IH].
Qed.

Lemma bsplit_nl_app :
  forall s txt o base,
    bsplit_nl s txt (oout_app base o)
    = (fst (bsplit_nl s txt o), oout_app base (snd (bsplit_nl s txt o))).
Proof.
  induction s as [|c s IH]; intros txt o base; cbn [bsplit_nl];
    [reflexivity|].
  destruct (Ascii.eqb c nl_char);
    [rewrite flush_text_app, oemit_app|]; apply IH.
Qed.

Lemma bclosed_lit_app :
  forall kids image o base,
    starts_str base = false ->
    bclosed_lit kids image (oout_app base o)
    = (fst (bclosed_lit kids image o),
       oout_app base (snd (bclosed_lit kids image o))).
Proof.
  intros kids image o base Hb. unfold bclosed_lit.
  rewrite (opop_str_app o base Hb).
  destruct (opop_str o) as [pre o1]; cbn [fst snd].
  rewrite bflat_app.
  destruct (bflat kids (pre ++ bracket_open image)%string o1) as [txt o2].
  reflexivity.
Qed.

Lemma bdest_lit_app :
  forall kids image esc dst o base,
    starts_str base = false ->
    bdest_lit kids image esc dst (oout_app base o)
    = (fst (bdest_lit kids image esc dst o),
       oout_app base (snd (bdest_lit kids image esc dst o))).
Proof.
  intros kids image esc dst o base Hb. unfold bdest_lit.
  rewrite (bclosed_lit_app kids image o base Hb).
  destruct (bclosed_lit kids image o) as [txt o']; cbn [fst snd].
  apply bsplit_nl_app.
Qed.

Lemma bref_lit_app :
  forall kids image label o base,
    starts_str base = false ->
    bref_lit kids image label (oout_app base o) =
    let '(txt, o') := bref_lit kids image label o in
    (txt, oout_app base o').
Proof.
  intros kids image label o base Hb. unfold bref_lit.
  rewrite (bclosed_lit_app kids image o base Hb).
  destruct (bclosed_lit kids image o). reflexivity.
Qed.

Lemma bspan_lit_app :
  forall kids image src o base,
    starts_str base = false ->
    bspan_lit kids image src (oout_app base o) =
    let '(txt, o') := bspan_lit kids image src o in
    (txt, oout_app base o').
Proof.
  intros kids image src o base Hb. unfold bspan_lit.
  rewrite (bclosed_lit_app kids image o base Hb).
  destruct (bclosed_lit kids image o). reflexivity.
Qed.

Lemma ilead_app :
  forall c txt prev o base,
    ilead c txt prev (oout_app base o) = iout_app base (ilead c txt prev o).
Proof.
  intros c txt prev o base. unfold ilead.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c); [cbn [iout_app]; rewrite flush_text_app; reflexivity|].
  destruct (Ascii.eqb c lbrace); [reflexivity|].
  destruct (Ascii.eqb c bang); [reflexivity|].
  destruct (Ascii.eqb c lbrack);
    [cbn [iout_app]; rewrite flush_text_app, bpush_app; reflexivity|].
  destruct (Ascii.eqb c rbrack);
    [rewrite flush_text_app, bclose_app;
     destruct (bclose (flush_text txt o)) as [[[kids image] o']|]; reflexivity|].
  destruct (dstyle_of c); reflexivity.
Qed.

Lemma ospan_bang_app :
  forall image o base,
    starts_str base = false ->
    ospan_bang image (oout_app base o) = oout_app base (ospan_bang image o).
Proof.
  intros image o base Hb. unfold ospan_bang. destruct image; [|reflexivity].
  rewrite (opop_str_app o base Hb).
  destruct (opop_str o) as [pre o1]; cbn [fst snd].
  apply flush_text_app.
Qed.

Lemma iattr_attach_app :
  forall a src txt prev o base,
    starts_str base = false ->
    iattr_attach a src txt prev (oout_app base o)
    = iout_app base (iattr_attach a src txt prev o).
Proof.
  intros a src txt prev o base Hb. unfold iattr_attach.
  destruct a as [|kv a'];
    [destruct (nonempty_str txt); reflexivity|].
  destruct (last_ws_split txt) as [pre w].
  destruct (nonempty_str w); [|destruct (nonempty_str txt); reflexivity].
  cbn [iout_app]. rewrite flush_text_app, oemit_app. reflexivity.
Qed.

Lemma iattr_feed_app :
  forall c p src txt prev o base,
    starts_str base = false ->
    iattr_feed c p src txt prev (oout_app base o)
    = iout_app base (iattr_feed c p src txt prev o).
Proof.
  intros c p src txt prev o base Hb. unfold iattr_feed.
  destruct (ap_failed (astep p c)); [apply ilead_app|].
  destruct (ap_done (astep p c)); [apply iattr_attach_app, Hb|reflexivity].
Qed.

Lemma ispan_feed_app :
  forall c kids image p src o base,
    starts_str base = false ->
    ispan_feed c kids image p src (oout_app base o)
    = iout_app base (ispan_feed c kids image p src o).
Proof.
  intros c kids image p src o base Hb. unfold ispan_feed.
  destruct (ap_failed (astep p c)).
  - rewrite (bspan_lit_app kids image src o base Hb).
    destruct (bspan_lit kids image src o) as [txt o']. apply ilead_app.
  - destruct (ap_done (astep p c)); [|reflexivity].
    cbn [iout_app]. rewrite ospan_bang_app by exact Hb.
    rewrite oemit_app. reflexivity.
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
  forall base st,
    starts_str base = false ->
    iresolve (iout_app base st) = iout_app base (iresolve st).
Proof.
  intros base [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|kids img esc depth dst ob] Hb;
    try reflexivity.
  - apply idelim_resolve_app.
  - cbn [iresolve iout_app]. rewrite (bclosed_lit_app kids img ob base Hb).
    destruct (bclosed_lit kids img ob) as [txt o']. reflexivity.
Qed.

Lemma istep_out_app :
  forall c base st,
    starts_str base = false ->
    istep c (iout_app base st) = iout_app base (istep c st).
Proof.
  intros c base [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|kids img esc depth dst ob] Hb;
    cbn [iout_app istep].
  - reflexivity.
  - apply ilead_app.
  - unfold ibrace_step. destruct (dstyle_of c);
      [cbn [iout_app]; rewrite flush_text_app, opush_app; reflexivity
      |apply iattr_feed_app, Hb].
  - rewrite idelim_resolve_app. destruct (Ascii.eqb c rbrace); [reflexivity|].
    destruct (idelim_resolve k txt cc false (Some c) o)
      as [[] txt' prev' o'|? ? ?|? ? ? ?|? ?|? ? ? ?|? ? ?|? ? ?|? ? ? ? ?|? ? ? ? ?|? ? ? ?|? ? ? ? ? ?]; cbn [iout_app];
      try reflexivity.
    apply ilead_app.
  - destruct (is_tick c); reflexivity.
  - destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); [|reflexivity].
    rewrite (oemit_app (mk (Verbatim (trim_verb txt))) o base).
    apply ilead_app.
  - unfold ibang_step. destruct (Ascii.eqb c lbrack);
      [cbn [iout_app]; rewrite flush_text_app, bpush_app; reflexivity
      |apply ilead_app].
  - destruct (Ascii.eqb c lparen); [reflexivity|].
    destruct (Ascii.eqb c lbrack); [reflexivity|].
    destruct (Ascii.eqb c lbrace); [reflexivity|].
    rewrite (bclosed_lit_app kids img ob base Hb).
    destruct (bclosed_lit kids img ob) as [txt o']. apply ilead_app.
  - apply ispan_feed_app, Hb.
  - apply iattr_feed_app, Hb.
  - destruct (Ascii.eqb c rbrack); [cbn [iout_app]; rewrite oemit_app|];
      reflexivity.
  - destruct esc; [reflexivity|].
    destruct (is_bslash c); [reflexivity|].
    destruct (Ascii.eqb c lparen); [reflexivity|].
    destruct (Ascii.eqb c rparen); [|reflexivity].
    destruct depth; [cbn [iout_app]; rewrite oemit_app|]; reflexivity.
Qed.

Lemma iscan_str_out_app :
  forall s base st,
    starts_str base = false ->
    iscan_str s (iout_app base st) = iout_app base (iscan_str s st).
Proof.
  induction s as [|c s IH]; intros base st Hb; cbn [iscan_str]; [reflexivity|].
  rewrite istep_out_app by exact Hb. apply IH, Hb.
Qed.

Lemma ibreak_out_app :
  forall base st,
    starts_str base = false ->
    ibreak (iout_app base st) = iout_app base (ibreak st).
Proof.
  intros base st Hb. unfold ibreak. rewrite iresolve_app by exact Hb.
  destruct (iresolve st) as [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|kids img esc depth dst ob];
    cbn [iout_app]; try reflexivity.
  1,2: rewrite flush_text_app, oemit_app; reflexivity.
  2: apply ispan_feed_app, Hb.
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
    starts_str base = false ->
    iscan_lines l (iout_app base st) = iout_app base (iscan_lines l st).
Proof.
  induction l as [|x [|y rest] IH]; intros base st Hb; cbn [iscan_lines].
  - reflexivity.
  - apply iscan_str_out_app, Hb.
  - rewrite iscan_str_out_app, ibreak_out_app by exact Hb. apply IH, Hb.
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
  rewrite iresolve_app by exact Hb.
  destruct (iresolve st) as [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|kids img esc depth dst ob];
    cbn [iout_app].
  1,2: rewrite flush_text_app; apply ofinish_out_app, Hb.
  1,2: apply ofinish_out_app, Hb.
  1,2: rewrite oemit_app; apply ofinish_out_app, Hb.
  all: try (apply ofinish_out_app, Hb).
  - rewrite (bspan_lit_app kids img ssrc sob base Hb).
    destruct (bspan_lit kids img ssrc sob) as [txt o']; cbn [fst snd].
    rewrite flush_text_app. apply ofinish_out_app, Hb.
  - rewrite (bref_lit_app kids img label ob base Hb).
    destruct (bref_lit kids img label ob) as [txt o']; cbn [fst snd].
    rewrite flush_text_app. apply ofinish_out_app, Hb.
  - rewrite (bdest_lit_app kids img esc dst ob base Hb).
    destruct (bdest_lit kids img esc dst ob) as [txt o']; cbn [fst snd].
    rewrite flush_text_app. apply ofinish_out_app, Hb.
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
  apply orb_false_iff in Hc as [Hc Hbg].
  apply orb_false_iff in Hc as [Hc Hrk].
  apply orb_false_iff in Hc as [Hc Hlk].
  apply orb_false_iff in Hc as [Hc Hrb].
  apply orb_false_iff in Hc as [Hc Hlb].
  apply orb_false_iff in Hc as [Hc Hdl].
  apply orb_false_iff in Hc as [Hbs Htk].
  unfold ilead. rewrite Hbs, Htk, Hlb, Hbg, Hlk, Hrk.
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
  destruct r as [t|v|k kids|img kids dst|rimg rkids rlabel];
    [|unfold text_sep_ok; destruct s; reflexivity ..].
  unfold cis_ok in H. cbn [ci_sep_ok ci_pair_ok] in H.
  repeat rewrite andb_false_r in H. discriminate.
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

Definition marked_close (k : dstyle) (tail : string) : string :=
  String (dchar k) (String rbrace tail).

Lemma ilead_dchar :
  forall k txt prev o,
    ilead (dchar k) txt prev o
    = IDelim k txt (nonspace_at (str_last txt prev)) o.
Proof. intros [] txt prev o; reflexivity. Qed.

Lemma istep_marked_close :
  forall k txt prev o o',
    oclose k true (flush_text txt o) = Some o' ->
    istep rbrace (ilead (dchar k) txt prev o)
    = IText false EmptyString (Some rbrace) o'.
Proof.
  intros k txt prev o o' H. rewrite ilead_dchar.
  cbn [istep].
  change (idelim_resolve k txt (nonspace_at (str_last txt prev)) true
            (Some rbrace) o
          = IText false EmptyString (Some rbrace) o').
  unfold idelim_resolve. rewrite orb_true_r, H. reflexivity.
Qed.

Lemma iscan_marked_flush :
  forall k tail txt prev before base,
    (nonempty before || nonempty_str txt)%bool = true ->
    exists p,
      iscan_str (marked_close k tail)
        (IText false txt prev (oemit_all before (opush k true base)))
      = iscan_str (marked_close k tail)
          (IText false EmptyString p
            (flush_text txt (oemit_all before (opush k true base)))).
Proof.
  intros k tail txt prev before base Hne.
  assert (Hclose : exists o',
    oclose k true
      (flush_text txt (oemit_all before (opush k true base))) = Some o').
  { destruct (nonempty_str txt) eqn:Htxt.
    - exists (oemit (mk (dnode k (before ++ [mk (Str txt)])%list)) base).
      unfold flush_text. rewrite Htxt.
      change (oclose k true
                (oemit_all [mk (Str txt)]
                  (oemit_all before (opush k true base)))
              = Some
                  (oemit (mk (dnode k (before ++ [mk (Str txt)])%list))
                    base)).
      rewrite <- (oemit_all_app before [mk (Str txt)] (opush k true base)).
      cbn [oemit_all]. apply oclose_oemit_all_marked. destruct before; reflexivity.
    - apply orb_true_iff in Hne as [Hbefore|Htxt']; [|discriminate].
      exists (oemit (mk (dnode k before)) base).
      unfold flush_text. rewrite Htxt.
      apply oclose_oemit_all_marked, Hbefore. }
  destruct Hclose as [o' Hclose]. exists None.
  unfold marked_close. cbn [iscan_str istep].
  rewrite (istep_marked_close k txt prev _ o' Hclose).
  rewrite (istep_marked_close k EmptyString None _ o').
  - reflexivity.
  - cbn [flush_text]. exact Hclose.
Qed.

Lemma iscan_marked_open :
  forall d txt prev o,
    iscan_str (String lbrace (one (dchar d))) (IText false txt prev o)
    = IText false EmptyString (Some (dchar d))
        (opush d true (flush_text txt o)).
Proof. intros [] txt prev o; reflexivity. Qed.

Lemma iscan_marked_close_emit :
  forall d tail ns base p,
    nonempty ns = true ->
    iscan_str (marked_close d tail)
      (IText false EmptyString p (oemit_all ns (opush d true base)))
    = iscan_str tail
        (IText false EmptyString (Some rbrace)
          (oemit (mk (dnode d ns)) base)).
Proof.
  intros d tail ns base p Hne. unfold marked_close. cbn [iscan_str istep].
  rewrite (istep_marked_close d EmptyString p
    (oemit_all ns (opush d true base))
    (oemit (mk (dnode d ns)) base)).
  - reflexivity.
  - cbn [flush_text]. apply oclose_oemit_all_marked, Hne.
Qed.

Lemma iscan_after_verb_nontick :
  forall s n body o,
    nonempty_str s = true -> starts_tick s = false ->
    iscan_str s (IVerb n n body o)
    = iscan_str s
        (IText false EmptyString (Some tick)
          (oemit (mk (Verbatim (trim_verb body))) o)).
Proof.
  intros [|c s] n body o Hne Htick; [discriminate|].
  cbn [starts_tick] in Htick. cbn [iscan_str istep]. rewrite Htick.
  rewrite nat_eqb_refl. reflexivity.
Qed.

Lemma escape_str_starts_nontick :
  forall s, nonempty_str s = true -> starts_tick (escape_str s) = false.
Proof.
  intros [|c s] H; [discriminate|]. cbn [escape_str].
  destruct (needs_escape c) eqn:Hc; [reflexivity|].
  cbn [starts_tick]. destruct (is_tick c) eqn:Ht; [|reflexivity].
  rewrite (needs_escape_tick c Ht) in Hc. discriminate.
Qed.

Lemma escape_str_nonempty :
  forall s, nonempty_str s = true -> nonempty_str (escape_str s) = true.
Proof.
  intros [|c s] H; [discriminate|]. cbn [escape_str].
  destruct (needs_escape c); reflexivity.
Qed.

Lemma marked_close_nonempty :
  forall k tail, nonempty_str (marked_close k tail) = true.
Proof. intros k tail. destruct k; reflexivity. Qed.

Lemma marked_close_starts_nontick :
  forall k tail, starts_tick (marked_close k tail) = false.
Proof. intros k tail. destruct k; reflexivity. Qed.

(* What a verbatim needs of whatever follows it: a nonempty continuation
   that does not start with a backtick, or its closing run would grow.
   Stated over an arbitrary closer because two constructs now supply one
   -- a marked delimiter and a bracket -- and the proof never looks at
   which. *)
(*
Scanning a link
---------------

The bracket analogues of `iscan_marked_open` and
`iscan_marked_close_emit`.  The close is longer than a delimiter's
because it spans three dispatches -- the `]`, the `(` and the balanced
`)` -- with the destination scanned as escaped text in between. *)

(* One lemma for both openers: the `!` is a separate dispatch, but it
   only decides which frame is pushed. *)
Lemma iscan_bracket_open :
  forall image txt prev o,
    iscan_str (bracket_open image) (IText false txt prev o)
    = IText false EmptyString (Some lbrack) (bpush image (flush_text txt o)).
Proof. intros [] txt prev o; reflexivity. Qed.

Lemma bclose_flush_bpush :
  forall txt image before base,
    bclose (flush_text txt (oemit_all before (bpush image base)))
    = Some (if nonempty_str txt
            then (before ++ [mk (Str txt)])%list else before, image, base).
Proof.
  intros txt image before base. unfold flush_text.
  destruct (nonempty_str txt).
  - replace (oemit (mk (Str txt)) (oemit_all before (bpush image base)))
      with (oemit_all [mk (Str txt)] (oemit_all before (bpush image base)))
      by reflexivity.
    rewrite <- (oemit_all_app before [mk (Str txt)] (bpush image base)).
    apply bclose_oemit_all.
  - apply bclose_oemit_all.
Qed.

Lemma drop_nl_no_nl : forall s, no_nl s = true -> drop_nl s = s.
Proof.
  induction s as [|c s IH]; intros H; [reflexivity|].
  cbn [no_nl] in H. apply andb_true_iff in H as [Hc H].
  apply negb_true_iff in Hc. cbn [drop_nl].
  change nl_char with "010"%char. rewrite Hc, (IH H). reflexivity.
Qed.

(* The destination is escaped text, and reads back the way escaped text
   does: `needs_escape_dest` claims every byte the mode dispatches on,
   and its escapes decode because each such byte is punctuation. *)
Lemma iscan_dest_escape :
  forall s kids image depth dst o,
    iscan_str (escape_dest s) (IDest kids image false depth dst o)
    = IDest kids image false depth (dst ++ s)%string o.
Proof.
  induction s as [|c s IH]; intros kids image depth dst o;
    cbn [escape_dest]; [rewrite append_empty_r; reflexivity|].
  assert (Hsplit : forall t, (dst ++ String c t)%string
                             = ((dst ++ one c) ++ t)%string).
  { intro t. rewrite (append_assoc dst (one c) t). reflexivity. }
  destruct (needs_escape_dest c) eqn:Hc.
  - pose proof (needs_escape_dest_punct c Hc) as Hp.
    cbn [iscan_str istep]. change (is_bslash "\"%char) with true.
    cbn [istep]. rewrite Hp, IH, Hsplit. reflexivity.
  - assert (Hbs : is_bslash c = false).
    { destruct (is_bslash c) eqn:E; [|reflexivity].
      unfold needs_escape_dest, needs_escape in Hc.
      apply Ascii.eqb_eq in E. subst c. discriminate. }
    assert (Hlp : Ascii.eqb c lparen = false).
    { destruct (Ascii.eqb c lparen) eqn:E; [|reflexivity].
      unfold needs_escape_dest in Hc. rewrite E in Hc.
      rewrite orb_true_r in Hc. discriminate. }
    assert (Hrp : Ascii.eqb c rparen = false).
    { destruct (Ascii.eqb c rparen) eqn:E; [|reflexivity].
      unfold needs_escape_dest in Hc. rewrite E in Hc.
      rewrite orb_true_r in Hc. discriminate. }
    cbn [iscan_str istep]. rewrite Hbs, Hlp, Hrp, IH, Hsplit. reflexivity.
Qed.

Lemma istep_rbrack_close :
  forall txt prev o kids image o',
    bclose (flush_text txt o) = Some (kids, image, o') ->
    istep rbrack (IText false txt prev o) = IClosed kids image o'.
Proof.
  intros txt prev o kids image o' H. cbn [istep]. unfold ilead.
  change (is_bslash rbrack) with false.
  change (is_tick rbrack) with false.
  change (Ascii.eqb rbrack lbrace) with false.
  change (Ascii.eqb rbrack bang) with false.
  change (Ascii.eqb rbrack lbrack) with false.
  change (Ascii.eqb rbrack rbrack) with true.
  rewrite H. reflexivity.
Qed.

Lemma iscan_link_close :
  forall dst tail ns image base p,
    no_nl dst = true ->
    iscan_str (link_close dst tail)
      (IText false EmptyString p (oemit_all ns (bpush image base)))
    = iscan_str tail
        (IText false EmptyString (Some rparen)
          (oemit (mk (bnode image ns (Direct dst))) base)).
Proof.
  intros dst tail ns image base p Hnl. unfold link_close.
  cbn [iscan_str].
  rewrite (istep_rbrack_close EmptyString p _ ns image base
             (bclose_flush_bpush EmptyString image ns base)).
  cbn [istep]. change (Ascii.eqb lparen lparen) with true.
  rewrite iscan_str_app, iscan_dest_escape.
  change ((EmptyString ++ dst)%string) with dst.
  cbn [iscan_str istep].
  change (is_bslash rparen) with false.
  change (Ascii.eqb rparen lparen) with false.
  change (Ascii.eqb rparen rparen) with true.
  rewrite (drop_nl_no_nl dst Hnl). reflexivity.
Qed.

(* The bracket's flush law, and it needs no precondition: a `]` closes an
   empty label as happily as a full one, which is what `empty_ok` below
   records and what makes `[](u)` representable. *)
Lemma iscan_bracket_flush :
  forall dst tail txt prev image before base,
    exists p,
      iscan_str (link_close dst tail)
        (IText false txt prev (oemit_all before (bpush image base)))
      = iscan_str (link_close dst tail)
          (IText false EmptyString p
            (flush_text txt (oemit_all before (bpush image base)))).
Proof.
  intros dst tail txt prev image before base. exists (Some lbrack).
  pose (ns := if nonempty_str txt
              then (before ++ [mk (Str txt)])%list else before).
  unfold link_close. cbn [iscan_str].
  rewrite (istep_rbrack_close txt prev _ ns image base
             (bclose_flush_bpush txt image before base)).
  rewrite (istep_rbrack_close EmptyString (Some lbrack)
             (flush_text txt (oemit_all before (bpush image base)))
             ns image base);
    [reflexivity|].
  cbn [flush_text nonempty_str].
  apply (bclose_flush_bpush txt image before base).
Qed.

Lemma link_close_app :
  forall dst t, (link_close dst EmptyString ++ t)%string = link_close dst t.
Proof.
  intros dst t. unfold link_close. cbn [append].
  rewrite append_assoc. cbn [append]. reflexivity.
Qed.

(*
Scanning a reference link
-------------------------

The same three dispatches as a direct link's closer, with `[`, the label
and `]` in place of `(`, the destination and `)`.  The label is easier:
the mode escapes nothing and dispatches on nothing but `]`, so the whole
of it goes in one induction.
*)

Lemma iscan_ref_label :
  forall label kids image acc o,
    no_char rbrack label = true ->
    iscan_str label (IReference kids image acc o)
    = IReference kids image (acc ++ label)%string o.
Proof.
  induction label as [|c label IH]; intros kids image acc o H;
    [rewrite append_empty_r; reflexivity|].
  cbn [no_char] in H. apply andb_true_iff in H as [Hc H].
  apply negb_true_iff in Hc.
  cbn [iscan_str istep]. rewrite Hc, (IH _ _ _ _ H).
  rewrite append_assoc. reflexivity.
Qed.

Lemma iscan_ref_close :
  forall label tail ns image base p,
    nonempty_str label = true ->
    no_char rbrack label = true ->
    iscan_str (ref_close label tail)
      (IText false EmptyString p (oemit_all ns (bpush image base)))
    = iscan_str tail
        (IText false EmptyString (Some rbrack)
          (oemit (mk (bnode image ns (Reference (normalize_label label)))) base)).
Proof.
  intros label tail ns image base p Hne Hbr. unfold ref_close.
  cbn [iscan_str].
  rewrite (istep_rbrack_close EmptyString p _ ns image base
             (bclose_flush_bpush EmptyString image ns base)).
  cbn [istep]. change (Ascii.eqb lbrack lparen) with false.
  change (Ascii.eqb lbrack lbrack) with true.
  rewrite iscan_str_app, (iscan_ref_label label ns image EmptyString _ Hbr).
  change ((EmptyString ++ label)%string) with label.
  cbn [iscan_str istep]. change (Ascii.eqb rbrack rbrack) with true.
  destruct label as [|c label']; [discriminate Hne|reflexivity].
Qed.

(* The flush law, as for a direct link and by the same `]` dispatch. *)
Lemma iscan_ref_flush :
  forall label tail txt prev image before base,
    exists p,
      iscan_str (ref_close label tail)
        (IText false txt prev (oemit_all before (bpush image base)))
      = iscan_str (ref_close label tail)
          (IText false EmptyString p
            (flush_text txt (oemit_all before (bpush image base)))).
Proof.
  intros label tail txt prev image before base. exists (Some lbrack).
  pose (ns := if nonempty_str txt
              then (before ++ [mk (Str txt)])%list else before).
  unfold ref_close. cbn [iscan_str].
  rewrite (istep_rbrack_close txt prev _ ns image base
             (bclose_flush_bpush txt image before base)).
  rewrite (istep_rbrack_close EmptyString (Some lbrack)
             (flush_text txt (oemit_all before (bpush image base)))
             ns image base);
    [reflexivity|].
  cbn [flush_text nonempty_str].
  apply (bclose_flush_bpush txt image before base).
Qed.

Lemma ref_close_app :
  forall label t, (ref_close label EmptyString ++ t)%string = ref_close label t.
Proof.
  intros label t. unfold ref_close. cbn [append].
  rewrite append_assoc. cbn [append]. reflexivity.
Qed.

Lemma ref_close_nonempty :
  forall label tail, nonempty_str (ref_close label tail) = true.
Proof. intros label tail. reflexivity. Qed.

Lemma ref_close_starts_nontick :
  forall label tail, starts_tick (ref_close label tail) = false.
Proof. intros label tail. reflexivity. Qed.

Lemma link_close_nonempty :
  forall dst tail, nonempty_str (link_close dst tail) = true.
Proof. intros dst tail. reflexivity. Qed.

Lemma link_close_starts_nontick :
  forall dst tail, starts_tick (link_close dst tail) = false.
Proof. intros dst tail. reflexivity. Qed.

Lemma after_verb_source_nontick :
  forall v rest cl,
    cis_ok (CIVerb v :: rest) = true ->
    nonempty_str cl = true -> starts_tick cl = false ->
    nonempty_str (ci_text rest ++ cl) = true /\
    starts_tick (ci_text rest ++ cl) = false.
Proof.
  intros v [|c rest] cl Hok Hcl Hct.
  - cbn [ci_text append]. split; assumption.
  - destruct c as [s|w|d kids|img kids dst|rimg rkids rlabel].
    + pose proof (cis_ok_head (CIStr s) rest (cis_ok_tail _ _ Hok)) as Hs.
      cbn [ci_ok] in Hs. apply andb_true_iff in Hs as [Hs _].
      cbn [ci_text ci_src]. split.
      * destruct (escape_str s) eqn:E;
          [pose proof (escape_str_nonempty s Hs); rewrite E in H; discriminate
          |reflexivity].
      * rewrite starts_tick_app_l.
        -- rewrite starts_tick_app_l.
           ++ apply escape_str_starts_nontick, Hs.
           ++ apply escape_str_nonempty, Hs.
        -- destruct (escape_str s) eqn:E; [|reflexivity].
           pose proof (escape_str_nonempty s Hs). rewrite E in H.
           discriminate.
    + unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
      repeat rewrite andb_false_r in Hok. discriminate.
    + cbn [ci_text]. rewrite ci_src_delim.
      cbn [append starts_tick]. split; reflexivity.
    + cbn [ci_text]. rewrite ci_src_link. unfold bracket_open.
      destruct img; cbn [append starts_tick]; split; reflexivity.
    + cbn [ci_text]. rewrite ci_src_ref. unfold bracket_open.
      destruct rimg; cbn [append starts_tick]; split; reflexivity.
Qed.

Lemma after_verb_rest_nontick :
  forall v c rest,
    cis_ok (CIVerb v :: c :: rest) = true ->
    nonempty_str (ci_text (c :: rest)) = true /\
    starts_tick (ci_text (c :: rest)) = false.
Proof.
  intros v c rest Hok.
  destruct (after_verb_source_nontick v (c :: rest)
              (marked_close DEmph EmptyString) Hok
              (marked_close_nonempty _ _) (marked_close_starts_nontick _ _))
    as [Hne Htick].
  destruct c as [s|w|d kids|img kids dst|rimg rkids rlabel].
  - pose proof (cis_ok_head (CIStr s) rest (cis_ok_tail _ _ Hok)) as Hs.
    cbn [ci_ok] in Hs. apply andb_true_iff in Hs as [Hs _].
    cbn [ci_text ci_src]. split.
    + destruct (escape_str s) eqn:E;
        [pose proof (escape_str_nonempty s Hs); rewrite E in H; discriminate
        |reflexivity].
    + rewrite starts_tick_app_l;
        [apply escape_str_starts_nontick, Hs|apply escape_str_nonempty, Hs].
  - unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
    repeat rewrite andb_false_r in Hok. discriminate.
  - cbn [ci_text]. rewrite ci_src_delim. cbn [starts_tick nonempty_str].
    split; reflexivity.
  - cbn [ci_text]. rewrite ci_src_link. unfold bracket_open.
    destruct img; cbn [append starts_tick nonempty_str]; split; reflexivity.
  - cbn [ci_text]. rewrite ci_src_ref. unfold bracket_open.
    destruct rimg; cbn [append starts_tick nonempty_str]; split; reflexivity.
Qed.

Lemma orb_false_r_true : forall b, (b || false)%bool = true -> b = true.
Proof. intros [] H; [reflexivity | exact H]. Qed.

(* The scanner inversion, one scope deep.

   Scanning a canonical run of inlines from inside an open scope reaches
   the same state as emitting their nodes.  The scope's *closer* is a
   parameter, because two constructs supply one -- a marked delimiter and
   a bracket -- and the proof needs exactly three things of it: that it
   is nonempty and does not start with a backtick (so a verbatim before
   it resolves), and that scanning it flushes the pending text.  That
   last is the `Hflush` hypothesis, and `empty_ok` is where the two
   differ: `oclose` refuses an empty scope, `bclose` does not, which is
   what makes `[](u)` representable and `{__}` not. *)
Lemma iscan_cis_scope :
  forall cis cl O empty_ok txt prev before,
    nonempty_str cl = true -> starts_tick cl = false ->
    (forall txt' prev' before',
       (nonempty before' || nonempty_str txt' || empty_ok)%bool = true ->
       exists p,
         iscan_str cl (IText false txt' prev' (oemit_all before' O))
         = iscan_str cl
             (IText false EmptyString p
               (flush_text txt' (oemit_all before' O)))) ->
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    (nonempty before || nonempty_str txt || nonempty cis || empty_ok)%bool
      = true ->
    exists p,
      iscan_str (ci_text cis ++ cl)
        (IText false txt prev (oemit_all before O))
      = iscan_str cl
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt (oemit_all before O)))).
Proof.
  intro cis. pattern cis.
  apply (well_founded_induction (well_founded_ltof _ cis_size)).
  clear cis. intros cis IH cl O empty_ok txt prev before Hcl Hct Hflush Hok Hsep Hne.
  destruct cis as [|c rest].
  - cbn [ci_text ci_inlines map append nonempty] in Hne |- *.
    apply Hflush. rewrite <- Hne. destruct (nonempty before), (nonempty_str txt);
      reflexivity.
  - destruct c as [s|v|d kids|img kids dst|rimg rkids rlabel].
    + destruct txt as [|x txt']; [|discriminate].
      pose proof (cis_ok_head (CIStr s) rest Hok) as Hsok.
      cbn [ci_ok] in Hsok. apply andb_true_iff in Hsok as [Hs _].
      assert (Hlt : ltof (list cinline) cis_size rest (CIStr s :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      pose proof (IH rest Hlt cl O empty_ok s prev before Hcl Hct Hflush
        (cis_ok_tail _ _ Hok) (ci_str_tail_sep s rest Hok Hs)) as IHr.
      assert (Hnr : nonempty before || nonempty_str s || nonempty rest
                    || empty_ok = true).
      { rewrite Hs, orb_true_r. reflexivity. }
      destruct (IHr Hnr) as [p Ep]. exists p.
      cbn [ci_text ci_src ci_inlines map append].
      rewrite append_assoc, iscan_str_app, iscan_escape.
      change (EmptyString ++ s)%string with s. rewrite Ep.
      unfold flush_text at 1 2. cbn [nonempty_str ci_ast mk oemit_all].
      rewrite Hs. reflexivity.
    + pose proof (ci_verb_nonempty v rest Hok) as Hvne.
      pose proof (ci_verb_content_ok v rest Hok) as Hvok.
      destruct (after_verb_source_nontick v rest cl Hok Hcl Hct)
        as [Hsrcne Hsrctick].
      assert (Hlt : ltof (list cinline) cis_size rest (CIVerb v :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some tick) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hlt cl O empty_ok EmptyString (Some tick) pre
                 Hcl Hct Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [mk (Verbatim v)])%list
                    ltac:(destruct before; reflexivity)) as [p Ep].
        exists p.
        cbn [ci_text ci_src ci_inlines map]. rewrite append_assoc, iscan_str_app.
        rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
        cbn [flush_text nonempty_str].
        rewrite (iscan_after_verb_nontick _ _ _ _ Hsrcne Hsrctick),
          trim_verb_pad by exact Hvok.
        rewrite oemit_all_app in Ep.
        cbn [oemit_all flush_text nonempty_str] in Ep.
        rewrite Ep. cbn [oemit_all ci_ast]. reflexivity.
      * destruct (Hstep (before ++ [mk (Str (String x txt')); mk (Verbatim v)])%list
                    ltac:(destruct before; reflexivity)) as [p Ep].
        exists p.
        cbn [ci_text ci_src ci_inlines map]. rewrite append_assoc, iscan_str_app.
        rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
        cbn [flush_text nonempty_str].
        rewrite (iscan_after_verb_nontick _ _ _ _ Hsrcne Hsrctick),
          trim_verb_pad by exact Hvok.
        rewrite oemit_all_app in Ep.
        cbn [oemit_all flush_text nonempty_str] in Ep.
        rewrite Ep. cbn [oemit_all ci_ast]. reflexivity.
    + pose proof (cis_ok_head (CIDelim d kids) rest Hok) as Hdk.
      rewrite ci_ok_delim in Hdk. apply andb_true_iff in Hdk as [Hkidsne Hkidsok].
      assert (Hkidslt :
        ltof (list cinline) cis_size kids (CIDelim d kids :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_delim. lia. }
      pose proof (IH kids Hkidslt (marked_close d (ci_text rest ++ cl))
        (opush d true (flush_text txt (oemit_all before O))) false
        EmptyString (Some (dchar d)) []
        (marked_close_nonempty _ _) (marked_close_starts_nontick _ _)
        (fun txt' prev' before' e =>
           iscan_marked_flush d (ci_text rest ++ cl) txt' prev' before'
             (flush_text txt (oemit_all before O)) (orb_false_r_true _ e)))
        as IHkids.
      assert (Hkn :
        nonempty (@nil (node inline)) || nonempty_str EmptyString ||
        nonempty kids || false = true).
      { cbn. rewrite orb_false_r. exact Hkidsne. }
      destruct (IHkids Hkidsok eq_refl Hkn) as [pk Ekids].
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CIDelim d kids :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_delim. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rbrace) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hrestlt cl O empty_ok EmptyString (Some rbrace) pre
                 Hcl Hct Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      assert (Hsrc : forall t,
        (((String lbrace
             (String (dchar d)
               (ci_text kids ++ String (dchar d) (one rbrace))) ++ t))%string)
        = ((String lbrace (one (dchar d))) ++
            (ci_text kids ++ marked_close d t))%string).
      { intro t. unfold marked_close, one. cbn [append].
        repeat rewrite append_assoc. reflexivity. }
      assert (Hkins : nonempty (ci_inlines kids) = true).
      { destruct kids; [discriminate|reflexivity]. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CIDelim d kids)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_delim.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_marked_open.
        cbn [flush_text nonempty_str oemit_all] in Ekids |- *. rewrite Ekids.
        rewrite (iscan_marked_close_emit d _ (ci_inlines kids) _ pk Hkins).
        rewrite <- ci_ast_delim. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text nonempty_str oemit_all]. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIDelim d kids)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_delim.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_marked_open.
        cbn [flush_text nonempty_str oemit_all] in Ekids |- *. rewrite Ekids.
        rewrite (iscan_marked_close_emit d _ (ci_inlines kids) _ pk Hkins).
        rewrite <- ci_ast_delim. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text nonempty_str oemit_all]. reflexivity.
    + pose proof (cis_ok_head (CILink img kids dst) rest Hok) as Hdk.
      rewrite ci_ok_link in Hdk. apply andb_true_iff in Hdk as [Hnl Hkidsok].
      assert (Hkidslt :
        ltof (list cinline) cis_size kids (CILink img kids dst :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_link. lia. }
      pose proof (IH kids Hkidslt (link_close dst (ci_text rest ++ cl))
        (bpush img (flush_text txt (oemit_all before O))) true
        EmptyString (Some lbrack) []
        (link_close_nonempty _ _) (link_close_starts_nontick _ _)
        (fun txt' prev' before' _ =>
           iscan_bracket_flush dst (ci_text rest ++ cl) txt' prev' img before'
             (flush_text txt (oemit_all before O)))) as IHkids.
      destruct (IHkids Hkidsok eq_refl (orb_true_r _)) as [pk Ekids].
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CILink img kids dst :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_link. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rparen) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hrestlt cl O empty_ok EmptyString (Some rparen) pre
                 Hcl Hct Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      assert (Hsrc : forall t,
        (((bracket_open img ++ (ci_text kids ++ link_close dst EmptyString))
          ++ t))%string
        = (bracket_open img ++ (ci_text kids ++ link_close dst t))%string).
      { intro t. rewrite append_assoc, append_assoc, link_close_app.
        reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CILink img kids dst)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_link.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open.
        cbn [flush_text nonempty_str oemit_all] in Ekids |- *. rewrite Ekids.
        rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
        rewrite <- ci_ast_link. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text nonempty_str oemit_all]. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CILink img kids dst)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_link.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open.
        cbn [flush_text nonempty_str oemit_all] in Ekids |- *. rewrite Ekids.
        rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
        rewrite <- ci_ast_link. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text nonempty_str oemit_all]. reflexivity.
    + (* a reference link: the direct link's case with the other closer *)
      pose proof (cis_ok_head (CIRef rimg rkids rlabel) rest Hok) as Hdk.
      rewrite ci_ok_ref in Hdk.
      apply andb_true_iff in Hdk as [Hlab Hkidsok].
      apply andb_true_iff in Hlab as [Hlab Hnorm].
      apply andb_true_iff in Hlab as [Hne' Hbr].
      apply String.eqb_eq in Hnorm.
      assert (Hkidslt :
        ltof (list cinline) cis_size rkids (CIRef rimg rkids rlabel :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_ref. lia. }
      pose proof (IH rkids Hkidslt (ref_close rlabel (ci_text rest ++ cl))
        (bpush rimg (flush_text txt (oemit_all before O))) true
        EmptyString (Some lbrack) []
        (ref_close_nonempty _ _) (ref_close_starts_nontick _ _)
        (fun txt' prev' before' _ =>
           iscan_ref_flush rlabel (ci_text rest ++ cl) txt' prev' rimg before'
             (flush_text txt (oemit_all before O)))) as IHkids.
      destruct (IHkids Hkidsok eq_refl (orb_true_r _)) as [pk Ekids].
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CIRef rimg rkids rlabel :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_ref. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rbrack) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hrestlt cl O empty_ok EmptyString (Some rbrack) pre
                 Hcl Hct Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      assert (Hsrc : forall t,
        (((bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel EmptyString))
          ++ t))%string
        = (bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel t))%string).
      { intro t. rewrite append_assoc, append_assoc, ref_close_app.
        reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CIRef rimg rkids rlabel)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_ref.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open.
        cbn [flush_text nonempty_str oemit_all] in Ekids |- *. rewrite Ekids.
        rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr),
                Hnorm.
        rewrite <- ci_ast_ref. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text nonempty_str oemit_all]. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIRef rimg rkids rlabel)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_ref.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open.
        cbn [flush_text nonempty_str oemit_all] in Ekids |- *. rewrite Ekids.
        rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr),
                Hnorm.
        rewrite <- ci_ast_ref. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text nonempty_str oemit_all]. reflexivity.
Qed.

(* The delimiter instance, which is what the two callers below use. *)
Lemma iscan_cis_marked :
  forall cis k tail txt prev before base,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    (nonempty before || nonempty_str txt || nonempty cis)%bool = true ->
    exists p,
      iscan_str (ci_text cis ++ marked_close k tail)
        (IText false txt prev (oemit_all before (opush k true base)))
      = iscan_str (marked_close k tail)
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt (oemit_all before (opush k true base))))).
Proof.
  intros cis k tail txt prev before base Hok Hsep Hne.
  apply (iscan_cis_scope cis (marked_close k tail) (opush k true base) false
           txt prev before
           (marked_close_nonempty _ _) (marked_close_starts_nontick _ _)
           (fun txt' prev' before' e =>
              iscan_marked_flush k tail txt' prev' before' base
                (orb_false_r_true _ e))
           Hok Hsep).
  rewrite orb_false_r. exact Hne.
Qed.

(* And the bracket instance, for a label scanned inside its own scope. *)
Lemma iscan_cis_bracket :
  forall cis dst tail txt prev image before base,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    exists p,
      iscan_str (ci_text cis ++ link_close dst tail)
        (IText false txt prev (oemit_all before (bpush image base)))
      = iscan_str (link_close dst tail)
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt (oemit_all before (bpush image base))))).
Proof.
  intros cis dst tail txt prev image before base Hok Hsep.
  apply (iscan_cis_scope cis (link_close dst tail) (bpush image base) true
           txt prev before
           (link_close_nonempty _ _) (link_close_starts_nontick _ _)
           (fun txt' prev' before' _ =>
              iscan_bracket_flush dst tail txt' prev' image before' base)
           Hok Hsep).
  apply orb_true_r.
Qed.

(* And the reference instance, which differs only in the closer. *)
Lemma iscan_cis_ref :
  forall cis label tail txt prev image before base,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    exists p,
      iscan_str (ci_text cis ++ ref_close label tail)
        (IText false txt prev (oemit_all before (bpush image base)))
      = iscan_str (ref_close label tail)
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt (oemit_all before (bpush image base))))).
Proof.
  intros cis label tail txt prev image before base Hok Hsep.
  apply (iscan_cis_scope cis (ref_close label tail) (bpush image base) true
           txt prev before
           (ref_close_nonempty _ _) (ref_close_starts_nontick _ _)
           (fun txt' prev' before' _ =>
              iscan_ref_flush label tail txt' prev' image before' base)
           Hok Hsep).
  apply orb_true_r.
Qed.

(* Once a canonical scan has closed every nested delimiter, the output
   state again has an empty scope stack. *)
Definition flush_out (txt : string) (out : inlines) : inlines :=
  if nonempty_str txt then mk (Str txt) :: out else out.

Lemma flush_text_flat :
  forall txt out, flush_text txt (OState out []) = OState (flush_out txt out) [].
Proof.
  intros txt out. unfold flush_text, flush_out, oemit; cbn [os_stk].
  destruct (nonempty_str txt); reflexivity.
Qed.

Lemma iscan_cis :
  forall cis prev' txt out,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    ifinish (iscan_str (ci_text cis)
               (IText false txt prev' (OState out [])))
    = (List.rev (flush_out txt out) ++ ci_inlines cis)%list.
Proof.
  intro cis. pattern cis.
  apply (well_founded_induction (well_founded_ltof _ cis_size)).
  clear cis. intros cis IH prev' txt out Hok Hsep.
  destruct cis as [|c rest].
  - cbn [ci_text ci_inlines iscan_str]. rewrite app_nil_r.
    rewrite ifinish_text, flush_text_flat. reflexivity.
  - assert (Hrestlt : ltof (list cinline) cis_size rest (c :: rest)).
    { unfold ltof. cbn [cis_size]. pose proof (ci_size_pos c). lia. }
    destruct c as [s|v|d kids|img kids dst|rimg rkids rlabel].
    + destruct txt as [|x txt']; [|discriminate].
      pose proof (cis_ok_head (CIStr s) rest Hok) as Hsok.
      cbn [ci_ok] in Hsok. apply andb_true_iff in Hsok as [Hs _].
      cbn [ci_text ci_src]. rewrite iscan_str_app, iscan_escape.
      cbn [ci_inlines map append].
      rewrite (IH rest Hrestlt prev' s out).
      * unfold flush_out at 1. rewrite Hs.
        cbn [List.rev nonempty_str ci_ast map].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * apply ci_str_tail_sep; assumption.
    + pose proof (ci_verb_nonempty v rest Hok) as Hvne.
      pose proof (ci_verb_content_ok v rest Hok) as Hvok.
      cbn [ci_text ci_src]. rewrite iscan_str_app.
      rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
      rewrite flush_text_flat.
      destruct rest as [|r rest'].
      * cbn [ci_text ci_inlines map append].
        cbn [iscan_str].
        unfold ifinish, ifinish_rev, ifinish_ostate, iresolve.
        rewrite nat_eqb_refl, trim_verb_pad by exact Hvok.
        unfold oemit, ofinish; cbn [os_stk os_out oflatten oapp].
        cbn [List.rev ci_ast]. reflexivity.
      * destruct (after_verb_rest_nontick v r rest' Hok) as [Hne Htick].
        rewrite (iscan_after_verb_nontick _ _ _ _ Hne Htick).
        rewrite trim_verb_pad by exact Hvok.
        cbn [oemit os_stk os_out].
        rewrite (IH (r :: rest') Hrestlt (Some tick) EmptyString
          (mk (Verbatim v) :: flush_out txt out)).
        -- cbn [flush_out nonempty_str ci_inlines map ci_ast List.rev].
           rewrite <- List.app_assoc. reflexivity.
        -- exact (cis_ok_tail _ _ Hok).
        -- reflexivity.
    + pose proof (cis_ok_head (CIDelim d kids) rest Hok) as Hdk.
      rewrite ci_ok_delim in Hdk. apply andb_true_iff in Hdk as [Hkidsne Hkidsok].
      pose proof (iscan_cis_marked kids d (ci_text rest) EmptyString
        (Some (dchar d)) [] (flush_text txt (OState out []))
        Hkidsok eq_refl) as IHkids.
      assert (Hkn :
        nonempty (@nil (node inline)) || nonempty_str EmptyString ||
        nonempty kids = true).
      { cbn. exact Hkidsne. }
      destruct (IHkids Hkn) as [pk Ekids].
      cbn [ci_text ci_inlines map]. rewrite ci_src_delim.
      assert (Hsrc :
        (String lbrace
            (String (dchar d)
              (ci_text kids ++ String (dchar d) (one rbrace))) ++
          ci_text rest)%string
        = ((String lbrace (one (dchar d))) ++
            (ci_text kids ++ marked_close d (ci_text rest)))%string).
      { unfold marked_close, one. cbn [append].
        repeat rewrite append_assoc. reflexivity. }
      rewrite Hsrc, iscan_str_app, iscan_marked_open.
      cbn [flush_text nonempty_str oemit_all] in Ekids. rewrite Ekids.
      assert (Hkins : nonempty (ci_inlines kids) = true).
      { destruct kids; [discriminate|reflexivity]. }
      rewrite (iscan_marked_close_emit d _ (ci_inlines kids) _ pk Hkins).
      rewrite <- ci_ast_delim.
      destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk. subst out' stk'.
      cbn [oemit os_out os_stk].
      rewrite (IH rest Hrestlt (Some rbrace) EmptyString
        (ci_ast (CIDelim d kids) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_inlines map List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CILink img kids dst) rest Hok) as Hdk.
      rewrite ci_ok_link in Hdk. apply andb_true_iff in Hdk as [Hnl Hkidsok].
      destruct (iscan_cis_bracket kids dst (ci_text rest) EmptyString
        (Some lbrack) img [] (flush_text txt (OState out []))
        Hkidsok eq_refl) as [pk Ekids].
      cbn [ci_text ci_inlines map]. rewrite ci_src_link.
      assert (Hsrc :
        ((bracket_open img ++ (ci_text kids ++ link_close dst EmptyString)) ++
          ci_text rest)%string
        = (bracket_open img ++
            (ci_text kids ++ link_close dst (ci_text rest)))%string).
      { rewrite append_assoc, append_assoc, link_close_app. reflexivity. }
      rewrite Hsrc, iscan_str_app, iscan_bracket_open.
      cbn [flush_text nonempty_str oemit_all] in Ekids. rewrite Ekids.
      rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
      rewrite <- ci_ast_link.
      destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk. subst out' stk'.
      cbn [oemit os_out os_stk].
      rewrite (IH rest Hrestlt (Some rparen) EmptyString
        (ci_ast (CILink img kids dst) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_inlines map List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CIRef rimg rkids rlabel) rest Hok) as Hdk.
      rewrite ci_ok_ref in Hdk.
      apply andb_true_iff in Hdk as [Hlab Hkidsok].
      apply andb_true_iff in Hlab as [Hlab Hnorm].
      apply andb_true_iff in Hlab as [Hne' Hbr].
      apply String.eqb_eq in Hnorm.
      destruct (iscan_cis_ref rkids rlabel (ci_text rest) EmptyString
        (Some lbrack) rimg [] (flush_text txt (OState out []))
        Hkidsok eq_refl) as [pk Ekids].
      cbn [ci_text ci_inlines map]. rewrite ci_src_ref.
      assert (Hsrc :
        ((bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel EmptyString)) ++
          ci_text rest)%string
        = (bracket_open rimg ++
            (ci_text rkids ++ ref_close rlabel (ci_text rest)))%string).
      { rewrite append_assoc, append_assoc, ref_close_app. reflexivity. }
      rewrite Hsrc, iscan_str_app, iscan_bracket_open.
      cbn [flush_text nonempty_str oemit_all] in Ekids. rewrite Ekids.
      rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr),
              Hnorm.
      rewrite <- ci_ast_ref.
      destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk. subst out' stk'.
      cbn [oemit os_out os_stk].
      rewrite (IH rest Hrestlt (Some rbrack) EmptyString
        (ci_ast (CIRef rimg rkids rlabel) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_inlines map List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
Qed.

(* The other half of what a canonical line owes the paragraph: it leaves
   the scan owing nothing to the next line.  Every canonical constituent
   either stays in `IText` (a string) or resolves its closing run before
   the line ends (a verbatim), which is exactly why the empty verbatim
   had to go: two adjacent runs leave `IOpen`. *)
Lemma iscan_cis_closed :
  forall cis prev' txt out,
    cis_ok cis = true ->
    iscan_closed (iscan_str (ci_text cis)
                    (IText false txt prev' (OState out []))) = true.
Proof.
  intro cis. pattern cis.
  apply (well_founded_induction (well_founded_ltof _ cis_size)).
  clear cis. intros cis IH prev' txt out Hok.
  destruct cis as [|c rest]; [reflexivity|].
  assert (Hrestlt : ltof (list cinline) cis_size rest (c :: rest)).
  { unfold ltof. cbn [cis_size]. pose proof (ci_size_pos c). lia. }
  destruct c as [s|v|d kids|img kids dst|rimg rkids rlabel].
  - cbn [ci_text ci_src]. rewrite iscan_str_app, iscan_escape.
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (ci_verb_nonempty v rest Hok) as Hvne.
    pose proof (ci_verb_content_ok v rest Hok) as Hvok.
    cbn [ci_text ci_src]. rewrite iscan_str_app.
    rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
    rewrite flush_text_flat.
    destruct rest as [|r rest'].
    + cbn [ci_text iscan_str iscan_closed iresolve os_stk null].
      rewrite nat_eqb_refl. reflexivity.
    + destruct (after_verb_rest_nontick v r rest' Hok) as [Hne Htick].
      rewrite (iscan_after_verb_nontick _ _ _ _ Hne Htick).
      rewrite trim_verb_pad by exact Hvok. cbn [oemit os_out os_stk].
      apply (IH (r :: rest') Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CIDelim d kids) rest Hok) as Hdk.
    rewrite ci_ok_delim in Hdk. apply andb_true_iff in Hdk as [Hkidsne Hkidsok].
    pose proof (iscan_cis_marked kids d (ci_text rest) EmptyString
      (Some (dchar d)) [] (flush_text txt (OState out []))
      Hkidsok eq_refl) as IHkids.
    assert (Hkn :
      nonempty (@nil (node inline)) || nonempty_str EmptyString ||
      nonempty kids = true).
    { cbn. exact Hkidsne. }
    destruct (IHkids Hkn) as [pk Ekids].
    cbn [ci_text]. rewrite ci_src_delim.
    assert (Hsrc :
      (String lbrace
          (String (dchar d)
            (ci_text kids ++ String (dchar d) (one rbrace))) ++
        ci_text rest)%string
      = ((String lbrace (one (dchar d))) ++
          (ci_text kids ++ marked_close d (ci_text rest)))%string).
    { unfold marked_close, one. cbn [append].
      repeat rewrite append_assoc. reflexivity. }
    rewrite Hsrc, iscan_str_app, iscan_marked_open.
    cbn [flush_text nonempty_str oemit_all] in Ekids. rewrite Ekids.
    assert (Hkins : nonempty (ci_inlines kids) = true).
    { destruct kids; [discriminate|reflexivity]. }
    rewrite (iscan_marked_close_emit d _ (ci_inlines kids) _ pk Hkins).
    destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk. subst out' stk'.
    cbn [oemit os_out os_stk].
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CILink img kids dst) rest Hok) as Hdk.
    rewrite ci_ok_link in Hdk. apply andb_true_iff in Hdk as [Hnl Hkidsok].
    destruct (iscan_cis_bracket kids dst (ci_text rest) EmptyString
      (Some lbrack) img [] (flush_text txt (OState out []))
      Hkidsok eq_refl) as [pk Ekids].
    cbn [ci_text]. rewrite ci_src_link.
    assert (Hsrc :
      ((bracket_open img ++ (ci_text kids ++ link_close dst EmptyString)) ++
        ci_text rest)%string
      = (bracket_open img ++
          (ci_text kids ++ link_close dst (ci_text rest)))%string).
    { rewrite append_assoc, append_assoc, link_close_app. reflexivity. }
    rewrite Hsrc, iscan_str_app, iscan_bracket_open.
    cbn [flush_text nonempty_str oemit_all] in Ekids. rewrite Ekids.
    rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
    destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk. subst out' stk'.
    cbn [oemit os_out os_stk].
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CIRef rimg rkids rlabel) rest Hok) as Hdk.
    rewrite ci_ok_ref in Hdk.
    apply andb_true_iff in Hdk as [Hlab Hkidsok].
    apply andb_true_iff in Hlab as [Hlab Hnorm].
    apply andb_true_iff in Hlab as [Hne' Hbr].
    destruct (iscan_cis_ref rkids rlabel (ci_text rest) EmptyString
      (Some lbrack) rimg [] (flush_text txt (OState out []))
      Hkidsok eq_refl) as [pk Ekids].
    cbn [ci_text]. rewrite ci_src_ref.
    assert (Hsrc :
      ((bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel EmptyString)) ++
        ci_text rest)%string
      = (bracket_open rimg ++
          (ci_text rkids ++ ref_close rlabel (ci_text rest)))%string).
    { rewrite append_assoc, append_assoc, ref_close_app. reflexivity. }
    rewrite Hsrc, iscan_str_app, iscan_bracket_open.
    cbn [flush_text nonempty_str oemit_all] in Ekids. rewrite Ekids.
    rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr).
    destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk. subst out' stk'.
    cbn [oemit os_out os_stk].
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
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
Definition iscan_productive (st : iscan) : bool :=
  match st with
  | IText false txt _ o => (nonempty_str txt || ostate_nonempty o)%bool
  | _ => true
  end.

Lemma nonempty_str_app_l :
  forall a b, nonempty_str b = true -> nonempty_str (a ++ b)%string = true.
Proof. intros [|x a] b H; [exact H | reflexivity]. Qed.

(* Both reconstructions end in a bracket, so the buffer they hand back is
   never empty: a literal bracket always owes at least its own source. *)
Lemma bclosed_lit_nonempty :
  forall kids image o,
    nonempty_str (fst (bclosed_lit kids image o)) = true.
Proof.
  intros kids image o. unfold bclosed_lit.
  destruct (opop_str o) as [pre o1].
  destruct (bflat kids (pre ++ bracket_open image)%string o1) as [txt o2].
  cbn [fst]. apply nonempty_str_app_l. reflexivity.
Qed.

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

Lemma ostate_nonempty_bpush :
  forall image o, ostate_nonempty (bpush image o) = true.
Proof.
  intros image o. unfold ostate_nonempty, bpush; cbn [os_stk].
  rewrite orb_true_r. reflexivity.
Qed.

(* Splitting at a break either leaves the text in the buffer or emits a
   `SoftBreak`, so a nonempty destination stays owed either way. *)
Lemma bsplit_nl_productive :
  forall s txt o,
    (nonempty_str txt || ostate_nonempty o)%bool = true ->
    (nonempty_str (fst (bsplit_nl s txt o))
     || ostate_nonempty (snd (bsplit_nl s txt o)))%bool = true.
Proof.
  induction s as [|c s IH]; intros txt o H; cbn [bsplit_nl]; [exact H|].
  destruct (Ascii.eqb c nl_char).
  - apply IH. rewrite ostate_nonempty_emit. apply orb_true_r.
  - apply IH. rewrite nonempty_str_app_l by reflexivity. reflexivity.
Qed.

Lemma bdest_lit_productive :
  forall kids image esc dst o,
    (nonempty_str (fst (bdest_lit kids image esc dst o))
     || ostate_nonempty (snd (bdest_lit kids image esc dst o)))%bool = true.
Proof.
  intros kids image esc dst o. unfold bdest_lit.
  destruct (bclosed_lit kids image o) as [txt o'].
  apply bsplit_nl_productive.
  rewrite nonempty_str_app_l by reflexivity. reflexivity.
Qed.

Lemma bref_lit_productive :
  forall kids image label o,
    (nonempty_str (fst (bref_lit kids image label o))
     || ostate_nonempty (snd (bref_lit kids image label o)))%bool = true.
Proof.
  intros kids image label o. unfold bref_lit.
  destruct (bclosed_lit kids image o) as [txt o']. cbn [fst snd].
  apply orb_true_iff. left. destruct txt; reflexivity.
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
  destruct (Ascii.eqb c bang); [reflexivity|].
  destruct (Ascii.eqb c lbrack);
    [cbn [iscan_productive]; rewrite ostate_nonempty_bpush; apply orb_true_r|].
  destruct (Ascii.eqb c rbrack);
    [destruct (bclose (flush_text txt o)) as [[[kids image] o']|];
     [reflexivity|];
     cbn [iscan_productive];
     rewrite nonempty_str_app_l by reflexivity; reflexivity|].
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
    | IBrace _ _ _ | IAttr _ _ _ _ _ | IBang _ _ _ | IDelim _ _ _ _
    | IClosed _ _ _ => False
    | _ => True
    end.
Proof.
  intros [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|kids img esc depth dst ob];
    cbn [iresolve]; try exact I.
  - destruct (idelim_resolve_text k txt cc false None o) as [txt' [prev' [o' E]]].
    rewrite E. exact I.
  - destruct (bclosed_lit kids img ob) as [txt o']. exact I.
Qed.

Lemma iscan_productive_resolve :
  forall st, iscan_productive st = true -> iscan_productive (iresolve st) = true.
Proof.
  intros [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|kids img esc depth dst ob] H;
    cbn [iresolve]; try exact H.
  (* `IBrace`, `IAttr` and `IBang` all push their own byte into the
     buffer, so the text they resolve to is nonempty *)
  all: try (cbn [iscan_productive]; apply orb_true_iff; left;
            apply nonempty_str_app_l; reflexivity).
  - apply idelim_resolve_productive.
  - pose proof (bclosed_lit_nonempty kids img ob) as Hne.
    destruct (bclosed_lit kids img ob) as [txt o']; cbn [fst] in Hne.
    cbn [iscan_productive]. rewrite Hne. reflexivity.
Qed.

Lemma bspan_lit_productive :
  forall kids image src o,
    (nonempty_str (fst (bspan_lit kids image src o))
     || ostate_nonempty (snd (bspan_lit kids image src o)))%bool = true.
Proof.
  intros kids image src o. unfold bspan_lit.
  destruct (bclosed_lit kids image o) as [txt o']; cbn [fst snd].
  apply orb_true_iff. left. apply nonempty_str_app_l. reflexivity.
Qed.

(* Every disposition owes something: the literal fallback puts the text
   back with its `{`, an attachment emits a node, and the drop either
   keeps pending text or, when there is none, keeps the source. *)
Lemma iattr_attach_productive :
  forall a src txt prev o,
    iscan_productive (iattr_attach a src txt prev o) = true.
Proof.
  intros a src txt prev o. unfold iattr_attach.
  assert (Hd : iscan_productive
                 (if nonempty_str txt
                  then IText false txt prev o
                  else IText false (txt ++ one lbrace ++ src)%string prev o)
               = true).
  { destruct (nonempty_str txt) eqn:E; cbn [iscan_productive];
      [rewrite E; reflexivity|].
    apply orb_true_iff. left. destruct txt; [reflexivity|discriminate E]. }
  destruct a as [|kv a']; [exact Hd|].
  destruct (last_ws_split txt) as [pre w].
  destruct (nonempty_str w); [|exact Hd].
  cbn [iscan_productive]. rewrite ostate_nonempty_emit. apply orb_true_r.
Qed.

Lemma iattr_feed_productive :
  forall c p src txt prev o,
    iscan_productive (iattr_feed c p src txt prev o) = true.
Proof.
  intros c p src txt prev o. unfold iattr_feed.
  destruct (ap_failed (astep p c)).
  - apply iscan_productive_lead. apply orb_true_iff. left.
    apply nonempty_str_app_l. reflexivity.
  - destruct (ap_done (astep p c)); [apply iattr_attach_productive|reflexivity].
Qed.

Lemma ispan_feed_productive :
  forall c kids image p src o,
    iscan_productive (ispan_feed c kids image p src o) = true.
Proof.
  intros c kids image p src o. unfold ispan_feed.
  destruct (ap_failed (astep p c)).
  - pose proof (bclosed_lit_nonempty kids image o) as Hne.
    unfold bspan_lit. destruct (bclosed_lit kids image o) as [txt o'];
      cbn [fst] in Hne.
    apply iscan_productive_lead. apply orb_true_iff. left.
    apply nonempty_str_app_l. reflexivity.
  - destruct (ap_done (astep p c)); [|reflexivity].
    cbn [iscan_productive]. rewrite ostate_nonempty_emit. apply orb_true_r.
Qed.

Lemma iscan_productive_step :
  forall c st, iscan_productive st = true -> iscan_productive (istep c st) = true.
Proof.
  intros c [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|kids img esc depth dst ob] H;
    cbn [istep].
  - cbn [iscan_productive]. apply orb_true_iff. left.
    apply nonempty_str_app_l. destruct (is_punct c); reflexivity.
  - apply iscan_productive_lead, H.
  - unfold ibrace_step. destruct (dstyle_of c).
    + cbn [iscan_productive]. rewrite ostate_nonempty_push.
      apply orb_true_r.
    + apply iattr_feed_productive.
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
  - unfold ibang_step. destruct (Ascii.eqb c lbrack).
    + cbn [iscan_productive]. rewrite ostate_nonempty_bpush. apply orb_true_r.
    + apply iscan_productive_lead. apply orb_true_iff. left.
      apply nonempty_str_app_l. reflexivity.
  - (* a literal bracket owes its own source; a destination owes more *)
    destruct (Ascii.eqb c lparen); [reflexivity|].
    destruct (Ascii.eqb c lbrack); [reflexivity|].
    destruct (Ascii.eqb c lbrace); [reflexivity|].
    pose proof (bclosed_lit_nonempty kids img ob) as Hne.
    destruct (bclosed_lit kids img ob) as [txt o']; cbn [fst] in Hne.
    apply iscan_productive_lead. rewrite Hne. reflexivity.
  - apply ispan_feed_productive.
  - apply iattr_feed_productive.
  - destruct (Ascii.eqb c rbrack); [|reflexivity].
    cbn [iscan_productive]. rewrite ostate_nonempty_emit. apply orb_true_r.
  - destruct esc; [reflexivity|].
    destruct (is_bslash c); [reflexivity|].
    destruct (Ascii.eqb c lparen); [reflexivity|].
    destruct (Ascii.eqb c rparen); [|reflexivity].
    destruct depth; [|reflexivity].
    cbn [iscan_productive]. rewrite ostate_nonempty_emit. apply orb_true_r.
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
  destruct (iresolve st) as [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|kids img esc depth dst ob];
    cbn [iscan_productive]; try reflexivity;
    try apply ispan_feed_productive.
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
    [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|kids img esc depth dst ob];
    try contradiction; apply nonempty_ofinish.
  - apply ostate_nonempty_flush_str, nonempty_str_app_l. reflexivity.
  - cbn [iscan_productive] in Hres.
    apply orb_true_iff in Hres as [Hres|Hres];
      [apply ostate_nonempty_flush_str, Hres
      |apply ostate_nonempty_flush, Hres].
  - apply ostate_nonempty_emit.
  - apply ostate_nonempty_emit.
  - pose proof (bspan_lit_productive kids img ssrc sob) as Hs.
    destruct (bspan_lit kids img ssrc sob) as [txt o']; cbn [fst snd] in Hs.
    apply orb_true_iff in Hs as [Hs|Hs];
      [apply ostate_nonempty_flush_str, Hs | apply ostate_nonempty_flush, Hs].
  - pose proof (bref_lit_productive kids img label ob) as Hr.
    destruct (bref_lit kids img label ob) as [txt o']; cbn [fst snd] in Hr.
    apply orb_true_iff in Hr as [Hr|Hr];
      [apply ostate_nonempty_flush_str, Hr | apply ostate_nonempty_flush, Hr].
  - pose proof (bdest_lit_productive kids img esc dst ob) as Hd.
    destruct (bdest_lit kids img esc dst ob) as [txt o']; cbn [fst snd] in Hd.
    apply orb_true_iff in Hd as [Hd|Hd];
      [apply ostate_nonempty_flush_str, Hd | apply ostate_nonempty_flush, Hd].
Qed.

Lemma iscan_productive_first :
  forall c, iscan_productive (istep c istart) = true.
Proof.
  intros c. unfold istart. cbn [istep]. unfold ilead.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c); [reflexivity|].
  destruct (Ascii.eqb c lbrace); [reflexivity|].
  destruct (Ascii.eqb c bang); [reflexivity|].
  destruct (Ascii.eqb c lbrack); [reflexivity|].
  (* nothing is open at the start, so a `]` is text *)
  destruct (Ascii.eqb c rbrack); [reflexivity|].
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

(* Classification sees the source and nothing else.  The environment is
   named here before brackets arrive so their parser can produce
   unresolved `Reference` and `FootnoteReference` nodes without consulting
   either side table; a later resolution pass may fill targets but may not
   change this tree. *)
Record inline_env : Type := InlineEnv {
  inline_notes : note_map;
  inline_references : reference_map;
  inline_auto_references : reference_map
}.

Definition classify_inlines (_ : inline_env) (l : list string) : inlines :=
  para_inlines l.

Theorem classify_inlines_locality :
  forall a b l, classify_inlines a l = classify_inlines b l.
Proof. reflexivity. Qed.

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
  rewrite (iscan_cis cis None EmptyString []).
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

Fixpoint inline_text (il : inline) : string :=
  let go :=
    fix go (ns : inlines) : string :=
      match ns with
      | [] => EmptyString
      | Node _ _ x :: rest => (inline_text x ++ go rest)%string
      end in
  let marked (k : dstyle) (ns : inlines) :=
    String lbrace
      (String (dchar k) (go ns ++ String (dchar k) (one rbrace))) in
  match il with
  | Str s => escape_str s
  | Verbatim s => verb_text s
  | Emph ns => marked DEmph ns
  | Strong ns => marked DStrong ns
  | Superscript ns => marked DSuper ns
  | Subscript ns => marked DSub ns
  | Highlight ns => marked DMark ns
  | Insert ns => marked DInsert ns
  | Link ns (Direct dst) =>
      (bracket_open false ++ (go ns ++ link_close dst EmptyString))%string
  | Image ns (Direct dst) =>
      (bracket_open true ++ (go ns ++ link_close dst EmptyString))%string
  | Link ns (Reference label) =>
      (bracket_open false ++ (go ns ++ ref_close label EmptyString))%string
  | Image ns (Reference label) =>
      (bracket_open true ++ (go ns ++ ref_close label EmptyString))%string
  | _ => EmptyString
  end.

Lemma inline_text_ci_ast : forall ci, inline_text (node_contents (ci_ast ci)) = ci_src ci.
Proof.
  fix IH 1. intro ci. destruct ci as [s|s|k kids|img kids dst|rimg rkids rlabel];
    [reflexivity|reflexivity| | |].
  - destruct k; cbn [ci_ast ci_src dnode node_contents inline_text].
    all: cbn [inline_text node_contents mk]; f_equal; f_equal; f_equal;
      induction kids as [|c rest IHkids]; [reflexivity|]; cbn;
      destruct (ci_ast c) as [p a x] eqn:E;
      pose proof (IH c) as Hc; rewrite E in Hc;
      cbn [node_contents] in Hc; rewrite Hc, IHkids; reflexivity.
  - cbn [ci_ast ci_src node_contents inline_text mk bnode].
    destruct img;
      (cbn [bnode inline_text]; f_equal; f_equal;
       induction kids as [|c rest IHkids]; [reflexivity|]; cbn;
       destruct (ci_ast c) as [p a x] eqn:E;
       pose proof (IH c) as Hc; rewrite E in Hc;
       cbn [node_contents] in Hc; rewrite Hc, IHkids; reflexivity).
  - cbn [ci_ast ci_src node_contents inline_text mk bnode].
    destruct rimg;
      (cbn [bnode inline_text]; f_equal; f_equal;
       induction rkids as [|c rest IHkids]; [reflexivity|]; cbn;
       destruct (ci_ast c) as [p a x] eqn:E;
       pose proof (IH c) as Hc; rewrite E in Hc;
       cbn [node_contents] in Hc; rewrite Hc, IHkids; reflexivity).
Qed.

(* Recover the lines of a paragraph from its inlines: `Str` extends the
   current line, `SoftBreak` ends it. *)
Fixpoint inline_lines (ils : inlines) (cur : string) : list string :=
  match ils with
  | [] => [cur]
  | Node _ _ SoftBreak :: rest => cur :: inline_lines rest EmptyString
  | Node _ _ il :: rest => inline_lines rest (cur ++ inline_text il)
  end.

Lemma inline_lines_softbreak :
  forall rest cur,
    inline_lines (mk SoftBreak :: rest) cur = cur :: inline_lines rest EmptyString.
Proof. reflexivity. Qed.

Lemma inline_lines_ci_ast :
  forall ci rest cur,
    inline_lines (ci_ast ci :: rest) cur
    = inline_lines rest (cur ++ ci_src ci).
Proof.
  intros ci rest cur. destruct ci as [s|s|k kids|img kids dst|rimg rkids rlabel];
    [reflexivity|reflexivity| | |].
  - rewrite ci_ast_delim, <- inline_text_ci_ast.
    destruct k; reflexivity.
  - rewrite ci_ast_link, <- inline_text_ci_ast, ci_ast_link.
    destruct img; reflexivity.
  - rewrite ci_ast_ref, <- inline_text_ci_ast, ci_ast_ref.
    destruct rimg; reflexivity.
Qed.

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
  - cbn [ci_inlines map app]. rewrite inline_lines_ci_ast, IH.
    cbn [ci_line ci_text]. rewrite append_assoc. reflexivity.
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

Example canonical_emph_source :
  ci_line [CIDelim DEmph [CIStr "a"]] = "{_a_}".
Proof. reflexivity. Qed.

Example canonical_nested_delimiter_roundtrip :
  parse_inline_line
    (ci_line [CIDelim DEmph
      [CIStr "a"; CIDelim DStrong [CIStr "b"]]])
  = ci_inlines [CIDelim DEmph
      [CIStr "a"; CIDelim DStrong [CIStr "b"]]].
Proof. vm_compute. reflexivity. Qed.

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

(*
Direct links
------------

Every reading below was taken from djot.js first. *)

Definition bkids : inlines := [mk (Str "a")].

Example link_basic : parse_inline_line "[a](b)" = [mk (Link bkids (Direct "b"))].
Proof. vm_compute. reflexivity. Qed.

Example link_balanced_parens :
  parse_inline_line "[a](b(c)d)" = [mk (Link bkids (Direct "b(c)d"))].
Proof. vm_compute. reflexivity. Qed.

Example link_escaped_paren :
  parse_inline_line "[a](b\)c)" = [mk (Link bkids (Direct "b)c"))].
Proof. vm_compute. reflexivity. Qed.

(* Without a destination the brackets are text, and they merge with the
   text on both sides: `opop_str` takes back what the `[` had flushed. *)
Example bracket_literal_merges :
  parse_inline_line "z[a]x" = [mk (Str "z[a]x")].
Proof. vm_compute. reflexivity. Qed.

(* A label's non-text children stay classified when the brackets do not
   become a link, which is why the fallback cannot work from source. *)
Example bracket_literal_keeps_children :
  parse_inline_line "[_a_]x"
  = [mk (Str "["); mk (Emph [mk (Str "a")]); mk (Str "]x")].
Proof. vm_compute. reflexivity. Qed.

(* A delimiter opened inside a label is abandoned by the close, since the
   label is a scope and the delimiter did not close inside it. *)
Example link_label_abandons_opener :
  parse_inline_line "[_a](b)_"
  = [mk (Link [mk (Str "_a")] (Direct "b")); mk (Str "_")].
Proof. vm_compute. reflexivity. Qed.

(* A destination crosses a line break and drops it; an unterminated one
   keeps it, since the break is then an ordinary soft break.  A `]` at a
   break is already literal: the `(` has to be the very next byte. *)
Example dest_crosses_break :
  para_inlines ["[a](b"; "c)"] = [mk (Link bkids (Direct "bc"))].
Proof. vm_compute. reflexivity. Qed.

Example dest_unterminated_keeps_break :
  para_inlines ["[a](b"; "c"]
  = [mk (Str "[a](b"); mk SoftBreak; mk (Str "c")].
Proof. vm_compute. reflexivity. Qed.

Example bracket_needs_paren_on_the_same_line :
  para_inlines ["[a]"; "(b)"]
  = [mk (Str "[a]"); mk SoftBreak; mk (Str "(b)")].
Proof. vm_compute. reflexivity. Qed.

(* The canonical spelling, and what it excludes.  An empty label is
   canonical, which is the one place a link differs from a delimiter. *)
(* Images are the bracket family's second member, and the `!` is a
   lookbehind djot.js takes off the subject at the close; we cannot, so
   the scanner has a mode for it and the frame records the answer. *)
Example image_basic :
  parse_inline_line "![a](u)" = [mk (Image bkids (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

Example image_escaped_bang_is_a_link :
  parse_inline_line "\![a](u)" = [mk (Str "!"); mk (Link bkids (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

Example image_needs_the_bracket :
  parse_inline_line "!x" = [mk (Str "!x")].
Proof. vm_compute. reflexivity. Qed.

Example image_bang_before_image :
  parse_inline_line "!![a](u)"
  = [mk (Str "!"); mk (Image bkids (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

Example image_without_destination_is_text :
  parse_inline_line "![a]" = [mk (Str "![a]")].
Proof. vm_compute. reflexivity. Qed.

Example canonical_link_source :
  ci_line [CIStr "x"; CILink false [CIStr "a"] "b"; CIStr "y"] = "x[a](b)y".
Proof. vm_compute. reflexivity. Qed.

Example canonical_image_source :
  ci_line [CILink true [CIStr "a"] "u"] = "![a](u)".
Proof. vm_compute. reflexivity. Qed.

Example canonical_link_empty_label : ci_line [CILink false [] "u"] = "[](u)".
Proof. vm_compute. reflexivity. Qed.

Example reference_link_explicit :
  parse_inline_line "[foobar][1]" =
  [mk (Link [mk (Str "foobar")] (Reference "1"))].
Proof. vm_compute. reflexivity. Qed.

Example reference_link_collapsed :
  parse_inline_line "[link][]" =
  [mk (Link [mk (Str "link")] (Reference "link"))].
Proof. vm_compute. reflexivity. Qed.

Example reference_link_multiline_label :
  para_inlines ["[link][a and"; "b]"] =
  [mk (Link [mk (Str "link")] (Reference "a and b"))].
Proof. vm_compute. reflexivity. Qed.

Example reference_image :
  parse_inline_line "![alt][img]" =
  [mk (Image [mk (Str "alt")] (Reference "img"))].
Proof. vm_compute. reflexivity. Qed.

Example unclosed_reference_is_literal :
  parse_inline_line "[link][open" = [mk (Str "[link][open")].
Proof. vm_compute. reflexivity. Qed.

Example canonical_link_escapes_destination :
  ci_line [CILink false [CIDelim DEmph [CIStr "a"]] "u(v)\"]
  = "[{_a_}](u\(v\)\\)".
Proof. vm_compute. reflexivity. Qed.

Example canonical_link_roundtrip :
  parse_inline_line (ci_line [CILink false [CIDelim DEmph [CIStr "a"]] "u(v)\"])
  = ci_inlines [CILink false [CIDelim DEmph [CIStr "a"]] "u(v)\"].
Proof. vm_compute. reflexivity. Qed.

(* A `!` before a link is escaped, so both parsers read the rendering as
   a link rather than one of them reading an image. *)
Example bang_before_link_escaped :
  ci_line [CIStr "a!"; CILink false [CIStr "b"] "u"] = "a\![b](u)".
Proof. vm_compute. reflexivity. Qed.

Example bang_before_link_roundtrip :
  parse_inline_line (ci_line [CIStr "a!"; CILink false [CIStr "b"] "u"])
  = ci_inlines [CIStr "a!"; CILink false [CIStr "b"] "u"].
Proof. vm_compute. reflexivity. Qed.

(* Excluded: a destination that spans a line cannot come back. *)
Example link_destination_with_break_not_canonical :
  ci_ok (CILink false [CIStr "a"] "u
v") = false.
Proof. vm_compute. reflexivity. Qed.

(* The canonical reference spelling is the explicit one, and it survives
   a nested delimiter in the text exactly as a direct link does. *)
Example canonical_reference_source :
  ci_line [CIStr "x"; CIRef false [CIStr "a"] "lab"] = "x[a][lab]".
Proof. vm_compute. reflexivity. Qed.

Example canonical_reference_image_source :
  ci_line [CIRef true [CIStr "a"] "lab"] = "![a][lab]".
Proof. vm_compute. reflexivity. Qed.

Example canonical_reference_roundtrip :
  parse_inline_line (ci_line [CIRef false [CIDelim DEmph [CIStr "a"]] "lab"])
  = ci_inlines [CIRef false [CIDelim DEmph [CIStr "a"]] "lab"].
Proof. vm_compute. reflexivity. Qed.

(* Excluded, and each for its own reason: an empty label is the collapsed
   spelling, whose label comes from the text rather than the source; a
   `]` would end the label early; and a label the parser would normalize
   comes back as something else. *)
Example reference_empty_label_not_canonical :
  ci_ok (CIRef false [CIStr "a"] "") = false.
Proof. vm_compute. reflexivity. Qed.

Example reference_bracket_label_not_canonical :
  ci_ok (CIRef false [CIStr "a"] "a]b") = false.
Proof. vm_compute. reflexivity. Qed.

Example reference_unnormalized_label_not_canonical :
  ci_ok (CIRef false [CIStr "a"] "a  b") = false.
Proof. vm_compute. reflexivity. Qed.

(*
Spans
=====

`[...]` followed immediately by an attribute spec.  Each of these was
pinned against djot.js before the mode was written; they are the mode's
dispositions read back off the scanner.
*)

Example span_simple :
  parse_inline_line "[s]{.a}"
  = [Node NoPos [("class", "a")] (Span [mk (Str "s")])].
Proof. vm_compute. reflexivity. Qed.

(* An empty spec still builds the node, and so does an empty label --
   `wf_inline` exempts a span from `nonempty` for exactly this reason. *)
Example span_empty_spec :
  parse_inline_line "[s]{}" = [mk (Span [mk (Str "s")])].
Proof. vm_compute. reflexivity. Qed.

Example span_empty_label :
  parse_inline_line "[]{.a}" = [Node NoPos [("class", "a")] (Span [])].
Proof. vm_compute. reflexivity. Qed.

(* The brace must be adjacent: a space between it and the `]` leaves an
   ordinary bracket, and the spec then has nothing to attach to -- the
   pending text ends in whitespace -- so it is dropped. *)
Example span_needs_adjacent_brace :
  parse_inline_line "[s] {.a}" = [mk (Str "[s] ")].
Proof. vm_compute. reflexivity. Qed.

(* A failed spec puts the region back as text and resumes the scan at the
   byte that failed, so the `*` still opens a delimiter run. *)
Example span_failed_spec_resumes :
  parse_inline_line "[s]{bad*x*y"
  = [mk (Str "[s]{bad"); mk (Strong [mk (Str "x")]); mk (Str "y")].
Proof. vm_compute. reflexivity. Qed.

(* `!` is not part of a span: the image opener decays to text. *)
Example span_ignores_image_marker :
  parse_inline_line "![x]{.a}"
  = [mk (Str "!"); Node NoPos [("class", "a")] (Span [mk (Str "x")])].
Proof. vm_compute. reflexivity. Qed.

(* And it merges with the text before it rather than leaving two
   adjacent `Str` nodes, which `wf_inlines` forbids. *)
Example span_image_marker_merges :
  parse_inline_line "a![x]{.a}"
  = [mk (Str "a!"); Node NoPos [("class", "a")] (Span [mk (Str "x")])].
Proof. vm_compute. reflexivity. Qed.

(* A second spec belongs to the span too (djot.js merges the classes),
   but attaching to a *node* is the piece still missing, so it stays
   text.  See `iattr_attach`. *)
Example span_stacked_specs_not_yet :
  parse_inline_line "[s]{.a}{.b}"
  = [Node NoPos [("class", "a")] (Span [mk (Str "s")]); mk (Str "{.b}")].
Proof. vm_compute. reflexivity. Qed.

(*
Inline attributes
=================

A spec attaches to the run of text before it.  The table in
.project/260811.inline-parser.md is the measured source for these.
*)

Example attr_on_word :
  parse_inline_line "foo{.a}"
  = [Node NoPos [("class", "a")] (Str "foo")].
Proof. vm_compute. reflexivity. Qed.

(* The split is at the last whitespace, so only the final word takes the
   spec -- and an attributed `Str` therefore never contains a space. *)
Example attr_splits_at_last_space :
  parse_inline_line "foo bar{.a}"
  = [mk (Str "foo "); Node NoPos [("class", "a")] (Str "bar")].
Proof. vm_compute. reflexivity. Qed.

Example attr_punctuation_does_not_split :
  parse_inline_line "a-b{.a}"
  = [Node NoPos [("class", "a")] (Str "a-b")].
Proof. vm_compute. reflexivity. Qed.

(* Parentheses are not a span: the spec still lands on the last word. *)
Example attr_parens_are_not_a_span :
  parse_inline_line "(some text){.attr}"
  = [mk (Str "(some "); Node NoPos [("class", "attr")] (Str "text)")].
Proof. vm_compute. reflexivity. Qed.

(* Adjacency: a space before the brace means there is no last word, and
   the spec is dropped. *)
Example attr_needs_adjacency :
  parse_inline_line "foo {.a}" = [mk (Str "foo ")].
Proof. vm_compute. reflexivity. Qed.

(* An empty spec attaches nothing.  djot.js cuts the text in two here;
   both halves are plain, so one run is the same HTML and keeps us inside
   `no_adjacent_str`. *)
Example attr_empty_spec :
  parse_inline_line "foo{}bar" = [mk (Str "foobar")].
Proof. vm_compute. reflexivity. Qed.

(* `{` before a delimiter character is a braced delimiter, never a spec:
   djot.js resolves the ambiguity that way even when the contents would
   have parsed as attributes. *)
Example attr_brace_delimiter_wins :
  parse_inline_line "a{_x=y_}"
  = [mk (Str "a"); mk (Emph [mk (Str "x=y")])].
Proof. vm_compute. reflexivity. Qed.

(* A failed spec resumes the scan at the byte that failed, as a span
   does. *)
Example attr_failed_spec_resumes :
  parse_inline_line "x{bad*y*z"
  = [mk (Str "x{bad"); mk (Strong [mk (Str "y")]); mk (Str "z")].
Proof. vm_compute. reflexivity. Qed.

(* Not yet: with no pending text the spec would have to decorate the node
   just emitted, which means reading the current scope -- see
   `iattr_attach`.  Here it keeps its source instead. *)
Example attr_on_node_not_yet :
  parse_inline_line "*e*{.a}"
  = [mk (Strong [mk (Str "e")]); mk (Str "{.a}")].
Proof. vm_compute. reflexivity. Qed.
