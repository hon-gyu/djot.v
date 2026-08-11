(* ai-disclosure: ai-generated *)

(* The inline layer: the parser's within-line pass, and the canonical
   (renderable) view it inverts.

   The same two-sided shape as the block layer, one level down.  There,
   `Line.v` classifies a line and `Step.v` folds lines into blocks, while
   `Render.v`'s `cblock` describes the parser's image by the source data
   that determines it.  Here `parse_inline_line` is the pass, `cinline`
   is the image, and the two meet in `parse_inline_line_ci`.

   Nothing recognizes inline syntax yet: a line is one `Str`, which is
   what `Step.para_inlines` already did, and `para_inlines_one` /
   `para_inlines_cons2` still hold by `reflexivity`.  What this file adds
   is the shape the constructs in `.project/260811.inline-parser.md` need
   (escapes, verbatim, the delimiter table, brackets), fixed while it is
   still cheap to fix.

   Parser and renderer share the file because at this size a split would
   be three files of twenty lines.  It splits the way the block parser
   did once a side outgrows the other. *)

From Stdlib Require Import String Ascii List Bool.
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
Definition needs_escape (c : ascii) : bool := Ascii.eqb c "\"%char.

(* Obligation 1: an escaped character must be one the decoder accepts. *)
Lemma needs_escape_punct : forall c, needs_escape c = true -> is_punct c = true.
Proof.
  intros c H. unfold needs_escape in H. apply Ascii.eqb_eq in H. subst.
  reflexivity.
Qed.

(* Obligation 2: the escape character escapes itself, or a text ending in
   a backslash would decode as an escape of whatever followed. *)
Lemma needs_escape_backslash : needs_escape "\"%char = true.
Proof. reflexivity. Qed.

Fixpoint escape_str (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if needs_escape c
      then String "\"%char (String c (escape_str rest))
      else String c (escape_str rest)
  end.

(* A backslash before a non-punctuation character is a literal backslash
   (djot.js inline.ts:244).  Two djot readings are *not* implemented
   here: `\` before a space is a non-breaking space, and `\` at end of
   line is a hard break.  Both are distinct AST nodes rather than
   escapes, so they belong with their own constructors; and neither can
   arise from a canonical rendering, since `escape_str` never emits a
   bare backslash.  So the roundtrip does not see them. *)
Fixpoint unescape (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if needs_escape c
      then match rest with
           | String d rest' =>
               if is_punct d then String d (unescape rest')
               else String c (unescape rest)
           | EmptyString => String c EmptyString
           end
      else String c (unescape rest)
  end.

(** Escaping is invertible.  This is the whole of step 2. *)
Lemma unescape_escape : forall s, unescape (escape_str s) = s.
Proof.
  induction s as [|c rest IH]; [reflexivity|].
  cbn [escape_str]. destruct (needs_escape c) eqn:Hc.
  - cbn [unescape]. rewrite needs_escape_backslash.
    rewrite (needs_escape_punct c Hc), IH. reflexivity.
  - cbn [unescape]. rewrite Hc, IH. reflexivity.
Qed.

(* Every branch of `unescape` emits a character, so it never empties a
   nonempty text.  `wf_inline` needs this: a `Str` must be nonempty. *)
Lemma unescape_nonempty :
  forall s, nonempty_str s = true -> nonempty_str (unescape s) = true.
Proof.
  intros [|c rest] H; [discriminate|].
  cbn [unescape]. destruct (needs_escape c).
  - destruct rest as [|d rest']; [reflexivity|].
    destruct (is_punct d); reflexivity.
  - reflexivity.
Qed.

(*
Canonical inlines
=================
*)

(* One line's inline content, described by the source that determines it.
   One constructor per inline construct the roundtrip covers, exactly as
   `cblock` carries one per block construct. *)
Inductive cinline : Type :=
  | CIStr (s : string).

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
  end.

Definition ci_line (cis : list cinline) : string := ci_text None cis.

(* ...and the AST the parser builds from that text. *)
Definition ci_ast (ci : cinline) : node inline :=
  match ci with CIStr s => mk (Str s) end.

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
   a newline is not within-line content. *)
Definition ci_ok (ci : cinline) : bool :=
  match ci with CIStr s => nonempty_str s && no_nl s end.

(* Two adjacent `CIStr` would have parsed as one, the `no_adjacent_str`
   of `Wf.v` moved to the canonical view.  With `CIStr` the only
   constructor this forces a line to be a single element; it stops being
   degenerate at the first construct that is not a `Str`. *)
Fixpoint no_adjacent_ci_str (cis : list cinline) : bool :=
  match cis with
  | CIStr _ :: ((CIStr _ :: _) as rest) => false && no_adjacent_ci_str rest
  | _ => true
  end.

Definition cis_ok (cis : list cinline) : bool :=
  forallb ci_ok cis && no_adjacent_ci_str cis.

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

(* Parse one line's inline content.  Every construct of
   `.project/260811.inline-parser.md` lands here. *)
Definition parse_inline_line (s : string) : inlines := [mk (Str (unescape s))].

(* A paragraph's lines, in order, into inlines: each line's content, with
   `SoftBreak` between.  Trailing whitespace is stripped at the end of a
   paragraph but kept on interior lines (observed djot.js/djoths
   behaviour on para.test, and djot.js's own trailing-softbreak trim in
   `inline.ts` getMatches). *)
Fixpoint para_inlines (l : list string) : inlines :=
  match l with
  | [] => []
  | [x] => parse_inline_line (strip_trailing_ws x)
  | x :: rest => (parse_inline_line x ++ mk SoftBreak :: para_inlines rest)%list
  end.

Lemma para_inlines_one :
  forall x, para_inlines [x] = [mk (Str (unescape (strip_trailing_ws x)))].
Proof. reflexivity. Qed.

Lemma para_inlines_cons2 :
  forall x y rest,
    para_inlines (x :: y :: rest) =
    mk (Str (unescape x)) :: mk SoftBreak :: para_inlines (y :: rest).
Proof. reflexivity. Qed.

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
  intros [|c rest] Hok Hne; [discriminate|].
  destruct c as [s]. destruct rest as [|c2 rest'].
  - unfold ci_inlines, parse_inline_line. cbn [map ci_ast].
    rewrite ci_line_str, unescape_escape. reflexivity.
  - destruct c2 as [s2]. unfold cis_ok in Hok.
    cbn [no_adjacent_ci_str] in Hok. rewrite andb_false_r in Hok. discriminate.
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
    rewrite para_inlines_cons2, ci_para_cons2.
    rewrite <- (parse_inline_line_ci cis Hc Hn).
    unfold parse_inline_line. cbn [app].
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
  intros [|c cs] cur rest Hok Hne; [discriminate|].
  destruct c as [s]. destruct cs as [|c2 cs'].
  - unfold ci_inlines. cbn [map ci_ast app inline_lines].
    rewrite ci_line_str. reflexivity.
  - destruct c2 as [s2]. unfold cis_ok in Hok.
    cbn [no_adjacent_ci_str] in Hok. rewrite andb_false_r in Hok. discriminate.
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

(* The decoder accepts any punctuation after a backslash... *)
Example unescape_punct : unescape "\*" = "*".
Proof. reflexivity. Qed.

(* ...and leaves a backslash before anything else alone. *)
Example unescape_nonpunct : unescape "\a" = "\a".
Proof. reflexivity. Qed.

(* The encoder emits only what `needs_escape` names, which is why a
   comma renders bare where a backslash does not.  Matching djot.js,
   which renders `\,` back as `,`. *)
Example escape_backslash : escape_str "a\b" = "a\\b".
Proof. reflexivity. Qed.

Example escape_leaves_punct : escape_str "a,*b" = "a,*b".
Proof. reflexivity. Qed.
