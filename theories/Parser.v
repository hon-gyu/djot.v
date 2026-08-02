(* Block parsing: a fold over classified lines with an explicit paragraph
   accumulator.  Total and structurally recursive.

   Structure per line kind (Line.v):
   - KBlank ends any open paragraph.
   - KThematic starts a thematic break — but only when no paragraph is
     open: paragraphs can never be interrupted (spec), so inside one it is
     ordinary text.
   - KText extends or opens a paragraph.

   The equation lemmas at the bottom are the interface the wf and
   roundtrip proofs use; keep them in sync with the definition. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Line Ast.
Import ListNotations.

Local Open Scope string_scope.

(*
Paragraph assembly
==================
*)

(* Trailing whitespace is stripped at the end of a paragraph (but kept on
   interior lines) — observed djot.js/djoths behavior on para.test. *)

Fixpoint para_inlines (l : list string) : inlines :=
  match l with
  | [] => []
  | [x] => [mk (Str (strip_trailing_ws x))]
  | x :: rest => mk (Str x) :: mk SoftBreak :: para_inlines rest
  end.

(*
The line fold
=============
*)

Fixpoint parse_lines (lines : list string) (cur : list string) : blocks :=
  let flush := fun (k : blocks) =>
    match cur with
    | [] => k
    | _ => mk (Para (para_inlines (rev cur))) :: k
    end in
  match lines with
  | [] => flush []
  | l :: rest =>
      match classify l, cur with
      | KBlank, _ => flush (parse_lines rest [])
      | KThematic, [] => mk ThematicBreak :: parse_lines rest []
      | KThematic, _ => parse_lines rest (l :: cur)  (* paragraph continuation *)
      | KText, _ => parse_lines rest (l :: cur)
      end
  end.

Definition parse_doc (s : string) : doc :=
  {| doc_blocks := parse_lines (split_lines s) []
   ; doc_footnotes := []
   ; doc_references := []
   ; doc_auto_references := []
   ; doc_auto_identifiers := [] |}.

(*
Equation lemmas
===============
*)

Lemma para_inlines_one :
  forall x, para_inlines [x] = [mk (Str (strip_trailing_ws x))].
Proof. reflexivity. Qed.

Lemma para_inlines_cons2 :
  forall x y rest,
    para_inlines (x :: y :: rest) =
    mk (Str x) :: mk SoftBreak :: para_inlines (y :: rest).
Proof. reflexivity. Qed.

Lemma parse_lines_nil_cons :
  forall c cur',
    parse_lines [] (c :: cur') = [mk (Para (para_inlines (rev (c :: cur'))))].
Proof. reflexivity. Qed.

Lemma parse_lines_blank_nil :
  forall l rest, classify l = KBlank ->
  parse_lines (l :: rest) [] = parse_lines rest [].
Proof. intros l rest H. cbn [parse_lines]. rewrite H. reflexivity. Qed.

Lemma parse_lines_blank_cons :
  forall l rest c cur', classify l = KBlank ->
  parse_lines (l :: rest) (c :: cur') =
  mk (Para (para_inlines (rev (c :: cur')))) :: parse_lines rest [].
Proof. intros l rest c cur' H. cbn [parse_lines]. rewrite H. reflexivity. Qed.

Lemma parse_lines_thematic_nil :
  forall l rest, classify l = KThematic ->
  parse_lines (l :: rest) [] = mk ThematicBreak :: parse_lines rest [].
Proof. intros l rest H. cbn [parse_lines]. rewrite H. reflexivity. Qed.

Lemma parse_lines_text :
  forall l rest cur, classify l = KText ->
  parse_lines (l :: rest) cur = parse_lines rest (l :: cur).
Proof.
  intros l rest cur H. cbn [parse_lines]. rewrite H.
  destruct cur; reflexivity.
Qed.

(* Any nonblank line continues an open paragraph. *)
Lemma parse_lines_cont :
  forall l rest c cur', classify l <> KBlank ->
  parse_lines (l :: rest) (c :: cur') = parse_lines rest (l :: c :: cur').
Proof.
  intros l rest c cur' H. cbn [parse_lines].
  destruct (classify l) eqn:E; [congruence | reflexivity | reflexivity].
Qed.

(* Feeding a run of nonblank lines just accumulates them (reversed). *)
Lemma parse_lines_cont_seed :
  forall ls tail c cur',
    forallb nonblank ls = true ->
    parse_lines (ls ++ tail)%list (c :: cur') =
    parse_lines tail (rev ls ++ (c :: cur'))%list.
Proof.
  induction ls as [|l ls IH]; intros tail c cur' H.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hl Hls].
    unfold nonblank in Hl. apply negb_true_iff in Hl.
    change ((l :: ls) ++ tail)%list with (l :: (ls ++ tail))%list.
    rewrite parse_lines_cont
      by (intros E; rewrite (classify_kblank_blank _ E) in Hl; discriminate).
    rewrite IH by exact Hls.
    simpl rev. rewrite <- app_assoc. reflexivity.
Qed.

(* Opening a paragraph with a text line, then feeding its remaining lines. *)
Lemma parse_lines_para_seed :
  forall a ls tail,
    classify a = KText ->
    forallb nonblank ls = true ->
    parse_lines ((a :: ls) ++ tail)%list [] =
    parse_lines tail (rev (a :: ls))%list.
Proof.
  intros a ls tail Ha Hls.
  change ((a :: ls) ++ tail)%list with (a :: (ls ++ tail))%list.
  rewrite parse_lines_text by exact Ha.
  rewrite parse_lines_cont_seed by exact Hls.
  reflexivity.
Qed.

(*
Sanity checks
=============
*)

Example parse_two_paras :
  doc_blocks (parse_doc "hi
there

bye") =
  [ mk (Para [mk (Str "hi"); mk SoftBreak; mk (Str "there")])
  ; mk (Para [mk (Str "bye")]) ].
Proof. reflexivity. Qed.

Example parse_thematic :
  doc_blocks (parse_doc "one

  * * * *

two") =
  [ mk (Para [mk (Str "one")])
  ; mk ThematicBreak
  ; mk (Para [mk (Str "two")]) ].
Proof. reflexivity. Qed.

(* Paragraphs are never interrupted: a thematic-break-shaped line inside
   a paragraph is text. *)
Example parse_no_interrupt :
  doc_blocks (parse_doc "one
---") =
  [ mk (Para [mk (Str "one"); mk SoftBreak; mk (Str "---")]) ].
Proof. reflexivity. Qed.

Example parse_blank_only : doc_blocks (parse_doc "  ") = [].
Proof. reflexivity. Qed.
