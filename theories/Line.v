(* Line classification: the prefix-determinism seam.

   Block structure in djot is a function of what each line looks like
   (spec: "blocks can be parsed line by line ... the contribution a line
   makes to block-level structure never depends on a future line").  This
   module gives each line its kind; the parser consumes kinds, and the
   classifier is the single place a new block construct's start syntax is
   added.  Renderability (Render.v) is phrased as "each rendered line
   classifies as intended", which is what makes roundtrip proofs local. *)

From Stdlib Require Import String Ascii Bool PeanoNat.
From DjotV Require Import Strings.

Local Open Scope string_scope.
Local Open Scope char_scope.

Inductive line_kind : Type :=
  | KBlank      (* only whitespace *)
  | KThematic   (* thematic break: 3+ of - or * (mixed ok), ws between *)
  | KText.      (* anything else: paragraph text *)

(*
Recognizers
===========
*)

Definition is_marker (c : ascii) : bool :=
  Ascii.eqb c "-" || Ascii.eqb c "*".

(* djot.js pattThematicBreak: markers and whitespace only, >= 3 markers.
   (Indentation is allowed; leading ws goes through the ws branch.) *)

Fixpoint thematic_count (s : string) (count : nat) : bool :=
  match s with
  | EmptyString => Nat.leb 3 count
  | String c s' =>
      if is_marker c then thematic_count s' (S count)
      else if is_ws c then thematic_count s' count
      else false
  end.

Definition is_thematic (l : string) : bool := thematic_count l 0.

Definition classify (l : string) : line_kind :=
  if is_blank l then KBlank
  else if is_thematic l then KThematic
  else KText.

(*
Classification facts
====================
*)

Lemma classify_blank :
  forall l, is_blank l = true -> classify l = KBlank.
Proof. intros l H. unfold classify. rewrite H. reflexivity. Qed.

Lemma classify_kblank_blank :
  forall l, classify l = KBlank -> is_blank l = true.
Proof.
  intros l H. unfold classify in H.
  destruct (is_blank l); [reflexivity|].
  destruct (is_thematic l); discriminate.
Qed.

Lemma classify_not_kblank_nonblank :
  forall l, classify l <> KBlank -> is_blank l = false.
Proof.
  intros l H. destruct (is_blank l) eqn:E; [|reflexivity].
  exfalso. apply H, classify_blank, E.
Qed.

Lemma classify_ktext :
  forall l, is_blank l = false -> is_thematic l = false -> classify l = KText.
Proof. intros l Hb Ht. unfold classify. rewrite Hb, Ht. reflexivity. Qed.

(* The canonical thematic-break rendering classifies as one. *)
Lemma classify_canonical_thematic : classify "* * * *" = KThematic.
Proof. reflexivity. Qed.

Definition is_text (l : string) : bool :=
  match classify l with KText => true | _ => false end.

Lemma is_text_classify :
  forall l, is_text l = true -> classify l = KText.
Proof.
  intros l H. unfold is_text in H.
  destruct (classify l); [discriminate | discriminate | reflexivity].
Qed.
