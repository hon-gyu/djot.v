(* Minimal djot AST — Phase 0 toy fragment: paragraphs only.

   The real AST (Phase 1) will transcribe djoths's Djot.AST, with
   well-formedness as indices on the inductive family.  This fragment exists
   to exercise the extraction and differential-test loop end to end. *)

From Stdlib Require Import String List.
Import ListNotations.

Inductive inline : Type :=
  | Str (s : string)
  | SoftBreak.

Inductive block : Type :=
  | Para (ils : list inline).

Definition doc : Type := list block.
