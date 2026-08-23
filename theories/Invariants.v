(* ai-disclosure: autonomous *)

(* Phase 4's first parser-level invariant bundle.

   This bundle is deliberately narrower than "everything proved about the
   parser": its three fields say exactly that the block fold commits a prefix,
   cannot revise that commitment in response to future lines, and carries no
   hidden history beyond its explicit state.  Inline locality and delimiter
   admissibility live over a different configuration domain and should not be
   hidden in this record before their composition is designed. *)

From Stdlib Require Import String List.
From DjotV Require Import Config Parser.

Record incremental_invariants (T : dtable) (K : bconfig) : Prop := {
  incremental_prefix_determinism :
    forall xs ys st,
      @parse_lines T K (xs ++ ys)%list st =
      (@committed T K xs st ++
       @parse_lines T K ys (snd (@run_lines T K xs st)))%list;
  incremental_no_future_line_dependence :
    forall xs ys ys' st,
      firstn (List.length (@committed T K xs st))
        (@parse_lines T K (xs ++ ys)%list st) =
      firstn (List.length (@committed T K xs st))
        (@parse_lines T K (xs ++ ys')%list st);
  incremental_prefix_state_suffices :
    forall xs xs' ys st,
      @run_lines T K xs st = @run_lines T K xs' st ->
      @parse_lines T K (xs ++ ys)%list st =
      @parse_lines T K (xs' ++ ys)%list st
}.

Definition block_incremental (T : dtable) : invariant bconfig :=
  incremental_invariants T.

(* These guarantees are parametric in the block configuration: they follow
   from the fold's shape, not from either decision currently stored in it. *)
Theorem block_incremental_holds :
  forall T K, block_incremental T K.
Proof.
  intros T K. constructor.
  - exact (@prefix_determinism T K).
  - exact (@no_future_line_dependence T K).
  - exact (@prefix_state_suffices T K).
Qed.

(* The two behavioural block knobs preserve the bundle without a side
   condition.  Their signatures restrict them to changing the paragraph's
   local decision; neither can change the fold or add hidden history. *)
Theorem with_marker_interrupts_preserves_incremental :
  forall T f, preserves (with_marker_interrupts f) (block_incremental T).
Proof.
  intros T f K _. apply block_incremental_holds.
Qed.

Theorem with_underline_preserves_incremental :
  forall T f, preserves (with_underline f) (block_incremental T).
Proof.
  intros T f K _. apply block_incremental_holds.
Qed.
