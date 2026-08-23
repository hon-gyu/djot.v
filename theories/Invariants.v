(* ai-disclosure: autonomous *)

(* Phase 4's first parser-level invariant bundle.

   This bundle is deliberately narrower than "everything proved about the
   parser": its three fields say exactly that the block fold commits a prefix,
   cannot revise that commitment in response to future lines, and carries no
   hidden history beyond its explicit state.  Delimiter admissibility lives
   over a different configuration domain.  The independent block-setting
   invariant below is kept separate too: it constrains prefix overlap, not the
   fold's incremental behaviour. *)

From Stdlib Require Import String List Ascii.
From DjotV Require Import Config Ast Line Parser.
Import ListNotations.

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

(* The only line that can answer both block decisions is a lone dash: it is
   the bullet marker with no body, and it is also a one-character underline.
   Longer dash runs are not list markers, and equals runs are never markers.
   Keeping this invariant about the settings, rather than the order in which
   [step] asks them, makes the two decisions genuinely independent. *)
Definition block_prefix_ok (K : bconfig) : bool :=
  match @bunderline_of K "-" with
  | Some _ => negb (@binterrupt K (classify "-"))
  | None => true
  end.

Definition block_prefix_admissible : invariant bconfig :=
  fun K => block_prefix_ok K = true.

(* Each field-local edit checks only its half of the lone-dash boundary. *)
Definition bmarker_update_compatible
  (f : list lstyle -> string -> option task_status -> string -> bool)
  (K : bconfig) : bool :=
  match @bunderline K "-"%char 1 with
  | Some _ => negb (f [SBullet "-"%char] EmptyString None EmptyString)
  | None => true
  end.

Definition bunderline_update_compatible
  (f : ascii -> nat -> option nat) (K : bconfig) : bool :=
  match f "-"%char 1 with
  | Some _ =>
      negb (@bmarker_interrupts K [SBullet "-"%char] EmptyString None EmptyString)
  | None => true
  end.

Theorem with_marker_interrupts_preserves_prefix_admissible :
  forall f,
    preserves_when
      (fun K => bmarker_update_compatible f K = true)
      (with_marker_interrupts f)
      block_prefix_admissible.
Proof. intros f K Hcompatible _. exact Hcompatible. Qed.

Theorem with_underline_preserves_prefix_admissible :
  forall f,
    preserves_when
      (fun K => bunderline_update_compatible f K = true)
      (with_underline f)
      block_prefix_admissible.
Proof. intros f K Hcompatible _. exact Hcompatible. Qed.

Example djot_prefix_admissible : block_prefix_ok djot_bconfig = true.
Proof. reflexivity. Qed.

Example sublist_prefix_admissible : block_prefix_ok sublist_bconfig = true.
Proof. reflexivity. Qed.

Example setext_prefix_admissible : block_prefix_ok setext_bconfig = true.
Proof. reflexivity. Qed.

Example markdown_prefix_admissible : block_prefix_ok markdown_bconfig = true.
Proof. reflexivity. Qed.

Example lone_dash_overlap_rejected :
  block_prefix_ok
    (with_underline (fun _ _ => Some 0) sublist_bconfig) = false.
Proof. reflexivity. Qed.
