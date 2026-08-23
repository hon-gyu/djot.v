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
Local Open Scope string_scope.

(* The inline guarantees Phase 3 established independently are one structural
   invariant of an admissible delimiter table.  They intentionally say no
   more than the original theorems: one unit of fuel per source byte, and no
   dependence on resolution environments while classifying source. *)
Record inline_invariants (T : dtable) : Prop := {
  inline_single_pass :
    forall s st,
      @iscan_str_fuel T (String.length s) s st =
      Some (@iscan_str T s st);
  inline_classification_locality :
    forall a b l,
      @classify_inlines T a l = @classify_inlines T b l
}.

Definition inline_structural : invariant dtable := inline_invariants.

Theorem inline_structural_holds : forall T, inline_structural T.
Proof.
  intros T. constructor.
  - exact (@iscan_str_no_reread T).
  - exact (@classify_inlines_locality T).
Qed.

(* These properties come from the scanner's control-flow shape, not from any
   row value.  Consequently every total edit of an already-admissible table
   preserves them; row compatibility is needed to construct the output
   [dtable], not to re-prove either structural guarantee. *)
Theorem dtable_knob_preserves_inline_structural :
  forall k, preserves k inline_structural.
Proof. intros k T _. apply inline_structural_holds. Qed.

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

Theorem with_tables_preserves_incremental :
  forall T enabled, preserves (with_tables enabled) (block_incremental T).
Proof.
  intros T enabled K _. apply block_incremental_holds.
Qed.

Theorem with_heading_continuation_preserves_incremental :
  forall T enabled,
    preserves (with_heading_continuation enabled) (block_incremental T).
Proof. intros T enabled K _. apply block_incremental_holds. Qed.

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

Theorem with_tables_preserves_prefix_admissible :
  forall enabled, preserves (with_tables enabled) block_prefix_admissible.
Proof. intros enabled K H. exact H. Qed.

Theorem with_heading_continuation_preserves_prefix_admissible :
  forall enabled,
    preserves (with_heading_continuation enabled) block_prefix_admissible.
Proof. intros enabled K H. exact H. Qed.

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

(*
Accidental-list immunity
------------------------

An interrupting ordered marker is safe in ordinary prose only at the
conventional list start [1].  Bullets have an empty core and are unambiguous;
every other nonempty core includes years, initials, and other text that may
legitimately begin a continuation line.  State the boundary over the marker
policy itself, so it is independent of parser state and can be checked before
installing the knob. *)
Definition marker_interrupt_precondition
  (f : list lstyle -> string -> option task_status -> string -> bool) : Prop :=
  forall sty core chk rest,
    f sty core chk rest = true ->
    prose_safe_markers sty core chk rest = true.

Definition accidental_list_immune : invariant bconfig :=
  fun K => marker_interrupt_precondition (@bmarker_interrupts K).

(* This is the extracted weakest precondition for the field-local update:
   because [with_marker_interrupts] replaces exactly this field, the updated
   configuration has the property iff the replacement policy satisfies the
   local condition. *)
Theorem with_marker_interrupts_accidental_list_immune_iff :
  forall f K,
    accidental_list_immune (with_marker_interrupts f K) <->
    marker_interrupt_precondition f.
Proof. reflexivity. Qed.

Theorem with_marker_interrupts_preserves_accidental_list_immunity :
  forall f,
    preserves_when
      (fun _ => marker_interrupt_precondition f)
      (with_marker_interrupts f)
      accidental_list_immune.
Proof. intros f K Hsafe _. exact Hsafe. Qed.

Theorem prose_safe_markers_is_immune :
  marker_interrupt_precondition prose_safe_markers.
Proof. intros sty core chk rest H. exact H. Qed.

(* [prose_safe_markers] is the maximally permissive immune policy: every
   policy satisfying the property is pointwise below it. *)
Theorem prose_safe_markers_maximal :
  forall f,
    marker_interrupt_precondition f ->
    forall sty core chk rest,
      f sty core chk rest = true ->
      prose_safe_markers sty core chk rest = true.
Proof. intros f Hsafe sty core chk rest H. exact (Hsafe _ _ _ _ H). Qed.

Example djot_accidental_list_immune :
  accidental_list_immune djot_bconfig.
Proof. intros sty core chk rest H. discriminate H. Qed.

Example sublist_accidental_list_immune :
  accidental_list_immune sublist_bconfig.
Proof. exact prose_safe_markers_is_immune. Qed.

Example unrestricted_markers_are_not_accidental_list_immune :
  ~ marker_interrupt_precondition (fun _ _ _ _ => true).
Proof.
  intros H.
  specialize (H [SOrd Decimal RightPeriod] "1865" None "x" eq_refl).
  vm_compute in H. discriminate H.
Qed.
