(* ai-disclosure: autonomous *)

(** * Configuration changes and invariant preservation

   The vocabulary for configuration obligations. An invariant
   describes the configurations admitted by a development; a knob changes a
   configuration; preservation is the local proof that the change stays
   inside the admitted family.

   Feature-specific work proves [preserves] (or [preserves_when] under a
   local compatibility condition). [preserves_compose] then combines those
   local results without a proof for every named profile. *)

Definition invariant (C : Type) : Type := C -> Prop.
Definition knob (C : Type) : Type := C -> C.

(** [preserves k I] says that applying [k] to any configuration admitted by
    [I] produces another admitted configuration. *)
Definition preserves {C : Type} (k : knob C) (I : invariant C) : Prop :=
  forall c, I c -> I (k c).

(** A local edit may have a decidable compatibility obligation that depends on
   the configuration it is applied to. *)
Definition preserves_when {C : Type}
  (compatible : C -> Prop) (k : knob C) (I : invariant C) : Prop :=
  forall c, compatible c -> I c -> I (k c).

Definition compose_knob {C : Type} (k1 k2 : knob C) : knob C :=
  fun c => k2 (k1 c).

Theorem preserves_compose :
  forall {C : Type} (I : invariant C) (k1 k2 : knob C),
    preserves k1 I ->
    preserves k2 I ->
    preserves (compose_knob k1 k2) I.
Proof.
  intros C I k1 k2 H1 H2 c Hc.
  apply H2, H1, Hc.
Qed.
