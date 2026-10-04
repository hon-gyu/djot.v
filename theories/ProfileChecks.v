(* ai-disclosure: autonomous *)

(** * Properties decided from a profile's options

   One boolean per design property, computed from [options], with a lemma
   that it agrees with the hypothesis the property's theorem asks for.  A
   caller holding an [options] value learns which theorems apply to it by
   running the check. *)

From Stdlib Require Import String List Ascii Bool.
From DjotV Require Import Ast Line Step Invariants Profile.
Import ListNotations.

(** Safe hard-wrapping: [hard_wrap_one_para] and [hard_wrap_para_then_rest]
   hold for the profile. *)
Definition wrap_safe (o : options) : bool :=
  negb (o_list_interrupts o) && negb (o_setext o) && negb (o_keyed o).

Theorem wrap_safe_iff : forall o,
  wrap_safe o = true <-> wrap_neutral (bconfig_of o).
Proof.
  intros o. unfold wrap_safe, wrap_neutral, bconfig_of. cbn.
  destruct (o_list_interrupts o), (o_setext o), (o_keyed o); cbn; split;
    try discriminate; try (intros _; repeat split; reflexivity);
    intros [Hm [Hu Hk]]; try discriminate Hk;
    try (specialize (Hu "="%char 0); discriminate Hu);
    specialize (Hm [] EmptyString None EmptyString); discriminate Hm.
Qed.

(** What breaks it, one input per cause.  A second line that the profile
   reads as a list marker or an underline ends the paragraph. *)
Theorem wrap_cut_list : forall o x,
  o_list_interrupts o = true -> o_keyed o = false ->
  @parse_lines (o_inline o) (bconfig_of o) _ _ ["a"; "- b"]%string (PPara [])
  <> [mk (Para x)].
Proof.
  intros o x Hi Hk.
  apply (hard_wrap_cut_not_one_para (o_inline o) (bconfig_of o) "a" [] "- b").
  - reflexivity.
  - unfold keyless, bconfig_of. cbn. rewrite Hk. reflexivity.
  - reflexivity.
  - unfold bcuts, bunderline_of, bconfig_of. cbn. destruct (o_setext o); reflexivity.
  - unfold bcuts, bunderline_of, bconfig_of. cbn. rewrite Hi.
    destruct (o_setext o), (o_tasks o); reflexivity.
Qed.

Theorem wrap_cut_setext : forall o x,
  o_setext o = true -> o_keyed o = false ->
  @parse_lines (o_inline o) (bconfig_of o) _ _ ["a"; "==="]%string (PPara [])
  <> [mk (Para x)].
Proof.
  intros o x Hs Hk.
  apply (hard_wrap_cut_not_one_para (o_inline o) (bconfig_of o) "a" [] "===").
  - reflexivity.
  - unfold keyless, bconfig_of. cbn. rewrite Hk. reflexivity.
  - reflexivity.
  - unfold bcuts, bunderline_of, bconfig_of. cbn.
    destruct (o_setext o), (o_list_interrupts o); reflexivity.
  - unfold bcuts, bunderline_of, bconfig_of. cbn. rewrite Hs. reflexivity.
Qed.

(** Heading wrapping: [heading_text_wrap_then_rest] and
   [heading_marker_wrap_then_rest] hold for the profile. *)
Definition heading_wrap_safe (o : options) : bool := o_heading_continuation o.

Lemma heading_wrap_safe_iff : forall o,
  heading_wrap_safe o = true <-> @bheading_continues (bconfig_of o) = true.
Proof. intros o. reflexivity. Qed.

(** Block quote uniformity with no excluded first line: the hypothesis of
   [quote_uniformity] holds of every line. *)
Definition quote_uniform (o : options) : bool := negb (o_callouts o).

Lemma quote_uniform_sound : forall o,
  quote_uniform o = true -> forall l, @quote_header (bconfig_of o) l = None.
Proof.
  intros o H l. unfold quote_uniform in H. unfold quote_header, bconfig_of. cbn.
  destruct (o_callouts o); [discriminate|reflexivity].
Qed.

(** Lazy continuation with no excluded line: the underline hypothesis of
   [lazy_stack_line] holds of every line. *)
Definition lazy_uniform (o : options) : bool := negb (o_setext o).

Lemma lazy_uniform_sound : forall o,
  lazy_uniform o = true -> forall l, @bunderline_of (bconfig_of o) l = None.
Proof.
  intros o H l. unfold lazy_uniform in H. unfold bunderline_of, bconfig_of. cbn.
  destruct (o_setext o); [discriminate|]. destruct (underline_of l) as [[c n]|]; reflexivity.
Qed.

(** Block structure first: the hypothesis of [block_shape_independent]. *)
Definition shape_first (o : options) : bool := negb (o_keyed o).

Lemma shape_first_iff : forall o,
  shape_first o = true <-> @bkeyed (bconfig_of o) = false.
Proof. intros o. unfold shape_first. cbn. destruct (o_keyed o); cbn; split; congruence. Qed.
