(* ai-disclosure: ai-generated *)

(* Spike A: termination of `many`-style repetition for combinator parsers.

   Decision this spike is meant to settle (see .project/260802-plan.md,
   Phase 0): measure-based recursion vs fuel for the repetition combinators
   when transcribing djoths's Parse.hs.

   Approach taken here: fuel, with the fuel *discharged by a lemma* rather
   than exposed to callers.  `many` runs with fuel = |input| + 1; the
   `consuming` hypothesis (a successful parse strictly shrinks the input)
   proves that this fuel never runs out, so `many` is total and
   fuel-invisible from the outside.  This is simpler than well-founded
   recursion on a measure and matches the spec's sanctioned nesting-limit
   style.  If this scales through Phase 2, the decision is: fuel. *)

From Stdlib Require Import String Ascii List Lia Bool.
Import ListNotations.

Local Open Scope string_scope.

(*
The parser shape
================

State-monad-over-Maybe, the Gallina rendering of djoths's
  Parser s a = ParserState s -> Maybe (ParserState s, a)
with the input threaded as part of the state.  For the spike we keep only
the input string.
*)

Definition parser (A : Type) : Type := string -> option (A * string).

Definition ret {A} (x : A) : parser A := fun s => Some (x, s).

Definition bind {A B} (p : parser A) (f : A -> parser B) : parser B :=
  fun s => match p s with
           | None => None
           | Some (x, s') => f x s'
           end.

Definition any_char : parser ascii :=
  fun s => match s with
           | EmptyString => None
           | String c s' => Some (c, s')
           end.

Definition satisfy (f : ascii -> bool) : parser ascii :=
  fun s => match s with
           | String c s' => if f c then Some (c, s') else None
           | EmptyString => None
           end.

(*
The consuming discipline
------------------------
*)

Definition consuming {A} (p : parser A) : Prop :=
  forall s x s', p s = Some (x, s') -> String.length s' < String.length s.

Lemma any_char_consuming : consuming any_char.
Proof.
  intros s x s' H. destruct s; simpl in H.
  - discriminate.
  - inversion H; subst. simpl. lia.
Qed.

Lemma satisfy_consuming : forall f, consuming (satisfy f).
Proof.
  intros f s x s' H. destruct s; simpl in H.
  - discriminate.
  - destruct (f a); inversion H; subst. simpl. lia.
Qed.

(*
`many` via discharged fuel
--------------------------
*)

Fixpoint many_fuel {A} (p : parser A) (fuel : nat) (s : string)
  : list A * string :=
  match fuel with
  | O => ([], s)   (* dead branch when fuel > |s| and p is consuming *)
  | S fuel' =>
      match p s with
      | None => ([], s)
      | Some (x, s') =>
          let (xs, rest) := many_fuel p fuel' s' in
          (x :: xs, rest)
      end
  end.

Definition many {A} (p : parser A) : parser (list A) :=
  fun s => Some (many_fuel p (S (String.length s)) s).

(* The discharge lemma: for a consuming parser, any fuel beyond the input
   length gives the same answer — the O branch is unreachable.  This is
   what makes `many` well-defined rather than fuel-sensitive. *)

Lemma many_fuel_stable :
  forall {A} (p : parser A), consuming p ->
  forall n m s,
    String.length s < n -> String.length s < m ->
    many_fuel p n s = many_fuel p m s.
Proof.
  intros A p Hp.
  induction n as [|n IH]; intros m s Hn Hm; [lia|].
  destruct m as [|m]; [lia|].
  simpl.
  destruct (p s) as [[x s']|] eqn:Hps; [|reflexivity].
  apply Hp in Hps.
  rewrite (IH m s'); [reflexivity|lia|lia].
Qed.

(* Corollary in the form later proofs will use: unfolding one step of
   `many` never hits the fuel bottom. *)

Lemma many_unfold :
  forall {A} (p : parser A), consuming p ->
  forall s,
    many p s = Some (match p s with
                     | None => ([], s)
                     | Some (x, s') =>
                         match many p s' with
                         | Some (xs, rest) => (x :: xs, rest)
                         | None => ([], s)   (* unreachable: many never fails *)
                         end
                     end).
Proof.
  intros A p Hp s. unfold many at 1. f_equal.
  cbn [many_fuel].
  destruct (p s) as [[x s']|] eqn:Hps; [|reflexivity].
  pose proof (Hp _ _ _ Hps) as Hlen.
  rewrite (many_fuel_stable p Hp (String.length s) (S (String.length s')) s')
    by lia.
  unfold many.
  destruct (many_fuel p (S (String.length s')) s') as [xs rest]; reflexivity.
Qed.

(* `many p` consumes weakly (never grows the input); useful as the glue
   when a repetition sits inside another consuming context. *)

Lemma many_fuel_weak :
  forall {A} (p : parser A) fuel s xs rest,
    consuming p ->
    many_fuel p fuel s = (xs, rest) ->
    String.length rest <= String.length s.
Proof.
  intros A p fuel.
  induction fuel as [|fuel IH]; intros s xs rest Hp H; simpl in H.
  - inversion H; subst; lia.
  - destruct (p s) as [[x s']|] eqn:Hps.
    + destruct (many_fuel p fuel s') as [xs' rest'] eqn:Hm.
      inversion H; subst.
      apply Hp in Hps.
      specialize (IH _ _ _ Hp Hm). lia.
    + inversion H; subst; lia.
Qed.

(*
Spike verdict
=============

Recorded here so the decision is greppable:

- VERDICT (2026-08-02): fuel with discharge lemmas (`many_fuel_stable`).
  Costs one lemma per recursion pattern; no Program/Function machinery, no
  Acc-based unfolding pain, extraction stays clean (the fuel is a nat the
  extracted code computes in O(1) from the input length).
- Revisit if Phase 2's block loop (lexicographic in (position, stack
  depth)) makes the discharge lemmas compound awkwardly.
*)
