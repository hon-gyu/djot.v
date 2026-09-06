(* ai-disclosure: ai-generated *)

(* Falsification apparatus: search a finite pool for a counterexample to
   a candidate statement, and report the input that breaks it.

   The problem this is for.  A statement about `step` or `parse_lines` is
   a claim about what a program computes, and the parser is executable,
   so the claim is decidable on any one input long before it is provable.

   What it is not.  There is no shrinking and no random generation: the
   pools are small and curated, so a witness is already small.  A `Pass`
   is evidence, never a proof -- it says the pool contains no
   counterexample, which for a statement quantified over all states and
   all lines is a much weaker claim than the statement.  Use it to
   *reject* candidates cheaply, then prove the survivors.

   Stdlib only, by design.  Nothing here mentions the parser, so this
   file never rebuilds when the parser changes and costs nothing to keep
   in the default build.  The pools, the comparisons and the probe runs
   are parser-coupled and live in `dev/check/Probe.v`, which dune does not
   build. *)

From Stdlib Require Import String List Bool.
Import ListNotations.

(*
Verdicts
========
*)

(* Three outcomes rather than a bool, so that a *conditional* statement
   can distinguish "the guard held and the conclusion did" from "the
   guard never held".  Without `Skip` the two are both `true`, and a
   probe whose guard is unsatisfiable over the pool reports a clean pass
   while having tested nothing -- the exact failure mode this file exists
   to remove. *)
Inductive verdict : Type := Pass | Fail | Skip.

Definition holds (b : bool) : verdict := if b then Pass else Fail.

(* `guarded g c` is the probe form of `g = true -> c = true`. *)
Definition guarded (g c : bool) : verdict := if g then holds c else Skip.

(*
Products
========
*)

(* A statement over two or three variables becomes a statement over one
   by pairing the pools.  `pairs xs ys` has |xs| * |ys| elements, so keep
   the pools small; that is what makes curation rather than volume the
   right shape for them. *)
Definition pairs {A B : Type} (xs : list A) (ys : list B) : list (A * B) :=
  flat_map (fun x => map (fun y => (x, y)) ys) xs.

Definition triples {A B C : Type} (xs : list A) (ys : list B) (zs : list C)
  : list (A * B * C) :=
  flat_map (fun x => flat_map (fun y => map (fun z => (x, y, z)) zs) ys) xs.

(*
Searching
=========
*)

(* The first input the statement fails on, if any.  Short-circuits, so a
   pool whose tail is expensive costs nothing once a witness is found. *)
Fixpoint first_fail {A : Type} (p : A -> verdict) (xs : list A) : option A :=
  match xs with
  | [] => None
  | x :: rest =>
      match p x with
      | Fail => Some x
      | Pass | Skip => first_fail p rest
      end
  end.

(* Up to `n` failing inputs.  One witness says the statement is false; a
   handful says whether it is false on a boundary case or false
   everywhere, which is the difference between weakening a hypothesis and
   abandoning the approach. *)
Fixpoint fails {A : Type} (n : nat) (p : A -> verdict) (xs : list A)
  : list A :=
  match n, xs with
  | O, _ | _, [] => []
  | S n', x :: rest =>
      match p x with
      | Fail => x :: fails n' p rest
      | Pass | Skip => fails n p rest
      end
  end.

(*
Vacuity
=======
*)

(* Read this before believing a `None` from `first_fail`.  A conditional
   probe with `t_pass = 0` has been refuted by nothing: every input was
   discarded by the guard, and the statement is untested rather than
   supported. *)
Record tally : Type := Tally
  { t_pass : nat
  ; t_fail : nat
  ; t_skip : nat }.

Definition tally_add (v : verdict) (t : tally) : tally :=
  match v with
  | Pass => Tally (S (t_pass t)) (t_fail t) (t_skip t)
  | Fail => Tally (t_pass t) (S (t_fail t)) (t_skip t)
  | Skip => Tally (t_pass t) (t_fail t) (S (t_skip t))
  end.

Definition count {A : Type} (p : A -> verdict) (xs : list A) : tally :=
  fold_right (fun x t => tally_add (p x) t) (Tally 0 0 0) xs.

(*
Reporting
=========
*)

(* A witness is only useful if it can be read.  `probe` pairs the search
   with the pool's own printer, so a run answers "false, and here is the
   input" in one line rather than returning a term the reader then has to
   normalize by hand. *)
Definition probe {A : Type} (show : A -> string) (p : A -> verdict)
                 (xs : list A) : option string :=
  option_map show (first_fail p xs).

(* The full report: the counts beside the witness, so that a `None` is
   never read without the evidence that the pool exercised the guard. *)
Definition report {A : Type} (show : A -> string) (p : A -> verdict)
                  (xs : list A) : tally * option string :=
  (count p xs, probe show p xs).
