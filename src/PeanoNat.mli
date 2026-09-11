open Datatypes

module Nat :
 sig
  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val divmod : nat -> nat -> nat -> nat -> nat * nat

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat
 end
