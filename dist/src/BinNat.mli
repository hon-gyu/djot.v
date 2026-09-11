open BinNums
open BinPos
open Datatypes
open PosDef

module N :
 sig
  val compare : coq_N -> coq_N -> comparison

  val add : coq_N -> coq_N -> coq_N

  val mul : coq_N -> coq_N -> coq_N

  val to_nat : coq_N -> nat

  val of_nat : nat -> coq_N
 end
