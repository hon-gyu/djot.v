open BinNums
open Datatypes
open Decimal
open Hexadecimal
open PosDef

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> coq_N

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val pow : positive -> positive -> positive

  val square : positive -> positive

  val size_nat : positive -> int

  val size : positive -> positive

  val gcdn : int -> positive -> positive -> positive

  val gcd : positive -> positive -> positive

  val ggcdn : int -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val shiftl : positive -> coq_N -> positive

  val testbit_nat : positive -> int -> bool

  val testbit : positive -> coq_N -> bool

  val of_uint_acc : Decimal.uint -> positive -> positive

  val of_uint : Decimal.uint -> coq_N

  val of_hex_uint_acc : uint -> positive -> positive

  val of_hex_uint : uint -> coq_N

  val to_little_uint : positive -> Decimal.uint

  val to_uint : positive -> Decimal.uint

  val to_little_hex_uint : positive -> uint

  val to_hex_uint : positive -> uint

  val eq_dec : positive -> positive -> bool

  val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
 end
