open Ascii
open Ast
open Datatypes
open Line
open List0
open ListDef
open Nat0
open PeanoNat
open Strings

val dec_acc : string -> nat -> nat

val dec_value : string -> nat

val digit_char : nat -> char

val dec_str_fuel : nat -> nat -> string

val dec_str : nat -> string

module Roman :
 sig
  val digit : char -> nat

  val acc : string -> nat -> nat -> nat

  val value : string -> nat

  val upper : nat

  val table : bool -> (nat * string) list

  val pick : (nat * string) list -> nat -> (nat * string) option

  val of_fuel : bool -> nat -> nat -> string

  val str : bool -> nat -> string
 end

module Alpha :
 sig
  val value : bool -> string -> nat

  val str : bool -> nat -> string

  val upper : nat
 end

val style_start : lstyle -> string -> nat

val with_starts : lstyle list -> string -> (lstyle * nat) list

val narrow : (lstyle * nat) list -> lstyle list -> (lstyle * nat) list
