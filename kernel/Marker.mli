open Ascii
open Ast
open Datatypes
open Line
open List0
open ListDef
open Nat0
open PeanoNat
open Strings

val dec_acc : string -> int -> int

val dec_value : string -> int

val digit_char : int -> char

val dec_str_fuel : int -> int -> string

val dec_str : int -> string

val dec_fits : int -> bool

module Roman :
 sig
  val digit : char -> int

  val acc : string -> int -> int -> int

  val value : string -> int

  val upper : int

  val table : bool -> (int * string) list

  val pick : (int * string) list -> int -> (int * string) option

  val of_fuel : bool -> int -> int -> string

  val str : bool -> int -> string
 end

module Alpha :
 sig
  val value : bool -> string -> int

  val str : bool -> int -> string

  val upper : int
 end

val style_start : lstyle -> string -> int

val with_starts : lstyle list -> string -> (lstyle * int) list

val narrow : (lstyle * int) list -> lstyle list -> (lstyle * int) list
