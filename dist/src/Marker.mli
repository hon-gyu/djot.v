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

val roman_digit : char -> nat

val roman_acc : string -> nat -> nat -> nat

val roman_value : string -> nat

val alpha_value : bool -> string -> nat

val roman_upper : nat

val roman_table : bool -> (nat * string) list

val roman_pick : (nat * string) list -> nat -> (nat * string) option

val roman_fuel : bool -> nat -> nat -> string

val roman_str : bool -> nat -> string

val alpha_str : bool -> nat -> string

val alpha_upper : nat

val style_start : lstyle -> string -> nat

val with_starts : lstyle list -> string -> (lstyle * nat) list

val narrow : (lstyle * nat) list -> lstyle list -> (lstyle * nat) list
