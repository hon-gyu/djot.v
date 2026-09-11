open Ascii
open Ast
open Datatypes
open Line
open List0
open ListUniformity
open Marker
open Nat0
open PeanoNat
open Step

val nsc_marker : (nat -> string) -> ordered_list_delim -> nat -> marker

val nsc_items :
  (nat -> string) -> ordered_list_delim -> nat -> string list list -> litem
  list

val dec_marker : ordered_list_delim -> nat -> marker

val dec_items : ordered_list_delim -> nat -> string list list -> litem list

val roman_sty : bool -> ordered_list_style

val alpha_sty : bool -> ordered_list_style

val alpha_char : bool -> nat -> char

val alpha_roman_digit : bool -> nat -> bool

type list_kind =
| LKBullet
| LKDef
| LKTask of task_status list
| LKDecimal of ordered_list_delim * nat
| LKRoman of bool * ordered_list_delim * nat
| LKAlpha of bool * ordered_list_delim * nat

val ck_first : list_kind -> marker

val task_ck_items : task_status list -> string list list -> litem list

val ck_items : list_kind -> string list list -> litem list

val ck_block : list_kind -> list_spacing -> blocks list -> block

val ck_ok : bconfig -> list_kind -> nat -> bool
