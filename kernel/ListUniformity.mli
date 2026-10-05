open Ast
open Datatypes
open InlineTable
open Line
open List0
open ListDef
open Step
open Strings

val item_end_ok : string -> bool

val indent_lines : string -> string -> string list -> string list

val list_lines : list_spacing -> string list list -> string list

val run_safe : dtable -> bconfig -> string list -> pstate -> bool

val lines_loose :
  dtable -> bconfig -> bool -> bool -> pstate -> string list -> bool

val item_loose : dtable -> bconfig -> string list -> bool

type litem = marker * string list

val litem_lines : litem -> string list

val item_ok : dtable -> bconfig -> marker -> string list -> bool

val seps_loosen : string list list -> bool

val same_marker : marker -> string list list -> litem list
