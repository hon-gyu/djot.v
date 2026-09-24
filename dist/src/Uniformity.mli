open Ast
open Datatypes
open InlineTable
open Line
open Step
open Strings

val run_lines : dtable -> bconfig -> string list -> pstate -> blocks * pstate

val run_div_open : dtable -> bconfig -> nat -> string list -> pstate -> bool

val div_content_ok : dtable -> bconfig -> string list -> bool

val pend_carriable : pstate -> bool

val key_carriable : pstate -> bool

val key_content_ok : dtable -> bconfig -> string list -> pstate -> bool
