open Ast
open AstEq
open Attributes
open InlineTable
open ListDef
open Nat0
open Render
open Step
open String0
open Strings

val del : int -> string -> string

val first_at : (string -> bool) -> string -> int -> string option

val first_in : (string -> bool) -> string -> int list -> (string * int) option

val next : (string -> bool) -> int -> string -> (string * int) option

val shrink_from : (string -> bool) -> int -> int -> string -> string

val shrink : (string -> bool) -> int -> string -> string

val parses_to : dtable -> bconfig -> blocks -> string -> bool

val irredundant_spec : dtable -> bconfig -> blocks -> string

val block_lines : dtable -> bconfig -> block node -> string list

val render_djot_irredundant : dtable -> bconfig -> blocks -> string
