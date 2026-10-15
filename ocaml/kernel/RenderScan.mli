open Ast
open Attributes
open Bool0
open Datatypes
open InlineTable
open InlineView
open ListDef
open Render
open Step
open Strings

val attr_eqb : attr -> attr -> bool

val target_eqb : target -> target -> bool

val opt_eqb : string option -> string option -> bool

val inline_eqb : inline -> inline -> bool

val inlines_eqb : inlines -> inlines -> bool

val text_bytes : string -> (bool * char) list

val fixed : string -> (bool * char) list

val inline_bytes : dtable -> inline -> (bool * char) list

val para_bytes : dtable -> inlines -> (bool * char) list

val full : (bool * char) list -> string

val line_rev : string -> string -> string

val line_forced : dtable -> string -> char -> string -> bool

val reads : dtable -> bconfig -> string -> inlines option

val reads_eqb : inlines option -> inlines option -> bool

val spell :
  dtable -> bconfig -> inlines option -> string -> (bool * char) list ->
  string

val text_lines_scan : dtable -> bconfig -> inlines -> string list

val render_djot_scan : dtable -> bconfig -> blocks -> string
