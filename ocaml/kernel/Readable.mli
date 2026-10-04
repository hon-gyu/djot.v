open Ast
open Attributes
open Datatypes
open InlineTable
open InlineView
open Line
open List0
open ListDef
open ListUniformity
open Nat0
open OrderedList
open PeanoNat
open Render
open Step
open Strings

val own_char : dtable -> dstyle -> char option -> bool

val bare_ok : dtable -> dstyle -> char option -> string -> dstyle list -> bool

val direct_close : string -> string

val readable_text : dtable -> inline -> char option -> dstyle list -> string

val readable_nodes : dtable -> inlines -> char option -> string

val readable_inline_lines : dtable -> inlines -> string list

val prefixed : string -> string -> string

val quoted : string -> string

val first_then : string -> string -> string list -> string list

val item_lines : litem -> string list

val task_lines : (task_status * string list) -> string list

val note_lines : string -> bool -> string list -> string list

val caption_lines : string list -> string list

val cell_text : dtable -> cell -> string

val cell_align : cell -> align

val max_zip : int list -> int list -> int list

val col_widths : string list list -> int list

val row_body : int list -> string list -> string

val sep_cell : int -> align -> string

val sep_row_body : int list -> align list -> string

val table_lines : dtable -> cell list list -> string list

val readable_lines : dtable -> bconfig -> attr -> block -> string list

val readable_djot : dtable -> bconfig -> blocks -> string

val readable_doc : dtable -> bconfig -> doc -> string
