open Ast
open Datatypes
open InlineScan
open InlineTable
open InlineView
open ListDef
open Nat0
open String0
open Strings

val cursor_in : nat -> nat -> spot -> coq_InlineCursor

val iscan_str_located :
  dtable -> coq_PosPolicy -> bool -> nat -> spot -> nat -> string -> iscan ->
  iscan

val lines_start : (nat * string) list -> spot

val lines_stop : (nat * string) list -> spot

val allow_attrs : dtable -> nat -> bool

val iscan_lines_located :
  dtable -> coq_PosPolicy -> nat -> spot -> (nat * string) list -> iscan ->
  iscan

val ifinish_located :
  dtable -> coq_PosPolicy -> (nat * string) list -> iscan -> inlines

val para_inlines_located :
  dtable -> coq_PosPolicy -> nat -> (nat * string) list -> inlines

val para_inlines_at :
  dtable -> coq_PosPolicy -> nat -> (nat * string) list -> inlines

val parse_inline_line_located :
  dtable -> coq_PosPolicy -> nat -> nat -> string -> inlines
