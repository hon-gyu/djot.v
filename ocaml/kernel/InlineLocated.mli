open Ast
open Datatypes
open InlineScan
open InlineTable
open InlineView
open ListDef
open Nat0
open Strings

val cursor_in : int -> int -> spot -> coq_InlineCursor

val iscan_str_located :
  dtable -> coq_PosPolicy -> bool -> int -> spot -> int -> string -> string
  iscan_g -> string iscan_g

val lines_start : (int * string) list -> spot

val lines_stop : (int * string) list -> spot

val allow_attrs : dtable -> int -> bool

val iscan_lines_located :
  dtable -> coq_PosPolicy -> int -> spot -> (int * string) list -> string
  iscan_g -> string iscan_g

val ifinish_located :
  dtable -> coq_PosPolicy -> (int * string) list -> string iscan_g -> inlines

val sscan_str_located :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> bool -> int -> spot -> int ->
  string -> 'a1 sscan -> 'a1 sscan

val sscan_lines_located :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> int -> spot -> (int * string)
  list -> 'a1 sscan -> 'a1 sscan

val para_inlines_located_stk :
  dtable -> coq_PosPolicy -> int -> (int * string) list -> inlines

val parse_inline_line_located_stk :
  dtable -> coq_PosPolicy -> int -> int -> string -> inlines

val para_inlines_located :
  dtable -> coq_PosPolicy -> int -> (int * string) list -> inlines

val para_inlines_at :
  dtable -> coq_PosPolicy -> int -> (int * string) list -> inlines

val parse_inline_line_located :
  dtable -> coq_PosPolicy -> int -> int -> string -> inlines
