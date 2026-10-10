open Ast
open Datatypes
open List0
open Nat0

val is_ws : char -> bool

val is_blank : string -> bool

val nonblank : string -> bool

val nonempty : 'a1 list -> bool

val nonempty_str : string -> bool

val nat_str : int -> string

val rev_string : string -> string

val drop_leading_ws : string -> string

val indent_of : string -> int

val strip_trailing_ws : string -> string

val drop_ws_upto : int -> string -> string

val sdrop : int -> string -> string

val nl : string

val split_lines : string -> string list

type source_line = { source_line_start : int; source_line_length : int;
                     source_line_ending : int }

val line_table : string -> source_line list

val source_line_at : source_line list -> int -> source_line option

type source_point = { source_byte : int; source_line_index : int;
                      source_column : int }

type source_span = { source_span_start : source_point;
                     source_span_stop : source_point }

val resolve_spot : source_line list -> spot -> source_point option

val resolve_span : source_line list -> span -> source_span option

val no_nl : string -> bool

val no_char : char -> string -> bool

val is_ws_nl : char -> bool

val no_ws : string -> bool

val line_ok : string -> bool

val join_nl : string list -> string
