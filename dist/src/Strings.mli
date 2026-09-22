open Ast
open Datatypes
open DecimalString
open List0
open Nat0

val is_ws : char -> bool

val is_blank : string -> bool

val nonblank : string -> bool

val nonempty : 'a1 list -> bool

val nonempty_str : string -> bool

val nat_str : nat -> string

val rev_string : string -> string

val drop_leading_ws : string -> string

val indent_of : string -> nat

val strip_trailing_ws : string -> string

val drop_ws_upto : nat -> string -> string

val nl : string

val split_lines : string -> string list

val index_lines_from : nat -> string list -> (nat * string) list

val split_lines_indexed : string -> (nat * string) list

type source_line = { source_line_start : nat; source_line_length : nat;
                     source_line_ending : nat }

val line_table_aux : string -> nat -> nat -> source_line list

val line_table : string -> source_line list

val source_line_at : source_line list -> nat -> source_line option

type source_point = { source_byte : nat; source_line_index : nat;
                      source_column : nat }

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
