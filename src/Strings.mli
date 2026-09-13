open Datatypes
open DecimalString
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

val no_nl : string -> bool

val no_char : char -> string -> bool

val is_ws_nl : char -> bool

val no_ws : string -> bool

val line_ok : string -> bool

val join_nl : string list -> string
