open Datatypes
open List0
open ListDef
open Precedence

type gparse = ((matching * int list) * int) * token list

val kmem : key -> key list -> bool

val kis : key -> key option -> bool

val after : matching -> int list -> gparse list -> gparse list

val seq :
  int -> token list -> int -> token list -> key list -> key option -> key
  option -> key list -> gparse list

val grammar_read : token list -> (matching * int list) list
