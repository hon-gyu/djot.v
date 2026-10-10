open Datatypes
open InlineTable
open List0
open ListDef
open Precedence

val toks_from : dtable -> string -> int -> int -> (int * token) list

val para_toks : dtable -> string -> (int * token) list

val index_of : int -> int list -> int -> int option

val region_ix : string -> int list -> int -> bool -> int option

type gparse = ((matching * int list) * int) * token list

val kmem : key -> key list -> bool

val kis : key -> key option -> bool

val after : matching -> int list -> gparse list -> gparse list

val seq :
  int -> string -> int list -> token list -> int -> token list -> key list ->
  key option -> key option -> key list -> gparse list

val grammar_read : dtable -> string -> (matching * int list) list
