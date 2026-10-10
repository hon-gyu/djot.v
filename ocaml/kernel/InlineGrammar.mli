open Datatypes
open InlineTable
open List0
open ListDef
open Nat0
open Precedence

val kmem : key -> key list -> bool

val kis : key -> key option -> bool

val closer_from : dtable -> string -> key -> int -> bool

type gparse = (matching * int list) * int

val after : matching -> int list -> gparse list -> gparse list

val level :
  dtable -> int -> string -> int -> key list -> key option -> key option ->
  key list -> gparse list

val grammar_read : dtable -> string -> (matching * int list) list
