open Ast
open AstEq
open Attributes
open Datatypes
open InlineTable
open List0
open Nat0
open Render
open Step
open String0
open Strings

val del : int -> string -> string

val stop_go : int -> int -> string -> int

val para_stop : string -> int -> int

val first_at :
  (string -> 'a1 option) -> string -> int -> (string * 'a1) option

val first_from :
  (string -> 'a1 option) -> string -> int -> int -> ((string * 'a1) * int)
  option

val next :
  (string -> 'a1 option) -> int -> string -> ((string * 'a1) * int) option

val shrink_by :
  ('a1 -> string -> 'a1 option) -> int -> int -> 'a1 -> string -> string

val same_state : pstate -> pstate -> bool

type entry = (string * pstate) * blocks

val trace : dtable -> bconfig -> string list -> pstate -> entry list * pstate

val rest_of : dtable -> bconfig -> entry list -> pstate -> blocks

type known = { k_rev : string list; k_trace : entry list; k_fin : pstate }

val known_of : dtable -> bconfig -> string -> known

val resync :
  dtable -> bconfig -> int -> int -> pstate -> blocks -> blocks -> entry list
  -> entry list -> string list -> pstate -> (entry list * pstate) option

val walk :
  dtable -> bconfig -> int -> int -> entry list -> entry list -> string list
  -> pstate -> (entry list * pstate) option

val common_prefix : string list -> string list -> int

val fast_test : dtable -> bconfig -> known -> string -> known option

val render_djot_irredundant : dtable -> bconfig -> blocks -> string
