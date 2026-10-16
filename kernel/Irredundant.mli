open Ast
open AstEq
open Attributes
open Datatypes
open InlineTable
open List0
open ListDef
open Nat0
open PeanoNat
open Render
open Step
open String0
open Strings

val del : int -> string -> string

val stop_go : int -> int -> string -> int

val para_stop : string -> int -> int

type cand = string * (int * int option)

val first_at : (cand -> 'a1 option) -> string -> int -> (cand * 'a1) option

val first_from :
  (cand -> 'a1 option) -> string -> int -> int -> ((cand * 'a1) * int) option

val next :
  (cand -> 'a1 option) -> int -> string -> ((cand * 'a1) * int) option

val shrink_by :
  ('a1 -> cand -> 'a1 option) -> int -> int -> 'a1 -> string -> string

val same_state : pstate -> pstate -> bool

type entry = (string * pstate) * blocks

val trace : dtable -> bconfig -> string list -> pstate -> entry list * pstate

val state_of : entry list -> pstate -> pstate

val rest_of : dtable -> bconfig -> entry list -> pstate -> blocks

type known = { k_lines : string list; k_nl : bool; k_trace : entry list;
               k_fin : pstate }

val ends_nl : string -> bool

val known_of : dtable -> bconfig -> string -> known

val resync :
  dtable -> bconfig -> int -> int -> pstate -> blocks -> blocks -> entry list
  -> entry list -> string list -> pstate -> (entry list * pstate) option

val walk :
  dtable -> bconfig -> int -> int -> entry list -> entry list -> string list
  -> pstate -> (entry list * pstate) option

val common_prefix : string list -> string list -> int

val walk_test : dtable -> bconfig -> known -> string -> known option

val locate : int -> string list -> (int * int) option

val replace : int -> (string -> string) -> string list -> string list

val del_lines :
  (int * int option) -> string list -> ((string list * int) * int) option

val ends_ok : string list -> bool -> bool

val fast_test : dtable -> bconfig -> known -> cand -> known option

val render_djot_irredundant : dtable -> bconfig -> blocks -> string
