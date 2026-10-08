open Ast
open Datatypes
open InlineTable
open List0
open ListDef
open Step
open Strings

type piece = { piece_lines : string list; piece_blocks : blocks }

val pieces_text : piece list -> string list

val pieces_tree : piece list -> blocks

type pending = { pend_lines : string list; pend_blocks : blocks;
                 pend_state : pstate; pend_count : int }

val fresh : pending

val cut :
  (int -> string -> pstate -> blocks * pstate) -> string list -> pending ->
  piece list * pending

val close : (pstate -> blocks) -> pending -> piece list

val pieces :
  (int -> string -> pstate -> blocks * pstate) -> (pstate -> blocks) -> string
  list -> piece list

val settle :
  (int -> string -> pstate -> blocks * pstate) -> (pstate -> blocks) ->
  pending -> piece list -> piece list

val replace :
  (int -> string -> pstate -> blocks * pstate) -> (pstate -> blocks) -> piece
  list -> string list -> piece list -> piece list

val splice :
  (int -> string -> pstate -> blocks * pstate) -> (pstate -> blocks) -> piece
  list -> int -> int -> string list -> piece list

val sem_step : dtable -> bconfig -> int -> string -> pstate -> blocks * pstate

val loc_step : dtable -> bconfig -> int -> string -> pstate -> blocks * pstate

val loc_pieces : dtable -> bconfig -> string list -> piece list

val assemble : int -> piece list -> blocks

val parse_blocks_located : dtable -> bconfig -> string -> blocks
