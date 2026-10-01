open Ast
open Datatypes
open InlineTable
open List0
open ListDef
open Step

type piece = { piece_lines : string list; piece_blocks : blocks }

val pieces_text : piece list -> string list

val pieces_tree : piece list -> blocks

type pending = { pend_lines : string list; pend_blocks : blocks;
                 pend_state : pstate }

val fresh : pending

val cut : dtable -> bconfig -> string list -> pending -> piece list * pending

val close : dtable -> bconfig -> pending -> piece list

val pieces : dtable -> bconfig -> string list -> piece list

val settle : dtable -> bconfig -> pending -> piece list -> piece list

val replace :
  dtable -> bconfig -> piece list -> string list -> piece list -> piece list

val splice :
  dtable -> bconfig -> piece list -> int -> int -> string list -> piece list
