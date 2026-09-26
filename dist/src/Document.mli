open Ast
open Datatypes
open InlineTable
open List0
open ListDef
open Step
open Strings

val inline_text : inline -> string

val inlines_text : inlines -> string

val is_id_sep : char -> bool

val id_base : string -> string

val id_taken : string list -> string -> bool

val id_candidate : string -> int -> string

val unique_id_from : int -> int -> string list -> string -> string

val unique_id : string list -> string -> string

type id_state = { id_used : string list; id_refs : reference_map }

val id_state_init : id_state

val add_auto_ref : string -> string -> id_state -> id_state

val register_id : attr -> id_state -> id_state

val assign_heading_id :
  pos -> attr -> int -> inlines -> id_state -> id_state * block node

module Ids :
 sig
  val of_block : block -> pos -> attr -> id_state -> id_state * block node

  val of_node : block node -> id_state -> id_state * block node

  val of_list : blocks -> id_state -> id_state * blocks
 end

type sect_state = ((int * attr) * blocks) list

val sect_init : sect_state

val section_node : coq_PosPolicy -> attr -> blocks -> block node

val close_ge : coq_PosPolicy -> int -> blocks -> sect_state -> sect_state

val close_all : coq_PosPolicy -> blocks -> sect_state -> sect_state

val sect_push : block node -> sect_state -> sect_state

val sect_step : coq_PosPolicy -> sect_state -> block node -> sect_state

val sect_bottom : sect_state -> blocks

val sectionize : coq_PosPolicy -> blocks -> blocks

val add_ref : pos -> attr -> block -> reference_map -> reference_map

module Refs :
 sig
  val of_block : block -> pos -> attr -> reference_map -> reference_map

  val of_list : blocks -> reference_map -> reference_map
 end

module Notes :
 sig
  val of_block :
    block -> pos -> attr -> note_map -> note_map * block node option

  val of_list : blocks -> note_map -> note_map * blocks
 end

val doc_pass : coq_PosPolicy -> blocks -> doc

val parse_doc : dtable -> bconfig -> coq_PosPolicy -> string -> doc

val parse_doc_located : dtable -> bconfig -> string -> doc
