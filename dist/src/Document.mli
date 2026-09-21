open Ast
open Datatypes
open Inline
open List0
open ListDef
open Nat0
open Step
open Strings

val inline_text : inline -> string

val inlines_text : inlines -> string

val is_id_sep : char -> bool

val id_base : string -> string

val id_taken : string list -> string -> bool

val id_candidate : string -> nat -> string

val unique_id_from : nat -> nat -> string list -> string -> string

val unique_id : string list -> string -> string

type id_state = { id_used : string list; id_refs : reference_map }

val id_state_init : id_state

val add_auto_ref : string -> string -> id_state -> id_state

val register_id : attr -> id_state -> id_state

val assign_heading_id :
  pos -> attr -> nat -> inlines -> id_state -> id_state * block node

val assign_ids : block -> pos -> attr -> id_state -> id_state * block node

val assign_ids_node : block node -> id_state -> id_state * block node

val assign_ids_list : blocks -> id_state -> id_state * blocks

type sect_state = ((nat * attr) * blocks) list

val sect_init : sect_state

val section_node : coq_PosPolicy -> attr -> blocks -> block node

val close_ge : coq_PosPolicy -> nat -> blocks -> sect_state -> sect_state

val close_all : coq_PosPolicy -> blocks -> sect_state -> sect_state

val sect_push : block node -> sect_state -> sect_state

val sect_step : coq_PosPolicy -> sect_state -> block node -> sect_state

val sect_bottom : sect_state -> blocks

val sectionize : coq_PosPolicy -> blocks -> blocks

val add_ref : pos -> attr -> block -> reference_map -> reference_map

val collect_refs : block -> pos -> attr -> reference_map -> reference_map

val collect_refs_list : blocks -> reference_map -> reference_map

val collect_notes :
  block -> pos -> attr -> note_map -> note_map * block node option

val collect_notes_list : blocks -> note_map -> note_map * blocks

val doc_pass : coq_PosPolicy -> blocks -> doc

val parse_doc : dtable -> bconfig -> coq_PosPolicy -> string -> doc

val parse_doc_located : dtable -> bconfig -> string -> doc
