open Ascii
open Ast
open Datatypes
open Document
open Inline
open InlineTable
open List0
open ListDef
open Step
open Strings

val escape : string -> string

val escape_attr : string -> string

val render_attrs : attr -> string

type helt =
| HText of string
| HRaw of string
| HVoid of string * bool * attr
| HElem of string * int * attr * helt list

val open_tag : string -> bool -> attr -> string

val pieces_elt : helt -> string list -> string list

val pieces : helt list -> string list -> string list

val serialize_flat : helt list -> string

val checkbox_elt : task_status -> helt

val ref_extra : attr -> attr -> attr

val ol_attrs : ordered_list_attributes -> attr

val plain_text : inline -> string

val plain_texts : inline node list -> string

type resolver = string -> (string * attr) option

val resolve : reference_map -> resolver

val ascii_lower : char -> char

val str_lower : string -> string

val tag_letter : char -> bool

val tag_tail_ok : string -> bool

val unordinary_elements : string list

val html_tag_ok : string -> bool

val named_elem : string -> string -> attr -> string * attr

val render_inline : resolver -> inline -> attr -> helt list

val render_inlines : resolver -> inlines -> helt list

val align_attr : align -> attr

val render_cell : resolver -> cell node -> helt

val render_row : resolver -> cell node list node -> helt

val render_caption : resolver -> inlines node -> helt list

val render_block : resolver -> bool -> block -> attr -> helt list

type foot_state = { foot_labels : string list; foot_index : int StrMap.t;
                    foot_next : int }

val foot_initial : foot_state

val flat_map_st :
  (foot_state -> 'a1 -> foot_state * helt list) -> foot_state -> 'a1 list ->
  foot_state * helt list

val number_footnote : string -> foot_state -> (foot_state * int) * bool

val render_inline_foot :
  resolver -> foot_state -> inline -> attr -> foot_state * helt list

val render_inlines_foot :
  resolver -> foot_state -> inlines -> foot_state * helt list

val render_cell_foot :
  resolver -> foot_state -> cell node -> foot_state * helt

val render_cells_foot :
  resolver -> foot_state -> cell node list -> foot_state * helt list

val render_rows_foot :
  resolver -> foot_state -> cell node list node list -> foot_state * helt list

val render_caption_foot :
  resolver -> foot_state -> inlines node -> foot_state * helt list

val render_block_foot :
  resolver -> foot_state -> bool -> block -> attr -> foot_state * helt list

val render_blocks_foot :
  resolver -> foot_state -> blocks -> foot_state * helt list

val note_backlink : int -> helt

val add_backlink : helt list -> int -> helt list

val render_note_defs :
  resolver -> foot_state -> note_map -> foot_state * (string * helt list) list

val rendered_note : helt list StrMap.t -> string -> helt list

val render_note_items : int -> string list -> helt list StrMap.t -> helt list

val render_document_foot : resolver -> blocks -> note_map -> helt list

val doc_refs : doc -> reference_map

val html_tree : doc -> helt list

val render_html : doc -> string

val convert : string -> string
