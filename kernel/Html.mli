open Ascii
open Ast
open Datatypes
open Document
open Inline
open InlineTable
open List0
open ListDef
open Nat0
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

val ascii_lower : char -> char

val str_lower : string -> string

val tag_letter : char -> bool

val tag_tail_ok : string -> bool

val unordinary_elements : string list

val html_tag_ok : string -> bool

val named_elem : string -> string -> attr -> string * attr

val render_inline : reference_map -> inline -> attr -> helt list

val render_inlines : reference_map -> inlines -> helt list

val align_attr : align -> attr

val render_cell : reference_map -> cell node -> helt

val render_row : reference_map -> cell node list node -> helt

val render_caption : reference_map -> inlines node -> helt list

val render_block : reference_map -> bool -> block -> attr -> helt list

type foot_state = { foot_numbers : (string * int) list; foot_next : int }

val foot_initial : foot_state

val number_footnote : string -> foot_state -> (foot_state * int) * bool

val render_inline_foot :
  reference_map -> foot_state -> inline -> attr -> foot_state * helt list

val render_inlines_foot :
  reference_map -> foot_state -> inlines -> foot_state * helt list

val render_cell_foot :
  reference_map -> foot_state -> cell node -> foot_state * helt

val render_cells_foot :
  reference_map -> foot_state -> cell node list -> foot_state * helt list

val render_rows_foot :
  reference_map -> foot_state -> cell node list node list -> foot_state * helt
  list

val render_caption_foot :
  reference_map -> foot_state -> inlines node -> foot_state * helt list

val render_block_foot :
  reference_map -> foot_state -> bool -> block -> attr -> foot_state * helt
  list

val render_blocks_foot :
  reference_map -> foot_state -> blocks -> foot_state * helt list

val note_backlink : int -> helt

val add_backlink : helt list -> int -> helt list

val render_note_defs :
  reference_map -> foot_state -> note_map -> foot_state * (string * helt list)
  list

val label_at : int -> (string * int) list -> string option

val rendered_note_at :
  int -> foot_state -> (string * helt list) list -> helt list

val render_note_items :
  int -> int -> foot_state -> (string * helt list) list -> helt list

val render_document_foot : reference_map -> blocks -> note_map -> helt list

val doc_refs : doc -> reference_map

val html_tree : doc -> helt list

val render_html : doc -> string

val convert : string -> string
