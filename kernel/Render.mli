open Ast
open Attributes
open Datatypes
open InlineScan
open InlineTable
open InlineView
open Line
open List0
open ListDef
open ListUniformity
open OrderedList
open PeanoNat
open Step
open Strings
open Uniformity

val thematic_line : string

val ref_line : string -> string -> string

val key_line : string -> string -> string

val key_inline_ok : dtable -> string -> string -> bool

val key_lines : dtable -> string -> bool -> string list -> string list

val code_close : string

val code_open : string -> string

val align_dashes : align -> string

val sep_body : align list -> string

val sep_line : align list -> string

val cells_line : string list -> string

val sep_lines : string list list -> string list

type ctrow =
| CTBody of cinline list list
| CTHead of align list * cinline list list

val ctrow_cells : ctrow -> cinline list list

val ctrow_lines : dtable -> ctrow -> string list

val ccells_of : cell_type -> align list -> cinline list list -> cell list

val ctable_cells : align list -> ctrow list -> cell list list

type cblock =
| CPara of cinline list list
| CThematic
| CCode of string * string list
| CRaw of string * string list
| CHeading of int * cinline list list
| CQuote of cblock list
| CCallout of string * callout_fold option * cinline list * cblock list
| CDiv of string * cblock list
| CList of list_kind * list_spacing * cblock list list
| CRef of string * string
| CTable of ctrow list
| CId of string * cblock
| CKey of cinline * cblock

val cb_lines : dtable -> cblock -> string list

val cb_ast : cblock -> block node

val item_lines : dtable -> cblock list -> string list

val blocks_of_cblocks : cblock list -> blocks

val cline : string -> cinline list

val cpara : string list -> cblock

val cheading : int -> string list -> cblock

val para_ok : dtable -> bconfig -> string list -> bool

val code_ok : string -> string list -> bool

val raw_ok : string -> string list -> bool

val heading_ok : bconfig -> int -> string list -> bool

val quote_header_safe : dtable -> bconfig -> cblock list -> bool

val callout_title_ok : dtable -> cinline list -> bool

val item_forces_loose : dtable -> bconfig -> cblock list -> bool

val items_force_loose : dtable -> bconfig -> cblock list list -> bool

val items_seps_loosen : dtable -> bconfig -> cblock list list -> bool

val is_clist : cblock -> bool

val is_cid : cblock -> bool

val ends_clist : cblock -> bool

val ends_ctable : cblock -> bool

val is_cref : cblock -> bool

val closes_table : dtable -> cblock -> bool

val cb_pair_ok : dtable -> cblock -> cblock -> bool

val cb_pairs_ok : dtable -> cblock list -> bool

val ref_ok : string -> string -> bool

val row_reparses : trow -> string -> bool

val cdef_head_ok : cblock list -> bool

val ck_content_ok : list_kind -> cblock list list -> bool

val ctrow_ok : dtable -> ctrow -> bool

val ckey_label_ok : dtable -> cinline -> bool

val div_name_ok : bconfig -> string -> bool

val cb_ok : dtable -> bconfig -> cblock -> bool

val lk_of_ol : ordered_list_attributes -> list_kind

val cell_text : dtable -> cell -> string

val cell_align : cell -> align

val render_row : dtable -> cell list -> string list

val initial_sep : cell list list -> string list

val table_lines : dtable -> cell list list -> string list

val text_lines : dtable -> inlines -> string list

val caption_lines : dtable -> inlines -> string list

val task_open : task_status -> string

val task_empty : task_status -> string

val task_litem_lines : (task_status * string list) -> string list

val item_or_marker_lines : litem -> string list

val attr_lines : attr -> string list

val fence_class : bconfig -> attr -> block -> string

val drop_class : string -> attr -> attr

val closer_run : string -> int

val div_fence_for : dtable -> bconfig -> string list -> string

val note_indent : string -> string

val render_lines : dtable -> bconfig -> attr -> block -> string list

val render_node_lines : dtable -> bconfig -> block node -> string list

val render_blocks_lines : dtable -> bconfig -> blocks -> string list list

val render_djot : dtable -> bconfig -> blocks -> string

val drop_derived : attr -> string list -> string list * attr

val drop_auto_ids :
  block -> pos -> attr -> string list -> string list * block node

val doc_source_blocks : doc -> blocks

val render_doc : dtable -> bconfig -> doc -> string
