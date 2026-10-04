open Datatypes
open List0
open ListDef

val alist_lookup : string -> (string * 'a1) list -> 'a1 option

val alist_set : string -> 'a1 -> (string * 'a1) list -> (string * 'a1) list

type attr = (string * string) list

module Attr :
 sig
  val integrate : (string * string) -> attr -> attr

  val union : attr -> attr -> attr

  val set : string -> string -> attr -> attr

  val add_class : string -> attr -> attr

  val remove : string -> attr -> attr

  val set_classes : string list -> attr -> attr

  val put : (string * string) -> attr -> attr

  val merge : attr -> attr -> attr

  val apply_pending : attr -> attr -> attr
 end

type spot = { spot_line : int; spot_rem : int }

type span = { span_start : spot; span_stop : spot }

type coq_InlineCursor = { cursor_start : spot; cursor_stop : spot;
                          cursor_origin : spot }

val semantic_inline_cursor : coq_InlineCursor

type syntax_role =
| RAttrSpec
| ROpenFence
| RCloseFence

type provenance = { node_span : span; syntax_spans : (syntax_role * span) list }

type pos =
| NoPos
| SomePos of provenance

type 'a node =
| Node of pos * attr * 'a

val node_provenance : 'a1 node -> provenance option

val mk : 'a1 -> 'a1 node

val node_contents : 'a1 node -> 'a1

val node_attrs : 'a1 node -> attr

val add_attr : attr -> 'a1 node -> 'a1 node

type coq_PosPolicy = { mkpos : (provenance -> pos); pos_records : bool }

val semantic_pos : coq_PosPolicy

val located_pos : coq_PosPolicy

val posnode : coq_PosPolicy -> provenance -> 'a1 -> 'a1 node

val null_span : span

val pspan : coq_PosPolicy -> span -> span

val prov_at : span -> provenance

val prov_with : span -> (syntax_role * span) list -> provenance

val attr_roles : span list -> (syntax_role * span) list

val set_pos : coq_PosPolicy -> provenance -> 'a1 node -> 'a1 node

val pos_head : coq_PosPolicy -> provenance -> 'a1 node list -> 'a1 node list

val add_roles :
  coq_PosPolicy -> (syntax_role * span) list -> 'a1 node -> 'a1 node

val add_roles_head :
  coq_PosPolicy -> (syntax_role * span) list -> 'a1 node list -> 'a1 node list

val hull_pos : coq_PosPolicy -> 'a1 node list -> pos

val hull_pos_with : coq_PosPolicy -> 'a1 node list -> pos

type math_style =
| DisplayMath
| InlineMath

type target =
| Direct of string
| Reference of string

type quote_type =
| SingleQuotes
| DoubleQuotes

type inline =
| Str of string
| Emph of inline node list
| Strong of inline node list
| Highlight of inline node list
| Insert of inline node list
| Delete of inline node list
| Superscript of inline node list
| Subscript of inline node list
| Verbatim of string
| Symbol of string
| Math of math_style * string
| Link of inline node list * target
| Image of inline node list * target
| Span of string * inline node list
| FootnoteReference of string
| UrlLink of string
| EmailLink of string
| RawInline of string * string
| NonBreakingSpace
| Quoted of quote_type * inline node list
| SoftBreak
| HardBreak
| Ext_wikilink of bool * string * string option

type inlines = inline node list

type list_spacing =
| Tight
| Loose

type ordered_list_style =
| Decimal
| LetterUpper
| LetterLower
| RomanUpper
| RomanLower

type ordered_list_delim =
| RightPeriod
| RightParen
| LeftRightParen

type ordered_list_attributes = { ol_style : ordered_list_style;
                                 ol_delim : ordered_list_delim; ol_start :
                                 int }

type task_status =
| Complete
| Incomplete

type callout_fold =
| FoldExpanded
| FoldCollapsed

type align =
| AlignLeft
| AlignRight
| AlignCenter
| AlignDefault

type cell_type =
| HeadCell
| BodyCell

val align_eqb : align -> align -> bool

type cell =
| Cell of cell_type * align * inlines

type block =
| Para of inlines
| Section of block node list
| Heading of int * inlines
| BlockQuote of block node list
| CodeBlock of string * string
| Div of string * block node list
| OrderedList of ordered_list_attributes * list_spacing
   * block node list node list
| BulletList of char * list_spacing * block node list node list
| TaskList of list_spacing * (task_status * block node list) node list
| DefinitionList of list_spacing
   * (inlines node * block node list node) node list
| ThematicBreak
| Table of inlines node * cell node list node list
| RawBlock of string * string
| FootnoteDef of string * block node list
| RefDef of string * string
| Ext_keyed of inlines * block node
| Ext_callout of string * callout_fold option * inlines * block node list

type blocks = block node list

val decorate_head : attr -> blocks -> blocks

val invisible_block : block -> bool

val def_split : blocks -> (inlines * blocks) option

val def_item : blocks -> inlines * blocks

val def_node : blocks -> (inlines node * blocks node) node

val def_items : blocks list -> (inlines node * blocks node) node list

val task_items :
  task_status list -> blocks list -> (task_status * blocks) node list

type parts =
| PItems of span list
| PDefItems of ((span * span) * span) list
| PTable of span option * (span * span list) list

val set_each : coq_PosPolicy -> span list -> 'a1 node list -> 'a1 node list

val set_defs :
  coq_PosPolicy -> ((span * span) * span) list -> (inlines node * blocks
  node) node list -> (inlines node * blocks node) node list

val set_rows :
  coq_PosPolicy -> (span * span list) list -> cell node list node list ->
  cell node list node list

val parts_onto : coq_PosPolicy -> parts -> block -> block

val set_parts : coq_PosPolicy -> parts -> block node -> block node

module Shift :
 sig
  val of_spot : int -> spot -> spot

  val of_span : int -> span -> span

  val of_pos : int -> pos -> pos

  val of_inline : int -> inline -> inline

  val of_inlines : int -> inlines -> inlines

  val of_cell : int -> cell -> cell

  val cnode : int -> cell node -> cell node

  val row : int -> cell node list node -> cell node list node

  val inlines_node : int -> inlines node -> inlines node

  val of_block : int -> block -> block

  val of_blocks : int -> blocks -> blocks
 end

val rev_chars : char list -> string

val words : (char -> bool) -> string -> string list

val is_label_ws : char -> bool

val normalize_label : string -> string

type note_map = (string * blocks) list

type reference_map = (string * (string * attr)) list

val lookup_reference : string -> reference_map -> (string * attr) option

type doc = { doc_blocks : blocks; doc_footnotes : note_map;
             doc_references : reference_map;
             doc_auto_references : reference_map;
             doc_auto_identifiers : string list }
