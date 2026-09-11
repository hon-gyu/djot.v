open Datatypes
open List0
open ListDef

val alist_lookup : string -> (string * 'a1) list -> 'a1 option

val alist_set : string -> 'a1 -> (string * 'a1) list -> (string * 'a1) list

type attr = (string * string) list

val lookup_attr : string -> attr -> string option

val integrate : (string * string) -> attr -> attr

val attr_union : attr -> attr -> attr

val attr_set : string -> string -> attr -> attr

val attr_add_class : string -> attr -> attr

val attr_put : (string * string) -> attr -> attr

val attr_merge : attr -> attr -> attr

val attr_apply : attr -> attr -> attr

type pos =
| NoPos
| SomePos of nat * nat * nat * nat

type 'a node =
| Node of pos * attr * 'a

val mk : 'a1 -> 'a1 node

val node_contents : 'a1 node -> 'a1

val node_attrs : 'a1 node -> attr

val add_attr : attr -> 'a1 node -> 'a1 node

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
| Span of inline node list
| FootnoteReference of string
| UrlLink of string
| EmailLink of string
| RawInline of string * string
| NonBreakingSpace
| Quoted of quote_type * inline node list
| SoftBreak
| HardBreak

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
                                 nat }

type task_status =
| Complete
| Incomplete

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
| Heading of nat * inlines
| BlockQuote of block node list
| CodeBlock of string * string
| Div of block node list
| OrderedList of ordered_list_attributes * list_spacing * block node list list
| BulletList of list_spacing * block node list list
| TaskList of list_spacing * (task_status * block node list) list
| DefinitionList of list_spacing * (inlines * block node list) list
| ThematicBreak
| Table of inlines option * cell list list
| RawBlock of string * string
| FootnoteDef of string * block node list
| RefDef of string * string
| Keyed of inlines * block node

type blocks = block node list

val decorate_head : attr -> blocks -> blocks

val invisible_block : block -> bool

val def_split : blocks -> (inlines * blocks) option

val def_item : blocks -> inlines * blocks

val def_items : blocks list -> (inlines * blocks) list

val task_items :
  task_status list -> blocks list -> (task_status * blocks) list

val words_aux :
  (char -> bool) -> string -> string -> string list -> string list

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
