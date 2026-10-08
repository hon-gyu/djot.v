open InlineTable
open Profile
open ProfileChecks

type status =
| Proved
| Conditional of string
| Broken of string * string
| Conjectured
| Unknown
| Inapplicable of string

val status_name : status -> string

val claimed : status -> bool

type property = { p_id : string; p_group : string; p_statement : string;
                  p_implication : string; p_theorems : string list;
                  p_status : (options -> status) }

val always : status -> options -> status

val no_backtracking : string

val uniformity : string

val local : string

val wrapping : string

val structure : string

val precedence : string

val p_block_no_backtracking : property

val p_inline_no_backtracking : property

val p_incremental_reparse : property

val p_block_replace : property

val p_positions : property

val p_linear_time : property

val p_quote_uniformity : property

val keyed_items_condition : string

val p_list_uniformity : property

val p_definition_list_uniformity : property

val p_div_uniformity : property

val p_footnote_uniformity : property

val p_lazy_lines : property

val p_list_tightness : property

val p_indent_uniformity : property

val p_reference_locality : property

val p_reference_shape : property

val p_hard_wrap_paragraph : property

val p_hard_wrap_heading : property

val p_block_structure_first : property

val p_inline_precedence : property

val all : property list
