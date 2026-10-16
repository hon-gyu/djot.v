open Ast
open Bool0

val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val pair_eqb :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ('a1 * 'a2) -> ('a1 * 'a2)
  -> bool

val option_eqb : ('a1 -> 'a1 -> bool) -> 'a1 option -> 'a1 option -> bool

val spot_eqb : spot -> spot -> bool

val span_eqb : span -> span -> bool

val role_eqb : syntax_role -> syntax_role -> bool

val pos_eqb : pos -> pos -> bool

val attr_eqb : attr -> attr -> bool

val node_eqb : ('a1 -> 'a1 -> bool) -> 'a1 node -> 'a1 node -> bool

val math_style_eqb : math_style -> math_style -> bool

val quote_type_eqb : quote_type -> quote_type -> bool

val target_eqb : target -> target -> bool

val inline_eqb : inline -> inline -> bool

val inlines_eqb : inlines -> inlines -> bool

val spacing_eqb : list_spacing -> list_spacing -> bool

val ol_style_eqb : ordered_list_style -> ordered_list_style -> bool

val ol_delim_eqb : ordered_list_delim -> ordered_list_delim -> bool

val ol_attrs_eqb : ordered_list_attributes -> ordered_list_attributes -> bool

val task_eqb : task_status -> task_status -> bool

val cell_type_eqb : cell_type -> cell_type -> bool

val cell_eqb : cell -> cell -> bool

val fold_eqb : callout_fold -> callout_fold -> bool

val block_eqb : block -> block -> bool

val blocks_eqb : blocks -> blocks -> bool
