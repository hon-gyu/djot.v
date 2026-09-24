open Ast
open Attributes
open Datatypes
open InlineLocated
open InlineScan
open InlineTable
open Line
open List0
open ListDef
open Marker
open Nat0
open PeanoNat
open String0
open Strings

type bconfig = { bmarker_interrupts : (lstyle list -> string -> task_marker
                                      option -> string -> bool);
                 bunderline : (char -> nat -> nat option); btables : 
                 bool; bheading_continues : bool; bdivs : bool;
                 btasks : bool; braw_blocks : bool; bdeflists : bool;
                 battrs : bool; bfootnotes : bool; bkeyed : bool }

type coq_LineIx = nat
  (* singleton inductive, whose constructor was LineIxAt *)

val semantic_line_ix : coq_LineIx

val no_interrupt :
  lstyle list -> string -> task_marker option -> string -> bool

val no_underline : char -> nat -> nat option

val djot_bconfig : bconfig

val with_keyed : bool -> bconfig -> bconfig

val keyed_bconfig : bconfig

val configured_list_styles :
  bconfig -> lstyle list -> task_marker option -> lstyle list

val configured_list_check : bconfig -> task_marker option -> task_status

val configured_list_rest : bconfig -> task_marker option -> string -> string

val binterrupt : bconfig -> line_kind -> bool

val bunderline_of : bconfig -> string -> nat option

val bcuts : bconfig -> string -> bool

type stored_line = nat * string

val remember_line : coq_LineIx -> string -> stored_line

val line_texts : stored_line list -> string list

type extent = { extent_start : spot; extent_stop : spot }

val spot_at : coq_LineIx -> string -> nat -> spot

val line_stop : coq_LineIx -> spot

val line_span_from : coq_LineIx -> string -> nat -> span

val open_extent : coq_LineIx -> string -> nat -> extent

val touch_extent : coq_LineIx -> extent -> extent

val extent_span : extent -> span

val stored_start : stored_line -> spot

val stored_stop : stored_line -> spot

val stored_span : stored_line list -> span

val span_through_line : coq_LineIx -> span -> span

val fence_block : bconfig -> fence -> string list -> block node

val cells_of : dtable -> cell_type -> align list -> string list -> cell list

val head_of : align list -> cell list -> cell list

val table_fold :
  dtable -> trow list -> align list -> cell list list -> cell list list

type cell_part = { cell_range : span; cell_text_start : spot }

type row_part = span * cell_part list

type tcap =
| TOpen of row_part list
| TAfterBlank of row_part list
| TCaption of row_part list * spot * stored_line list

val caption_of : dtable -> coq_PosPolicy -> tcap -> inlines option

val cap_row_parts : tcap -> row_part list

val table_parts : dtable -> coq_PosPolicy -> tcap -> parts

val cells_of_located :
  dtable -> coq_PosPolicy -> cell_type -> align list -> string list ->
  cell_part list -> cell list

val table_fold_located :
  dtable -> coq_PosPolicy -> trow list -> row_part list -> align list -> cell
  list list -> cell list list

val table_block : dtable -> coq_PosPolicy -> trow list -> tcap -> block node

val table_row_part : coq_LineIx -> string -> trow -> row_part option

type list_state = { ls_indent : nat; ls_extent : extent;
                    ls_item_extent : extent; ls_item_extents : extent list;
                    ls_styles : (lstyle * nat) list; ls_loose : bool;
                    ls_blanks : bool; ls_items : blocks list;
                    ls_check : task_status; ls_checks : task_status list }

val list_touch : coq_LineIx -> list_state -> list_state

type pstate =
| PPara of stored_line list
| PHeading of nat * extent * stored_line list
| PFence of fence * nat * extent * span * stored_line list
| PQuote of extent * blocks * pstate
| PDiv of nat * string * extent * span * blocks * pstate
| PList of list_state * blocks * pstate
| PAttr of attr * span list * extent * nat * aparser * stored_line list
| PParaOff of nat * stored_line list
| PRef of extent * nat * string * string
| PFoot of extent * nat * string * blocks * pstate
| PTable of extent * trow list * tcap
| PPend of attr * span list * pstate
| PKey of extent * string * string * pstate

val pstate_depth : pstate -> nat

val is_idle : pstate -> bool

val heading_block :
  dtable -> coq_PosPolicy -> nat -> stored_line list -> block node

val heading_block_off :
  dtable -> coq_PosPolicy -> nat -> nat -> stored_line list -> block node

val para_recover : nat -> stored_line list -> pstate

val finish_para_recover :
  dtable -> coq_PosPolicy -> stored_line list -> blocks

val div_block : string -> blocks -> block node

val styles_list :
  bconfig -> (lstyle * nat) list -> list_spacing -> blocks list -> block node

val styles_list_checked :
  bconfig -> (lstyle * nat) list -> list_spacing -> task_status list ->
  blocks list -> block node

val def_term_span : blocks -> span option

val blocks_span : blocks -> spot -> span

val def_item_spans : span list -> blocks list -> ((span * span) * span) list

val list_parts : bconfig -> list_state -> blocks -> parts

val list_block : bconfig -> list_state -> blocks -> block node

val ref_block : string -> string -> block node

val foot_block : string -> blocks -> block node

val key_close : dtable -> string -> string -> blocks -> blocks

val ref_cont : string -> string option

val finish : dtable -> bconfig -> coq_PosPolicy -> pstate -> blocks

val lazy_ok : pstate -> bool

val in_fence : pstate -> bool

val is_lazy : line_kind -> pstate -> bool

val feed_lazy : coq_LineIx -> string -> pstate -> pstate

val push_text : coq_LineIx -> string -> stored_line list -> stored_line list

val open_text : dtable -> coq_LineIx -> bconfig -> string -> blocks * pstate

val keyless : dtable -> bconfig -> string -> bool

val open_kind :
  dtable -> coq_LineIx -> coq_PosPolicy -> bconfig -> string -> line_kind ->
  blocks * pstate

val close_reopen :
  dtable -> bconfig -> coq_PosPolicy -> pstate -> (blocks * pstate) ->
  blocks * pstate

val pend_result :
  coq_PosPolicy -> attr -> span list -> (blocks * pstate) -> blocks * pstate

val key_result :
  dtable -> coq_PosPolicy -> extent -> string -> string -> (blocks * pstate)
  -> blocks * pstate

val open_quote : coq_LineIx -> string -> (blocks * pstate) -> blocks * pstate

val open_attr :
  bconfig -> coq_LineIx -> attr -> span list -> nat -> aparser -> string ->
  blocks * pstate

val open_fence : coq_LineIx -> string -> nat -> fence -> blocks * pstate

val open_ref :
  coq_LineIx -> string -> nat -> string -> string -> blocks * pstate

val open_foot :
  bconfig -> coq_LineIx -> string -> nat -> string -> (blocks * pstate) ->
  blocks * pstate

val list_opened :
  coq_LineIx -> string -> nat -> (lstyle * nat) list -> task_status ->
  list_state

val open_list :
  coq_LineIx -> string -> nat -> (lstyle * nat) list -> task_status ->
  (blocks * pstate) -> blocks * pstate

val list_blank : list_state -> list_state

val list_narrow : list_state -> (lstyle * nat) list -> list_state

val announces_end : pstate -> bool

val claimable : line_kind -> bool

val key_claims : string -> pstate -> bool

val list_takes : list_state -> nat -> string -> pstate -> bool

val blank_absorbed : pstate -> bool

val div_closer : string -> pstate -> bool

val list_content : coq_LineIx -> list_state -> line_kind -> list_state

val list_next :
  coq_LineIx -> list_state -> blocks -> task_status -> string -> string ->
  list_state

val consumed : string -> string -> nat

val open_line :
  dtable -> bconfig -> coq_LineIx -> coq_PosPolicy -> (string ->
  blocks * pstate) -> nat -> string -> line_kind -> blocks * pstate

val step_fuel :
  dtable -> bconfig -> coq_LineIx -> coq_PosPolicy -> nat -> nat -> string ->
  pstate -> blocks * pstate

val step :
  dtable -> bconfig -> coq_LineIx -> coq_PosPolicy -> string -> pstate ->
  blocks * pstate

val parse_lines :
  dtable -> bconfig -> coq_LineIx -> coq_PosPolicy -> string list -> pstate
  -> blocks

val parse_blocks :
  dtable -> bconfig -> coq_LineIx -> coq_PosPolicy -> string -> blocks

val pad_safe : pstate -> bool

val blank_safe : pstate -> bool

val run_lines_tagged :
  dtable -> bconfig -> coq_PosPolicy -> (nat * string) list -> pstate ->
  blocks * pstate

val finish_lines_tagged :
  dtable -> bconfig -> coq_PosPolicy -> (nat * string) list -> pstate ->
  blocks

val parse_blocks_located : dtable -> bconfig -> string -> blocks
