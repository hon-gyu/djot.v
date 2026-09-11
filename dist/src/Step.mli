open Ast
open Attributes
open Datatypes
open Inline
open Line
open List0
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

val fence_block : bconfig -> fence -> string list -> block node

val cells_of : dtable -> cell_type -> align list -> string list -> cell list

val head_of : align list -> cell list -> cell list

val table_fold :
  dtable -> trow list -> align list -> cell list list -> cell list list

type tcap =
| TOpen
| TAfterBlank
| TCaption of string list

val caption_of : dtable -> tcap -> inlines option

val table_block : dtable -> trow list -> tcap -> block node

type list_state = { ls_indent : nat; ls_styles : (lstyle * nat) list;
                    ls_loose : bool; ls_blanks : bool;
                    ls_items : blocks list; ls_check : task_status;
                    ls_checks : task_status list }

type pstate =
| PPara of string list
| PHeading of nat * string list
| PFence of fence * nat * string list
| PQuote of blocks * pstate
| PDiv of nat * string * blocks * pstate
| PList of list_state * blocks * pstate
| PAttr of attr * nat * aparser * string list
| PParaOff of nat * string list
| PRef of nat * string * string
| PFoot of nat * string * blocks * pstate
| PTable of trow list * tcap
| PPend of attr * pstate
| PKey of string * string * pstate

val pstate_depth : pstate -> nat

val is_idle : pstate -> bool

val heading_block : dtable -> nat -> string list -> block node

val heading_block_off : dtable -> nat -> nat -> string list -> block node

val para_recover : nat -> string list -> pstate

val finish_para_recover : dtable -> string list -> blocks

val div_block : string -> blocks -> block node

val styles_list :
  bconfig -> (lstyle * nat) list -> list_spacing -> blocks list -> block node

val styles_list_checked :
  bconfig -> (lstyle * nat) list -> list_spacing -> task_status list ->
  blocks list -> block node

val list_block : bconfig -> list_state -> blocks -> block node

val ref_block : string -> string -> block node

val foot_block : string -> blocks -> block node

val key_close : dtable -> string -> string -> blocks -> blocks

val ref_cont : string -> string option

val finish : dtable -> bconfig -> pstate -> blocks

val lazy_ok : pstate -> bool

val in_fence : pstate -> bool

val is_lazy : line_kind -> pstate -> bool

val feed_lazy : string -> pstate -> pstate

val push_text : string -> string list -> string list

val open_text : dtable -> bconfig -> string -> blocks * pstate

val keyless : dtable -> bconfig -> string -> bool

val open_kind : dtable -> bconfig -> string -> line_kind -> blocks * pstate

val close_reopen :
  dtable -> bconfig -> pstate -> (blocks * pstate) -> blocks * pstate

val pend_result : attr -> (blocks * pstate) -> blocks * pstate

val key_result :
  dtable -> string -> string -> (blocks * pstate) -> blocks * pstate

val open_quote : (blocks * pstate) -> blocks * pstate

val open_attr : bconfig -> attr -> nat -> aparser -> string -> blocks * pstate

val open_fence : nat -> fence -> blocks * pstate

val open_ref : nat -> string -> string -> blocks * pstate

val open_foot :
  bconfig -> string -> nat -> string -> (blocks * pstate) -> blocks * pstate

val open_list :
  nat -> (lstyle * nat) list -> task_status -> (blocks * pstate) ->
  blocks * pstate

val list_blank : list_state -> list_state

val list_narrow : list_state -> (lstyle * nat) list -> list_state

val announces_end : pstate -> bool

val claimable : line_kind -> bool

val key_claims : string -> pstate -> bool

val list_takes : list_state -> nat -> string -> pstate -> bool

val blank_absorbed : pstate -> bool

val div_closer : string -> pstate -> bool

val list_content : list_state -> line_kind -> list_state

val list_next : list_state -> blocks -> task_status -> string -> list_state

val consumed : string -> string -> nat

val open_line :
  dtable -> bconfig -> (string -> blocks * pstate) -> nat -> string ->
  line_kind -> blocks * pstate

val step_fuel :
  dtable -> bconfig -> nat -> nat -> string -> pstate -> blocks * pstate

val step : dtable -> bconfig -> string -> pstate -> blocks * pstate

val parse_lines : dtable -> bconfig -> string list -> pstate -> blocks

val parse_blocks : dtable -> bconfig -> string -> blocks

val pad_safe : pstate -> bool

val blank_safe : pstate -> bool
