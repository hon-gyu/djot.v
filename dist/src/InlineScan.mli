open Ast
open Attributes
open Bool0
open Datatypes
open InlineTable
open InlineView
open List0
open Nat0
open PeanoNat
open String0
open Strings

val strip_pad : string -> string

val trim_verb : string -> string

type oitem =
| OIn of inline node
| OMark of attr * span * spot option

type oitems = oitem list

type frame_kind =
| FKDelim of dstyle * bool
| FKBracket of bool
| FKDest of bool

type frame = { fr_kind : frame_kind; fr_marked : bool; fr_open : span;
               fr_out : oitems }

val fr_src : dtable -> frame -> string

val fr_barrier : frame -> bool

type ostate = { os_out : oitems; os_stk : frame list;
                os_word_start : spot option }

val ostart : ostate

val spot_later : spot -> spot -> spot

val roles_stop : provenance -> spot

val node_stop : spot -> inline node -> spot

val items_stop : spot -> oitems -> spot

val text_start : coq_InlineCursor -> ostate -> spot

val remember_word_start :
  coq_PosPolicy -> coq_InlineCursor -> char -> ostate -> ostate

val oword_reset : ostate -> ostate

val inline_prov : spot -> spot -> provenance

val imk : coq_PosPolicy -> spot -> spot -> inline -> inline node

val imk_here : coq_PosPolicy -> coq_InlineCursor -> inline -> inline node

val fr_lit : dtable -> coq_PosPolicy -> frame -> inline node

val add_inline_role :
  coq_PosPolicy -> syntax_role -> span -> inline node -> inline node

val dmatch : dstyle -> bool -> frame -> bool

val merge_text_pos : pos -> pos -> pos

val isnoc : inline node -> inlines -> inlines

val istarts_str : inlines -> bool

val osnoc : oitem -> oitems -> oitems

val oapp : oitems -> oitems -> oitems

val oemit : inline node -> ostate -> ostate

val omark : attr -> span -> ostate -> ostate

val flush_text_at :
  coq_PosPolicy -> coq_InlineCursor -> string -> ostate -> ostate

val flush_text_to_at :
  coq_PosPolicy -> coq_InlineCursor -> spot -> string -> ostate -> ostate

val opush_at : dstyle -> bool -> bool -> span -> ostate -> ostate

val previous_spot : spot -> spot

val source_shape : string -> (nat * nat) * nat

val spot_before : spot -> string -> spot

val spot_plus : nat -> spot -> spot

val dtoken_span :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> span

val opush :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> ostate ->
  ostate

val bpush : coq_PosPolicy -> coq_InlineCursor -> bool -> ostate -> ostate

val dpush : bool -> span -> ostate -> ostate

val last_ws_split : string -> string * string

val split_text_pos : pos -> spot option -> pos * pos

val oattach_list :
  coq_PosPolicy -> attr -> span -> spot option -> inlines -> inlines

val oresolve_go : coq_PosPolicy -> oitems -> inlines * bool

val oresolve : coq_PosPolicy -> oitems -> inlines

val oclose_go :
  dtable -> coq_PosPolicy -> dstyle -> bool -> oitems -> frame list ->
  ((oitems * span) * frame list) option

val oclose_barred_go : dstyle -> bool -> bool -> frame list -> bool

val oclose_barred : dstyle -> bool -> ostate -> bool

val oclose :
  dtable -> coq_PosPolicy -> dstyle -> bool -> spot -> ostate -> ostate option

val bclose_go :
  dtable -> coq_PosPolicy -> oitems -> frame list ->
  (((oitems * bool) * span) * frame list) option

val bclose :
  dtable -> coq_PosPolicy -> ostate -> (((inlines * bool) * span) * ostate)
  option

val bunpush : ostate -> ((bool * span) * ostate) option

val opop_str : ostate -> string * ostate

val bflat :
  coq_PosPolicy -> coq_InlineCursor -> inlines -> string -> ostate ->
  string * ostate

val bsplit_nl :
  coq_PosPolicy -> coq_InlineCursor -> string -> string -> ostate ->
  string * ostate

val bclosed_lit :
  coq_PosPolicy -> coq_InlineCursor -> inlines -> bool -> ostate ->
  string * ostate

val bspan_lit :
  coq_PosPolicy -> coq_InlineCursor -> inlines -> bool -> string -> ostate ->
  string * ostate

val battr_lit :
  coq_PosPolicy -> coq_InlineCursor -> string -> string -> ostate ->
  string * ostate

val blit_prev : string -> char option

val bref_lit :
  coq_PosPolicy -> coq_InlineCursor -> inlines -> bool -> string -> ostate ->
  string * ostate

val drop_nl : string -> string

val oflatten :
  dtable -> coq_PosPolicy -> oitems -> frame list -> oitems -> oitems

val oitems_of : dtable -> coq_PosPolicy -> ostate -> oitems

val ofinish : dtable -> coq_PosPolicy -> ostate -> inlines

type vkind =
| VVerb
| VMath of math_style

val vnode : vkind -> string -> inline

val vkind_verb : vkind -> bool

type iscan =
| IText of bool * string * char option * ostate
| IEscWs of string * string * char option * ostate
| IBrace of string * char option * ostate
| IDelim of dstyle * nat * string * char option * bool * ostate
| IOpen of nat * vkind * ostate
| IVerb of nat * nat * string * vkind * ostate
| IDollar of bool * string * char option * ostate
| IPeriod of bool * string * char option * ostate
| IDash of nat * string * char option * ostate
| IBang of string * char option * ostate
| IClosed of string * ostate
| ISpan of inlines * bool * span * aparser * string * ostate
| IAttr of aparser * string * string * char option * iscan * ostate
| IReference of inlines * bool * span * string * ostate
| INote of bool * bool * string * span * ostate
| IWiki of bool * bool * bool * string * span * ostate
| IDest of inlines * bool * span * bool * nat * string * iscan * ostate
| IAuto of string * string * ostate
| ISymbol of string * string * iscan * ostate
| IRaw of string * string * ostate

val note_pos : string -> char option -> bool

val ilead :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> string -> char
  option -> ostate -> iscan

val idest_open :
  coq_PosPolicy -> coq_InlineCursor -> inlines -> bool -> span -> ostate ->
  iscan

val null : 'a1 list -> bool

val ellipsis : string

val endash : string

val emdash : string

val periods : bool -> string

val typography_ellipsis : dtable -> string

val srep : string -> nat -> string

val dash_counts : nat -> (nat * nat) * nat

val dashes : nat -> string

val typography_dashes : dtable -> nat -> string

val dollars : bool -> string

val auto_lit : string -> string -> string

val islice_end : dtable -> iscan -> iscan

val iattr_mark :
  coq_PosPolicy -> coq_InlineCursor -> string -> attr -> string -> ostate ->
  iscan

val iattr_feed :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> aparser -> string ->
  string -> char option -> iscan -> ostate -> iscan

val idelim_marked : dstyle -> nat -> string -> ostate -> iscan

val oopen_marked :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> string ->
  ostate -> ostate

val idelim_open_marked :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> string ->
  ostate -> iscan

val idelim_run : dtable -> dstyle -> nat -> bool -> string

val ibrace_step_at :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> bool -> char -> string ->
  char option -> ostate -> iscan

val ospan_bang : coq_PosPolicy -> coq_InlineCursor -> bool -> ostate -> ostate

val ispan_feed :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> inlines -> bool ->
  span -> aparser -> string -> ostate -> iscan

val inote_step :
  coq_PosPolicy -> coq_InlineCursor -> char -> bool -> bool -> string -> span
  -> ostate -> iscan

val iauto_step :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> string -> string ->
  ostate -> iscan

val isymbol_step :
  coq_PosPolicy -> coq_InlineCursor -> char -> string -> string -> ostate ->
  iscan -> iscan

val iraw_lit : string -> string

val iraw_step_at :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> bool -> char -> string ->
  string -> ostate -> iscan

val bnote_lit :
  coq_PosPolicy -> coq_InlineCursor -> bool -> bool -> string -> ostate ->
  string * ostate

val wiki_split : string -> string * string option

val wiki_lit : bool -> bool -> bool -> string -> string

val bwiki_lit : bool -> bool -> bool -> string -> ostate -> string * ostate

val iwiki_close :
  coq_PosPolicy -> coq_InlineCursor -> bool -> string -> span -> ostate ->
  iscan

val iwiki_step :
  coq_PosPolicy -> coq_InlineCursor -> char -> bool -> bool -> bool -> string
  -> span -> ostate -> iscan

val ibang_step :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> string -> char
  option -> ostate -> iscan

val idelim_lit : dtable -> dstyle -> string -> bool -> string

val idelim_lit_prev : dtable -> dstyle -> bool -> char option

val idelim_done :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> string -> char
  option -> bool -> char option -> ostate -> iscan

val idelim_resolve :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> string -> char
  option -> bool -> char option -> ostate -> iscan

val idollar_step :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> bool -> string ->
  char option -> ostate -> iscan

val iperiod_step :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> bool -> string ->
  char option -> ostate -> iscan

val idash_step :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> nat -> string ->
  char option -> ostate -> iscan

val iresolve : dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> iscan

val iescws_resolve :
  coq_PosPolicy -> coq_InlineCursor -> string -> string -> char option ->
  ostate -> (string * char option) * ostate

val iesc_hard :
  coq_PosPolicy -> coq_InlineCursor -> string -> string -> ostate -> ostate

val istep_at :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> bool -> char -> iscan ->
  iscan

val istep :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> iscan -> iscan

val ifinish_ostate_flat : coq_PosPolicy -> coq_InlineCursor -> iscan -> ostate

val ifinish_ostate :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> ostate

val ifinish_rev :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> inlines

val ifinish : dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> inlines

val ibreak_flat :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> iscan

val ibreak_at :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> bool -> iscan -> iscan

val ibreak : dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> iscan

val iclosed_at : iscan -> bool

val iresolve_next :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> iscan -> iscan

val iscan_settled :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> iscan -> bool

val iscan_str : dtable -> string -> iscan -> iscan

val iscan_lines : dtable -> string list -> iscan -> iscan

val iscan_str_off : dtable -> string -> iscan -> iscan

val iscan_lines_off : dtable -> nat -> string list -> iscan -> iscan

val istart : iscan

val parse_inline_line : dtable -> string -> inlines

val para_inlines : dtable -> string list -> inlines

val para_inlines_off : dtable -> nat -> string list -> inlines

val key_before : char option -> bool

val key_after : string -> bool

val key_scan :
  dtable -> string -> string -> char option -> iscan -> (string * string)
  option

val key_point : dtable -> string -> (string * string) option

val key_label_ok : dtable -> string -> bool

val key_split : dtable -> string -> (string * string) option
