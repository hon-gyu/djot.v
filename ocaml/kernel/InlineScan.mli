open Ast
open Attributes
open Bool0
open Datatypes
open InlineTable
open InlineView
open List0
open Nat0
open PeanoNat
open Strings

type 'buf coq_TextOps = { tnil : 'buf; tpush : ('buf -> string -> 'buf);
                          tof : (string -> 'buf); tval : ('buf -> string);
                          tnonempty : ('buf -> bool) }

type chunks = string list

val chunks_push : chunks -> string -> chunks

val chunks_value : chunks -> string

val chunks_text : chunks coq_TextOps

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
| FKTag of string

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

val source_shape : string -> (int * int) * int

val spot_before : spot -> string -> spot

val spot_plus : int -> spot -> spot

val dtoken_span :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> span

val opush :
  dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> ostate ->
  ostate

val bpush : coq_PosPolicy -> coq_InlineCursor -> bool -> ostate -> ostate

val dpush : bool -> span -> ostate -> ostate

val tag_push :
  coq_PosPolicy -> coq_InlineCursor -> string -> spot -> ostate -> ostate

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

val oclose_reaches : dstyle -> bool -> frame list -> bool

val bclose_go :
  dtable -> coq_PosPolicy -> oitems -> frame list ->
  (((oitems * bool) * span) * frame list) option

val bclose :
  dtable -> coq_PosPolicy -> ostate -> (((inlines * bool) * span) * ostate)
  option

val tag_close_go :
  dtable -> coq_PosPolicy -> oitems -> frame list ->
  (((oitems * string) * span) * frame list) option

val tag_close :
  dtable -> coq_PosPolicy -> ostate -> (((inlines * string) * span) * ostate)
  option

val bunpush : ostate -> ((bool * span) * ostate) option

val opop_str : ostate -> string * ostate

val bflat :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> inlines -> 'a1 ->
  ostate -> 'a1 * ostate

val bsplit_nl :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> string -> 'a1 ->
  ostate -> 'a1 * ostate

val bclosed_lit :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> inlines -> bool ->
  ostate -> 'a1 * ostate

val bspan_lit :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> inlines -> bool ->
  string -> ostate -> 'a1 * ostate

val battr_lit :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> string -> 'a1 ->
  ostate -> 'a1 * ostate

val blit_prev : string -> char option

val bref_lit :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> inlines -> bool ->
  string -> ostate -> 'a1 * ostate

val drop_nl : string -> string

val oapp_rev : oitems -> oitems -> oitems

val oflatten_rev :
  dtable -> coq_PosPolicy -> oitems -> frame list -> oitems -> oitems

val oitems_of : dtable -> coq_PosPolicy -> ostate -> oitems

val ofinish : dtable -> coq_PosPolicy -> ostate -> inlines

type vkind =
| VVerb
| VMath of math_style
| VMaybeDollarMath of string

val vnode : vkind -> string -> inline

val vkind_verb : vkind -> bool

type 'buf iscan_g =
| IText of bool * 'buf * char option * ostate
| IEscWs of 'buf * 'buf * char option * ostate
| IBrace of 'buf * char option * ostate
| IDelim of dstyle * int * 'buf * char option * bool * ostate
| IOpen of int * vkind * ostate
| IVerb of int * int * 'buf * vkind * ostate
| IDollar of bool * 'buf * char option * ostate
| IDollarMath of bool * bool * 'buf * 'buf * char option * 'buf iscan_g
   * ostate
| IDollarMathClose of bool * 'buf * 'buf * char option * 'buf iscan_g * ostate
| IPeriod of bool * 'buf * char option * ostate
| IDash of int * 'buf * char option * ostate
| IBang of 'buf * char option * ostate
| IClosed of 'buf * ostate
| ISpan of inlines * bool * span * aparser * 'buf * ostate
| IAttr of aparser * 'buf * 'buf * char option * 'buf iscan_g * ostate
| IReference of inlines * bool * span * 'buf * ostate
| INote of bool * bool * 'buf * span * ostate
| IWiki of bool * bool * bool * 'buf * span * ostate
| IDest of inlines * bool * span * bool * int * 'buf * 'buf iscan_g * ostate
| IAuto of 'buf * 'buf * ostate
| ISymbol of 'buf * 'buf * 'buf iscan_g * ostate
| IRaw of 'buf * string * ostate
| IPercent of 'buf * char option * ostate
| IHole of int * bool * 'buf * 'buf * 'buf iscan_g * ostate

val note_pos : 'a1 coq_TextOps -> 'a1 -> char option -> bool

val ilead :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  'a1 -> char option -> ostate -> 'a1 iscan_g

val idest_open :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> inlines -> bool ->
  span -> ostate -> 'a1 iscan_g

val null : 'a1 list -> bool

val ellipsis : string

val endash : string

val emdash : string

val periods : bool -> string

val typography_ellipsis : dtable -> string

val srep : string -> int -> string

val dash_counts : int -> (int * int) * int

val dashes : int -> string

val typography_dashes : dtable -> int -> string

val dollars : bool -> string

val auto_lit : 'a1 coq_TextOps -> string -> 'a1 -> 'a1

val islice_end : dtable -> 'a1 coq_TextOps -> 'a1 iscan_g -> 'a1 iscan_g

val iattr_mark :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> 'a1 -> attr -> 'a1
  -> ostate -> 'a1 iscan_g

val iattr_feed :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  aparser -> 'a1 -> 'a1 -> char option -> 'a1 iscan_g -> ostate -> 'a1 iscan_g

val idelim_marked : dstyle -> int -> 'a1 -> ostate -> 'a1 iscan_g

val oopen_marked :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> dstyle ->
  bool -> 'a1 -> ostate -> ostate

val idelim_open_marked :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> dstyle ->
  bool -> 'a1 -> ostate -> 'a1 iscan_g

val idelim_run : dtable -> dstyle -> int -> bool -> string

val ibrace_step_at :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> bool ->
  char -> 'a1 -> char option -> ostate -> 'a1 iscan_g

val ospan_bang : coq_PosPolicy -> coq_InlineCursor -> bool -> ostate -> ostate

val ispan_feed :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  inlines -> bool -> span -> aparser -> 'a1 -> ostate -> 'a1 iscan_g

val inote_step :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char -> bool -> bool
  -> 'a1 -> span -> ostate -> 'a1 iscan_g

val iauto_step :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  'a1 -> 'a1 -> ostate -> 'a1 iscan_g

val isymbol_step :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  'a1 -> 'a1 -> ostate -> 'a1 iscan_g -> 'a1 iscan_g

val iraw_lit : string -> string

val iraw_step_at :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> bool ->
  char -> 'a1 -> string -> ostate -> 'a1 iscan_g

val bnote_lit :
  coq_PosPolicy -> coq_InlineCursor -> bool -> bool -> string -> ostate ->
  string * ostate

val wiki_split : string -> string * string option

val wiki_lit : bool -> bool -> bool -> string -> string

val bwiki_lit : bool -> bool -> bool -> string -> ostate -> string * ostate

val iwiki_close :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> bool -> 'a1 -> span
  -> ostate -> 'a1 iscan_g

val iwiki_step :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char -> bool -> bool
  -> bool -> 'a1 -> span -> ostate -> 'a1 iscan_g

val ibang_step :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  'a1 -> char option -> ostate -> 'a1 iscan_g

val idelim_lit : dtable -> 'a1 coq_TextOps -> dstyle -> 'a1 -> bool -> 'a1

val idelim_lit_prev : dtable -> dstyle -> bool -> char option

val idelim_done :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> dstyle ->
  'a1 -> char option -> bool -> char option -> ostate -> 'a1 iscan_g

val idelim_resolve :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> dstyle ->
  'a1 -> char option -> bool -> char option -> ostate -> 'a1 iscan_g

val idollar_step :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  bool -> 'a1 -> char option -> ostate -> 'a1 iscan_g

val iperiod_step :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  bool -> 'a1 -> char option -> ostate -> 'a1 iscan_g

val idash_step :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  int -> 'a1 -> char option -> ostate -> 'a1 iscan_g

val ipercent_step :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  'a1 -> char option -> ostate -> 'a1 iscan_g

val ihole_close :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> string -> 'a1 ->
  ostate -> 'a1 iscan_g

val ihole_step :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char -> int -> bool
  -> 'a1 -> 'a1 -> 'a1 iscan_g -> ostate -> 'a1 iscan_g

val iresolve :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> 'a1
  iscan_g -> 'a1 iscan_g

val iescws_resolve :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> 'a1 -> 'a1 -> char
  option -> ostate -> ('a1 * char option) * ostate

val iesc_hard :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> 'a1 -> 'a1 -> ostate
  -> ostate

val istep_at :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> bool ->
  char -> 'a1 iscan_g -> 'a1 iscan_g

val istep :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  'a1 iscan_g -> 'a1 iscan_g

val ifinish_ostate_flat :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> 'a1 iscan_g ->
  ostate

val ifinish_ostate :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> 'a1
  iscan_g -> ostate

val ifinish_rev :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> 'a1
  iscan_g -> inlines

val ifinish :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> 'a1
  iscan_g -> inlines

val ibreak_flat :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> 'a1
  iscan_g -> 'a1 iscan_g

val ibreak_at :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> bool ->
  'a1 iscan_g -> 'a1 iscan_g

val ibreak :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> 'a1
  iscan_g -> 'a1 iscan_g

val iclosed_at : 'a1 iscan_g -> bool

val iresolve_next :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  'a1 iscan_g -> 'a1 iscan_g

val iscan_settled :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> char ->
  'a1 iscan_g -> bool

val map_text : 'a1 coq_TextOps -> 'a1 iscan_g -> string iscan_g

val lift : 'a1 coq_TextOps -> string iscan_g -> 'a1 iscan_g

val ddecode_from : bool -> string -> string

val ddecode : string -> string

type 'buf ckind =
| CDest of inlines * bool * span * ostate
| CHole of 'buf * ostate

type 'buf cframe = { cf_kind : 'buf ckind; cf_level : int; cf_under :
                     'buf; cf_dtop : int option; cf_htop : int option }

type 'buf sscan = { s_frames : 'buf cframe list; s_dtop : int option;
                    s_htop : int option; s_parens : int; s_braces : int;
                    s_esc : bool; s_seg : 'buf; s_cur : 'buf iscan_g }

val slift : 'a1 coq_TextOps -> 'a1 iscan_g -> 'a1 sscan

val sat_level : int option -> int -> bool

val sabove : int option -> int -> bool

val scount : bool -> char -> char -> char -> int -> int

val spop :
  'a1 coq_TextOps -> bool -> 'a1 cframe list -> string list -> (('a1
  cframe * 'a1 cframe list) * string) option

val speel :
  'a1 coq_TextOps -> 'a1 cframe list -> int option -> int option -> int -> int
  -> bool -> 'a1 -> 'a1 iscan_g -> 'a1 sscan

val sframe_close :
  'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> 'a1 ckind -> string
  -> 'a1 iscan_g

val sstep_at :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> bool ->
  char -> 'a1 sscan -> 'a1 sscan

val sbreak_at :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> bool ->
  'a1 sscan -> 'a1 sscan

val sfinish :
  dtable -> 'a1 coq_TextOps -> coq_PosPolicy -> coq_InlineCursor -> 'a1 sscan
  -> inlines

val iscan_str : dtable -> string -> string iscan_g -> string iscan_g

val iscan_lines : dtable -> string list -> string iscan_g -> string iscan_g

val iscan_str_off : dtable -> string -> string iscan_g -> string iscan_g

val iscan_lines_off :
  dtable -> int -> string list -> string iscan_g -> string iscan_g

val istart : string iscan_g

val sscan_str : dtable -> 'a1 coq_TextOps -> string -> 'a1 sscan -> 'a1 sscan

val sscan_str_off :
  dtable -> 'a1 coq_TextOps -> string -> 'a1 sscan -> 'a1 sscan

val sscan_lines :
  dtable -> 'a1 coq_TextOps -> string list -> 'a1 sscan -> 'a1 sscan

val sscan_lines_off :
  dtable -> 'a1 coq_TextOps -> int -> string list -> 'a1 sscan -> 'a1 sscan

val sstart : 'a1 coq_TextOps -> 'a1 sscan

val parse_inline_line_stk : dtable -> string -> inlines

val para_inlines_off_stk : dtable -> int -> string list -> inlines

val parse_inline_line : dtable -> string -> inlines

val para_inlines : dtable -> string list -> inlines

val para_inlines_off : dtable -> int -> string list -> inlines

val key_before : char option -> bool

val key_after : string -> bool

val key_scan :
  dtable -> string -> string -> char option -> string iscan_g ->
  (string * string) option

val key_point : dtable -> string -> (string * string) option

val key_label_ok : dtable -> string -> bool

val key_split : dtable -> string -> (string * string) option
