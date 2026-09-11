open Ascii
open Ast
open Attributes
open Bool0
open Datatypes
open List0
open ListDef
open Nat0
open PeanoNat
open String0
open Strings

val is_punct : char -> bool

val tick : char

val is_tick : char -> bool

val bslash : char

val is_bslash : char -> bool

val lbrace : char

val rbrace : char

val one : char -> string

val dollar : char

val sqchar : char

val dqchar : char

val hyphen : char

val bang : char

val period : char

val lbrack : char

val rbrack : char

val hat : char

val lparen : char

val rparen : char

val lt : char

val gt : char

val nl_char : char

val dreserved : char -> bool

type dstyle =
| DEmph
| DStrong
| DSuper
| DSub
| DMark
| DInsert
| DDelete
| DSQuote
| DDQuote

type dsyntax =
| DOff
| DBraced
| DBare
| DBareAfterBreak

type ddecay =
| DDSelf
| DDPair of bool * string * string

type dconfig = { dc_char : (dstyle -> char); dc_width : (dstyle -> nat);
                 dc_syntax : (dstyle -> dsyntax);
                 dc_decay : (dstyle -> ddecay); dc_smart_typography : 
                 bool; dc_raw_inline : bool; dc_math : bool; dc_attrs : 
                 bool; dc_footnotes : bool }

val djot_dchar : dstyle -> char

val djot_dsyntax : dstyle -> dsyntax

val lsquo : string

val rsquo : string

val ldquo : string

val rdquo : string

val djot_ddecay : dstyle -> ddecay

val djot_dwidth : dstyle -> nat

val djot_config : dconfig

val chars : char -> nat -> string

val dstyles : dstyle list

val denabled : dconfig -> dstyle -> bool

val dstyle_at : dconfig -> char -> dstyle option

val bnode : bool -> inlines -> target -> inline

val reference_text : inline -> string

val reference_inlines_text : inlines -> string

val dnode : dstyle -> inlines -> inline

type dtable = dconfig
  (* singleton inductive, whose constructor was DTable *)

val dchar : dtable -> dstyle -> char

val dsyntax_of : dtable -> dstyle -> dsyntax

val dwidth : dtable -> dstyle -> nat

val smart_typography : dtable -> bool

val raw_inline_enabled : dtable -> bool

val math_enabled : dtable -> bool

val inline_attrs_enabled : dtable -> bool

val notes_enabled : dtable -> bool

val denabled_of : dtable -> dstyle -> bool

val dstyle_of : dtable -> char -> dstyle option

val dtoken : dtable -> dstyle -> string

val is_space : char -> bool

val nonspace_at : char option -> bool

val dopens_after : char option -> bool

val ddecay_str : dtable -> dstyle -> bool -> bool -> string

val dbare : dtable -> dstyle -> char option -> bool

val is_delim : dtable -> char -> bool

val marked_open : dtable -> dstyle -> string

val marked_close : dtable -> dstyle -> string -> string

val needs_escape : dtable -> char -> bool

val needs_escape_dest : dtable -> char -> bool

val escape_str : dtable -> string -> string

val escape_dest : dtable -> string -> string

val tick_runs_from : nat -> string -> nat list

val tick_runs : string -> nat list

val first_missing : nat -> nat -> nat list -> nat

val verb_ticks : string -> nat

val starts_tick : string -> bool

val ends_tick : string -> bool

val pad_verb : string -> string

val ticks : nat -> string

val verb_text : string -> string

val verb_safe_from : nat -> nat -> string -> bool

val verb_safe : nat -> string -> bool

val starts_space_tick : string -> bool

val verb_content_ok : string -> bool

val bracket_open : bool -> string

val link_close : dtable -> string -> string -> string

val ref_close : string -> string -> string

val note_text : string -> string

val note_label_safe_from : bool -> string -> bool

val note_label_safe : string -> bool

val auto_email_from : char option -> string -> bool

val auto_email : string -> bool

val is_alpha : char -> bool

val auto_scheme : string -> bool

val auto_node : string -> inline

val auto_kind_ok : string -> bool

val auto_text : string -> string

val auto_region : string -> bool

val auto_body_ok : string -> bool

val eqchar : char

val raw_spec_ok : string -> bool

val raw_fmt_ok : string -> bool

val raw_format : string -> string

val raw_stop : char -> bool

val raw_text : string -> string -> string

type cinline =
| CIStr of string
| CIVerb of string
| CIDelim of dstyle * cinline list
| CILink of bool * cinline list * string
| CIRef of bool * cinline list * string
| CINote of string
| CIAuto of string
| CIRaw of string * string

val str_last : string -> char option -> char option

val ci_src : dtable -> cinline -> string

val ci_text : dtable -> cinline list -> string

val ci_line : dtable -> cinline list -> string

val ci_ast : cinline -> inline node

val ci_inlines : cinline list -> inlines

val ci_pair_ok : dtable -> cinline -> cinline -> bool

val ci_ok : dtable -> cinline -> bool

val ci_sep_ok : dtable -> cinline list -> bool

val cis_ok : dtable -> cinline list -> bool

val strip_pad : string -> string

val trim_verb : string -> string

type oitem =
| OIn of inline node
| OMark of attr

type oitems = oitem list

type frame_kind =
| FKDelim of dstyle * bool
| FKBracket of bool
| FKDest of bool

type frame = { fr_kind : frame_kind; fr_marked : bool; fr_out : oitems }

val fr_src : dtable -> frame -> string

val fr_barrier : frame -> bool

type ostate = { os_out : oitems; os_stk : frame list }

val ostart : ostate

val dstyle_eqb : dstyle -> dstyle -> bool

val dmatch : dstyle -> bool -> frame -> bool

val isnoc : inline node -> inlines -> inlines

val istarts_str : inlines -> bool

val osnoc : oitem -> oitems -> oitems

val oapp : oitems -> oitems -> oitems

val oemit : inline node -> ostate -> ostate

val omark : attr -> ostate -> ostate

val flush_text : string -> ostate -> ostate

val opush_at : dstyle -> bool -> bool -> ostate -> ostate

val opush : dstyle -> bool -> ostate -> ostate

val bpush : bool -> ostate -> ostate

val dpush : bool -> ostate -> ostate

val last_ws_split : string -> string * string

val oattach_list : attr -> inlines -> inlines

val oresolve_go : oitems -> inlines * bool

val oresolve : oitems -> inlines

val oclose_go :
  dtable -> dstyle -> bool -> oitems -> frame list -> (oitems * frame list)
  option

val oclose_barred_go : dstyle -> bool -> bool -> frame list -> bool

val oclose_barred : dstyle -> bool -> ostate -> bool

val oclose : dtable -> dstyle -> bool -> ostate -> ostate option

val bclose_go :
  dtable -> oitems -> frame list -> ((oitems * bool) * frame list) option

val bclose : dtable -> ostate -> ((inlines * bool) * ostate) option

val bunpush : ostate -> (bool * ostate) option

val opop_str : ostate -> string * ostate

val bflat : inlines -> string -> ostate -> string * ostate

val bsplit_nl : string -> string -> ostate -> string * ostate

val bclosed_lit : inlines -> bool -> ostate -> string * ostate

val bspan_lit : inlines -> bool -> string -> ostate -> string * ostate

val battr_lit : string -> string -> ostate -> string * ostate

val blit_prev : string -> char option

val bref_lit : inlines -> bool -> string -> ostate -> string * ostate

val drop_nl : string -> string

val oflatten : dtable -> oitems -> frame list -> oitems -> oitems

val oitems_of : dtable -> ostate -> oitems

val ofinish : dtable -> ostate -> inlines

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
| ISpan of inlines * bool * aparser * string * ostate
| IAttr of aparser * string * string * char option * iscan * ostate
| IReference of inlines * bool * string * ostate
| INote of bool * bool * string * ostate
| IDest of inlines * bool * bool * nat * string * iscan * ostate
| IAuto of string * string * ostate
| IRaw of string * string * ostate

val note_pos : string -> char option -> bool

val ilead : dtable -> char -> string -> char option -> ostate -> iscan

val idest_open : inlines -> bool -> ostate -> iscan

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

val iattr_mark : attr -> string -> ostate -> iscan

val iattr_feed :
  dtable -> char -> aparser -> string -> string -> char option -> iscan ->
  ostate -> iscan

val idelim_marked : dstyle -> nat -> string -> ostate -> iscan

val oopen_marked : dstyle -> bool -> string -> ostate -> ostate

val idelim_open_marked : dtable -> dstyle -> bool -> string -> ostate -> iscan

val idelim_run : dtable -> dstyle -> nat -> bool -> string

val ibrace_step_at :
  dtable -> bool -> char -> string -> char option -> ostate -> iscan

val ospan_bang : bool -> ostate -> ostate

val ispan_feed :
  dtable -> char -> inlines -> bool -> aparser -> string -> ostate -> iscan

val inote_step : char -> bool -> bool -> string -> ostate -> iscan

val iauto_step : dtable -> char -> string -> string -> ostate -> iscan

val iraw_lit : string -> string

val iraw_step_at :
  dtable -> bool -> char -> string -> string -> ostate -> iscan

val bnote_lit : bool -> bool -> string -> ostate -> string * ostate

val ibang_step : dtable -> char -> string -> char option -> ostate -> iscan

val idelim_lit : dtable -> dstyle -> string -> bool -> string

val idelim_lit_prev : dtable -> dstyle -> bool -> char option

val idelim_done :
  dtable -> dstyle -> string -> char option -> bool -> char option -> ostate
  -> iscan

val idelim_resolve :
  dtable -> dstyle -> string -> char option -> bool -> char option -> ostate
  -> iscan

val idollar_step :
  dtable -> char -> bool -> string -> char option -> ostate -> iscan

val iperiod_step :
  dtable -> char -> bool -> string -> char option -> ostate -> iscan

val idash_step :
  dtable -> char -> nat -> string -> char option -> ostate -> iscan

val iresolve : dtable -> iscan -> iscan

val iescws_resolve :
  string -> string -> char option -> ostate -> (string * char option) * ostate

val iesc_hard : string -> ostate -> ostate

val istep_at : dtable -> bool -> char -> iscan -> iscan

val istep : dtable -> char -> iscan -> iscan

val ifinish_ostate_flat : iscan -> ostate

val ifinish_ostate : dtable -> iscan -> ostate

val ifinish_rev : dtable -> iscan -> inlines

val ifinish : dtable -> iscan -> inlines

val ibreak_flat : dtable -> iscan -> iscan

val ibreak_at : dtable -> bool -> iscan -> iscan

val ibreak : dtable -> iscan -> iscan

val iclosed_at : iscan -> bool

val iresolve_next : dtable -> char -> iscan -> iscan

val iscan_settled : dtable -> char -> iscan -> bool

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

val ci_para : cinline list list -> inlines

val inline_text : dtable -> inline -> string

val inline_lines : dtable -> inlines -> string -> string list

val djot_table : dtable
