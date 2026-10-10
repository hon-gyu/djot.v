open Ast
open Attributes
open Bool0
open Datatypes
open InlineTable
open InlineView
open List0
open Nat0
open String0
open Strings

val self_row : dtable -> dstyle -> bool

val bare_opens : dtable -> dstyle -> bool

val in_alphabet : dtable -> char -> bool

val starts_row : dtable -> string -> bool

val starts_with : char -> string -> bool

val fmt_go : string -> string option

val raw_spec : string -> string option

val auto_stop : char -> bool

val auto_go : string -> string * char option

val auto_clean : string -> bool

val raw_ahead : dtable -> string -> bool

val follow_ok : dtable -> char -> string -> bool

val over_alphabet : dtable -> string -> bool

type token =
| TText of char
| TBreak
| TDelim of dstyle * bool * bool * bool
| TOpen
| TClose of bool
| TEsc of char
| TEscWs of string
| THard of string
| TVerb of int * int * string * bool * string option
| TDollars of int
| TAuto of string * bool

val ws_run : string -> string

val line_rest : string -> string

val tick_run : string -> int

val verb_go : int -> int -> string -> (string * int) * bool

val verb_tok : dtable -> int -> string -> token * int

val dollar_run : string -> int

val auto_tok : string -> token * int

val dollar_tok : dtable -> string -> token * int

val at_rbrace : char option -> bool

val next_tok : dtable -> char option -> string -> (token * int) option

val before : string -> int -> char option

val tok_at : dtable -> string -> int -> (token * int) option

val tok_of : dtable -> string -> int -> token option

val para_string : string list -> string

type matching = (int * int) list

type key =
| KDelim of dstyle * bool
| KBracket

val key_eq : key -> key -> bool

val needs_content : key -> bool

val opens_as : token -> key option

val closes_as : token -> key option

val tok_end : dtable -> string -> int -> int

val dest_close : bool -> int -> int -> string -> int option

val label_close : bool -> int -> string -> int option

val region_end : string -> int -> bool -> int option

val is_opener : matching -> int -> bool

val is_closer : matching -> int -> bool

val resume : string -> int -> bool -> int option

val chain_next : dtable -> string -> matching -> int -> int option

type reading = matching * int list

type litem =
| LOpen of int * key
| LBar of int

val has_key : key -> litem list -> bool

type pick_res =
| PFound of int * litem list
| PBarred
| PNone

val pick : key -> litem list -> pick_res

type rstate = { rs_live : litem list; rs_pairs : matching; rs_os : int list }

val ropen : int -> key -> bool -> rstate -> rstate

val rstep : dtable -> string -> int -> token -> rstate -> rstate

val rgo : dtable -> string -> int -> int -> rstate -> rstate

val rstart : rstate

val ref_read : dtable -> string -> reading

val str_snoc : string -> inlines -> inlines

val esc_text : char -> string

val raw_text : string option -> string

val tok_text : dtable -> token -> string

val nbsp_rest : string -> string option

val str_trim : inlines -> inlines

val no_nl : string -> string

val dest_text : bool -> string -> string

val region_text : string -> int -> int -> bool -> string

val region_node : bool -> inlines -> string -> inline

type tkind =
| TKDelim of dstyle
| TKBracket

type tframes = (tkind * inlines) list

val temit : inline node -> tframes -> inlines -> tframes * inlines

val temit_str : string -> tframes -> inlines -> tframes * inlines

val ttrim : tframes -> inlines -> tframes * inlines

val temit_all : inlines -> tframes -> inlines -> tframes * inlines

val is_hard : token -> bool

val verb_node : int -> string option -> string -> inline

val tstep :
  dtable -> string -> matching -> int -> token -> bool -> tframes -> inlines
  -> tframes * inlines

val tgo :
  dtable -> string -> matching -> int -> int -> bool -> tframes -> inlines ->
  tframes * inlines

val tree_of : dtable -> string -> matching -> inlines
