open Bool0
open Datatypes
open InlineTable
open InlineView
open ListDef
open Nat0
open String0
open Strings

val self_row : dtable -> dstyle -> bool

val bare_opens : dtable -> dstyle -> bool

val in_alphabet : dtable -> char -> bool

val starts_row : dtable -> string -> bool

val starts_with : char -> string -> bool

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

val ws_run : string -> string

val at_rbrace : char option -> bool

val lex : dtable -> char option -> int -> string -> token list

val tokens : dtable -> string -> token list

val para_tokens : dtable -> string list -> token list

type matching = (int * int) list

type key =
| KDelim of dstyle * bool
| KBracket

val key_eq : key -> key -> bool

val needs_content : key -> bool

val opens_as : token -> key option

val closes_as : token -> key option

val paren_close : int -> int -> token list -> int option

val rbrack_at : int -> token list -> int option

val region_end : token list -> int -> bool -> int option

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

type rmode =
| RNormal
| RInert of int option

type rstate = { rs_live : litem list; rs_pairs : matching; rs_os : int list;
                rs_mode : rmode }

val ropen : int -> key -> bool -> rstate -> rstate

val rstep : token list -> int -> token -> rstate -> rstate

val rrun : token list -> int -> token list -> rstate -> rstate

val rstart : rstate

val ref_read : token list -> reading
