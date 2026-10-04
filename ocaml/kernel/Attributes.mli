open Ast
open Datatypes
open List0
open ListDef
open Strings

val bslash : char

val dquote : char

val is_key_char : char -> bool

val attr_ws : char -> bool

val is_id_char : char -> bool

val is_attr_class_char : char -> bool

val collapse_from : bool -> string -> string

val collapse_ws : string -> string

val unescape : string -> string

val norm_value : string -> string

type astate =
| AScan
| AId
| AClass
| AKey
| AVal
| ABare
| AQuot
| AEsc
| AComment
| AFail
| ADone

type aparser = { ap_st : astate; ap_tok : char list; ap_key : string;
                 ap_attrs : attr }

val ap_init : aparser

val ap_token : aparser -> string

val ap_push : char -> aparser -> aparser

val ap_goto : astate -> aparser -> aparser

val ap_begin : astate -> aparser -> aparser

val ap_commit_id : astate -> aparser -> aparser

val ap_commit_class : astate -> aparser -> aparser

val ap_commit_value : astate -> aparser -> aparser

val astep : aparser -> char -> aparser

val afeed : string -> aparser -> aparser * string

val ap_done : aparser -> bool

val ap_failed : aparser -> bool

val attr_nl : string

val blank_to_eol : string -> bool

val attr_open : string -> aparser option

val attr_feed : string -> aparser -> aparser

val id_chars_ok : string -> bool

val explicit_id_ok : string -> bool

val class_words_ok : bool -> string -> bool

val classes_ok : string -> bool

val class_chars_ok : string -> bool

val class_word_ok : string -> bool

val dot_words : string -> string

val escape_value : string -> string

val attr_part : (string * string) -> string

val attr_spec : attr -> string

val key_ok : string -> bool

val attr_ok : attr -> bool
