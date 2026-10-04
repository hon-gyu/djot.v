open Ast
open Attributes
open Datatypes
open List0
open ListDef
open Strings

val is_punct : char -> bool

val tick : char

val is_tick : char -> bool

val is_bslash : char -> bool

val lbrace : char

val rbrace : char

val one : char -> string

val dollar : char

val sqchar : char

val dqchar : char

val hyphen : char

val period : char

val bang : char

val lbrack : char

val rbrack : char

val lparen : char

val rparen : char

val vbar : char

val hat : char

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

type dconfig = { dc_char : (dstyle -> char); dc_width : (dstyle -> int);
                 dc_syntax : (dstyle -> dsyntax);
                 dc_decay : (dstyle -> ddecay); dc_smart_typography :
                 bool; dc_raw_inline : bool; dc_math : bool;
                 dc_dollar_math : bool; dc_attrs : bool; dc_footnotes :
                 bool; dc_wikilinks : bool; dc_tags : bool }

val djot_dchar : dstyle -> char

val djot_dsyntax : dstyle -> dsyntax

val lsquo : string

val rsquo : string

val ldquo : string

val rdquo : string

val djot_ddecay : dstyle -> ddecay

val djot_dwidth : dstyle -> int

val djot_config : dconfig

val chars : char -> int -> string

val dstyles : dstyle list

val dstyle_eq : dstyle -> dstyle -> bool

val denabled : dconfig -> dstyle -> bool

val dstyle_at_fast : dconfig -> char -> dstyle option

val ddecay_ok : ddecay -> bool

val dsyntax_bare : dsyntax -> bool

val drow_ok : dconfig -> dstyle -> bool

val dconfig_distinct : dconfig -> bool

val dconfig_rows_ok : dconfig -> bool

val dconfig_ok : dconfig -> bool

type dentry = { de_char : char; de_width : int; de_syntax : dsyntax;
                de_decay : ddecay }

val update_drow : dstyle -> dentry -> dconfig -> dconfig

val with_smart_typography : bool -> dconfig -> dconfig

val with_raw_inline : bool -> dconfig -> dconfig

val with_math : bool -> dconfig -> dconfig

val with_dollar_math : bool -> dconfig -> dconfig

val with_inline_attrs : bool -> dconfig -> dconfig

val with_inline_footnotes : bool -> dconfig -> dconfig

val with_wikilinks : bool -> dconfig -> dconfig

val with_inline_tags : bool -> dconfig -> dconfig

type drow_refusal =
| RWidth
| RNotPunct
| RReserved
| RDecay
| RBareHyphen
| RTaken of dstyle

val drow_update_refusal : dconfig -> dstyle -> dentry -> drow_refusal option

val markdown_strong_entry : dentry

val markdown_like_config : dconfig

val bnode : bool -> inlines -> target -> inline

val dnode : dstyle -> inlines -> inline

val wiki_display : string -> string option -> string

val reference_text : inline -> string

val reference_inlines_text : inlines -> string

type dtable = dconfig
  (* singleton inductive, whose constructor was DTable *)
