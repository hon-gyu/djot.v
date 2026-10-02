open Ascii
open Ast
open Attributes
open Datatypes
open InlineTable
open Line
open List0
open ListDef
open Strings

val dchar : dtable -> dstyle -> char

val dsyntax_of : dtable -> dstyle -> dsyntax

val dwidth : dtable -> dstyle -> int

val smart_typography : dtable -> bool

val raw_inline_enabled : dtable -> bool

val math_enabled : dtable -> bool

val dollar_math_enabled : dtable -> bool

val inline_attrs_enabled : dtable -> bool

val notes_enabled : dtable -> bool

val wikilinks_enabled : dtable -> bool

val tags_enabled : dtable -> bool

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

val marker_core : string -> bool

val bare_ok : bool -> string -> char -> string -> bool

val escape_from : dtable -> bool -> string -> string -> string

val escape_str : dtable -> string -> string

val escape_dest : dtable -> string -> string

val tick_runs_from : int -> string -> int list

val tick_runs : string -> int list

val first_missing : int -> int -> int list -> int

val verb_ticks : string -> int

val starts_tick : string -> bool

val ends_tick : string -> bool

val pad_verb : string -> string

val ticks : int -> string

val verb_text : string -> string

val verb_safe_from : int -> int -> string -> bool

val verb_safe : int -> string -> bool

val starts_space_tick : string -> bool

val verb_content_ok : string -> bool

val bracket_open : bool -> string

val tag_open : string -> string

val link_close : dtable -> string -> string -> string

val ref_close : string -> string -> string

val wiki_text : bool -> string -> string option -> string

val note_text : string -> string

val note_label_safe_from : bool -> string -> bool

val note_label_safe : string -> bool

val auto_email : string -> bool

val is_alpha : char -> bool

val symbol_char : char -> bool

val auto_node : string -> inline

val auto_kind_ok : string -> bool

val auto_text : string -> string

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
| CIWiki of bool * string * string option
| CITag of string * cinline list

val str_last : string -> char option -> char option

val ci_src : dtable -> cinline -> string

val ci_text : dtable -> cinline list -> string

val ci_text_at : dtable -> bool -> cinline list -> string

val ci_line : dtable -> cinline list -> string

val ci_ast : cinline -> inline node

val ci_inlines : cinline list -> inlines

val ci_pair_ok : dtable -> cinline -> cinline -> bool

val ci_lbrack_head : cinline -> bool

val cis_lbrack_head : cinline list -> bool

val bracket_kids_ok : dtable -> cinline list -> bool

val wiki_part_ok : string -> bool

val tag_name_ok : string -> bool

val ci_ok : dtable -> cinline -> bool

val ci_sep_ok : dtable -> cinline list -> bool

val cis_ok : dtable -> cinline list -> bool

val ci_para : cinline list list -> inlines

val inline_text : dtable -> inline -> string

val line_ends : inlines -> bool

val inline_lines : dtable -> inlines -> string -> string list
