open Ascii
open Ast
open Attributes
open Datatypes
open List0
open ListDef
open PeanoNat
open String0
open Strings

type fence = { f_ch : char; f_len : nat; f_info : string }

type lstyle =
| SBullet of char
| STask of char
| SOrd of ordered_list_style * ordered_list_delim

type task_marker = { tm_status : task_status; tm_box : char;
                     tm_sep : char option }

val task_marker_source : task_marker -> string

val ols_eqb : ordered_list_style -> ordered_list_style -> bool

val old_eqb : ordered_list_delim -> ordered_list_delim -> bool

val lstyle_eqb : lstyle -> lstyle -> bool

type trow =
| TSep of align list
| TCells of string list

val aligns_eqb : align list -> align list -> bool

val strs_eqb : string list -> string list -> bool

val trow_eqb : trow -> trow -> bool

type line_kind =
| KBlank
| KThematic
| KFence of fence
| KDiv of nat * string
| KQuote of string
| KHeading of nat * string
| KList of lstyle list * string * task_marker option * string
| KAttr of aparser
| KFoot of string * string
| KRef of string * string
| KRow of trow
| KText

val is_marker : char -> bool

val thematic_count : string -> nat -> bool

val is_thematic : string -> bool

val all_char : char -> string -> bool

val underline_of : string -> (char * nat) option

val count_run : char -> string -> nat * string

val is_info_char : char -> bool

val take_info : string -> string * string

val fence_open : string -> fence option

val fence_close : fence -> string -> bool

val is_class_char : char -> bool

val take_class : string -> string * string

val div_open : string -> (nat * string) option

val div_close : nat -> string -> bool

val quote_prefix : string -> string option

val heading_open : string -> (nat * string) option

val is_bullet : char -> bool

val is_task_bullet : char -> bool

val in_range : nat -> nat -> char -> bool

val is_digit : char -> bool

val is_lower : char -> bool

val is_upper : char -> bool

val is_alnum : char -> bool

val is_roman_lo : char -> bool

val is_roman_up : char -> bool

val str_forallb : (char -> bool) -> string -> bool

val take_while : (char -> bool) -> string -> string * string

val marker_shape : string -> ((string * ordered_list_delim) * string) option

val styles_of_core : string -> ordered_list_delim -> lstyle list

val box_status : char -> task_status option

val task_check : string -> (task_marker * string) option

val list_marker :
  string -> (((lstyle list * string) * task_marker option) * string) option

val ref_label : string -> (string * string) option

val ref_value : string -> string option

val is_footnote_label : string -> bool

val foot_open : string -> (string * string) option

val ref_open : string -> (string * string) option

val sep_align : bool -> bool -> align

val sep_cell : string -> (align * string) option

val sep_cells_fuel : nat -> string -> align list option

val sep_cells : string -> align list option

val cell_trim_r : string -> string

val cell_trim : string -> string

val vb_step : nat -> nat -> nat

val row_cells_trace :
  string -> nat -> nat -> bool -> string -> ((string * nat) * nat) list ->
  nat -> nat -> ((string * nat) * nat) list option

val row_cells :
  string -> nat -> nat -> bool -> string -> string list -> string list option

val row_body : string -> string option

val row_inner : string -> string

val table_row : string -> trow option

val caption_open : string -> string option

val classify : string -> line_kind

val is_text : string -> bool

val all_info_chars : string -> bool

val quote_open : string

val quote_line : string -> string

val hashes : nat -> string

val heading_line : nat -> string -> string

val div_fence : string

val blanks : nat -> string

type marker =
| MBullet of char
| MTask of char * task_status
| MOrd of string * ordered_list_delim

val mk_open : marker -> string

val mk_pad : marker -> nat

val mk_cont : marker -> string

val bullet : marker

val colon : marker

val task_start : string -> bool
