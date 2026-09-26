open Ast
open Attributes
open Datatypes
open List0
open ListDef
open Nat0
open Strings

type fence = { f_ch : char; f_len : int; f_info : string }

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
| KDiv of int * string
| KQuote of string
| KHeading of int * string
| KList of lstyle list * string * task_marker option * string
| KAttr of aparser
| KFoot of string * string
| KRef of string * string
| KRow of trow
| KText

val is_marker : char -> bool

val thematic_count : string -> int -> bool

val is_thematic : string -> bool

val all_char : char -> string -> bool

val underline_of : string -> (char * int) option

val take_while : (char -> bool) -> string -> string * string

val count_run : char -> string -> int * string

val is_info_char : char -> bool

val fence_open : string -> fence option

val fence_close : fence -> string -> bool

val is_class_char : char -> bool

val div_open : string -> (int * string) option

val div_close : int -> string -> bool

val quote_prefix : string -> string option

val heading_open : string -> (int * string) option

val is_bullet : char -> bool

val is_task_bullet : char -> bool

val in_range : int -> int -> char -> bool

val is_digit : char -> bool

val is_lower : char -> bool

val is_upper : char -> bool

val is_alnum : char -> bool

val is_roman_lo : char -> bool

val is_roman_up : char -> bool

val str_forallb : (char -> bool) -> string -> bool

val marker_shape : string -> ((string * ordered_list_delim) * string) option

val dec_digits_max : int

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

val sep_cells_fuel : int -> string -> align list option

val sep_cells : string -> align list option

val cell_trim_r : string -> string

val cell_trim : string -> string

val vb_step : int -> int -> int

val row_cell_entry : string -> int -> int -> ((string * int) * int) * int

val row_cells_trace :
  string -> int -> int -> bool -> string -> (((string * int) * int) * int)
  list -> int -> int -> (((string * int) * int) * int) list option

val row_cells :
  string -> int -> int -> bool -> string -> string list -> string list option

val row_body : string -> string option

val row_inner : string -> string

val table_row : string -> trow option

val caption_open : string -> string option

val classify : string -> line_kind

val is_text : string -> bool

val all_info_chars : string -> bool

val quote_open : string

val quote_line : string -> string

val hashes : int -> string

val heading_line : int -> string -> string

val div_fence : string

val blanks : int -> string

type marker =
| MBullet of char
| MTask of char * task_status
| MOrd of string * ordered_list_delim

val mk_open : marker -> string

val mk_pad : marker -> int

val mk_cont : marker -> string

val bullet : marker

val colon : marker

val task_start : string -> bool
