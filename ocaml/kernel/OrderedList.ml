open Ascii
open Ast
open Datatypes
open Line
open List0
open ListDef
open ListUniformity
open Marker
open Nat0
open Step

(** val nsc_marker :
    (int -> string) -> ordered_list_delim -> int -> marker **)

let nsc_marker core d n =
  MOrd ((core n), d)

(** val nsc_items :
    (int -> string) -> ordered_list_delim -> int -> string list list -> litem
    list **)

let rec nsc_items core d n = function
| [] -> []
| l :: rest ->
  ((nsc_marker core d n), l) :: (nsc_items core d (Stdlib.succ n) rest)

(** val dec_marker : ordered_list_delim -> int -> marker **)

let dec_marker d n =
  MOrd ((dec_str n), d)

(** val dec_items :
    ordered_list_delim -> int -> string list list -> litem list **)

let rec dec_items d n = function
| [] -> []
| l :: rest -> ((dec_marker d n), l) :: (dec_items d (Stdlib.succ n) rest)

(** val roman_sty : bool -> ordered_list_style **)

let roman_sty = function
| true -> RomanUpper
| false -> RomanLower

(** val alpha_sty : bool -> ordered_list_style **)

let alpha_sty = function
| true -> LetterUpper
| false -> LetterLower

(** val alpha_char : bool -> int -> char **)

let alpha_char up n =
  ascii_of_nat
    (( + )
      (if up
       then Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ
              0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       else Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ
              0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      n)

(** val alpha_roman_digit : bool -> int -> bool **)

let alpha_roman_digit up n =
  if up then is_roman_up (alpha_char up n) else is_roman_lo (alpha_char up n)

type list_kind =
| LKBullet
| LKDef
| LKTask of task_status list
| LKDecimal of ordered_list_delim * int
| LKRoman of bool * ordered_list_delim * int
| LKAlpha of bool * ordered_list_delim * int

(** val ck_first : list_kind -> marker **)

let ck_first = function
| LKBullet -> bullet
| LKDef -> colon
| LKTask checks -> MTask ('-', (hd Incomplete checks))
| LKDecimal (d, start) -> dec_marker d start
| LKRoman (up, d, start) -> nsc_marker (Roman.str up) d start
| LKAlpha (up, d, start) -> nsc_marker (Alpha.str up) d start

(** val task_ck_items : task_status list -> string list list -> litem list **)

let rec task_ck_items checks = function
| [] -> []
| l :: rest ->
  (match checks with
   | [] -> ((MTask ('-', Incomplete)), l) :: (task_ck_items [] rest)
   | c :: cs -> ((MTask ('-', c)), l) :: (task_ck_items cs rest))

(** val ck_items : list_kind -> string list list -> litem list **)

let ck_items k lss =
  match k with
  | LKBullet -> same_marker bullet lss
  | LKDef -> same_marker colon lss
  | LKTask checks -> task_ck_items checks lss
  | LKDecimal (d, start) -> dec_items d start lss
  | LKRoman (up, d, start) -> nsc_items (Roman.str up) d start lss
  | LKAlpha (up, d, start) -> nsc_items (Alpha.str up) d start lss

(** val ck_block : list_kind -> list_spacing -> blocks list -> block **)

let ck_block k sp items =
  match k with
  | LKBullet -> BulletList (sp, (map mk items))
  | LKDef -> DefinitionList (sp, (def_items items))
  | LKTask checks -> TaskList (sp, (task_items checks items))
  | LKDecimal (d, start) ->
    OrderedList ({ ol_style = Decimal; ol_delim = d; ol_start = start }, sp,
      (map mk items))
  | LKRoman (up, d, start) ->
    OrderedList ({ ol_style = (roman_sty up); ol_delim = d; ol_start =
      start }, sp, (map mk items))
  | LKAlpha (up, d, start) ->
    OrderedList ({ ol_style = (alpha_sty up); ol_delim = d; ol_start =
      start }, sp, (map mk items))

(** val ck_ok : bconfig -> list_kind -> int -> bool **)

let ck_ok k k0 n =
  match k0 with
  | LKBullet -> true
  | LKDef -> k.bdeflists
  | LKTask checks -> (&&) k.btasks (( = ) (length checks) n)
  | LKDecimal (_, start) -> dec_fits (sub (( + ) start n) (Stdlib.succ 0))
  | LKRoman (_, _, start) ->
    (&&) (( <= ) (Stdlib.succ 0) start)
      (( <= ) (( + ) start n) (Stdlib.succ Roman.upper))
  | LKAlpha (up, _, start) ->
    (&&)
      ((&&) (( <= ) (Stdlib.succ 0) start)
        (( <= ) (( + ) start n) (Stdlib.succ Alpha.upper)))
      ((||)
        ((||) (negb (alpha_roman_digit up start))
          ((&&) (( <= ) (Stdlib.succ (Stdlib.succ 0)) n)
            (negb (alpha_roman_digit up (Stdlib.succ start)))))
        ((&&)
          ((&&) (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))) n)
            (alpha_roman_digit up (Stdlib.succ start)))
          (negb (alpha_roman_digit up (Stdlib.succ (Stdlib.succ start))))))
