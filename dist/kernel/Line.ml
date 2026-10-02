open Ast
open Attributes
open Datatypes
open ListDef
open Strings

type fence = { f_ch : char; f_len : int; f_info : string }

type lstyle =
| SBullet of char
| STask of char
| SOrd of ordered_list_style * ordered_list_delim

type task_marker = { tm_status : task_status; tm_box : char;
                     tm_sep : char option }

(** val task_marker_source : task_marker -> string **)

let task_marker_source m =
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    ('[',
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (m.tm_box,
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (']',
    (match m.tm_sep with
     | Some c ->
       (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

         (c, "")
     | None -> ""))))))

(** val ols_eqb : ordered_list_style -> ordered_list_style -> bool **)

let ols_eqb a b =
  match a with
  | Decimal -> (match b with
                | Decimal -> true
                | _ -> false)
  | LetterUpper -> (match b with
                    | LetterUpper -> true
                    | _ -> false)
  | LetterLower -> (match b with
                    | LetterLower -> true
                    | _ -> false)
  | RomanUpper -> (match b with
                   | RomanUpper -> true
                   | _ -> false)
  | RomanLower -> (match b with
                   | RomanLower -> true
                   | _ -> false)

(** val old_eqb : ordered_list_delim -> ordered_list_delim -> bool **)

let old_eqb a b =
  match a with
  | RightPeriod -> (match b with
                    | RightPeriod -> true
                    | _ -> false)
  | RightParen -> (match b with
                   | RightParen -> true
                   | _ -> false)
  | LeftRightParen -> (match b with
                       | LeftRightParen -> true
                       | _ -> false)

(** val lstyle_eqb : lstyle -> lstyle -> bool **)

let lstyle_eqb a b =
  match a with
  | SBullet x -> (match b with
                  | SBullet y -> (=) x y
                  | _ -> false)
  | STask x -> (match b with
                | STask y -> (=) x y
                | _ -> false)
  | SOrd (n, d) ->
    (match b with
     | SOrd (n', d') -> (&&) (ols_eqb n n') (old_eqb d d')
     | _ -> false)

type trow =
| TSep of align list
| TCells of string list

(** val aligns_eqb : align list -> align list -> bool **)

let rec aligns_eqb xs ys =
  match xs with
  | [] -> (match ys with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs' ->
    (match ys with
     | [] -> false
     | y :: ys' -> (&&) (align_eqb x y) (aligns_eqb xs' ys'))

(** val strs_eqb : string list -> string list -> bool **)

let rec strs_eqb xs ys =
  match xs with
  | [] -> (match ys with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs' ->
    (match ys with
     | [] -> false
     | y :: ys' -> (&&) ((=) x y) (strs_eqb xs' ys'))

(** val trow_eqb : trow -> trow -> bool **)

let trow_eqb x y =
  match x with
  | TSep a -> (match y with
               | TSep b -> aligns_eqb a b
               | TCells _ -> false)
  | TCells a -> (match y with
                 | TSep _ -> false
                 | TCells b -> strs_eqb a b)

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

(** val thematic_count : string -> int -> bool **)

let rec thematic_count = (fun s count ->
     let n = String.length s in
     let rec go i k =
       if i >= n then 3 <= k
       else if s.[i] = '-' || s.[i] = '*' then go (i + 1) (k + 1)
       else if s.[i] = ' ' || s.[i] = '\t' || s.[i] = '\r' then go (i + 1) k
       else false in
     go 0 count)

(** val is_thematic : string -> bool **)

let is_thematic l =
  thematic_count l 0

(** val all_char : char -> string -> bool **)

let rec all_char = (fun c s -> String.for_all (fun a -> a = c) s)

(** val underline_of : string -> (char * int) option **)

let underline_of l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c s ->
    if all_char c s then Some (c, (Stdlib.succ (String.length s))) else None)
    (strip_trailing_ws (drop_leading_ws l))

(** val take_while : (char -> bool) -> string -> string * string **)

let rec take_while = (fun p s ->
     let n = String.length s in
     let rec go i = if i < n && p s.[i] then go (i + 1) else i in
     let i = go 0 in
     if i = 0 then ("", s)
     else (String.sub s 0 i, String.sub s i (n - i)))

(** val count_run : char -> string -> int * string **)

let rec count_run = (fun c s ->
     let n = String.length s in
     let rec go i = if i < n && s.[i] = c then go (i + 1) else i in
     let i = go 0 in
     if i = 0 then (0, s) else (i, String.sub s i (n - i)))

(** val is_info_char : char -> bool **)

let is_info_char c =
  negb ((||) ((||) (is_ws c) ((=) c '`')) ((=) c '\n'))

(** val fence_open : string -> fence option **)

let fence_open l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c s ->
    if (||) ((=) c '`') ((=) c '~')
    then let (n, r) =
           count_run c
             ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

             (c, s))
         in
         if ( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))) n
         then let (info, r') = take_while is_info_char (drop_leading_ws r) in
              if is_blank r'
              then Some { f_ch = c; f_len = n; f_info = info }
              else None
         else None
    else None)
    (drop_leading_ws l)

(** val fence_close : fence -> string -> bool **)

let fence_close f l =
  let (n, r) = count_run f.f_ch (drop_leading_ws l) in
  (&&) (( <= ) f.f_len n) (is_blank r)

(** val is_class_char : char -> bool **)

let is_class_char c =
  let n = Char.code c in
  (||)
    ((||)
      ((||)
        ((||)
          ((&&)
            (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
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
              0)))))))))))))))))))))))))))))))))))))))))))))))) n)
            (( <= ) n (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
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
              (Stdlib.succ
              0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          ((&&)
            (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
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
              (Stdlib.succ
              0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              n)
            (( <= ) n (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
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
              (Stdlib.succ (Stdlib.succ
              0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        ((&&)
          (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ
            0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            n)
          (( <= ) n (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ
            0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      ((=) c '_'))
    ((=) c '-')

(** val div_open : string -> (int * string) option **)

let div_open l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c s ->
    if (=) c ':'
    then let (n, r) =
           count_run ':'
             ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

             (c, s))
         in
         if ( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))) n
         then let (cls, r') = take_while is_class_char (drop_leading_ws r) in
              if is_blank r' then Some (n, cls) else None
         else None
    else None)
    (drop_leading_ws l)

(** val div_close : int -> string -> bool **)

let div_close len l =
  let (n, r) = count_run ':' (drop_leading_ws l) in
  (&&)
    ((&&) (( <= ) len n)
      (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))) n))
    (is_blank r)

(** val quote_prefix : string -> string option **)

let quote_prefix l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c rest ->
    if (=) c '>'
    then ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> Some "")
            (fun c' rest' -> if is_ws c' then Some rest' else None)
            rest)
    else None)
    (drop_leading_ws l)

(** val heading_open : string -> (int * string) option **)

let heading_open l =
  let (n, r) = count_run '#' (drop_leading_ws l) in
  if ( <= ) (Stdlib.succ 0) n
  then ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

          (fun _ -> Some (n, ""))
          (fun c r' -> if is_ws c then Some (n, r') else None)
          r)
  else None

(** val is_bullet : char -> bool **)

let is_bullet c =
  (||) ((||) ((||) ((=) c '-') ((=) c '*')) ((=) c '+')) ((=) c ':')

(** val is_task_bullet : char -> bool **)

let is_task_bullet c =
  (||) ((||) ((=) c '-') ((=) c '*')) ((=) c '+')

(** val in_range : int -> int -> char -> bool **)

let in_range lo hi c =
  let n = Char.code c in (&&) (( <= ) lo n) (( <= ) n hi)

(** val is_digit : char -> bool **)

let is_digit c =
  in_range (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))) (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))) c

(** val is_lower : char -> bool **)

let is_lower c =
  in_range (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    c

(** val is_upper : char -> bool **)

let is_upper c =
  in_range (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    c

(** val is_alnum : char -> bool **)

let is_alnum c =
  (||) ((||) (is_digit c) (is_lower c)) (is_upper c)

(** val callout_kind_char : char -> bool **)

let callout_kind_char c =
  (||) ((||) (is_alnum c) ((=) c '-')) ((=) c '_')

(** val callout_sep : char -> bool **)

let callout_sep c =
  (||) ((=) c ' ') ((=) c '\t')

(** val callout_header :
    string -> ((string * callout_fold option) * string) option **)

let callout_header s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun a s0 ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> None)
      (fun b rest ->
      if (&&) ((=) a '[') ((=) b '!')
      then let (kind, rest0) = take_while callout_kind_char rest in
           ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

              (fun _ -> None)
              (fun _ _ ->
              (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                (fun _ -> None)
                (fun a1 tail ->
                (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                  (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
                  if b0
                  then if b1
                       then None
                       else if b2
                            then if b3
                                 then if b4
                                      then if b5
                                           then None
                                           else if b6
                                                then if b7
                                                     then None
                                                     else ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                             (fun _ ->
                                                             let fold = None
                                                             in
                                                             let tail0 = "" in
                                                             ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                (fun _ ->
                                                                Some ((kind,
                                                                fold),
                                                                ""))
                                                                (fun c title ->
                                                                if callout_sep
                                                                    c
                                                                then
                                                                  Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                else None)
                                                                tail0))
                                                             (fun a0 more ->
                                                             (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                               (fun b8 b9 b10 b11 b12 b13 b14 b15 ->
                                                               if b8
                                                               then if b9
                                                                    then
                                                                    if b10
                                                                    then
                                                                    let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail)
                                                                    else
                                                                    if b11
                                                                    then
                                                                    if b12
                                                                    then
                                                                    let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail)
                                                                    else
                                                                    if b13
                                                                    then
                                                                    if b14
                                                                    then
                                                                    let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail)
                                                                    else
                                                                    if b15
                                                                    then
                                                                    let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail)
                                                                    else
                                                                    let fold =
                                                                    Some
                                                                    FoldExpanded
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    more)
                                                                    else
                                                                    let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail)
                                                                    else
                                                                    let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail)
                                                                    else
                                                                    if b10
                                                                    then
                                                                    if b11
                                                                    then
                                                                    if b12
                                                                    then
                                                                    let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail)
                                                                    else
                                                                    if b13
                                                                    then
                                                                    if b14
                                                                    then
                                                                    let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail)
                                                                    else
                                                                    if b15
                                                                    then
                                                                    let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail)
                                                                    else
                                                                    let fold =
                                                                    Some
                                                                    FoldCollapsed
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    more)
                                                                    else
                                                                    let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail)
                                                                    else
                                                                    let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail)
                                                                    else
                                                                    let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail)
                                                               else let fold =
                                                                    None
                                                                    in
                                                                    (
                                                                    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    ""))
                                                                    (fun c title ->
                                                                    if
                                                                    callout_sep
                                                                    c
                                                                    then
                                                                    Some
                                                                    ((kind,
                                                                    fold),
                                                                    (drop_leading_ws
                                                                    title))
                                                                    else None)
                                                                    tail))
                                                               a0)
                                                             tail)
                                                else None
                                      else None
                                 else None
                            else None
                  else None)
                  a1)
                rest0)
              kind)
      else None)
      s0)
    s

(** val is_roman_lo : char -> bool **)

let is_roman_lo c =
  (||)
    ((||)
      ((||)
        ((||) ((||) ((||) ((=) c 'i') ((=) c 'v')) ((=) c 'x')) ((=) c 'l'))
        ((=) c 'c'))
      ((=) c 'd'))
    ((=) c 'm')

(** val is_roman_up : char -> bool **)

let is_roman_up c =
  (||)
    ((||)
      ((||)
        ((||) ((||) ((||) ((=) c 'I') ((=) c 'V')) ((=) c 'X')) ((=) c 'L'))
        ((=) c 'C'))
      ((=) c 'D'))
    ((=) c 'M')

(** val str_forallb : (char -> bool) -> string -> bool **)

let rec str_forallb = (fun p s -> String.for_all p s)

(** val marker_shape :
    string -> ((string * ordered_list_delim) * string) option **)

let marker_shape s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c s' ->
    if (=) c '('
    then let (core, r) = take_while is_alnum s' in
         ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> None)
            (fun c' r' ->
            if (=) c' ')' then Some ((core, LeftRightParen), r') else None)
            r)
    else let (core, r) = take_while is_alnum s in
         ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> None)
            (fun c' r' ->
            if (=) c' '.'
            then Some ((core, RightPeriod), r')
            else if (=) c' ')' then Some ((core, RightParen), r') else None)
            r))
    s

(** val dec_digits_max : int **)

let dec_digits_max =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))))))))))))))))

(** val styles_of_core : string -> ordered_list_delim -> lstyle list **)

let styles_of_core core d =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> [])
    (fun c rest ->
    if str_forallb is_digit core
    then if ( <= ) (String.length core) dec_digits_max
         then (SOrd (Decimal, d)) :: []
         else []
    else ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ ->
            if is_roman_lo c
            then (SOrd (RomanLower, d)) :: ((SOrd (LetterLower, d)) :: [])
            else if is_roman_up c
                 then (SOrd (RomanUpper, d)) :: ((SOrd (LetterUpper,
                        d)) :: [])
                 else if is_lower c
                      then (SOrd (LetterLower, d)) :: []
                      else if is_upper c
                           then (SOrd (LetterUpper, d)) :: []
                           else [])
            (fun _ _ ->
            if str_forallb is_roman_lo core
            then (SOrd (RomanLower, d)) :: []
            else if str_forallb is_roman_up core
                 then (SOrd (RomanUpper, d)) :: []
                 else [])
            rest))
    core

(** val box_status : char -> task_status option **)

let box_status c =
  if (=) c ' '
  then Some Incomplete
  else if (||) ((=) c 'x') ((=) c 'X') then Some Complete else None

(** val task_check : string -> (task_marker * string) option **)

let task_check l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c0 s ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> None)
      (fun b s0 ->
      (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

        (fun _ -> None)
        (fun c2 r ->
        if (&&) ((=) c0 '[') ((=) c2 ']')
        then (match box_status b with
              | Some st ->
                ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                   (fun _ -> Some ({ tm_status = st; tm_box = b; tm_sep =
                   None }, ""))
                   (fun c' r' ->
                   if is_ws c'
                   then Some ({ tm_status = st; tm_box = b; tm_sep = (Some
                          c') }, r')
                   else None)
                   r)
              | None -> None)
        else None)
        s0)
      s)
    l

(** val list_marker :
    string -> (((lstyle list * string) * task_marker option) * string) option **)

let list_marker l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c rest ->
    if is_bullet c
    then ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> Some (((((SBullet c) :: []), ""), None),
            ""))
            (fun c' rest' ->
            if is_ws c'
            then (match if is_task_bullet c then task_check rest' else None with
                  | Some p ->
                    let (chk, r) = p in
                    Some (((((STask c) :: []), ""), (Some chk)), r)
                  | None -> Some (((((SBullet c) :: []), ""), None), rest'))
            else None)
            rest)
    else (match marker_shape
                  ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                  (c, rest)) with
          | Some p ->
            let (p0, r) = p in
            let (core, d) = p0 in
            (match styles_of_core core d with
             | [] -> None
             | l0 :: l1 ->
               let sty = l0 :: l1 in
               ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                  (fun _ -> Some (((sty, core), None), ""))
                  (fun c' r' ->
                  if is_ws c' then Some (((sty, core), None), r') else None)
                  r))
          | None -> None))
    (drop_leading_ws l)

(** val ref_label : string -> (string * string) option **)

let rec ref_label = (fun s -> match String.index_opt s ']' with
     | None -> None
     | Some i ->
       Some (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1)))

(** val ref_value : string -> string option **)

let ref_value s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> Some "")
    (fun c _ ->
    if is_ws c
    then let t = drop_leading_ws s in if no_ws t then Some t else None
    else None)
    s

(** val is_footnote_label : string -> bool **)

let is_footnote_label lbl =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> false)
    (fun a s ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b b0 b1 b2 b3 b4 b5 b6 ->
      if b
      then false
      else if b0
           then if b1
                then if b2
                     then if b3
                          then if b4
                               then false
                               else if b5
                                    then if b6
                                         then false
                                         else ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                 (fun _ -> false)
                                                 (fun _ _ -> true)
                                                 s)
                                    else false
                          else false
                     else false
                else false
           else false)
      a)
    lbl

(** val foot_open : string -> (string * string) option **)

let foot_open l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c s ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> None)
      (fun h rest ->
      if negb ((=) c '[')
      then None
      else if negb ((=) h '^')
           then None
           else (match ref_label rest with
                 | Some p ->
                   let (lbl, s0) = p in
                   ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                      (fun _ -> None)
                      (fun col after ->
                      if negb ((=) col ':')
                      then None
                      else if negb (nonempty_str lbl)
                           then None
                           else ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                   (fun _ -> Some (lbl, ""))
                                   (fun w body ->
                                   if is_ws w then Some (lbl, body) else None)
                                   after))
                      s0)
                 | None -> None))
      s)
    (drop_leading_ws l)

(** val ref_open : string -> (string * string) option **)

let ref_open l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c rest ->
    if negb ((=) c '[')
    then None
    else (match ref_label rest with
          | Some p ->
            let (lbl, s) = p in
            ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

               (fun _ -> None)
               (fun c' after ->
               if negb ((=) c' ':')
               then None
               else if is_footnote_label lbl
                    then None
                    else (match ref_value after with
                          | Some v -> Some (lbl, v)
                          | None -> None))
               s)
          | None -> None))
    (drop_leading_ws l)

(** val sep_cells_fuel : int -> string -> align list option **)

let rec sep_cells_fuel = (fun fuel s ->
     let n = String.length s in
     let rec skip_ws i =
       if i < n && (s.[i] = ' ' || s.[i] = '\t' || s.[i] = '\r')
       then skip_ws (i + 1) else i in
     let rec dashes i = if i < n && s.[i] = '-' then dashes (i + 1) else i in
     let rec go fuel i acc =
       if fuel = 0 then None
       else if i >= n then Some (List.rev acc)
       else
         let left = s.[i] = ':' in
         let i = if left then i + 1 else i in
         let j = dashes i in
         if j = i then None
         else
           let right = j < n && s.[j] = ':' in
           let j = skip_ws (if right then j + 1 else j) in
           if j < n && s.[j] = '|' then
             let a = match left, right with
               | true, true -> AlignCenter | true, false -> AlignLeft
               | false, true -> AlignRight | false, false -> AlignDefault in
             go (fuel - 1) (skip_ws (j + 1)) (a :: acc)
           else None in
     go fuel 0 [])

(** val sep_cells : string -> align list option **)

let sep_cells s =
  sep_cells_fuel (Stdlib.succ (String.length s)) s

(** val row_cells_trace :
    string -> int -> int -> bool -> string -> (((string * int) * int) * int)
    list -> int -> int -> (((string * int) * int) * int) list option **)

let rec row_cells_trace = (fun s vb run bs cur acc pos start ->
     let n = String.length s in
     let ws c = c = ' ' || c = '\t' || c = '\r' in
     let vb_step vb run =
       if run = 0 then vb else if vb = 0 then run
       else if vb = run then 0 else vb in
     let rev s =
       let k = String.length s in String.init k (fun i -> s.[k - 1 - i]) in
     let trim_r s =
       let k = String.length s in
       let rec go i last =
         if i >= k then last
         else if s.[i] = '\\' then (if i + 1 < k then go (i + 2) (i + 2) else i + 1)
         else if ws s.[i] then go (i + 1) last
         else go (i + 1) (i + 1) in
       String.sub s 0 (go 0 0) in
     (* the cell's source: the reversed [pre] it started with, then
        [s] from [from] up to [i] *)
     let entry pre from i start stop =
       let raw = rev pre ^ String.sub s from (i - from) in
       let k = String.length raw in
       let rec lead j = if j < k && ws raw.[j] then lead (j + 1) else j in
       let d = lead 0 in
       (((trim_r (String.sub raw d (k - d)), start), stop), start + 1 + d) in
     let rec go i vb run bs pre from acc pos start =
       if i >= n then
         (if bs then None
          else if vb_step vb run = 0 then
            Some (List.rev (entry pre from i start (pos + 1) :: acc))
          else None)
       else
         let c = s.[i] in
         if c = '`' then go (i + 1) vb (run + 1) false pre from acc (pos + 1) start
         else
           let vb' = vb_step vb run in
           if vb' = 0 && c = '\\' then
             (if i + 1 >= n then None
              else go (i + 2) 0 0 (s.[i + 1] = '\\') pre from acc (pos + 2) start)
           else if c = '|' && vb' = 0 && not bs then
             go (i + 1) 0 0 false "" (i + 1)
               (entry pre from i start (pos + 1) :: acc) (pos + 1) pos
           else go (i + 1) vb' 0 (c = '\\') pre from acc (pos + 1) start in
     go 0 vb run bs cur 0 acc pos start)

(** val row_cells :
    string -> int -> int -> bool -> string -> string list -> string list
    option **)

let row_cells s vb run bs cur acc =
  option_map
    (map (fun x -> let (y, _) = x in let (y1, _) = y in let (c, _) = y1 in c))
    (row_cells_trace s vb run bs cur (map (fun c -> (((c, 0), 0), 0)) acc)
      (Stdlib.succ 0) 0)

(** val row_body : string -> string option **)

let row_body l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c rest ->
    if negb ((=) c '|')
    then None
    else let back = strip_trailing_ws rest in
         ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> None)
            (fun c' _ ->
            if (=) c' '|' then Some back else None)
            (rev_string back)))
    (drop_leading_ws l)

(** val row_inner : string -> string **)

let row_inner body =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun _ back -> rev_string back)
    (rev_string body)

(** val table_row : string -> trow option **)

let table_row l =
  match row_body l with
  | Some body ->
    (match sep_cells body with
     | Some aligns ->
       (match aligns with
        | [] ->
          (match row_cells (row_inner body) 0 0 false "" [] with
           | Some cells -> Some (TCells cells)
           | None -> None)
        | _ :: _ -> Some (TSep aligns))
     | None ->
       (match row_cells (row_inner body) 0 0 false "" [] with
        | Some cells -> Some (TCells cells)
        | None -> None))
  | None -> None

(** val cells_body : string list -> string **)

let rec cells_body = function
| [] -> ""
| c :: rest -> (^) " " ((^) c ((^) " |" (cells_body rest)))

(** val caption_open : string -> string option **)

let caption_open l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c rest ->
    if negb ((=) c '^')
    then None
    else ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> None)
            (fun c' _ ->
            if is_ws c' then Some (drop_leading_ws rest) else None)
            rest))
    (drop_leading_ws l)

(** val classify : string -> line_kind **)

let classify l =
  if is_blank l
  then KBlank
  else (match quote_prefix l with
        | Some rest -> KQuote rest
        | None ->
          (match heading_open l with
           | Some p -> let (lvl, rest) = p in KHeading (lvl, rest)
           | None ->
             (match fence_open l with
              | Some f -> KFence f
              | None ->
                (match div_open l with
                 | Some p -> let (n, cls) = p in KDiv (n, cls)
                 | None ->
                   if is_thematic l
                   then KThematic
                   else (match list_marker l with
                         | Some p ->
                           let (p0, rest) = p in
                           let (p1, chk) = p0 in
                           let (sty, core) = p1 in
                           KList (sty, core, chk, rest)
                         | None ->
                           (match attr_open l with
                            | Some p -> KAttr p
                            | None ->
                              (match foot_open l with
                               | Some p ->
                                 let (lbl, rest) = p in KFoot (lbl, rest)
                               | None ->
                                 (match ref_open l with
                                  | Some p ->
                                    let (lbl, v) = p in KRef (lbl, v)
                                  | None ->
                                    (match table_row l with
                                     | Some r -> KRow r
                                     | None -> KText)))))))))

(** val is_text : string -> bool **)

let is_text l =
  match classify l with
  | KText -> true
  | _ -> false

(** val all_info_chars : string -> bool **)

let rec all_info_chars = (fun s -> String.for_all (fun c ->
     not (c = ' ' || c = '\t' || c = '\r' || c = '`' || c = '\n')) s)

(** val quote_open : string **)

let quote_open =
  "> "

(** val quote_line : string -> string **)

let quote_line l =
  (^) quote_open l

(** val hashes : int -> string **)

let rec hashes n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> "")
    (fun n' -> (^) "#" (hashes n'))
    n

(** val heading_line : int -> string -> string **)

let heading_line lvl l =
  (^) (hashes lvl) ((^) " " l)

(** val div_fence : string **)

let div_fence =
  ":::"

(** val div_open_line : string -> string -> string **)

let div_open_line fence0 word =
  if (=) word "" then fence0 else (^) fence0 ((^) " " word)

(** val div_word_ok : string -> bool **)

let div_word_ok w =
  str_forallb is_class_char w

(** val blanks : int -> string **)

let rec blanks n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> "")
    (fun k ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (' ', (blanks k)))
    n

type marker =
| MBullet of char
| MTask of char * task_status
| MOrd of string * ordered_list_delim

(** val mk_open : marker -> string **)

let mk_open = function
| MBullet c ->
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (c, " ")
| MTask (c, chk) ->
  (match chk with
   | Complete ->
     (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

       (c, " [x] ")
   | Incomplete ->
     (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

       (c, " [ ] "))
| MOrd (core, d) ->
  (match d with
   | RightPeriod -> (^) core ". "
   | RightParen -> (^) core ") "
   | LeftRightParen -> (^) "(" ((^) core ") "))

(** val mk_pad : marker -> int **)

let mk_pad m =
  String.length (mk_open m)

(** val mk_cont : marker -> string **)

let mk_cont m =
  blanks (mk_pad m)

(** val bullet : marker **)

let bullet =
  MBullet '-'

(** val colon : marker **)

let colon =
  MBullet ':'

(** val callout_kind_ok : string -> bool **)

let callout_kind_ok kind =
  (&&) (nonempty_str kind) (str_forallb callout_kind_char kind)

(** val callout_fold_marker : callout_fold option -> string **)

let callout_fold_marker = function
| Some c -> (match c with
             | FoldExpanded -> "+"
             | FoldCollapsed -> "-")
| None -> ""

(** val callout_header_line :
    string -> callout_fold option -> string -> string **)

let callout_header_line kind fold title =
  (^) "[!"
    ((^) kind
      ((^) "]"
        ((^) (callout_fold_marker fold)
          ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

             (fun _ -> "")
             (fun _ _ -> (^) " " title)
             title))))

(** val task_start : string -> bool **)

let task_start l =
  match task_check l with
  | Some _ -> true
  | None -> false
