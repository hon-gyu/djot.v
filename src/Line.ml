open Ascii
open Ast
open Attributes
open Datatypes
open List0
open ListDef
open Nat0
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
| KDiv of nat * string
| KQuote of string
| KHeading of nat * string
| KList of lstyle list * string * task_marker option * string
| KAttr of aparser
| KFoot of string * string
| KRef of string * string
| KRow of trow
| KText

(** val is_marker : char -> bool **)

let is_marker c =
  (||) ((=) c '-') ((=) c '*')

(** val thematic_count : string -> nat -> bool **)

let rec thematic_count s count =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> Nat.leb (S (S (S O))) count)
    (fun c s' ->
    if is_marker c
    then thematic_count s' (S count)
    else if is_ws c then thematic_count s' count else false)
    s

(** val is_thematic : string -> bool **)

let is_thematic l =
  thematic_count l O

(** val all_char : char -> string -> bool **)

let rec all_char c s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun a s' -> (&&) ((=) a c) (all_char c s'))
    s

(** val underline_of : string -> (char * nat) option **)

let underline_of l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c s ->
    if all_char c s then Some (c, (S (length s))) else None)
    (strip_trailing_ws (drop_leading_ws l))

(** val take_while : (char -> bool) -> string -> string * string **)

let rec take_while p s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> ("", s))
    (fun c s' ->
    if p c
    then let (a, b) = take_while p s' in
         (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

         (c, a)), b)
    else ("", s))
    s

(** val count_run : char -> string -> nat * string **)

let rec count_run c s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> (O, s))
    (fun c' s' ->
    if (=) c c' then let (n, r) = count_run c s' in ((S n), r) else (O, s))
    s

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
         if Nat.leb (S (S (S O))) n
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
  (&&) (Nat.leb f.f_len n) (is_blank r)

(** val is_class_char : char -> bool **)

let is_class_char c =
  let n = nat_of_ascii c in
  (||)
    ((||)
      ((||)
        ((||)
          ((&&)
            (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))))))))))))))))))) n)
            (Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          ((&&)
            (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S
              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              n)
            (Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        ((&&)
          (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            n)
          (Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      ((=) c '_'))
    ((=) c '-')

(** val div_open : string -> (nat * string) option **)

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
         if Nat.leb (S (S (S O))) n
         then let (cls, r') = take_while is_class_char (drop_leading_ws r) in
              if is_blank r' then Some (n, cls) else None
         else None
    else None)
    (drop_leading_ws l)

(** val div_close : nat -> string -> bool **)

let div_close len l =
  let (n, r) = count_run ':' (drop_leading_ws l) in
  (&&) ((&&) (Nat.leb len n) (Nat.leb (S (S (S O))) n)) (is_blank r)

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

(** val heading_open : string -> (nat * string) option **)

let heading_open l =
  let (n, r) = count_run '#' (drop_leading_ws l) in
  if Nat.leb (S O) n
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

(** val in_range : nat -> nat -> char -> bool **)

let in_range lo hi c =
  let n = nat_of_ascii c in (&&) (Nat.leb lo n) (Nat.leb n hi)

(** val is_digit : char -> bool **)

let is_digit c =
  in_range (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S O)))))))))))))))))))))))))))))))))))))))))))))))) (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))) c

(** val is_lower : char -> bool **)

let is_lower c =
  in_range (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    c

(** val is_upper : char -> bool **)

let is_upper c =
  in_range (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    c

(** val is_alnum : char -> bool **)

let is_alnum c =
  (||) ((||) (is_digit c) (is_lower c)) (is_upper c)

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

let rec str_forallb p s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c s' -> (&&) (p c) (str_forallb p s'))
    s

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

(** val styles_of_core : string -> ordered_list_delim -> lstyle list **)

let styles_of_core core d =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> [])
    (fun c rest ->
    if str_forallb is_digit core
    then (SOrd (Decimal, d)) :: []
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

let rec ref_label s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c rest ->
    if (=) c ']'
    then Some ("", rest)
    else (match ref_label rest with
          | Some p ->
            let (lbl, tail) = p in
            Some
            (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

            (c, lbl)), tail)
          | None -> None))
    s

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

(** val sep_align : bool -> bool -> align **)

let sep_align left right =
  if left
  then if right then AlignCenter else AlignLeft
  else if right then AlignRight else AlignDefault

(** val sep_cell : string -> (align * string) option **)

let sep_cell s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ ->
    let left = false in
    let (n, s2) = count_run '-' s in
    (match n with
     | O -> None
     | S _ ->
       ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

          (fun _ ->
          let right = false in
          ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

             (fun _ -> None)
             (fun c r ->
             if (=) c '|'
             then Some ((sep_align left right), (drop_leading_ws r))
             else None)
             (drop_leading_ws s2)))
          (fun c r ->
          if (=) c ':'
          then let right = true in
               ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                  (fun _ -> None)
                  (fun c0 r0 ->
                  if (=) c0 '|'
                  then Some ((sep_align left right), (drop_leading_ws r0))
                  else None)
                  (drop_leading_ws r))
          else let right = false in
               ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                  (fun _ -> None)
                  (fun c0 r0 ->
                  if (=) c0 '|'
                  then Some ((sep_align left right), (drop_leading_ws r0))
                  else None)
                  (drop_leading_ws s2)))
          s2)))
    (fun c r ->
    if (=) c ':'
    then let left = true in
         let (n, s2) = count_run '-' r in
         (match n with
          | O -> None
          | S _ ->
            ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

               (fun _ ->
               let right = false in
               ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                  (fun _ -> None)
                  (fun c0 r0 ->
                  if (=) c0 '|'
                  then Some ((sep_align left right), (drop_leading_ws r0))
                  else None)
                  (drop_leading_ws s2)))
               (fun c0 r0 ->
               if (=) c0 ':'
               then let right = true in
                    ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                       (fun _ -> None)
                       (fun c1 r1 ->
                       if (=) c1 '|'
                       then Some ((sep_align left right),
                              (drop_leading_ws r1))
                       else None)
                       (drop_leading_ws r0))
               else let right = false in
                    ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                       (fun _ -> None)
                       (fun c1 r1 ->
                       if (=) c1 '|'
                       then Some ((sep_align left right),
                              (drop_leading_ws r1))
                       else None)
                       (drop_leading_ws s2)))
               s2))
    else let left = false in
         let (n, s2) = count_run '-' s in
         (match n with
          | O -> None
          | S _ ->
            ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

               (fun _ ->
               let right = false in
               ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                  (fun _ -> None)
                  (fun c0 r0 ->
                  if (=) c0 '|'
                  then Some ((sep_align left right), (drop_leading_ws r0))
                  else None)
                  (drop_leading_ws s2)))
               (fun c0 r0 ->
               if (=) c0 ':'
               then let right = true in
                    ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                       (fun _ -> None)
                       (fun c1 r1 ->
                       if (=) c1 '|'
                       then Some ((sep_align left right),
                              (drop_leading_ws r1))
                       else None)
                       (drop_leading_ws r0))
               else let right = false in
                    ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                       (fun _ -> None)
                       (fun c1 r1 ->
                       if (=) c1 '|'
                       then Some ((sep_align left right),
                              (drop_leading_ws r1))
                       else None)
                       (drop_leading_ws s2)))
               s2)))
    s

(** val sep_cells_fuel : nat -> string -> align list option **)

let rec sep_cells_fuel n s =
  match n with
  | O -> None
  | S n' ->
    ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

       (fun _ -> Some [])
       (fun _ _ ->
       match sep_cell s with
       | Some p ->
         let (a, rest) = p in
         (match sep_cells_fuel n' rest with
          | Some rest' -> Some (a :: rest')
          | None -> None)
       | None -> None)
       s)

(** val sep_cells : string -> align list option **)

let sep_cells s =
  sep_cells_fuel (S (length s)) s

(** val cell_trim_r : string -> string **)

let rec cell_trim_r s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c1 s1 ->
    if (=) c1 '\\'
    then ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ ->
            (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

            (c1, ""))
            (fun c2 s2 ->
            (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

            (c1,
            ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

            (c2, (cell_trim_r s2)))))
            s1)
    else if is_ws c1
         then ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                 (fun _ -> "")
                 (fun a s0 ->
                 (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                 (c1,
                 ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                 (a, s0))))
                 (cell_trim_r s1))
         else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                (c1, (cell_trim_r s1)))
    s

(** val cell_trim : string -> string **)

let cell_trim s =
  cell_trim_r (drop_leading_ws s)

(** val vb_step : nat -> nat -> nat **)

let vb_step vb run = match run with
| O -> vb
| S _ -> (match vb with
          | O -> run
          | S _ -> if Nat.eqb vb run then O else vb)

(** val row_cell_entry :
    string -> nat -> nat -> ((string * nat) * nat) * nat **)

let row_cell_entry cur start stop =
  let raw = rev_string cur in
  let content = drop_leading_ws raw in
  ((((cell_trim raw), start), stop),
  (sub (add (S start) (length raw)) (length content)))

(** val row_cells_trace :
    string -> nat -> nat -> bool -> string -> (((string * nat) * nat) * nat)
    list -> nat -> nat -> (((string * nat) * nat) * nat) list option **)

let rec row_cells_trace s vb run bs cur acc pos start =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ ->
    if bs
    then None
    else (match vb_step vb run with
          | O -> Some (rev ((row_cell_entry cur start (S pos)) :: acc))
          | S _ -> None))
    (fun c s' ->
    if (=) c '`'
    then row_cells_trace s' vb (S run) false
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, cur)) acc (S pos) start
    else let vb' = vb_step vb run in
         if (&&) (Nat.eqb vb' O) ((=) c '\\')
         then ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                 (fun _ -> None)
                 (fun c' s'' ->
                 row_cells_trace s'' O O ((=) c' '\\')
                   ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                   (c',
                   ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                   (c, cur)))) acc (S (S pos)) start)
                 s')
         else if (&&) ((&&) ((=) c '|') (Nat.eqb vb' O)) (negb bs)
              then row_cells_trace s' O O false ""
                     ((row_cell_entry cur start (S pos)) :: acc) (S pos) pos
              else row_cells_trace s' vb' O ((=) c '\\')
                     ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                     (c, cur)) acc (S pos) start)
    s

(** val row_cells :
    string -> nat -> nat -> bool -> string -> string list -> string list
    option **)

let row_cells s vb run bs cur acc =
  option_map
    (map (fun x -> let (y, _) = x in let (y1, _) = y in let (c, _) = y1 in c))
    (row_cells_trace s vb run bs cur (map (fun c -> (((c, O), O), O)) acc) (S
      O) O)

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
          (match row_cells (row_inner body) O O false "" [] with
           | Some cells -> Some (TCells cells)
           | None -> None)
        | _ :: _ -> Some (TSep aligns))
     | None ->
       (match row_cells (row_inner body) O O false "" [] with
        | Some cells -> Some (TCells cells)
        | None -> None))
  | None -> None

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

let rec all_info_chars s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c s' -> (&&) (is_info_char c) (all_info_chars s'))
    s

(** val quote_open : string **)

let quote_open =
  "> "

(** val quote_line : string -> string **)

let quote_line l =
  (^) quote_open l

(** val hashes : nat -> string **)

let rec hashes = function
| O -> ""
| S n' -> (^) "#" (hashes n')

(** val heading_line : nat -> string -> string **)

let heading_line lvl l =
  (^) (hashes lvl) ((^) " " l)

(** val div_fence : string **)

let div_fence =
  ":::"

(** val blanks : nat -> string **)

let rec blanks = function
| O -> ""
| S k ->
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (' ', (blanks k))

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

(** val mk_pad : marker -> nat **)

let mk_pad m =
  length (mk_open m)

(** val mk_cont : marker -> string **)

let mk_cont m =
  blanks (mk_pad m)

(** val bullet : marker **)

let bullet =
  MBullet '-'

(** val colon : marker **)

let colon =
  MBullet ':'

(** val task_start : string -> bool **)

let task_start l =
  match task_check l with
  | Some _ -> true
  | None -> false
