open Datatypes
open DecimalString
open Nat0

(** val is_ws : char -> bool **)

let is_ws c =
  (||) ((||) ((=) c ' ') ((=) c '\t')) ((=) c '\r')

(** val is_blank : string -> bool **)

let rec is_blank s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c s' -> (&&) (is_ws c) (is_blank s'))
    s

(** val nonblank : string -> bool **)

let nonblank l =
  negb (is_blank l)

(** val nonempty : 'a1 list -> bool **)

let nonempty = function
| [] -> false
| _ :: _ -> true

(** val nonempty_str : string -> bool **)

let nonempty_str s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> false)
    (fun _ _ -> true)
    s

(** val nat_str : nat -> string **)

let nat_str n =
  NilZero.string_of_uint (to_uint n)

(** val rev_string_aux : string -> string -> string **)

let rec rev_string_aux s acc =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> acc)
    (fun c s' ->
    rev_string_aux s'
      ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      (c, acc)))
    s

(** val rev_string : string -> string **)

let rev_string s =
  rev_string_aux s ""

(** val drop_leading_ws : string -> string **)

let rec drop_leading_ws s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c s' -> if is_ws c then drop_leading_ws s' else s)
    s

(** val indent_of : string -> nat **)

let rec indent_of s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> O)
    (fun c s' -> if is_ws c then S (indent_of s') else O)
    s

(** val strip_trailing_ws : string -> string **)

let strip_trailing_ws s =
  rev_string (drop_leading_ws (rev_string s))

(** val drop_ws_upto : nat -> string -> string **)

let rec drop_ws_upto n s =
  match n with
  | O -> s
  | S n' ->
    ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

       (fun _ -> s)
       (fun c s' -> if is_ws c then drop_ws_upto n' s' else s)
       s)

(** val nl : string **)

let nl =
  "\n"

(** val split_lines_aux : string -> string -> string list **)

let rec split_lines_aux s cur =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> [])
      (fun _ _ -> (rev_string cur) :: [])
      cur)
    (fun c s' ->
    if (=) c '\n'
    then (rev_string cur) :: (split_lines_aux s' "")
    else split_lines_aux s'
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, cur)))
    s

(** val split_lines : string -> string list **)

let split_lines s =
  split_lines_aux s ""

(** val no_nl : string -> bool **)

let rec no_nl s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c s' -> (&&) (negb ((=) c '\n')) (no_nl s'))
    s

(** val no_char : char -> string -> bool **)

let rec no_char c s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c' s' -> (&&) (negb ((=) c' c)) (no_char c s'))
    s

(** val is_ws_nl : char -> bool **)

let is_ws_nl c =
  (||) (is_ws c) ((=) c '\n')

(** val no_ws : string -> bool **)

let rec no_ws s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c s' -> (&&) (negb (is_ws_nl c)) (no_ws s'))
    s

(** val line_ok : string -> bool **)

let line_ok l =
  (&&) ((&&) (nonblank l) (no_nl l)) ((=) (drop_leading_ws l) l)

(** val join_nl : string list -> string **)

let rec join_nl = function
| [] -> ""
| l :: rest -> (^) l ((^) nl (join_nl rest))
