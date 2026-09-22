open Ast
open Datatypes
open DecimalString
open List0
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

(** val rev_string : string -> string **)

let rev_string = (fun s -> let n = String.length s in
     String.init n (fun i -> String.get s (n - 1 - i)))

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

(** val split_lines : string -> string list **)

let split_lines = (fun s -> match List.rev (String.split_on_char '\n' s) with
     | "" :: rest -> List.rev rest
     | parts -> List.rev parts)

(** val index_lines_from : nat -> string list -> (nat * string) list **)

let rec index_lines_from i = function
| [] -> []
| l :: rest -> (i, l) :: (index_lines_from (S i) rest)

(** val split_lines_indexed : string -> (nat * string) list **)

let split_lines_indexed s =
  index_lines_from O (split_lines s)

type source_line = { source_line_start : nat; source_line_length : nat;
                     source_line_ending : nat }

(** val line_table_aux : string -> nat -> nat -> source_line list **)

let rec line_table_aux s start len =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ ->
    match len with
    | O -> []
    | S _ ->
      { source_line_start = start; source_line_length = len;
        source_line_ending = O } :: [])
    (fun c rest ->
    if (=) c '\n'
    then { source_line_start = start; source_line_length = len;
           source_line_ending = (S
           O) } :: (line_table_aux rest (S (add start len)) O)
    else line_table_aux rest start (S len))
    s

(** val line_table : string -> source_line list **)

let line_table s =
  line_table_aux s O O

(** val source_line_at : source_line list -> nat -> source_line option **)

let source_line_at =
  nth_error

type source_point = { source_byte : nat; source_line_index : nat;
                      source_column : nat }

type source_span = { source_span_start : source_point;
                     source_span_stop : source_point }

(** val resolve_spot : source_line list -> spot -> source_point option **)

let resolve_spot lines p =
  match source_line_at lines p.spot_line with
  | Some l ->
    if leb p.spot_rem l.source_line_length
    then let col = sub l.source_line_length p.spot_rem in
         Some { source_byte = (add l.source_line_start col);
         source_line_index = p.spot_line; source_column = col }
    else None
  | None -> None

(** val resolve_span : source_line list -> span -> source_span option **)

let resolve_span lines r =
  match resolve_spot lines r.span_start with
  | Some a ->
    (match resolve_spot lines r.span_stop with
     | Some b -> Some { source_span_start = a; source_span_stop = b }
     | None -> None)
  | None -> None

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
