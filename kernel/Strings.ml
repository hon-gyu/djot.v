open Ast
open Datatypes
open List0
open Nat0

(** val is_ws : char -> bool **)

let is_ws c =
  (||) ((||) ((=) c ' ') ((=) c '\t')) ((=) c '\r')

(** val is_blank : string -> bool **)

let rec is_blank = (fun s -> String.for_all (fun c -> c = ' ' || c = '\t' || c = '\r') s)

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

(** val nat_str : int -> string **)

let nat_str = Stdlib.string_of_int

(** val rev_string : string -> string **)

let rev_string = (fun s -> let n = String.length s in
     String.init n (fun i -> String.get s (n - 1 - i)))

(** val drop_leading_ws : string -> string **)

let rec drop_leading_ws = (fun s ->
     let ws c = c = ' ' || c = '\t' || c = '\r' in
     let n = String.length s in
     let rec go i = if i < n && ws s.[i] then go (i + 1) else i in
     let i = go 0 in if i = 0 then s else String.sub s i (n - i))

(** val indent_of : string -> int **)

let rec indent_of = (fun s ->
     let ws c = c = ' ' || c = '\t' || c = '\r' in
     let n = String.length s in
     let rec go i = if i < n && ws s.[i] then go (i + 1) else i in
     go 0)

(** val strip_trailing_ws : string -> string **)

let strip_trailing_ws = (fun s ->
     let ws c = c = ' ' || c = '\t' || c = '\r' in
     let n = String.length s in
     let rec go i = if i > 0 && ws s.[i - 1] then go (i - 1) else i in
     let i = go n in if i = n then s else String.sub s 0 i)

(** val drop_ws_upto : int -> string -> string **)

let rec drop_ws_upto = (fun k s ->
     let ws c = c = ' ' || c = '\t' || c = '\r' in
     let n = Stdlib.min k (String.length s) in
     let rec go i = if i < n && ws s.[i] then go (i + 1) else i in
     let i = go 0 in
     if i = 0 then s else String.sub s i (String.length s - i))

(** val nl : string **)

let nl =
  "\n"

(** val split_lines : string -> string list **)

let split_lines = (fun s -> match List.rev (String.split_on_char '\n' s) with
     | "" :: rest -> List.rev rest
     | parts -> List.rev parts)

type source_line = { source_line_start : int; source_line_length : int;
                     source_line_ending : int }

(** val line_table : string -> source_line list **)

let line_table = (fun s ->
     let n = String.length s in
     let rec go start acc =
       match String.index_from_opt s start '\n' with
       | Some i ->
         go (i + 1)
           ({ source_line_start = start; source_line_length = i - start;
              source_line_ending = 1 } :: acc)
       | None ->
         List.rev
           (if start < n
            then { source_line_start = start; source_line_length = n - start;
                   source_line_ending = 0 } :: acc
            else acc)
     in
     go 0 [])

(** val source_line_at : source_line list -> int -> source_line option **)

let source_line_at =
  nth_error

type source_point = { source_byte : int; source_line_index : int;
                      source_column : int }

type source_span = { source_span_start : source_point;
                     source_span_stop : source_point }

(** val resolve_spot : source_line list -> spot -> source_point option **)

let resolve_spot lines p =
  match source_line_at lines p.spot_line with
  | Some l ->
    if ( <= ) p.spot_rem l.source_line_length
    then let col = sub l.source_line_length p.spot_rem in
         Some { source_byte = (( + ) l.source_line_start col);
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

let rec no_nl = (fun s -> not (String.contains s '\n'))

(** val no_char : char -> string -> bool **)

let rec no_char = (fun c s -> not (String.contains s c))

(** val is_ws_nl : char -> bool **)

let is_ws_nl c =
  (||) (is_ws c) ((=) c '\n')

(** val no_ws : string -> bool **)

let rec no_ws = (fun s -> not (String.exists (fun c ->
     c = ' ' || c = '\t' || c = '\r' || c = '\n') s))

(** val line_ok : string -> bool **)

let line_ok l =
  (&&) ((&&) (nonblank l) (no_nl l)) ((=) (drop_leading_ws l) l)

(** val join_nl : string list -> string **)

let rec join_nl = function
| [] -> ""
| l :: rest -> (^) l ((^) nl (join_nl rest))
