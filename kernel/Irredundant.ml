open Ast
open AstEq
open Attributes
open InlineTable
open ListDef
open Nat0
open Render
open Step
open String0
open Strings

(** val del : int -> string -> string **)

let rec del = (fun i s -> let n = String.length s in
     if i < n then String.sub s 0 i ^ String.sub s (i + 1) (n - i - 1) else s)

(** val first_at : (string -> bool) -> string -> int -> string option **)

let first_at ok s i =
  let test = fun t -> if ok t then Some t else None in
  (match get i s with
   | Some c ->
     if (=) c bslash
     then test (del i s)
     else if (=) c lbrace
          then let rec go = function
               | [] -> None
               | j :: rest ->
                 (match match get j s with
                        | Some d ->
                          if (=) d rbrace
                          then test (del i (del j s))
                          else None
                        | None -> None with
                  | Some t -> Some t
                  | None -> go rest)
               in go
                    (seq (Stdlib.succ i)
                      (sub (String.length s) (Stdlib.succ i)))
          else None
   | None -> None)

(** val first_in :
    (string -> bool) -> string -> int list -> (string * int) option **)

let rec first_in ok s = function
| [] -> None
| i :: rest ->
  (match first_at ok s i with
   | Some t -> Some (t, i)
   | None -> first_in ok s rest)

(** val next : (string -> bool) -> int -> string -> (string * int) option **)

let next ok k s =
  match first_in ok s (seq k (sub (String.length s) k)) with
  | Some r -> Some r
  | None -> first_in ok s (seq 0 (String.length s))

(** val shrink_from : (string -> bool) -> int -> int -> string -> string **)

let rec shrink_from ok fuel k s =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> s)
    (fun f ->
    match next ok k s with
    | Some p -> let (t, i) = p in shrink_from ok f i t
    | None -> s)
    fuel

(** val shrink : (string -> bool) -> int -> string -> string **)

let shrink ok fuel s =
  shrink_from ok fuel 0 s

(** val parses_to : dtable -> bconfig -> blocks -> string -> bool **)

let parses_to t k want t0 =
  blocks_eqb (parse_blocks t k semantic_line_ix semantic_pos t0) want

(** val irredundant_spec : dtable -> bconfig -> blocks -> string **)

let irredundant_spec t k bs =
  let s = render_djot t k bs in shrink (parses_to t k bs) (String.length s) s

(** val block_lines : dtable -> bconfig -> block node -> string list **)

let block_lines t k n =
  let ls = render_node_lines t k n in
  let s = String.concat nl ls in
  let ok = parses_to t k (n :: []) in
  if ok s then split_lines (shrink ok (String.length s) s) else ls

(** val render_djot_irredundant : dtable -> bconfig -> blocks -> string **)

let render_djot_irredundant t k bs =
  String.concat nl (sep_lines (map (block_lines t k) bs))
