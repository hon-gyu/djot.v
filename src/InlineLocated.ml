open Ast
open Datatypes
open InlineScan
open InlineTable
open InlineView
open ListDef
open Nat0
open String0
open Strings

(** val cursor_in : nat -> nat -> spot -> coq_InlineCursor **)

let cursor_in k rem origin =
  { cursor_start = { spot_line = k; spot_rem = rem }; cursor_stop =
    { spot_line = k; spot_rem = (pred rem) }; cursor_origin = origin }

(** val iscan_str_located :
    dtable -> coq_PosPolicy -> bool -> nat -> spot -> nat -> string -> iscan
    -> iscan **)

let rec iscan_str_located t h allow k origin rem s st =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> st)
    (fun c rest ->
    iscan_str_located t h allow k origin (pred rem) rest
      (istep_at t h (cursor_in k rem origin) allow c st))
    s

(** val lines_start : (nat * string) list -> spot **)

let lines_start = function
| [] -> { spot_line = O; spot_rem = O }
| p :: _ -> let (k, x) = p in { spot_line = k; spot_rem = (length x) }

(** val lines_stop : (nat * string) list -> spot **)

let rec lines_stop = function
| [] -> { spot_line = O; spot_rem = O }
| p :: rest ->
  let (k, x) = p in
  (match rest with
   | [] ->
     { spot_line = k; spot_rem =
       (sub (length x) (length (strip_trailing_ws x))) }
   | _ :: _ -> lines_stop rest)

(** val allow_attrs : dtable -> nat -> bool **)

let allow_attrs t = function
| O -> inline_attrs_enabled t
| S _ -> false

(** val iscan_lines_located :
    dtable -> coq_PosPolicy -> nat -> spot -> (nat * string) list -> iscan ->
    iscan **)

let rec iscan_lines_located t h off origin l st =
  match l with
  | [] -> st
  | p :: rest ->
    let (k, x) = p in
    (match rest with
     | [] ->
       iscan_str_located t h (allow_attrs t off) k origin (length x)
         (strip_trailing_ws x) st
     | _ :: _ ->
       iscan_lines_located t h (pred off) origin rest
         (ibreak_at t h { cursor_start = { spot_line = k; spot_rem = O };
           cursor_stop = (lines_start rest); cursor_origin = { spot_line = k;
           spot_rem = (length x) } } (allow_attrs t off)
           (iscan_str_located t h (allow_attrs t off) k origin (length x) x
             st)))

(** val ifinish_located :
    dtable -> coq_PosPolicy -> (nat * string) list -> iscan -> inlines **)

let ifinish_located t h l st =
  ifinish t h { cursor_start = (lines_stop l); cursor_stop = (lines_stop l);
    cursor_origin = (lines_start l) } st

(** val para_inlines_located :
    dtable -> coq_PosPolicy -> nat -> (nat * string) list -> inlines **)

let para_inlines_located t h off l =
  ifinish_located t h l (iscan_lines_located t h off (lines_start l) l istart)

(** val para_inlines_at :
    dtable -> coq_PosPolicy -> nat -> (nat * string) list -> inlines **)

let para_inlines_at t h off l =
  if h.pos_records
  then para_inlines_located t h off l
  else para_inlines_off t off (map snd l)

(** val parse_inline_line_located :
    dtable -> coq_PosPolicy -> nat -> nat -> string -> inlines **)

let parse_inline_line_located t h k rem s =
  let stop = { spot_line = k; spot_rem = (sub rem (length s)) } in
  ifinish t h { cursor_start = stop; cursor_stop = stop; cursor_origin =
    { spot_line = k; spot_rem = rem } }
    (iscan_str_located t h (inline_attrs_enabled t) k { spot_line = k;
      spot_rem = rem } rem s istart)
