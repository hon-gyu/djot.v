open Ast
open Datatypes
open InlineScan
open InlineTable
open InlineView
open ListDef
open Nat0
open Strings

(** val cursor_in : int -> int -> spot -> coq_InlineCursor **)

let cursor_in k rem origin =
  { cursor_start = { spot_line = k; spot_rem = rem }; cursor_stop =
    { spot_line = k; spot_rem = (pred rem) }; cursor_origin = origin }

(** val iscan_str_located :
    dtable -> coq_PosPolicy -> bool -> int -> spot -> int -> string -> string
    iscan_g -> string iscan_g **)

let rec iscan_str_located = (fun t h allow k origin rem s st ->
     let plain c =
       ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
        || (c >= '0' && c <= '9') || c = ' ')
       && dstyle_of t c = None in
     let cursor r = {
       cursor_start = { spot_line = k; spot_rem = r };
       cursor_stop = { spot_line = k; spot_rem = Stdlib.max 0 (r - 1) };
       cursor_origin = origin } in
     let i = ref 0 and pos = ref rem and state = ref (lift chunks_text st)
     and n = String.length s in
     while !i < n do
       match !state with
       | IText (false, txt, _, o) when plain s.[!i] ->
           let j = ref !i and p = ref !pos and scope = ref o in
           while !j < n && plain s.[!j] do
             let c = s.[!j] in
             if is_ws c then scope := remember_word_start h (cursor !p) c !scope;
             p := Stdlib.max 0 (!p - 1);
             incr j
           done;
           state := IText (false, chunks_push txt (String.sub s !i (!j - !i)),
                           Some s.[!j - 1], !scope);
           i := !j;
           pos := !p
       | _ ->
           state := istep_at t chunks_text h (cursor !pos) allow s.[!i] !state;
           pos := Stdlib.max 0 (!pos - 1);
           incr i
     done;
     map_text chunks_text !state)

(** val lines_start : (int * string) list -> spot **)

let lines_start = function
| [] -> { spot_line = 0; spot_rem = 0 }
| p :: _ -> let (k, x) = p in { spot_line = k; spot_rem = (String.length x) }

(** val lines_stop : (int * string) list -> spot **)

let rec lines_stop = function
| [] -> { spot_line = 0; spot_rem = 0 }
| p :: rest ->
  let (k, x) = p in
  (match rest with
   | [] ->
     { spot_line = k; spot_rem =
       (sub (String.length x) (String.length (strip_trailing_ws x))) }
   | _ :: _ -> lines_stop rest)

(** val allow_attrs : dtable -> int -> bool **)

let allow_attrs t off =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> inline_attrs_enabled t)
    (fun _ -> false)
    off

(** val iscan_lines_located :
    dtable -> coq_PosPolicy -> int -> spot -> (int * string) list -> string
    iscan_g -> string iscan_g **)

let rec iscan_lines_located t h off origin l st =
  match l with
  | [] -> st
  | p :: rest ->
    let (k, x) = p in
    (match rest with
     | [] ->
       iscan_str_located t h (allow_attrs t off) k origin (String.length x)
         (strip_trailing_ws x) st
     | _ :: _ ->
       iscan_lines_located t h (pred off) origin rest
         (ibreak_at t { tnil = ""; tpush = (^); tof = (fun s -> s); tval =
           (fun t0 -> t0); tnonempty = nonempty_str } h { cursor_start =
           { spot_line = k; spot_rem = 0 }; cursor_stop = (lines_start rest);
           cursor_origin = { spot_line = k; spot_rem = (String.length x) } }
           (allow_attrs t off)
           (iscan_str_located t h (allow_attrs t off) k origin
             (String.length x) x st)))

(** val ifinish_located :
    dtable -> coq_PosPolicy -> (int * string) list -> string iscan_g ->
    inlines **)

let ifinish_located t h l st =
  ifinish t { tnil = ""; tpush = (^); tof = (fun s -> s); tval = (fun t0 ->
    t0); tnonempty = nonempty_str } h { cursor_start = (lines_stop l);
    cursor_stop = (lines_stop l); cursor_origin = (lines_start l) } st

(** val para_inlines_located :
    dtable -> coq_PosPolicy -> int -> (int * string) list -> inlines **)

let para_inlines_located t h off l =
  ifinish_located t h l (iscan_lines_located t h off (lines_start l) l istart)

(** val para_inlines_at :
    dtable -> coq_PosPolicy -> int -> (int * string) list -> inlines **)

let para_inlines_at t h off l =
  if h.pos_records
  then para_inlines_located t h off l
  else para_inlines_off t off (map snd l)

(** val parse_inline_line_located :
    dtable -> coq_PosPolicy -> int -> int -> string -> inlines **)

let parse_inline_line_located t h k rem s =
  let stop = { spot_line = k; spot_rem = (sub rem (String.length s)) } in
  ifinish t { tnil = ""; tpush = (^); tof = (fun s0 -> s0); tval = (fun t0 ->
    t0); tnonempty = nonempty_str } h { cursor_start = stop; cursor_stop =
    stop; cursor_origin = { spot_line = k; spot_rem = rem } }
    (iscan_str_located t h (inline_attrs_enabled t) k { spot_line = k;
      spot_rem = rem } rem s istart)
