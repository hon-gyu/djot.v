(* ai-disclosure: ai-generated *)

(* Turning holes on only turns code spans into holes, on random
   paragraphs over the bytes that matter to them.

   Usage:
     holes [N] [--seed S] [--verbose]

   Each paragraph is parsed with holes on and off, under several tables.
   The holes-on parse, with every hole put back as the `%` and code span
   it was read from and adjacent text merged, must equal the holes-off
   parse.  The one exception is a hole followed by `{`: as after math,
   that brace cannot open a raw format, so the bytes after it are read as
   an attribute, where after a code span they are read as a raw spec
   first (`.project/261009.plan.backtick-holes.md`, E5).  The two differ
   on `{=html}`, and inside a failed attribute spec on what the brace's
   slice ends.  The other is a hole in a collapsed reference's text: the
   label is read from the text, where a hole contributes its expression
   and its source `%` too (E13).  Such paragraphs are counted and
   skipped.  N paragraphs per table (default 20000).  Exits
   nonzero on a difference and prints the first few, shrunk. *)

module S = Djot.InlineScan
open Djot.Ast

let string_text =
  { S.tnil = ""; tpush = ( ^ ); tof = (fun s -> s); tval = (fun s -> s);
    tnonempty = (fun s -> s <> "") }

let pieces =
  [| "%"; "%`"; "`"; "``"; "{"; "}"; "{.c}"; "{=html}"; "\\"; "\\%"; "a"; "b";
     " "; "$"; "*"; "_"; "["; "]"; "("; ")"; "]("; "<"; ">"; ":"; "\""; "'";
     "="; "-"; "."; "!"; "^"; "#"; "{k=\""; "%{"; "[a]("; ":a:" |]

let gen_line () =
  let n = Random.int 20 in
  String.concat "" (List.init n (fun _ -> pieces.(Random.int (Array.length pieces))))

let gen_para () = List.init (1 + Random.int 3) (fun _ -> gen_line ())

(* A hole back as its source's reading with holes off, then adjacent
   text merged. *)
let rec unhole (ns : inlines) : inlines =
  let one (Node (p, a, x)) =
    let k ns = [ Node (p, a, ns) ] in
    match x with
    | Hole s -> [ Node (p, [], Str "%"); Node (p, a, Verbatim s) ]
    | Emph c -> k (Emph (unhole c))
    | Strong c -> k (Strong (unhole c))
    | Highlight c -> k (Highlight (unhole c))
    | Insert c -> k (Insert (unhole c))
    | Delete c -> k (Delete (unhole c))
    | Superscript c -> k (Superscript (unhole c))
    | Subscript c -> k (Subscript (unhole c))
    | Link (c, t) -> k (Link (unhole c, t))
    | Image (c, t) -> k (Image (unhole c, t))
    | Span (n, c) -> k (Span (n, unhole c))
    | Quoted (q, c) -> k (Quoted (q, unhole c))
    | _ -> k x
  in
  let rec merge = function
    | Node (p, [], Str a) :: Node (_, [], Str b) :: rest ->
        merge (Node (p, [], Str (a ^ b)) :: rest)
    | n :: rest -> n :: merge rest
    | [] -> []
  in
  merge (List.concat_map one ns)

let parse t k l =
  S.ifinish t string_text semantic_pos semantic_inline_cursor
    (S.iscan_lines_off t k l S.istart)

(* Whether the holes-on parse has a hole where the two may differ: one
   followed by `{`, read off the located parse as the byte after the
   hole's span, or one in a reference link's text, which a collapsed
   reference reads its label from (E13). *)
let hole_unstable on k l =
  let lines = Array.of_list l in
  let ll = List.mapi (fun i s -> (i, s)) l in
  let rec has_hole (ns : inlines) =
    List.exists
      (fun (Node (_, _, x)) ->
         match x with
         | Hole _ -> true
         | Emph c | Strong c | Highlight c | Insert c | Delete c | Superscript c
         | Subscript c | Link (c, _) | Image (c, _) | Span (_, c) | Quoted (_, c) ->
             has_hole c
         | _ -> false)
      ns
  in
  let rec any (ns : inlines) =
    List.exists
      (fun (Node (p, _, x)) ->
         match x with
         | (Link (c, Reference _) | Image (c, Reference _)) when has_hole c -> true
         | Hole _ -> (
             match p with
             | SomePos pr ->
                 let stop = pr.node_span.span_stop in
                 let s = lines.(stop.spot_line) in
                 let i = String.length s - stop.spot_rem in
                 i < String.length s && s.[i] = '{'
             | NoPos -> false)
         | Emph c | Strong c | Highlight c | Insert c | Delete c | Superscript c
         | Subscript c | Link (c, _) | Image (c, _) | Span (_, c) | Quoted (_, c) ->
             any c
         | _ -> false)
      ns
  in
  any (Djot.InlineLocated.para_inlines_located_stk on located_pos k ll)

(* Delete bytes while the paragraph still differs. *)
let differs on off k l =
  (not (hole_unstable on k l)) && unhole (parse on k l) <> parse off k l

let shrink on off k l =
  let rec go l =
    let cands =
      List.concat
        (List.mapi
           (fun i s ->
              List.init (String.length s) (fun j ->
                  List.mapi
                    (fun i' s' ->
                       if i' = i then String.sub s' 0 j ^ String.sub s' (j + 1) (String.length s' - j - 1)
                       else s')
                    l))
           l)
      @ List.mapi (fun i _ -> List.filteri (fun i' _ -> i' <> i) l) l
    in
    match List.find_opt (fun c -> c <> [] && differs on off k c) cands with
    | Some c -> go c
    | None -> l
  in
  go l

let rec show (ns : inlines) =
  String.concat " "
    (List.map
       (fun (Node (_, a, x)) ->
          let at = if a = [] then "" else "{" ^ String.concat "," (List.map (fun (k, v) -> k ^ "=" ^ v) a) ^ "}" in
          let c n l = n ^ "[" ^ show l ^ "]" in
          at ^
          match x with
          | Str s -> Printf.sprintf "%S" s
          | Verbatim s -> Printf.sprintf "V%S" s
          | Hole s -> Printf.sprintf "H%S" s
          | Math (_, s) -> Printf.sprintf "M%S" s
          | RawInline (f, s) -> Printf.sprintf "R%s%S" f s
          | Emph l -> c "E" l | Strong l -> c "S" l | Span (_, l) -> c "Sp" l
          | Link (l, _) -> c "L" l | Image (l, _) -> c "I" l | Quoted (_, l) -> c "Q" l
          | Highlight l -> c "Hi" l | Insert l -> c "Ins" l | Delete l -> c "Del" l
          | Superscript l -> c "Sup" l | Subscript l -> c "Sub" l
          | SoftBreak -> "SB" | HardBreak -> "HB" | _ -> "?")
       ns)

let base = Djot.Inline.djot_table

let tables =
  [ "djot", base;
    "dollar", { base with Djot.InlineTable.dc_dollar_math = true };
    "attrs off", { base with Djot.InlineTable.dc_attrs = false } ]

let () =
  let n = ref 20000 and seed = ref 7 and verbose = ref false in
  let rec args = function
    | [] -> ()
    | "--seed" :: v :: rest -> seed := int_of_string v; args rest
    | "--verbose" :: rest -> verbose := true; args rest
    | v :: rest -> n := int_of_string v; args rest
  in
  args (List.tl (Array.to_list Sys.argv));
  Random.init !seed;
  let bad = ref 0 and skipped = ref 0 in
  List.iter
    (fun (name, off) ->
       let on = { off with Djot.InlineTable.dc_holes = true } in
       for _ = 1 to !n do
         let l = gen_para () in
         let k = Random.int 2 in
         if hole_unstable on k l then incr skipped
         else if differs on off k l then begin
           incr bad;
           if !bad <= 8 || !verbose then
             Printf.printf "--- %s, off %d:\n%s\n" name k
               (let l = shrink on off k l in
                String.concat "\n" (List.map (fun s -> Printf.sprintf "  %S" s) l)
                ^ "\n  on:  " ^ show (parse on k l) ^ "\n  off: " ^ show (parse off k l))
         end
       done)
    tables;
  Printf.printf
    "holes against no holes: %d paragraphs x %d tables, %d skipped (a hole before `{` or in a reference), %d differ\n"
    !n (List.length tables) !skipped !bad;
  if !bad > 0 then exit 1
