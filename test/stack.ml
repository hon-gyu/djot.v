(* ai-disclosure: autonomous *)

(* The candidate stack against the specification scan, on random
   paragraphs over the bytes the stack is about.

   Usage:
     stack [N] [--seed S] [--verbose]

   `InlineStack.v` proves the stacked scan equal to the specification
   one, but the extraction runs neither as written: both line drivers
   are native loops (`Extract.v`).  This compares the two as extracted,
   semantic and located, under tables with holes, dollar math and
   attributes on and off, and with leading lines read with attributes
   off.  N paragraphs per table (default 20000).  Exits nonzero on a
   difference and prints the first few. *)

module S = Djot.InlineScan
module L = Djot.InlineLocated

let string_text =
  { S.tnil = ""; tpush = ( ^ ); tof = (fun s -> s); tval = (fun s -> s);
    tnonempty = (fun s -> s <> "") }

(* Openers, closers and the escapes and candidates around them, with a
   few letters so that runs exist. *)
let pieces =
  [| "["; "]"; "("; ")"; "]("; "%"; "%{"; "{"; "}"; "\\"; "a"; "b"; " ";
     "$"; "`"; "<"; ":"; "*"; "_"; "!"; "^"; "\""; "="; "."; "#"; "-";
     "[a]("; "{.c}"; "{k=\""; ":a:"; "$`x`"; "\\("; "\\)"; "\\{"; "\\}" |]

let gen_line () =
  let n = Random.int 24 in
  String.concat "" (List.init n (fun _ -> pieces.(Random.int (Array.length pieces))))

let gen_para () = List.init (1 + Random.int 4) (fun _ -> gen_line ())

let base = Djot.Inline.djot_table

let tables =
  [ "djot", base;
    "holes", { base with Djot.InlineTable.dc_holes = true };
    "holes+dollar", { base with Djot.InlineTable.dc_holes = true; dc_dollar_math = true };
    "holes, attrs off", { base with Djot.InlineTable.dc_holes = true; dc_attrs = false } ]

let spec_semantic t k l =
  S.ifinish t string_text Djot.Ast.semantic_pos Djot.Ast.semantic_inline_cursor
    (S.iscan_lines_off t k l S.istart)

let spec_located t off l =
  let h = Djot.Ast.located_pos in
  L.ifinish_located t h l (L.iscan_lines_located t h off (L.lines_start l) l S.istart)

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
  let bad = ref 0 in
  let report name t k l =
    incr bad;
    if !bad <= 5 then
      Printf.printf "--- %s, off %d:\n%s\n" name k
        (String.concat "\n" (List.map (fun s -> Printf.sprintf "  %S" s) l))
  in
  List.iter
    (fun (name, t) ->
       for _ = 1 to !n do
         let l = gen_para () in
         let k = Random.int 3 in
         if S.para_inlines_off_stk t k l <> spec_semantic t k l then
           report (name ^ ", semantic") t k l;
         let ll = List.mapi (fun i s -> (i, s)) l in
         if L.para_inlines_located_stk t Djot.Ast.located_pos k ll
            <> spec_located t k ll then
           report (name ^ ", located") t k l
       done;
       if !verbose then Printf.printf "%s: done\n%!" name)
    tables;
  Printf.printf "stack against specification: %d paragraphs x %d tables, %d differ\n"
    !n (List.length tables) !bad;
  exit (if !bad = 0 then 0 else 1)
