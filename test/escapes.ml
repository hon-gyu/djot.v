(* ai-disclosure: autonomous *)

(* Which of the canonical renderer's escapes does the parse need?

   For every document of `Generate.escape_accepted`, delete each backslash
   of its rendering in turn, and each pair of an opening and a closing
   brace, and parse what is left.  A deletion that leaves the parse
   unchanged is an escape the renderer could have left out.  They are
   counted by the character escaped, or by the delimiter braced.

   Usage:
     escapes [--report FILE] [--verbose]

   The pinned count is the distance to a renderer with no redundant
   escape.  It may only go down: lower it when a relaxation lands. *)

open Djot_test

let pinned = 1668

let delete s i = String.sub s 0 i ^ String.sub s (i + 1) (String.length s - i - 1)

(* A neighbouring byte, as far as an escaping rule could tell them apart:
   a line's edge, a space, a word character, or the punctuation itself. *)
let kind s i =
  if i < 0 || i >= String.length s || s.[i] = '\n' then "|"
  else
    match s.[i] with
    | ' ' -> "_"
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> "w"
    | c -> String.make 1 c

(* The deletions of [s] that parse as [s] does, each with its class: the
   byte before the escape, the escaped character, the byte after it. *)
let redundant parse s =
  let ast = parse s and n = String.length s and found = ref [] in
  let try_ cls s' =
    if parse s' = ast && not (List.exists (fun (_, t) -> t = s') !found) then
      found := (cls, s') :: !found
  in
  for i = 0 to n - 1 do
    match s.[i] with
    | '\\' when i + 1 < n ->
      try_
        (Printf.sprintf "%s \\%s %s" (kind s (i - 1)) (kind s (i + 1))
           (kind s (i + 2)))
        (delete s i)
    | '{' when i + 1 < n ->
      for j = i + 2 to n - 1 do
        if s.[j] = '}' then
          try_
            (Printf.sprintf "%s {%c %c} %s" (kind s (i - 1)) s.[i + 1]
               s.[j - 1] (kind s (j + 1)))
            (delete (delete s j) i)
      done
    | _ -> ()
  done;
  List.rev !found

let () =
  let report = ref "" and verbose = ref false in
  let rec args = function
    | [] -> ()
    | "--report" :: v :: rest -> report := v; args rest
    | "--verbose" :: rest -> verbose := true; args rest
    | a :: _ -> prerr_endline ("escapes: unknown argument " ^ a); exit 2
  in
  args (List.tl (Array.to_list Sys.argv));
  let r = Report.create !report in
  let module G = Djot_fixtures.Generate in
  let docs = G.escape_accepted in
  let classes = Hashtbl.create 64 and total = ref 0 in
  List.iter
    (fun c ->
      let s = G.rt_src c in
      List.iter
        (fun (cls, s') ->
          incr total;
          let n, examples =
            Option.value (Hashtbl.find_opt classes cls) ~default:(0, [])
          in
          Hashtbl.replace classes cls (n + 1, (s, s') :: examples))
        (redundant G.rt_parse s))
    docs;
  Report.out r "\n== escapes: %d documents, %d redundant ==\n" (List.length docs)
    !total;
  Hashtbl.fold (fun cls v acc -> (cls, v) :: acc) classes []
  |> List.sort (fun (_, (a, _)) (_, (b, _)) -> compare b a)
  |> List.iter (fun (cls, (n, examples)) ->
         let examples = List.rev examples in
         let shown = if !verbose then examples else [ List.hd examples ] in
         Report.out r "%-12s %5d\n" cls n;
         List.iter
           (fun (s, s') ->
             Report.out r "    %s  =>  %s\n" (String.escaped (String.trim s))
               (String.escaped (String.trim s')))
           shown);
  let ok = !total <= pinned in
  if not ok then
    Report.out r "COUNT ROSE: at most %d redundant escapes expected, got %d\n"
      pinned !total;
  Report.save r;
  exit (if ok then 0 else 1)
