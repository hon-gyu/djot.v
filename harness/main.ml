(* Differential test harness: runs corpus cases through the extracted
   Gallina parser and the two oracles (djot.js, djoths), and reports
   agreement per engine and per case.

   Usage:
     main [--engines gallina,djotjs,djoths] [--baseline] [--shape]
          [--report FILE] [--verbose] [TEST_FILES...]

   With no files, runs the whole djot.js corpus.  --baseline compares the
   two oracles against each other (and against expected output), ignoring
   the Gallina parser — used to seed .project/oracle-disagreements.md.
   --shape compares block structure only; see "Block shape" below. *)

let root =
  (* harness runs from _build/default/harness; walk up to the repo root *)
  let rec find dir =
    if Sys.file_exists (Filename.concat dir "dune-project")
       && Sys.file_exists (Filename.concat dir "djot.js")
    then dir
    else
      let parent = Filename.dirname dir in
      if parent = dir then failwith "repo root not found" else find parent
  in
  find (Sys.getcwd ())

let ( / ) = Filename.concat

(*
Engines
=======
*)

(* stdin via a temp file rather than a pipe: no write/read interleaving,
   no deadlock risk regardless of input size *)
let run_process argv input =
  let tmp = Filename.temp_file "djotv" ".in" in
  let oc = open_out_bin tmp in
  output_string oc input;
  close_out oc;
  let fd_in = Unix.openfile tmp [ Unix.O_RDONLY ] 0 in
  let stdout_r, stdout_w = Unix.pipe () in
  let pid = Unix.create_process argv.(0) argv fd_in stdout_w Unix.stderr in
  Unix.close fd_in;
  Unix.close stdout_w;
  let ic = Unix.in_channel_of_descr stdout_r in
  let buf = Buffer.create 1024 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  close_in ic;
  let _, status = Unix.waitpid [] pid in
  Sys.remove tmp;
  match status with
  | Unix.WEXITED 0 -> Ok (Buffer.contents buf)
  | Unix.WEXITED n -> Error (Printf.sprintf "exit %d" n)
  | _ -> Error "killed"

type engine = { ename : string; run : string -> (string, string) result }

let gallina = { ename = "gallina"; run = (fun s -> Ok (Core.convert s)) }

let djotjs =
  let script = root / "harness" / "oracles" / "djotjs.mjs" in
  { ename = "djotjs"; run = (fun s -> run_process [| "node"; script |] s) }

let djoths_bin = ref ""

let djoths =
  { ename = "djoths"; run = (fun s -> run_process [| !djoths_bin |] s) }

let find_djoths () =
  if !djoths_bin = "" then begin
    match Sys.getenv_opt "DJOTHS_BIN" with
    | Some p -> djoths_bin := p
    | None ->
      let ic =
        Unix.open_process_in
          (Printf.sprintf "cd %s && cabal list-bin exe:djoths 2>/dev/null"
             (Filename.quote (root / "djoths")))
      in
      let line = try input_line ic with End_of_file -> "" in
      ignore (Unix.close_process_in ic);
      if line = "" then failwith "djoths binary not found; run: make oracles";
      djoths_bin := line
  end

(*
Runner
======
*)

(*
Block shape
===========

Structure only: keep the block-level tags, drop everything inline.

Why it exists: inline parsing is Phase 3, so most corpus cases mismatch on
inline content alone.  An exact-HTML diff therefore cannot tell a genuine
container bug from that expected noise — which is how the nested-list bug
in .project/oracle-disagreements.md (2026-08-08) survived: its shape is
absent from the corpus, and would have been invisible in the aggregate
even if present.  Comparing shapes makes the block layer legible while
the inline layer is still empty, and is the Phase 2 exit criterion
("inline content compared as raw text at this stage") brought forward.

Derived from each engine's HTML rather than its AST, so all three engines
are compared on the same footing with no changes to any of them.  The
cost is that a construct our renderer stubs out (OrderedList, tables)
reads as a shape difference — which is honest: we do not render it. *)

let block_tags =
  [ "p"; "h1"; "h2"; "h3"; "h4"; "h5"; "h6"; "hr"; "blockquote"; "ul"; "ol";
    "li"; "pre"; "section"; "dl"; "dt"; "dd"; "table"; "tr"; "td"; "th" ]

let shape html =
  let buf = Buffer.create 256 in
  let n = String.length html in
  let i = ref 0 in
  while !i < n do
    if html.[!i] = '<' then begin
      let j = match String.index_from_opt html !i '>' with
        | Some j -> j
        | None -> n - 1
      in
      let raw = String.sub html (!i + 1) (j - !i - 1) in
      let closing = String.length raw > 0 && raw.[0] = '/' in
      let raw =
        if closing then String.sub raw 1 (String.length raw - 1) else raw
      in
      let name =
        match String.index_opt raw ' ' with
        | Some k -> String.sub raw 0 k
        | None -> raw
      in
      let name = String.lowercase_ascii (String.trim name) in
      let name =
        (* <hr />, <br /> *)
        if String.length name > 0 && name.[String.length name - 1] = '/'
        then String.sub name 0 (String.length name - 1)
        else name
      in
      if List.mem name block_tags then
        Buffer.add_string buf
          (if closing then "</" ^ name ^ ">" else "<" ^ name ^ ">");
      i := j + 1
    end
    else incr i
  done;
  Buffer.contents buf

let shape_mode = ref false

let normalize s =
  (* compare modulo trailing newlines *)
  let n = String.length s in
  let rec last i = if i > 0 && s.[i - 1] = '\n' then last (i - 1) else i in
  String.sub s 0 (last n)

type outcome = Match | Mismatch of string | EngineError of string

let run_case engine (c : Corpus.case) =
  match engine.run c.input with
  | Error e -> EngineError e
  | Ok out ->
    let proj s = if !shape_mode then shape s else normalize s in
    if proj out = proj c.expected then Match else Mismatch out

let default_files () =
  let dir = root / "djot.js" / "test" in
  Sys.readdir dir |> Array.to_list
  |> List.filter (fun f -> Filename.check_suffix f ".test")
  |> List.sort compare
  |> List.map (fun f -> dir / f)

let () =
  let engines = ref [ gallina; djotjs; djoths ] in
  let files = ref [] in
  let report = ref "" in
  let verbose = ref false in
  let baseline = ref false in
  let rec parse_args = function
    | [] -> ()
    | "--engines" :: v :: rest ->
      let sel = String.split_on_char ',' v in
      engines :=
        List.filter (fun e -> List.mem e.ename sel) [ gallina; djotjs; djoths ];
      parse_args rest
    | "--baseline" :: rest ->
      baseline := true;
      engines := [ djotjs; djoths ];
      parse_args rest
    | "--report" :: v :: rest -> report := v; parse_args rest
    | "--shape" :: rest -> shape_mode := true; parse_args rest
    | "--verbose" :: rest -> verbose := true; parse_args rest
    | f :: rest -> files := f :: !files; parse_args rest
  in
  parse_args (List.tl (Array.to_list Sys.argv));
  if List.exists (fun e -> e.ename = "djoths") !engines then find_djoths ();
  let files = if !files = [] then default_files () else List.rev !files in
  let rbuf = Buffer.create 4096 in
  let out fmt = Printf.ksprintf (fun s ->
    print_string s; Buffer.add_string rbuf s) fmt
  in
  let grand_total = ref 0 and grand_skip = ref 0 in
  let stats = Hashtbl.create 8 in  (* ename -> (match, mismatch, error) *)
  let bump ename slot =
    let m, mm, e = try Hashtbl.find stats ename with Not_found -> (0, 0, 0) in
    Hashtbl.replace stats ename
      (match slot with
       | `M -> (m + 1, mm, e)
       | `MM -> (m, mm + 1, e)
       | `E -> (m, mm, e + 1))
  in
  List.iter
    (fun file ->
      let cases = Corpus.parse_file file in
      List.iter
        (fun (c : Corpus.case) ->
          if c.options <> "" then incr grand_skip
          else begin
            incr grand_total;
            let results =
              List.map (fun e -> (e.ename, run_case e c)) !engines
            in
            let bad =
              List.filter (fun (_, r) -> r <> Match) results
            in
            List.iter
              (fun (n, r) ->
                bump n
                  (match r with
                   | Match -> `M
                   | Mismatch _ -> `MM
                   | EngineError _ -> `E))
              results;
            if bad <> [] && !verbose then begin
              out "\n--- %s:%d\n" (Filename.basename c.file) c.linenum;
              out "input:\n%s" c.input;
              out "expected:\n%s" c.expected;
              List.iter
                (fun (n, r) ->
                  match r with
                  | Match -> ()
                  | Mismatch o -> out "%s:\n%s" n o
                  | EngineError e -> out "%s: ERROR %s\n" n e)
                bad
            end
          end)
        cases)
    files;
  out "\n== summary: %d cases run, %d skipped (options) ==\n" !grand_total
    !grand_skip;
  List.iter
    (fun e ->
      let m, mm, er =
        try Hashtbl.find stats e.ename with Not_found -> (0, 0, 0)
      in
      out "%-8s  match %4d   mismatch %4d   error %4d\n" e.ename m mm er)
    !engines;
  if !baseline then
    out "(baseline mode: mismatches are oracle-vs-expected disagreements)\n";
  if !report <> "" then begin
    let oc = open_out !report in
    output_string oc (Buffer.contents rbuf);
    close_out oc
  end;
  (* exit code: nonzero only when a selected engine errored, not on
     mismatches — mismatch is data at this stage, not failure *)
  let any_err =
    Hashtbl.fold (fun _ (_, _, e) acc -> acc || e > 0) stats false
  in
  exit (if any_err then 1 else 0)
