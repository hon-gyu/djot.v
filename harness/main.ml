(* ai-disclosure: autonomous *)

(* Differential test harness: runs corpus cases through the extracted
   Gallina parser and the two oracles (djot.js, djoths), and reports
   agreement per engine and per case.

   Usage:
     main [--engines gallina,djotjs,djoths] [--baseline] [--generated]
          [--shape] [--roundtrip [DEPTH]] [--keyed-roundtrip [DEPTH]] [--report FILE] [--verbose]
          [TEST_FILES...]

   With no files, runs the whole djot.js corpus.  --baseline compares the
   two oracles against each other (and against expected output), ignoring
   the Gallina parser — used to seed .project/oracle-disagreements.md.
   --generated runs the enumerated corpus instead of the file corpus,
   engine against engine; see "Generated mode" below.
   --shape compares block structure only; see "Block shape" below.
   --roundtrip checks `parse (render d) = d` over the enumerated
   documents and consults no oracle at all; see "Roundtrip" below. *)

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

(* Length-delimited framing, for engines that can take a whole batch in
   one process.  Byte lengths rather than a separator: a djot document may
   contain any bytes, so no sentinel is safe. *)
let frame docs =
  let buf = Buffer.create 4096 in
  List.iter
    (fun d ->
      Buffer.add_string buf (string_of_int (String.length d));
      Buffer.add_char buf '\n';
      Buffer.add_string buf d)
    docs;
  Buffer.contents buf

let unframe s =
  let n = String.length s in
  let rec go acc at =
    if at >= n then List.rev acc
    else
      match String.index_from_opt s at '\n' with
      | None -> List.rev acc
      | Some nl ->
        let len = int_of_string (String.sub s at (nl - at)) in
        let start = nl + 1 in
        go (String.sub s start len :: acc) (start + len)
  in
  go [] 0

type engine = {
  ename : string;
  run : string -> (string, string) result;
  (* whole batch in one process, when the engine supports it; the fallback
     is one process per document, which node startup makes untenable at
     corpus scale *)
  run_batch : (string list -> (string, string) result list) option;
}

let gallina =
  { ename = "gallina";
    run = (fun s -> Ok (Core.convert s));
    run_batch = None }

let djotjs =
  let script = root / "harness" / "oracles" / "djotjs.mjs" in
  { ename = "djotjs";
    run = (fun s -> run_process [| "node"; script |] s);
    run_batch =
      Some
        (fun docs ->
          match run_process [| "node"; script; "--batch" |] (frame docs) with
          | Error e -> List.map (fun _ -> Error e) docs
          | Ok out ->
            let outs = unframe out in
            if List.length outs <> List.length docs then
              List.map
                (fun _ ->
                  Error
                    (Printf.sprintf "batch returned %d of %d"
                       (List.length outs) (List.length docs)))
                docs
            else List.map (fun o -> Ok o) outs) }

let djoths_bin = ref ""

let djoths =
  { ename = "djoths";
    run = (fun s -> run_process [| !djoths_bin |] s);
    run_batch = None }

let run_all e docs =
  match e.run_batch with
  | Some f -> f docs
  | None -> List.map e.run docs

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

(*
Generated mode
==============

The corpus compares each engine against a recorded expected output.  A
generated document has none: it comes from `Generate.enum_cblock` via the
renderer, so the only available judgement is engine against engine.  The
reference is djot.js — the corpus is its test suite, so it is the
implementation we are conforming to.

Why this exists at all: `roundtrip_blocks` is a meta-property, and cannot
catch a rule we got wrong in both the parser and the renderer.  Every
shape the fragment admits is checked here against something we did not
write.

Exact HTML by default, not `--shape`.  Measured on 2026-08-09: gallina
and djot.js agree byte-for-byte on these documents, because the
enumerator's inline content is single words, so the empty inline layer
that forces `--shape` on the real corpus does not bite here.  `--shape`
still applies if given, but reaching for it would drop the field under
test. *)

let run_generated engines docs rbuf verbose =
  let out fmt =
    Printf.ksprintf (fun s -> print_string s; Buffer.add_string rbuf s) fmt
  in
  let reference =
    match List.find_opt (fun e -> e.ename = "djotjs") engines with
    | Some e -> e
    | None -> List.hd engines
  in
  let subjects = List.filter (fun e -> e.ename <> reference.ename) engines in
  if subjects = [] then begin
    out "--generated needs an engine to compare against %s\n" reference.ename;
    exit 2
  end;
  let proj s = if !shape_mode then shape s else normalize s in
  let ref_out = Array.of_list (run_all reference docs) in
  let docs_a = Array.of_list docs in
  let total = Array.length docs_a in
  let stats = Hashtbl.create 4 in
  List.iter
    (fun e ->
      let outs = Array.of_list (run_all e docs) in
      let m = ref 0 and mm = ref 0 and er = ref 0 in
      Array.iteri
        (fun i o ->
          match (o, ref_out.(i)) with
          | Error msg, _ ->
            incr er;
            if !verbose then out "\n--- doc %d: %s ERROR %s\n" i e.ename msg
          | _, Error msg ->
            incr er;
            if !verbose then
              out "\n--- doc %d: %s ERROR %s\n" i reference.ename msg
          | Ok a, Ok b ->
            if proj a = proj b then incr m
            else begin
              incr mm;
              if !verbose then begin
                out "\n--- doc %d\n" i;
                out "input:\n%s\n" docs_a.(i);
                out "%s:\n%s\n" reference.ename b;
                out "%s:\n%s\n" e.ename a
              end
            end)
        outs;
      Hashtbl.replace stats e.ename (!m, !mm, !er))
    subjects;
  out "\n== generated: %d documents, reference %s%s ==\n" total reference.ename
    (if !shape_mode then ", block shape only" else ", exact HTML");
  List.iter
    (fun e ->
      let m, mm, er =
        try Hashtbl.find stats e.ename with Not_found -> (0, 0, 0)
      in
      out "%-8s  match %4d   mismatch %4d   error %4d\n" e.ename m mm er)
    subjects;
  let any_err =
    Hashtbl.fold (fun _ (_, _, e) acc -> acc || e > 0) stats false
  in
  any_err

(*
Roundtrip
---------

`parse (render d) = d` over every canonical document the enumerator
accepts, which is the statement `Generate.gen_roundtrip_1` and
`gen_roundtrip_2` prove in the kernel at depths 1 and 2.  Depth 3 used to
be `check/Deep.v` and cost ~20 minutes, because the kernel evaluates the
whole sweep and then evaluates it again to check the proof term.  Here it
is ~5 seconds, on the same extracted parser every other mode runs.

What that trades away is the kernel's certification of the computation.
It buys back the only thing certification was for: nothing depends on
`gen_roundtrip_3` -- it is an `Example`, not a lemma -- and every other
piece of evidence this harness produces already rides on the extraction.
The depths the kernel does certify, 1 and 2, stay where they are.

`expected_counts` is the coverage witness `Deep.v`'s `accepted_counts`
was: the fragment must grow when a construct lands, and a *shrinking*
count is a regression that zero mismatches would not show.  Update the
line when the fragment legitimately grows, exactly as before. *)

let expected_counts = [ (1, 296); (2, 3695); (3, 43857) ]

(* Same witness for the keyed pool, which no oracle covers: the only
   evidence a key generator still reaches keys is the count. *)
let keyed_expected_counts = [ (1, 6628); (2, 81536) ]

let rec nat_of_int n = if n <= 0 then Core.O else Core.S (nat_of_int (n - 1))

let run_roundtrip ~keyed depth rbuf verbose =
  let out fmt =
    Printf.ksprintf (fun s -> print_string s; Buffer.add_string rbuf s) fmt
  in
  let t0 = Unix.gettimeofday () in
  let accepted, lhs, counts =
    if keyed then Core.keyed_accepted, Core.keyed_rt_lhs, keyed_expected_counts
    else Core.accepted, Core.rt_lhs, expected_counts
  in
  let docs = accepted (nat_of_int depth) in
  let t1 = Unix.gettimeofday () in
  let total = ref 0 and bad = ref 0 in
  List.iter
    (fun c ->
      incr total;
      if lhs c <> Core.rt_rhs c then begin
        incr bad;
        if !verbose || !bad <= 5 then
          out "\n--- roundtrip mismatch %d\n%s\n" !bad (Core.render_cb c)
      end)
    docs;
  let t2 = Unix.gettimeofday () in
  out "\n== %sroundtrip: depth %d, %d documents, %.2fs enumerate, %.2fs check ==\n"
    (if keyed then "keyed " else "") depth !total (t1 -. t0) (t2 -. t1);
  out "parse (render d) = d   ok %6d   mismatch %4d\n" (!total - !bad) !bad;
  let count_ok =
    match List.assoc_opt depth counts with
    | None -> out "(no pinned count for depth %d)\n" depth; true
    | Some n when n = !total -> true
    | Some n ->
      out "COUNT MOVED: expected %d accepted at depth %d, got %d\n" n depth
        !total;
      false
  in
  (!bad = 0) && count_ok

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
  let generated = ref false in
  let roundtrip = ref None in
  let keyed_roundtrip = ref false in
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
    | "--generated" :: rest -> generated := true; parse_args rest
    | "--keyed-roundtrip" :: d :: rest when int_of_string_opt d <> None ->
      keyed_roundtrip := true; roundtrip := Some (int_of_string d); parse_args rest
    | "--keyed-roundtrip" :: rest ->
      keyed_roundtrip := true; roundtrip := Some 1; parse_args rest
    | "--roundtrip" :: d :: rest when int_of_string_opt d <> None ->
      roundtrip := Some (int_of_string d);
      parse_args rest
    | "--roundtrip" :: rest -> roundtrip := Some 3; parse_args rest
    | f :: rest -> files := f :: !files; parse_args rest
  in
  parse_args (List.tl (Array.to_list Sys.argv));
  if List.exists (fun e -> e.ename = "djoths") !engines then find_djoths ();
  let files = if !files = [] then default_files () else List.rev !files in
  let rbuf = Buffer.create 4096 in
  let out fmt = Printf.ksprintf (fun s ->
    print_string s; Buffer.add_string rbuf s) fmt
  in
  let finish_report () =
    if !report <> "" then begin
      let oc = open_out !report in
      output_string oc (Buffer.contents rbuf);
      close_out oc
    end
  in
  (* the roundtrip consults no oracle and reads no corpus file, so it
     answers before either is touched *)
  (match !roundtrip with
   | Some depth ->
     let ok = run_roundtrip ~keyed:!keyed_roundtrip depth rbuf verbose in
     finish_report ();
     exit (if ok then 0 else 1)
   | None -> ());
  if !generated then begin
    let any_err = run_generated !engines Core.generated rbuf verbose in
    finish_report ();
    exit (if any_err then 1 else 0)
  end;
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
  (* All cases up front, then each engine over the whole list: the batched
     engines get one process for the run instead of one per case. *)
  let all_cases =
    List.concat_map (fun file -> Corpus.parse_file file) files
  in
  let cases =
    List.filter
      (fun (c : Corpus.case) ->
        if c.options <> "" then (incr grand_skip; false) else true)
      all_cases
  in
  grand_total := List.length cases;
  let cases_a = Array.of_list cases in
  let outs =
    List.map
      (fun e -> (e, Array.of_list (run_all e (List.map (fun (c : Corpus.case) -> c.input) cases))))
      !engines
  in
  Array.iteri
    (fun i (c : Corpus.case) ->
      let proj s = if !shape_mode then shape s else normalize s in
      let results =
        List.map
          (fun (e, o) ->
            ( e.ename,
              match o.(i) with
              | Error msg -> EngineError msg
              | Ok out ->
                if proj out = proj c.expected then Match else Mismatch out ))
          outs
      in
      let bad = List.filter (fun (_, r) -> r <> Match) results in
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
      end)
    cases_a;
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
  finish_report ();
  (* exit code: nonzero only when a selected engine errored, not on
     mismatches — mismatch is data at this stage, not failure *)
  let any_err =
    Hashtbl.fold (fun _ (_, _, e) acc -> acc || e > 0) stats false
  in
  exit (if any_err then 1 else 0)
