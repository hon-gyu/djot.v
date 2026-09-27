(* ai-disclosure: autonomous *)

(* Compares the extracted parser's HTML with the djot.js test suite's
   expected HTML, or with djot.js's own on generated documents.

   Usage:
     diff [--generated] [--shape] [--subject CMD] [--report FILE] [--verbose]
          [TEST_FILES...]

   With no files, runs the whole djot.js test suite.  `--subject` tests
   the program CMD, run as `CMD --batch`, in place of the extracted
   parser linked in here.  Exit status is nonzero only when a parser
   errored: a mismatch is data, not failure. *)

open Djot_test
open Parsers

(*
Block shape
===========

Structure only: keep the block-level tags, drop everything inline.

An exact-HTML diff mixes block and inline differences, so a container
bug can be lost among inline mismatches; comparing shapes isolates the
block layer.  Derived from HTML rather than an AST, so the expected
output, djot.js and our parser are compared on the same footing. *)

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

let normalize s =
  (* compare modulo trailing newlines *)
  let n = String.length s in
  let rec last i = if i > 0 && s.[i - 1] = '\n' then last (i - 1) else i in
  String.sub s 0 (last n)

let project ~shape:s html = if s then shape html else normalize html

(*
Test suite
==========
*)

(* Only our parser runs: djot.js on its own test suite would show
   nothing. *)
let run_suite ~shape subject files r verbose =
  let cases, skipped =
    List.concat_map Corpus.parse_file files
    |> List.partition (fun (c : Corpus.case) -> c.options = "")
  in
  let outs = run_all subject (List.map (fun (c : Corpus.case) -> c.input) cases) in
  let m = ref 0 and mm = ref 0 and er = ref 0 in
  List.iter2
    (fun (c : Corpus.case) o ->
      let bad =
        match o with
        | Error e -> incr er; Some (Printf.sprintf "%s: ERROR %s\n" subject.name e)
        | Ok html when project ~shape html = project ~shape c.expected ->
          incr m; None
        | Ok html -> incr mm; Some (Printf.sprintf "%s:\n%s" subject.name html)
      in
      match bad with
      | Some msg when verbose ->
        Report.out r "\n--- %s:%d\n" (Filename.basename c.file) c.linenum;
        Report.out r "input:\n%s" c.input;
        Report.out r "expected:\n%s" c.expected;
        Report.out r "%s" msg
      | _ -> ())
    cases outs;
  Report.out r "\n== summary: %d cases run, %d skipped (options) ==\n"
    (List.length cases) (List.length skipped);
  Report.out r "%-8s  match %4d   mismatch %4d   error %4d\n" subject.name !m
    !mm !er;
  !er = 0

(*
Generated documents
===================

A test-suite case has recorded expected output.  A generated document
has none: it comes from `Generate.enum_cblock` via the renderer, so the
only available judgement is our parser against djot.js, the
implementation we conform to.

`roundtrip_blocks` is a meta-property, and cannot catch a rule we got
wrong in both the parser and the renderer.  Every shape the fragment
admits is checked here against something we did not write.

Exact HTML by default, not `--shape`, which would drop the field under
test. *)

let run_generated ~shape subject docs r verbose =
  let reference = djotjs in
  let ref_out = Array.of_list (run_all reference docs) in
  let docs_a = Array.of_list docs in
  let m = ref 0 and mm = ref 0 and er = ref 0 in
  List.iteri
    (fun i o ->
      match (o, ref_out.(i)) with
      | Error msg, _ ->
        incr er;
        if verbose then Report.out r "\n--- doc %d: %s ERROR %s\n" i subject.name msg
      | _, Error msg ->
        incr er;
        if verbose then
          Report.out r "\n--- doc %d: %s ERROR %s\n" i reference.name msg
      | Ok a, Ok b ->
        if project ~shape a = project ~shape b then incr m
        else begin
          incr mm;
          if verbose then begin
            Report.out r "\n--- doc %d\n" i;
            Report.out r "input:\n%s\n" docs_a.(i);
            Report.out r "%s:\n%s\n" reference.name b;
            Report.out r "%s:\n%s\n" subject.name a
          end
        end)
    (run_all subject docs);
  Report.out r "\n== generated: %d documents, reference %s%s ==\n"
    (Array.length docs_a) reference.name
    (if shape then ", block shape only" else ", exact HTML");
  Report.out r "%-8s  match %4d   mismatch %4d   error %4d\n" subject.name !m
    !mm !er;
  !er = 0

let () =
  let generated = ref false and shape = ref false in
  let subject = ref gallina in
  let report = ref "" and verbose = ref false and files = ref [] in
  let rec args = function
    | [] -> ()
    | "--generated" :: rest -> generated := true; args rest
    | "--shape" :: rest -> shape := true; args rest
    | "--subject" :: cmd :: rest ->
      subject := batch_process (Filename.basename cmd) [| cmd |]; args rest
    | "--report" :: v :: rest -> report := v; args rest
    | "--verbose" :: rest -> verbose := true; args rest
    | f :: rest -> files := f :: !files; args rest
  in
  args (List.tl (Array.to_list Sys.argv));
  let r = Report.create !report in
  let ok =
    if !generated then
      run_generated ~shape:!shape !subject Djot_fixtures.Fixtures.generated r !verbose
    else
      let files = if !files = [] then Corpus.default_files () else List.rev !files in
      run_suite ~shape:!shape !subject files r !verbose
  in
  Report.save r;
  exit (if ok then 0 else 1)
