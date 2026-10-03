(* ai-disclosure: autonomous *)

(* Source spans of the located parse, checked over whole inputs rather
   than over the fixtures' hand-written ones.

   Usage:
     spans [DEPTH] [--report FILE] [--verbose] [TEST_FILES...]

   Runs over the generated documents at DEPTH (default 2) and the djot.js
   test suite, or TEST_FILES.  Exits nonzero on a failure.

   *Bounds*: every span the tree carries resolves to a byte range inside
   the document, running forwards.  *Containment*: the tree nests, so a
   child's span lies inside its parent's and a part's inside the node
   that owns it.

   Syntax roles are bounds-checked and not contained, and that is by
   design rather than by omission: an `RAttrSpec` sits outside the node it
   decorates, because a spec belongs to a node without widening it
   (`.project/260916.plan.source-locations.md` section 4.4).  The fence
   roles do sit inside their block, but one rule per role buys nothing
   here -- containment's teeth are on children and parts, which is where
   the table caption's divergence showed up. *)

open Djot_test
open Parsers

type failure = { kind : string; src : string; detail : string }

let located_failures src =
  let lines = Djot.Strings.line_table src in
  let len = String.length src in
  let bad = ref [] in
  let note kind detail = bad := { kind; src; detail } :: !bad in
  let bytes what span =
    match Djot.Strings.resolve_span lines span with
    | None -> note "unresolvable" what; None
    | Some r ->
      let a = r.Djot.Strings.source_span_start.Djot.Strings.source_byte
      and b = r.Djot.Strings.source_span_stop.Djot.Strings.source_byte in
      if a > b then (note "reversed" (Printf.sprintf "%s [%d,%d)" what a b); None)
      else if b > len then
        (note "out of bounds" (Printf.sprintf "%s [%d,%d) of %d" what a b len); None)
      else Some (a, b)
  in
  let inside what child parent =
    match child, parent with
    | Some (a, b), Some (pa, pb) when a < pa || b > pb ->
      note "not contained"
        (Printf.sprintf "%s [%d,%d) outside [%d,%d)" what a b pa pb)
    | _ -> ()
  in
  let prov what = function
    | Djot.Ast.Node (Djot.Ast.NoPos, _, _) -> note "no position" what; None
    | Djot.Ast.Node (Djot.Ast.SomePos p, _, _) ->
      let own = bytes what p.Djot.Ast.node_span in
      List.iter (fun (_, s) -> ignore (bytes (what ^ " role") s))
        p.Djot.Ast.syntax_spans;
      (match p.Djot.Ast.part_spans with
       | Djot.Ast.PNone -> ()
       | Djot.Ast.PItems items ->
         List.iter (fun s -> inside (what ^ " item") (bytes (what ^ " item") s) own)
           items
       | Djot.Ast.PDefItems items ->
         List.iter
           (fun ((i, t), d) ->
              List.iter
                (fun (n, s) -> inside (what ^ n) (bytes (what ^ n) s) own)
                [ (" def item", i); (" def term", t); (" def body", d) ])
           items
       | Djot.Ast.PTable (caption, rows) ->
         (match caption with
          | None -> ()
          | Some s -> inside (what ^ " caption") (bytes (what ^ " caption") s) own);
         List.iter
           (fun (row, cells) ->
              let r = bytes (what ^ " row") row in
              inside (what ^ " row") r own;
              List.iter
                (fun c -> inside (what ^ " cell") (bytes (what ^ " cell") c) r)
                cells)
           rows);
      own
  in
  let rec inlines parent ils =
    List.iter
      (fun n ->
         let own = prov "inline" n in
         inside "inline" own parent;
         match n with
         | Djot.Ast.Node (_, _, contents) ->
           (match contents with
            | Djot.Ast.Emph k | Djot.Ast.Strong k | Djot.Ast.Highlight k
            | Djot.Ast.Insert k | Djot.Ast.Delete k
            | Djot.Ast.Superscript k | Djot.Ast.Subscript k
            | Djot.Ast.Span (_, k) | Djot.Ast.Quoted (_, k)
            | Djot.Ast.Link (k, _) | Djot.Ast.Image (k, _) -> inlines own k
            | _ -> ()))
      ils
  and blocks parent bs =
    List.iter
      (fun n ->
         let own = prov "block" n in
         inside "block" own parent;
         match n with
         | Djot.Ast.Node (_, _, contents) ->
           (match contents with
            | Djot.Ast.Para ils | Djot.Ast.Heading (_, ils) -> inlines own ils
            | Djot.Ast.Section bs' | Djot.Ast.BlockQuote bs'
            | Djot.Ast.Div (_, bs') | Djot.Ast.FootnoteDef (_, bs') -> blocks own bs'
            | Djot.Ast.Ext_keyed (_, kid) -> blocks own [kid]
            | Djot.Ast.OrderedList (_, _, items)
            | Djot.Ast.BulletList (_, items) -> List.iter (blocks own) items
            | Djot.Ast.TaskList (_, items) ->
              List.iter (fun (_, item) -> blocks own item) items
            | Djot.Ast.DefinitionList (_, items) ->
              List.iter (fun (term, item) -> inlines own term; blocks own item) items
            | Djot.Ast.Table (caption, rows) ->
              inlines own caption;
              List.iter
                (List.iter (function Djot.Ast.Cell (_, _, ils) -> inlines own ils))
                rows
            | _ -> ()))
      bs
  in
  blocks None
    (Djot.Reparse.parse_blocks_located Djot.Inline.djot_table
       Djot.Step.djot_bconfig src);
  List.rev !bad

let run depth files r verbose =
  (* Both inputs: the generator emits canonical source, so anything the
     renderer escapes is outside its image by construction, and the test
     suite is where those bytes live. *)
  let sources =
    List.map Djot_fixtures.Fixtures.render_cb
      (Djot_fixtures.Generate.accepted depth)
    @ List.map (fun (c : Corpus.case) -> c.input)
        (List.concat_map Corpus.parse_file files)
  in
  let total = ref 0 and bad = ref 0 in
  let seen = Hashtbl.create 16 in
  List.iter
    (fun src ->
       incr total;
       match located_failures src with
       | [] -> ()
       | fs ->
         incr bad;
         List.iter
           (fun f ->
              let n = try Hashtbl.find seen f.kind with Not_found -> 0 in
              Hashtbl.replace seen f.kind (n + 1);
              if verbose || n < 3 then
                Report.out r "\n--- %s: %s\nin %S\n" f.kind f.detail f.src)
           fs)
    sources;
  Report.out r
    "\n== located bounds: %d documents (generated depth %d, plus the file corpus) ==\n"
    !total depth;
  Report.out r "spans bounded and contained   ok %6d   bad %4d\n"
    (!total - !bad) !bad;
  Hashtbl.iter (fun k n -> Report.out r "  %-16s %4d\n" k n) seen;
  !bad = 0

let () =
  let depth = ref 2 and report = ref "" and verbose = ref false in
  let files = ref [] in
  let rec args = function
    | [] -> ()
    | "--report" :: v :: rest -> report := v; args rest
    | "--verbose" :: rest -> verbose := true; args rest
    | d :: rest when int_of_string_opt d <> None ->
      depth := int_of_string d; args rest
    | f :: rest -> files := f :: !files; args rest
  in
  args (List.tl (Array.to_list Sys.argv));
  let files = if !files = [] then Corpus.default_files () else List.rev !files in
  let r = Report.create !report in
  let ok = run !depth files r !verbose in
  Report.save r;
  exit (if ok then 0 else 1)
