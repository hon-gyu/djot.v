(* ai-disclosure: autonomous *)

(* A consumer outside the generated library: exercise the extracted
   entry points and their byte-coordinate conversion. *)
let rec int_of_nat = function
  | Djot.Datatypes.O -> 0
  | Djot.Datatypes.S n -> 1 + int_of_nat n

let range lines span =
  match Djot.Strings.resolve_span lines span with
  | None -> failwith "unresolvable source span"
  | Some r ->
      (int_of_nat r.source_span_start.source_byte,
       int_of_nat r.source_span_stop.source_byte)

let expect_span lines expected = function
  | Djot.Ast.Node (Djot.Ast.SomePos p, _, _) ->
      assert (range lines p.node_span = expected)
  | _ -> failwith "missing source span"

let () =
  let src = "# hi\n\nbody\n" in
  let lines = Djot.Strings.line_table src in
  (match Djot.Step.parse_blocks_located Djot.Inline.djot_table
           Djot.Step.djot_bconfig src with
   | heading :: paragraph :: [] ->
       expect_span lines (0, 4) heading;
       expect_span lines (6, 10) paragraph
   | _ -> failwith "unexpected block parse");
  (match (Djot.Document.parse_doc_located Djot.Inline.djot_table
            Djot.Step.djot_bconfig src).doc_blocks with
   | section :: [] -> expect_span lines (0, 10) section
   | _ -> failwith "unexpected document parse");
  let table_src = "| a | b |\n|---|---|\n| x | y |\n\n^ cap\n" in
  let table_lines = Djot.Strings.line_table table_src in
  (match Djot.Step.parse_blocks_located Djot.Inline.djot_table
           Djot.Step.djot_bconfig table_src with
   | [Djot.Ast.Node (Djot.Ast.SomePos p, _, _)] ->
       assert (range table_lines p.node_span = (0, 36));
       (match p.part_spans with
        | Djot.Ast.PTable (Some caption, [row1; row2]) ->
            assert (range table_lines caption = (31, 36));
            assert (range table_lines (fst row1) = (0, 9));
            assert (List.map (range table_lines) (snd row1)
                    = [(0, 5); (4, 9)]);
            assert (range table_lines (fst row2) = (20, 29));
            assert (List.map (range table_lines) (snd row2)
                    = [(20, 25); (24, 29)])
        | _ -> failwith "missing table parts")
   | _ -> failwith "unexpected table parse")
