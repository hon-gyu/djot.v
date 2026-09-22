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

(* A node's syntax-role spans (attribute specs, fence lines), as
   Located.v's `roles` reads them off a single node. *)
let expect_roles lines expected = function
  | Djot.Ast.Node (Djot.Ast.SomePos p, _, _) ->
      assert (List.map (fun (r, s) -> (r, range lines s)) p.syntax_spans
              = expected)
  | _ -> failwith "missing source span"

(* The inlines of the first paragraph or heading a block parse hands
   back, as `first_para` picks it out in Located.v. *)
let first_para = function
  | Djot.Ast.Node (_, _, Djot.Ast.Para ils) :: _ -> ils
  | _ -> failwith "expected a paragraph first"

(* Inline node spans in document order, mirroring Located.v's
   `inline_walk`. *)
let rec inline_ranges lines ils =
  List.concat_map
    (function
      | Djot.Ast.Node (Djot.Ast.SomePos p, _, contents) ->
          let kids =
            match contents with
            | Djot.Ast.Emph k | Djot.Ast.Strong k | Djot.Ast.Highlight k
            | Djot.Ast.Insert k | Djot.Ast.Delete k
            | Djot.Ast.Superscript k | Djot.Ast.Subscript k
            | Djot.Ast.Span k | Djot.Ast.Quoted (_, k)
            | Djot.Ast.Link (k, _) | Djot.Ast.Image (k, _) ->
                inline_ranges lines k
            | _ -> []
          in
          range lines p.node_span :: kids
      | Djot.Ast.Node (Djot.Ast.NoPos, _, _) -> failwith "missing inline span")
    ils

(* An inline node's attrs paired with its syntax-role spans, as
   Located.v's `inline_roles` reads them. *)
let inline_roles lines ils =
  List.map
    (function
      | Djot.Ast.Node (Djot.Ast.SomePos p, attrs, _) ->
          (attrs, List.map (fun (r, s) -> (r, range lines s)) p.syntax_spans)
      | Djot.Ast.Node (Djot.Ast.NoPos, attrs, _) -> (attrs, []))
    ils

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
   | [Djot.Ast.Node (Djot.Ast.SomePos p, _, Djot.Ast.Table (_, rows))] ->
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
        | _ -> failwith "missing table parts");
       (* Cell inlines, as `i_table_cells` pins them in the Rocq fixture. *)
       let cell_inlines =
         List.map
           (fun row ->
              List.concat
                (List.map
                   (fun cell ->
                      match cell with
                      | Djot.Ast.Cell (_, _, ils) ->
                          List.map
                            (fun n ->
                               match n with
                               | Djot.Ast.Node (Djot.Ast.SomePos q, _, _) ->
                                   range table_lines q.node_span
                               | _ -> failwith "missing cell inline span")
                            ils)
                   row))
           rows
       in
       assert (cell_inlines = [[(2, 3); (6, 7)]; [(22, 23); (26, 27)]])
   | _ -> failwith "unexpected table parse")

(* Heading span and the id its document pass assigns to the enclosing
   section, mirroring r_heading_anchor / r_heading_anchor_span. *)
let () =
  let src = "{#anchor}\n# Head\n" in
  let lines = Djot.Strings.line_table src in
  match (Djot.Document.parse_doc_located Djot.Inline.djot_table
           Djot.Step.djot_bconfig src).doc_blocks with
  | [Djot.Ast.Node (Djot.Ast.SomePos p, attrs,
                     Djot.Ast.Section
                       [Djot.Ast.Node (Djot.Ast.SomePos hp, _,
                                        Djot.Ast.Heading _)])] ->
      assert (range lines p.node_span = (10, 16));
      assert (range lines hp.node_span = (10, 16));
      assert (attrs = [("id", "anchor")]);
      assert (List.map (fun (r, s) -> (r, range lines s)) p.syntax_spans
              = [(Djot.Ast.RAttrSpec, (0, 9))])
  | _ -> failwith "unexpected document parse"

(* Block-attribute anchor on a paragraph, and its authored specs:
   r_attr_para, y_attr_specs. *)
let () =
  let src = "{#id}\n{.cls}\npara\n" in
  let lines = Djot.Strings.line_table src in
  match Djot.Step.parse_blocks_located Djot.Inline.djot_table
          Djot.Step.djot_bconfig src with
  | [Djot.Ast.Node (Djot.Ast.SomePos _, _, Djot.Ast.Para _) as para] ->
      expect_span lines (13, 17) para;
      expect_roles lines
        [(Djot.Ast.RAttrSpec, (0, 5)); (Djot.Ast.RAttrSpec, (6, 12))] para
  | _ -> failwith "unexpected block parse"

(* Block-attribute anchor on a div, with the decorated block's own span
   left unwidened: r_attr_div. *)
let () =
  let src = "{#i}\n::: warn\ninside\n:::\n" in
  let lines = Djot.Strings.line_table src in
  match Djot.Step.parse_blocks_located Djot.Inline.djot_table
          Djot.Step.djot_bconfig src with
  | [Djot.Ast.Node (Djot.Ast.SomePos _, _,
                     Djot.Ast.Div [Djot.Ast.Node (Djot.Ast.SomePos _, _,
                                                    Djot.Ast.Para _)]) as div] ->
      expect_span lines (5, 24) div;
      (match div with
       | Djot.Ast.Node (_, _, Djot.Ast.Div [para]) ->
           expect_span lines (14, 20) para
       | _ -> failwith "unexpected div parse")
  | _ -> failwith "unexpected div parse"

(* Fence-line spans and whether a closer exists, for a div and a code
   fence: y_div_closed, y_div_unclosed, y_code_fence. *)
let () =
  let src = "::: warn\ninside\n:::\n" in
  let lines = Djot.Strings.line_table src in
  match Djot.Step.parse_blocks_located Djot.Inline.djot_table
          Djot.Step.djot_bconfig src with
  | [div] ->
      expect_roles lines
        [(Djot.Ast.ROpenFence, (0, 8)); (Djot.Ast.RCloseFence, (16, 19))] div
  | _ -> failwith "unexpected div parse"

(* The input ended inside the div: no RCloseFence. *)
let () =
  let src = "::: warn\ninside\n" in
  let lines = Djot.Strings.line_table src in
  match Djot.Step.parse_blocks_located Djot.Inline.djot_table
          Djot.Step.djot_bconfig src with
  | [div] -> expect_roles lines [(Djot.Ast.ROpenFence, (0, 8))] div
  | _ -> failwith "unexpected div parse"

(* Code fence lines and the code block's own span, which runs to the
   closing fence like a div's does. *)
let () =
  let src = "```py\nx = 1\n```\n" in
  let lines = Djot.Strings.line_table src in
  match Djot.Step.parse_blocks_located Djot.Inline.djot_table
          Djot.Step.djot_bconfig src with
  | [Djot.Ast.Node (Djot.Ast.SomePos _, _, Djot.Ast.CodeBlock _) as cb] ->
      expect_span lines (0, 15) cb;
      expect_roles lines
        [(Djot.Ast.ROpenFence, (0, 5)); (Djot.Ast.RCloseFence, (12, 15))] cb
  | _ -> failwith "unexpected code block parse"

(* Inline construct spans in a paragraph's first line: i_link,
   i_reference, i_footnote_ref, i_image, i_span_attr. *)
let () =
  let check src expected =
    let lines = Djot.Strings.line_table src in
    let bs = Djot.Step.parse_blocks_located Djot.Inline.djot_table
               Djot.Step.djot_bconfig src in
    assert (inline_ranges lines (first_para bs) = expected)
  in
  check "a [link](dest){.c} b" [(0, 2); (2, 14); (3, 7); (18, 20)];
  check "k [r][lbl] l" [(0, 2); (2, 10); (3, 4); (10, 12)];
  check "p [^fn] q" [(0, 2); (2, 7); (7, 9)];
  check "i ![alt](i.png) j" [(0, 2); (2, 15); (4, 7); (15, 17)];
  check "s [txt]{.c} t" [(0, 2); (2, 7); (3, 6); (11, 13)]

(* The attribute spec attached to an inline node: i_span_spec. *)
let () =
  let src = "[s]{.c}" in
  let lines = Djot.Strings.line_table src in
  let bs = Djot.Step.parse_blocks_located Djot.Inline.djot_table
             Djot.Step.djot_bconfig src in
  assert (inline_roles lines (first_para bs)
          = [([("class", "c")], [(Djot.Ast.RAttrSpec, (3, 7))])])

(* Wikilinks, which a consumer switches on: r_wiki_alias and
   r_wiki_embed, together. *)
let () =
  let table = Djot.Inline.with_wikilinks true Djot.Inline.djot_config in
  let src = "p [[a|b]] ![[c]] q" in
  let lines = Djot.Strings.line_table src in
  match first_para
          (Djot.Step.parse_blocks_located table Djot.Step.djot_bconfig src) with
  | [ _; (Djot.Ast.Node (_, _, Djot.Ast.Wikilink (false, "a", Some "b")) as w);
      _; (Djot.Ast.Node (_, _, Djot.Ast.Wikilink (true, "c", None)) as e); _ ] ->
      expect_span lines (2, 9) w;
      expect_span lines (10, 16) e
  | _ -> failwith "unexpected wikilink parse"
