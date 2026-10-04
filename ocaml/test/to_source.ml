(* ai-disclosure: ai-generated *)

(* Djot source rendering. Each case prints the source written back, and
   checks that it parses to the same tree. Compared against
   to_source.expected. *)

open Djot

let render ?(profile = Profile.djot) name src =
  Printf.printf "\n== %s\n" name;
  let d = Doc.of_string ~profile src in
  let out = Doc.to_string d in
  print_endline out;
  assert (For_testing.kernel (Doc.of_string ~profile out) = For_testing.kernel d)
;;

(* Sections and derived heading ids, attributes and a div's class,
   footnotes, and breaks inside emphasis. The second heading keeps its
   derived id [Intro-1], the first leaves its id out. *)
let () =
  let src =
    "# Intro\n\n\
     {#main k=\"a b\"}\n\
     ::: warn\n\
     Text[^n] with _soft\n\
     break_.\n\
     :::\n\n\
     # Intro\n\n\
     [^n]: A note.\n\n\
    \  - x\n\
    \  - y\n"
  in
  render "document" src;
  render ~profile:Profile.markdown_like "document, markdown_like" src;
  render "empty list item" "- a\n-\n- b\n\nB.\n";
  render
    ~profile:(Profile.with_ext_keyed true Profile.djot)
    "key over a paragraph"
    "key: value\nmore\n\nkey:\n- a\n";
  render
    ~profile:(Profile.with_ext_callouts true Profile.djot)
    "callout"
    "> [!warning]- Do not rename\n> body\n"
;;

(* Source of part of a tree. *)
let () =
  let d = Doc.of_string "{.c}\n> a *b*\\\n> c\n\npara\n" in
  match Doc.blocks d with
  | [ (Node (_, _, Block.BlockQuote [ Node (_, _, Block.Para ils) ]) as quote); _ ] ->
    Printf.printf "\n== of_blocks\n%s\n" (Block.to_string [ quote ]);
    Printf.printf "\n== of_inlines\n%s\n" (Inline.to_string ils)
  | _ -> failwith "unexpected document"
;;

(* The readable form of a tree built by hand: text as given, bare
   delimiters, a padded table, and empty blank lines inside containers. *)
let () =
  let n = Node.make in
  let str s = n (Inline.Str s) in
  let para ils = n (Block.Para ils) in
  let cell kind al s = n (Block.Cell (kind, al, [ str s ])) in
  let blocks =
    [ n (Block.Heading (1, [ str "Notes: v1.2" ]))
    ; para
        [ str "Ratio 3:1 and snake_case, "
        ; n (Inline.Emph [ str "fine" ])
        ; str " and "
        ; n (Inline.Quoted (Inline.DoubleQuotes, [ str "quoted" ]))
        ; str ", see "
        ; n (Inline.Link ([ str "docs" ], Inline.Direct "https://example.com/x_y"))
        ; str "."
        ]
    ; n
        (Block.BulletList
           ( Block.Loose
           , [ n [ para [ str "one" ]; para [ str "two" ] ]; n [ para [ str "three" ] ] ]
           ))
    ; n (Block.BlockQuote [ para [ str "a" ]; para [ str "b" ] ])
    ; n
        (Block.Table
           ( n []
           , [ n
                 [ cell Block.HeadCell Block.AlignLeft "name"
                 ; cell Block.HeadCell Block.AlignRight "value"
                 ]
             ; n
                 [ cell Block.BodyCell Block.AlignLeft "longer cell"
                 ; cell Block.BodyCell Block.AlignRight "1"
                 ]
             ] ))
    ]
  in
  Printf.printf "\n== readable\n%s\n" (Block.to_string ~style:`Naive blocks);
  Printf.printf
    "\n== the same blocks, not readable\n%s\n"
    (Block.to_string ~style:`Safe blocks)
;;

(* A delimiter is bare where it reads back as one and braced otherwise. *)
let () =
  let n = Node.make in
  let str s = n (Inline.Str s) in
  let em ils = n (Inline.Emph ils) in
  let quoted ils = n (Inline.Quoted (Inline.SingleQuotes, ils)) in
  Printf.printf "\n== readable delimiters\n";
  List.iter
    (fun ils ->
      let out = Inline.to_string ~style:`Naive ils in
      let tree s = For_testing.kernel (Doc.of_string s) in
      assert (tree out = tree (Inline.to_string ~style:`Safe ils));
      print_endline out)
    [ [ str "a"; em [ str "b" ]; str "c" ]
    ; [ str "a "; em [ str " b " ]; str " c" ]
    ; [ em [ str "a"; em [ str "b" ]; str "c" ] ]
    ; [ em [ str "a "; em [ str "b" ]; str " c" ] ]
    ; [ em [ str "a" ]; em [ str "b" ] ]
    ; [ str "a"; quoted [ str "b" ] ]
    ; [ str "a "; quoted [ str "b" ] ]
    ]
;;

(* [`Checked] keeps the readable form of a block unless it would parse
   differently, alone or next to its neighbours. *)
let () =
  let n = Node.make in
  let para s = n (Block.Para [ n (Inline.Str s) ]) in
  let cell s =
    n (Block.Cell (Block.BodyCell, Block.AlignDefault, [ n (Inline.Str s) ]))
  in
  let blocks =
    [ para "Ratio 3:1, a * b, see (x)."
    ; para "- not a list"
    ; para "snake_case_name"
    ; n (Block.Table (n [], [ n [ cell "a" ] ]))
    ; para "^ not a caption"
    ; para "plain again"
    ]
  in
  let out = Block.to_string ~style:`Checked blocks in
  let tree s = For_testing.kernel (Doc.of_string s) in
  assert (tree out = tree (Block.to_string ~style:`Safe blocks));
  assert (tree (Block.to_string ~style:`Naive blocks) <> tree out);
  Printf.printf "\n== checked\n%s\n" out
;;
