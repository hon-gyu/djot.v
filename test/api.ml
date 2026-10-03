(* ai-disclosure: ai-generated *)

(* Tests of the hand-written API: parsing, profiles, locations, traversals,
   HTML. *)

open Djot

let bytes t = Textloc.first_byte t, Textloc.last_byte t
let lines t = Textloc.first_line t, Textloc.last_line t

(* A heading opens a section carrying its id; locations are inclusive
   byte ranges with one-based lines. *)
let () =
  let src = "# hi\n\nbody\n" in
  let d = Doc.of_string ~locs:true src in
  (match Doc.blocks d with
   | [ (Node (_, attrs, Block.Section [ heading; para ]) as section) ] ->
     assert (Attr.id attrs = Some "hi");
     assert (bytes (Doc.textloc d section) = (0, 9));
     assert (Doc.source d = Some src);
     assert (lines (Doc.textloc d section) = ((1, 0), (3, 6)));
     assert (bytes (Doc.textloc d heading) = (0, 3));
     assert (bytes (Doc.textloc d para) = (6, 9))
   | _ -> failwith "unexpected document");
  let plain = Doc.of_string src in
  assert (List.for_all (fun n -> Textloc.is_none (Doc.textloc plain n)) (Doc.blocks plain))
;;

(* A block's range excludes its attribute lines; a div's and a code
   block's run to the closing fence. *)
let () =
  let d = Doc.of_string ~locs:true "{#id}\n{.cls}\npara\n" in
  (match Doc.blocks d with
   | [ para ] -> assert (bytes (Doc.textloc d para) = (13, 16))
   | _ -> failwith "unexpected document");
  let d = Doc.of_string ~locs:true "{#i}\n::: warn\ninside\n:::\n" in
  (match Doc.blocks d with
   | [ (Node (_, _, Block.Div (_, [ para ])) as div) ] ->
     assert (bytes (Doc.textloc d div) = (5, 23));
     assert (bytes (Doc.textloc d para) = (14, 19))
   | _ -> failwith "unexpected document");
  let d = Doc.of_string ~locs:true "```py\nx = 1\n```\n" in
  match Doc.blocks d with
  | [ code ] -> assert (lines (Doc.textloc d code) = ((1, 0), (3, 12)))
  | _ -> failwith "unexpected document"
;;

(* A node's delimiting syntax, in source order; an unclosed div has no
   closing fence. *)
let () =
  let syntax src =
    let d = Doc.of_string ~locs:true src in
    match Doc.blocks d with
    | [ n ] -> List.map (fun (r, t) -> r, bytes t) (Doc.syntax_locs d n)
    | _ -> failwith "unexpected document"
  in
  assert (
    syntax "{#i}\n::: warn\ninside\n:::\n"
    = [ Doc.RAttrSpec, (0, 3); ROpenFence, (5, 12); RCloseFence, (21, 23) ]);
  assert (syntax "```py\nx\n```\n" = [ ROpenFence, (0, 4); RCloseFence, (8, 10) ]);
  assert (syntax "::: a\nx\n" = [ ROpenFence, (0, 4) ]);
  let plain = Doc.of_string "```\nx\n```\n" in
  assert (List.for_all (fun n -> Doc.syntax_locs plain n = []) (Doc.blocks plain))
;;

(* The parts of a list, a definition list and a table. *)
let () =
  let parts src =
    let d = Doc.of_string ~locs:true src in
    match Doc.blocks d with
    | [ n ] -> Doc.parts d n
    | _ -> failwith "unexpected document"
  in
  (match parts "- a\n- b\n" with
   | Items l -> assert (List.map bytes l = [ 0, 2; 4, 6 ])
   | _ -> failwith "unexpected parts");
  (match parts ": t\n\n  d\n" with
   | DefItems [ (i, t, d) ] ->
     assert ((bytes i, bytes t, bytes d) = ((0, 7), (2, 2), (7, 7)))
   | _ -> failwith "unexpected parts");
  match parts "| a | b |\n| 1 | 2 |\n^ cap\n" with
  | TableRows (Some cap, [ (r1, [ _; _ ]); (r2, [ c21; c22 ]) ]) ->
    assert (bytes cap = (20, 24));
    assert ((bytes r1, bytes r2) = ((0, 8), (10, 18)));
    assert ((bytes c21, bytes c22) = ((10, 14), (14, 18)))
  | _ -> failwith "unexpected parts"
;;

(* Building a range from two others. *)
let () =
  let d = Doc.of_string ~locs:true "a\n\nb\n" in
  match Doc.blocks d with
  | [ a; b ] ->
    let t = Textloc.reloc ~first:(Doc.textloc d a) ~last:(Doc.textloc d b) in
    assert (bytes t = (0, 3));
    assert (lines t = ((1, 0), (3, 3)));
    assert (t = Textloc.make ~first_byte:0 ~last_byte:3 ~first_line:(1, 0) ~last_line:(3, 3))
  | _ -> failwith "unexpected document"
;;

(* Inline ranges in document order, containers before their contents. *)
let () =
  let rec ranges d ns =
    List.concat_map
      (fun n ->
        let kids =
          match Node.content n with
          | Inline.Link (l, _) | Inline.Image (l, _) | Inline.Span (_, l) -> ranges d l
          | _ -> []
        in
        bytes (Doc.textloc d n) :: kids)
      ns
  in
  let check ?(profile = Profile.djot) src expected =
    let d = Doc.of_string ~profile ~locs:true src in
    match Doc.blocks d with
    | [ Node (_, _, Block.Para ils) ] -> assert (ranges d ils = expected)
    | _ -> failwith "unexpected document"
  in
  check "a [link](dest){.c} b" [ 0, 1; 2, 13; 3, 6; 18, 19 ];
  check "k [r][lbl] l" [ 0, 1; 2, 9; 3, 3; 10, 11 ];
  check "p [^fn] q" [ 0, 1; 2, 6; 7, 8 ];
  check "i ![alt](i.png) j" [ 0, 1; 2, 14; 4, 6; 15, 16 ];
  check "s [txt]{.c} t" [ 0, 1; 2, 6; 3, 5; 11, 12 ];
  check
    ~profile:(Profile.with_ext_wikilinks true Profile.djot)
    "p [[a|b]] ![[c]] q"
    [ 0, 1; 2, 8; 9, 9; 10, 15; 16, 17 ];
  check
    ~profile:(Profile.with_ext_dollar_math true Profile.djot)
    "a $x$ b"
    [ 0, 1; 2, 4; 5, 6 ];
  check
    ~profile:(Profile.with_ext_tags true Profile.djot)
    "p :kbd[a] q"
    [ 0, 1; 2, 8; 7, 7; 9, 10 ]
;;

(* The HTML tree serializes to the rendered document. *)
let () =
  let src = "# hi\n\n*a* [b](c)[^n]\n\n[^n]: note\n" in
  let d = Doc.of_string src in
  assert (Html.to_string (Html.tree d) = Html.of_doc d);
  assert (Html.of_doc d = Kernel.Html.convert src)
;;

(* The fold visits footnote bodies after the blocks, in source order. *)
let () =
  let d = Doc.of_string "*a* b [c](d)[^n]\n\n[^n]: note\n" in
  let inline _ acc = function
    | Node (_, _, Inline.Str s) -> Folder.ret (s :: acc)
    | _ -> Folder.default
  in
  let strs = Folder.fold_doc (Folder.make ~inline ()) [] d in
  assert (List.rev strs = [ "a"; " b "; "c"; "note" ])
;;

(* A mapper rewrites and deletes; untouched structure is kept. *)
let () =
  let d = Doc.of_string "_a_ [b](c)\n" in
  let inline _ = function
    | Node (p, a, Inline.Emph l) -> Mapper.ret (Node (p, a, Inline.Strong l))
    | Node (_, _, Inline.Link _) -> Mapper.delete
    | _ -> Mapper.default
  in
  let d = Mapper.map_doc (Mapper.make ~inline ()) d in
  assert (Html.of_doc d = "<p><strong>a</strong> </p>\n")
;;

(* Labels resolve against explicit definitions, then headings. *)
let () =
  let d = Doc.of_string "# Head\n\n[x]: /u\n\n[a][x] [b][Head]\n" in
  assert (Option.map fst (Doc.reference d "x") = Some "/u");
  assert (Option.map fst (Doc.reference d "Head") = Some "#Head");
  assert (List.map fst (Doc.references d) = [ "x" ])
;;

(* Wikilinks are an extension, off in djot. *)
let () =
  let src = "[[a|b]]\n" in
  let first d =
    match Doc.blocks d with
    | [ Node (_, _, Block.Para [ Node (_, _, il) ]) ] -> il
    | _ -> failwith "unexpected document"
  in
  assert (
    first (Doc.of_string ~profile:(Profile.with_ext_wikilinks true Profile.djot) src)
    = Inline.Ext_wikilink (false, "a", Some "b"));
  assert (first (Doc.of_string src) <> Inline.Ext_wikilink (false, "a", Some "b"))
;;

(* Profiles: a named starting point, then per-construct switches. *)
let () =
  let blocks p src = List.map Node.content (Doc.blocks (Doc.of_string ~profile:p src)) in
  let table = "| a |\n|---|\n" in
  assert (
    match blocks Profile.djot table with
    | [ Block.Table _ ] -> true
    | _ -> false);
  assert (
    match blocks (Profile.with_tables false Profile.djot) table with
    | [ Block.Para _ ] -> true
    | _ -> false);
  let strong = function
    | [ Block.Para [ Node (_, _, Inline.Strong [ Node (_, _, Inline.Str "a") ]) ] ] ->
      true
    | _ -> false
  in
  assert (strong (blocks Profile.markdown_like "**a**\n"));
  assert (not (strong (blocks Profile.djot "**a**\n")))
;;

(* Source rendering reads back to the same tree: sections and derived
   heading ids, attributes and a div's class, footnotes, and breaks
   inside emphasis. *)
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
  let same profile =
    let d = Doc.of_string ~profile src in
    let d' = Doc.of_string ~profile (Source.of_doc d) in
    assert (Doc.kernel d' = Doc.kernel d)
  in
  same Profile.djot;
  same Profile.markdown_like;
  let lines = String.split_on_char '\n' (Source.of_doc (Doc.of_string src)) in
  assert (List.mem "::: warn" lines);
  assert (List.mem "{#main k=\"a b\"}" lines);
  assert (List.mem "{#Intro-1}" lines);
  assert (not (List.mem "{#Intro}" lines))
;;

(* The callout switch exposes a distinct block, a fold marker, and an
   inline title.  The source renderer preserves the construct. *)
let () =
  let profile = Profile.with_ext_callouts true Profile.djot in
  let src = "> [!warning]- Do not rename\n> body\n" in
  (match Doc.blocks (Doc.of_string src) with
   | [ Node (_, _, Block.BlockQuote _) ] -> ()
   | _ -> failwith "callouts should be off by default");
  (match Doc.blocks (Doc.of_string ~profile:Profile.markdown_like src) with
   | [ Node (_, _, Block.BlockQuote _) ] -> ()
   | _ -> failwith "callouts should be off in markdown_like");
  let d = Doc.of_string ~profile ~locs:true src in
  (match Doc.blocks d with
   | [ Node
         ( _
         , _
         , Block.Ext_callout
             ( "warning"
             , Some Block.FoldCollapsed
             , [ (Node (_, _, Inline.Str "Do not rename") as title) ]
             , [ Node (_, _, Block.Para _) ] ) )
     ] -> assert (bytes (Doc.textloc d title) = (14, 26))
   | _ -> failwith "unexpected callout");
  let d' = Doc.of_string ~profile (Source.of_doc d) in
  assert (Doc.kernel d' = Doc.kernel (Doc.of_string ~profile src));
  let spaced = Doc.of_string ~profile ~locs:true "> [!note] T  \n" in
  match Doc.blocks spaced with
  | [ Node
        ( _
        , _
        , Block.Ext_callout ("note", None, [ (Node (_, _, Inline.Str "T") as title) ], [])
        )
    ] -> assert (bytes (Doc.textloc spaced title) = (10, 10))
  | _ -> failwith "unexpected spaced callout title"
;;

(* An empty list item renders as its marker alone. *)
let () =
  let src = "- a\n-\n- b\n\nB.\n" in
  let d = Doc.of_string src in
  assert (Source.of_doc d = "- a\n-\n- b\n\nB.");
  assert (Doc.kernel (Doc.of_string (Source.of_doc d)) = Doc.kernel d)
;;

(* A key's label is located like any other inline. *)
let () =
  let profile = Profile.with_ext_keyed true Profile.djot in
  let d = Doc.of_string ~profile ~locs:true "> key: value\n" in
  match Doc.blocks d with
  | [ Node (_, _, Block.BlockQuote [ Node (_, _, Block.Ext_keyed ([ label ], value)) ]) ]
    ->
    assert (bytes (Doc.textloc d label) = (2, 4));
    assert (bytes (Doc.textloc d value) = (7, 11))
  | _ -> failwith "unexpected key"
;;

(* Every footnote definition is kept, with its label's location; the
   note map keeps the last one per label. *)
let () =
  let d = Doc.of_string ~locs:true "[^a]\n\n[^a]: one\n\n> [^a]: two\n" in
  (match Doc.footnote_defs d with
   | [ (Node (_, _, Block.FootnoteDef ("a", _)) as one)
     ; (Node (_, _, Block.FootnoteDef ("a", _)) as two)
     ] ->
     assert (bytes (Doc.footnote_label_loc d one) = (8, 8));
     assert (bytes (Doc.footnote_label_loc d two) = (21, 21));
     assert (lines (Doc.footnote_label_loc d two) = ((5, 17), (5, 17)))
   | _ -> failwith "unexpected footnote definitions");
  match Doc.footnotes d with
  | [ ("a", [ Node (_, _, Block.Para [ Node (_, _, Inline.Str "two") ]) ]) ] -> ()
  | _ -> failwith "unexpected note map"
;;

(* A key over a paragraph renders on one line. *)
let () =
  let profile = Profile.with_ext_keyed true Profile.djot in
  let d = Doc.of_string ~profile "key: value\nmore\n\nkey:\n- a\n" in
  assert (Source.of_doc d = "key: value\nmore\n\nkey:\n- a")
;;

(* Replacing lines gives the parse of the edited source, with and
   without locations, for every range of a few documents and a few
   replacements, including ones that open a fence or a list and so reach
   into the lines after the edit. *)
let () =
  let docs =
    [ ""
    ; "a\n\
       b\n\n\
       # h\n\n\
       - x\n\n\
       - y\n\
       c\n\n\
       ```\n\
       k\n\
       ```\n\n\
       {#i}\n\
       d\n\n\
       > q\n\n\
       ***\n\
       [r]: u\n\n\
       [^n]: z\n\n\
       e\n"
    ; "# a\n\n# a\n\n- a\n- b\n\n::: d\nx\n:::\n"
    ; "> q\n\n| a |\n\n- b"
    ]
  in
  let news = [ ""; "x\n"; "```\n"; "- z\n"; "# a\n\n"; "> y\n\nw"; ":::\n"; "{.c}" ] in
  let lines_of s = Array.of_list (Kernel.Strings.split_lines s) in
  let ranges d = List.map (fun n -> bytes (Doc.textloc d n)) (Doc.blocks d) in
  List.iter
    (fun locs ->
      List.iter
        (fun src ->
          let d = Doc.of_string ~locs src in
          let ls = lines_of src in
          let n = Array.length ls in
          for first = 1 to n + 1 do
            for last = first - 1 to n do
              List.iter
                (fun s ->
                  let edited =
                    Array.to_list (Array.sub ls 0 (first - 1))
                    @ Array.to_list (lines_of s)
                    @ Array.to_list (Array.sub ls last (n - last))
                  in
                  let expected = Doc.of_string ~locs (String.concat "\n" edited ^ "\n") in
                  let got = Doc.replace_lines d ~first ~last s in
                  assert (Doc.kernel got = Doc.kernel expected);
                  assert (Doc.footnote_defs got = Doc.footnote_defs expected);
                  assert (ranges got = ranges expected))
                news
            done
          done)
        docs)
    [ false; true ];
  match Doc.replace_lines (Doc.of_blocks []) ~first:1 ~last:0 "b" with
  | _ -> failwith "a document without source is not spliced"
  | exception Invalid_argument _ -> ()
;;

(* Attributes: building, and a spec read and written. *)
let () =
  let a =
    Attr.(
      empty
      |> set_exn "id" "x"
      |> add_class_exn "a"
      |> add_class_exn "b"
      |> set_exn "k" "v w")
  in
  assert (Attr.id a = Some "x" && Attr.classes a = [ "a"; "b" ]);
  assert (Attr.to_string a = {|{#x .a .b k="v w"}|});
  assert (Attr.of_string (Attr.to_string a) = Some a);
  assert (Option.map Attr.to_string (Attr.set "id" "y" a) = Some {|{#y .a .b k="v w"}|});
  assert (Attr.to_string Attr.empty = "");
  assert (Attr.of_string "{.a .b}" = Some [ "class", "a b" ]);
  assert (Attr.of_string "{% note %}" = Some Attr.empty);
  List.iter
    (fun s -> assert (Attr.of_string s = None))
    [ ""; "#x"; "{#x"; "{#x} "; "{a=}"; "{!}" ];
  assert (Attr.is_valid a && Attr.is_valid Attr.empty);
  assert (not (Attr.is_valid [ "k", "1"; "k", "2" ]));
  assert (not (Attr.is_valid [ "a b", "v" ]));
  assert (Attr.to_string (Attr.remove "id" a) = {|{.a .b k="v w"}|});
  assert (Attr.remove "none" a = a);
  assert (Option.map Attr.to_string (Attr.set_classes [ "c"; "d" ] a) = Some {|{#x .c .d k="v w"}|});
  assert (Option.map Attr.classes (Attr.set_classes [] a) = Some []);
  assert (Attr.set_classes [] a = Some (Attr.remove "class" a));
  assert (Attr.set_classes [ "c"; "d e" ] a = None);
  assert (Attr.set "a b" "v" Attr.empty = None);
  assert (Attr.set "" "v" Attr.empty = None);
  assert (Attr.add_class "a b" Attr.empty = None);
  match Attr.set_exn "a b" "v" Attr.empty with
  | _ -> failwith "a key with a space is refused"
  | exception Invalid_argument _ -> ()
;;

(* Source of part of a tree. *)
let () =
  let d = Doc.of_string "{.c}\n> a *b*\\\n> c\n\npara\n" in
  match Doc.blocks d with
  | [ (Node (_, _, Block.BlockQuote [ Node (_, _, Block.Para ils) ]) as quote); _ ] ->
    assert (Source.of_blocks [ quote ] = "{.c}\n> a {*b*}\\\n> c");
    assert (Source.of_inlines ils = "a {*b*}\\\nc")
  | _ -> failwith "unexpected document"
;;
