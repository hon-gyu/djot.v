(* ai-disclosure: ai-generated *)

(* Tests of the hand-written API: parsing, profiles, locations, traversals,
   HTML. *)

open Djot

let bytes t = (Textloc.first_byte t, Textloc.last_byte t)
let lines t = (Textloc.first_line t, Textloc.last_line t)

(* A heading opens a section carrying its id; locations are inclusive
   byte ranges with one-based lines. *)
let () =
  let src = "# hi\n\nbody\n" in
  let d = Doc.of_string ~locs:true src in
  (match Doc.blocks d with
   | [ (Node (_, attrs, Block.Section [ heading; para ]) as section) ] ->
       assert (Attr.id attrs = Some "hi");
       assert (bytes (Doc.textloc d section) = (0, 9));
       assert (lines (Doc.textloc d section) = ((1, 0), (3, 6)));
       assert (bytes (Doc.textloc d heading) = (0, 3));
       assert (bytes (Doc.textloc d para) = (6, 9))
   | _ -> failwith "unexpected document");
  let plain = Doc.of_string src in
  assert (List.for_all (fun n -> Textloc.is_none (Doc.textloc plain n)) (Doc.blocks plain))

(* A block's range excludes its attribute lines; a div's and a code
   block's run to the closing fence. *)
let () =
  let d = Doc.of_string ~locs:true "{#id}\n{.cls}\npara\n" in
  (match Doc.blocks d with
   | [ para ] -> assert (bytes (Doc.textloc d para) = (13, 16))
   | _ -> failwith "unexpected document");
  let d = Doc.of_string ~locs:true "{#i}\n::: warn\ninside\n:::\n" in
  (match Doc.blocks d with
   | [ (Node (_, _, Block.Div [ para ]) as div) ] ->
       assert (bytes (Doc.textloc d div) = (5, 23));
       assert (bytes (Doc.textloc d para) = (14, 19))
   | _ -> failwith "unexpected document");
  let d = Doc.of_string ~locs:true "```py\nx = 1\n```\n" in
  match Doc.blocks d with
  | [ code ] -> assert (lines (Doc.textloc d code) = ((1, 0), (3, 12)))
  | _ -> failwith "unexpected document"

(* Inline ranges in document order, containers before their contents. *)
let () =
  let rec ranges d ns =
    List.concat_map
      (fun n ->
        let kids =
          match Node.contents n with
          | Inline.Link (l, _) | Inline.Image (l, _) | Inline.Span l -> ranges d l
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
  check "a [link](dest){.c} b" [ (0, 1); (2, 13); (3, 6); (18, 19) ];
  check "k [r][lbl] l" [ (0, 1); (2, 9); (3, 3); (10, 11) ];
  check "p [^fn] q" [ (0, 1); (2, 6); (7, 8) ];
  check "i ![alt](i.png) j" [ (0, 1); (2, 14); (4, 6); (15, 16) ];
  check "s [txt]{.c} t" [ (0, 1); (2, 6); (3, 5); (11, 12) ];
  check ~profile:(Profile.with_ext_wikilinks true Profile.djot) "p [[a|b]] ![[c]] q"
    [ (0, 1); (2, 8); (9, 9); (10, 15); (16, 17) ]

(* The HTML tree serializes to the rendered document. *)
let () =
  let src = "# hi\n\n*a* [b](c)[^n]\n\n[^n]: note\n" in
  let d = Doc.of_string src in
  assert (Html.to_string (Html.tree d) = Html.of_doc d);
  assert (Html.of_doc d = Kernel.Html.convert src)

(* The fold visits footnote bodies after the blocks, in source order. *)
let () =
  let d = Doc.of_string "*a* b [c](d)[^n]\n\n[^n]: note\n" in
  let inline _ acc = function
    | Node (_, _, Inline.Str s) -> Folder.ret (s :: acc)
    | _ -> Folder.default
  in
  let strs = Folder.fold_doc (Folder.make ~inline ()) [] d in
  assert (List.rev strs = [ "a"; " b "; "c"; "note" ])

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

(* Labels resolve against explicit definitions, then headings. *)
let () =
  let d = Doc.of_string "# Head\n\n[x]: /u\n\n[a][x] [b][Head]\n" in
  assert (Option.map fst (Doc.reference d "x") = Some "/u");
  assert (Option.map fst (Doc.reference d "Head") = Some "#Head");
  assert (List.map fst (Doc.references d) = [ "x" ])

(* Wikilinks are an extension, off in djot. *)
let () =
  let src = "[[a|b]]\n" in
  let first d =
    match Doc.blocks d with
    | [ Node (_, _, Block.Para [ Node (_, _, il) ]) ] -> il
    | _ -> failwith "unexpected document"
  in
  assert (first (Doc.of_string ~profile:(Profile.with_ext_wikilinks true Profile.djot) src)
          = Inline.Ext_wikilink (false, "a", Some "b"));
  assert (first (Doc.of_string src) <> Inline.Ext_wikilink (false, "a", Some "b"))

(* Profiles: a named starting point, then per-construct switches. *)
let () =
  let blocks p src = List.map Node.contents (Doc.blocks (Doc.of_string ~profile:p src)) in
  let table = "| a |\n|---|\n" in
  assert (match blocks Profile.djot table with [ Block.Table _ ] -> true | _ -> false);
  assert (match blocks (Profile.with_tables false Profile.djot) table with
          | [ Block.Para _ ] -> true | _ -> false);
  let strong = function
    | [ Block.Para [ Node (_, _, Inline.Strong [ Node (_, _, Inline.Str "a") ]) ] ] -> true
    | _ -> false
  in
  assert (strong (blocks Profile.markdown_like "**a**\n"));
  assert (not (strong (blocks Profile.djot "**a**\n")))
