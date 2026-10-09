(* ai-disclosure: ai-generated *)

(* Tests of the hand-written API that check properties rather than
   printed output: attributes, HTML, traversals, references. *)

open Djot

(* The HTML tree serializes to the rendered document. *)
let () =
  let src = "# hi\n\n*a* [b](c)[^n]\n\n[^n]: note\n" in
  let d = Doc.of_string src in
  assert (Html.to_string (Html.tree d) = Html.of_doc d);
  assert (Html.of_doc d = Kernel.Html.convert src)
;;

(* A fold over the blocks visits a footnote body under its definition. *)
let () =
  let d = Doc.of_string "*a* b [c](d)[^n]\n\n[^n]: note\n" in
  let inline _ acc = function
    | Node (_, _, Inline.Str s) -> Folder.ret (s :: acc)
    | _ -> Folder.default
  in
  let strs =
    List.fold_left (Folder.fold_block (Folder.make ~inline ())) [] (Doc.blocks d)
  in
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
  assert (
    Option.map Attr.to_string (Attr.set_classes [ "c"; "d" ] a)
    = Some {|{#x .c .d k="v w"}|});
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

(* Every footnote definition is kept, but the note map keeps the last
   one per label. *)
let () =
  let src = "[^a]\n\n[^a]: one\n\n> [^a]: two\n" in
  let d = Doc.of_string ~locs:true src in
  let block _ acc = function
    | Node (_, _, Block.FootnoteDef _) -> Folder.ret (acc + 1)
    | _ -> Folder.default
  in
  assert (List.fold_left (Folder.fold_block (Folder.make ~block ())) 0 (Doc.blocks d) = 2);
  match Doc.footnotes d with
  | [ ("a", [ Node (_, _, Block.Para [ Node (_, _, Inline.Str "two") ]) ]) ] -> ()
  | _ -> failwith "unexpected note map"
;;

(* A definition stays where it was written: the source parses back to the
   same document, a fold visits its text once, and deleting it empties the
   map. *)
let () =
  let src = "[^a]: one\n\nx[^a]\n" in
  let d = Doc.of_string src in
  assert (For_testing.kernel (Doc.of_string (Doc.to_string d)) = For_testing.kernel d);
  let inline _ acc = function
    | Node (_, _, Inline.Str s) -> Folder.ret (s :: acc)
    | _ -> Folder.default
  in
  assert (
    List.fold_left (Folder.fold_block (Folder.make ~inline ())) [] (Doc.blocks d)
    = [ "x"; "one" ]);
  let block _ = function
    | Node (_, _, Block.FootnoteDef _) -> Mapper.delete
    | _ -> Mapper.default
  in
  assert (Doc.footnotes (Mapper.map_doc (Mapper.make ~block ()) d) = [])
;;

(* A document made from the blocks of another has the same blocks and
   tables. Its derived identifiers were on the blocks, so they count as
   written. *)
let () =
  let d = Doc.of_string "# a\n\n{#x}\n## b\n\nc[^n]\n\n[^n]: note\n\n[r]: /u\n\n# a\n" in
  let d' = Doc.make (Doc.blocks d) in
  assert (Doc.blocks d' = Doc.blocks d);
  assert (Doc.footnotes d' = Doc.footnotes d);
  assert (Doc.references d' = Doc.references d);
  assert (Doc.auto_references d' = Doc.auto_references d);
  assert (Html.of_doc d' = Html.of_doc d);
  assert (Doc.auto_identifiers d = [ "a"; "a-1" ]);
  assert (Doc.auto_identifiers d' = [])
;;

(* Made from its source blocks, a document derives the same identifiers
   again and prints as it did. *)
let () =
  let d = Doc.of_string "# a\n\n{#x}\n## b\n\n- # a\n\n# a\n" in
  let d' = Doc.make (Doc.source_blocks d) in
  assert (Doc.auto_identifiers d' = Doc.auto_identifiers d);
  assert (Doc.to_string d' = Doc.to_string d);
  assert (Doc.blocks d' = Doc.blocks d)
;;

(* Mapping derives the identifiers again: with the first heading deleted,
   the second takes the identifier it had. A written one stays. *)
let () =
  let d = Doc.of_string "# a\n\n{#x}\n# b\n\n# a\n" in
  let first = ref true in
  let block _ = function
    | Node (_, _, Block.Section (_ :: rest)) when !first ->
      first := false;
      Mapper.ret (Node.make (Block.Div ("", rest)))
    | _ -> Mapper.default
  in
  let d = Mapper.map_doc (Mapper.make ~block ()) d in
  assert (Doc.auto_identifiers d = [ "a" ]);
  assert (Doc.to_string d = ":::\n:::\n\n{#x}\n# b\n\n# a")
;;

(* A mapper that drops an item keeps the range of the item it keeps. *)
let () =
  let d = Doc.of_string ~locs:true "- a\n- b\n" in
  let block _ = function
    | Node (p, a, Block.BulletList (c, sp, _ :: it :: _)) ->
      Mapper.ret (Node (p, a, Block.BulletList (c, sp, [ it ])))
    | _ -> Mapper.default
  in
  let mapped = Mapper.map_doc (Mapper.make ~block ()) d in
  match Doc.blocks mapped with
  | [ Node (_, _, Block.BulletList (_, _, [ it ])) ] ->
    assert (Textloc.first_byte (Doc.textloc mapped it) = 4)
  | _ -> failwith "unexpected document"
;;

(* Blocks built in code render without a document, with identifiers,
   sections and footnotes resolved among them; so do the blocks a stream
   returns. *)
let () =
  let para s = Node.make (Block.Para [ Node.make (Inline.Str s) ]) in
  let built =
    [ Node.make (Block.Heading (1, [ Node.make (Inline.Str "T") ]))
    ; Node.make (Block.Para [ Node.make (Inline.FootnoteReference "n") ])
    ; Node.make (Block.FootnoteDef ("n", [ para "note" ]))
    ]
  in
  assert (Html.of_blocks built = Html.of_doc (Doc.of_string "# T\n\n[^n]\n\n[^n]: note\n"));
  let src = "# a\n\nx[^n] [a][]\n\n# a\n\n[^n]: one\n" in
  let bs, t = Stream.feed_string (Stream.start ()) src in
  assert (Html.of_blocks (bs @ Stream.peek t) = Html.of_doc (Doc.of_string src))
;;

(* A source gives its text and the parse of it; an edit leaves the
   source it was made from as it was; a mapped document is not edited. *)
let () =
  let s = Source.of_string "one\n\ntwo\n" in
  assert (Source.to_string s = "one\n\ntwo\n");
  let s' = Source.replace_lines s ~first:3 ~last:3 "three" in
  assert (Source.to_string s = "one\n\ntwo\n");
  assert (Source.to_string s' = "one\n\nthree");
  assert (
    Source.to_string (Source.replace_lines s ~first:4 ~last:3 "end") = "one\n\ntwo\nend");
  assert (
    Source.to_string (Source.replace_lines s ~first:1 ~last:0 "top") = "top\none\n\ntwo\n");
  assert (Html.of_doc (Source.doc s') = Html.of_doc (Doc.of_string "one\n\nthree"))
;;

(* A hole as a raw inline in format `hole`, which is what `` `e`{=hole} ``
   reads as. *)
let () =
  let profile = Profile.with_ext_holes true Profile.djot in
  let d = Doc.of_string ~profile "a %`x` b\n" in
  assert (Html.of_doc d = "<p>a <code data-hole=\"\">x</code> b</p>\n");
  let raw = function
    | Node (_, _, Inline.RawInline ("hole", s)) -> [ s ]
    | _ -> []
  in
  let raws d =
    List.concat_map
      (fun n ->
         Folder.fold_block
           (Folder.make
              ~inline:(fun _ acc n ->
                match raw n with [] -> Folder.default | r -> Folder.ret (acc @ r))
              ())
           []
           n)
      (Doc.blocks d)
  in
  let d' = Mapper.map_doc Mapper.holes_as_raw d in
  assert (raws d' = [ "x" ]);
  assert (raws d' = raws (Doc.of_string ~profile "a `x`{=hole} b\n"))
;;
