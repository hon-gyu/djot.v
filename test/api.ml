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
  assert (List.length (Doc.footnote_defs d) = 2);
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
  assert (Folder.fold_doc (Folder.make ~inline ()) [] d = [ "x"; "one" ]);
  let block _ = function
    | Node (_, _, Block.FootnoteDef _) -> Mapper.delete
    | _ -> Mapper.default
  in
  assert (Doc.footnotes (Mapper.map_doc (Mapper.make ~block ()) d) = [])
;;

(* A mapper that drops an item keeps the range of the item it keeps. *)
let () =
  let d = Doc.of_string ~locs:true "- a\n- b\n" in
  let block _ = function
    | Node (p, a, Block.BulletList (sp, _ :: it :: _)) ->
      Mapper.ret (Node (p, a, Block.BulletList (sp, [ it ])))
    | _ -> Mapper.default
  in
  let mapped = Mapper.map_doc (Mapper.make ~block ()) d in
  match Doc.blocks mapped with
  | [ Node (_, _, Block.BulletList (_, [ it ])) ] ->
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
  assert (Source.to_string (Source.replace_lines s ~first:4 ~last:3 "end") = "one\n\ntwo\nend");
  assert (Source.to_string (Source.replace_lines s ~first:1 ~last:0 "top") = "top\none\n\ntwo\n");
  assert (Html.of_doc (Source.doc s') = Html.of_doc (Doc.of_string "one\n\nthree"))
;;
