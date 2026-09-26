(* ai-disclosure: ai-generated *)

(* A consumer of the public API: parsing, locations, traversals, HTML. *)

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

(* Wikilinks are a dialect switch. *)
let () =
  let src = "[[a|b]]\n" in
  let first d =
    match Doc.blocks d with
    | [ Node (_, _, Block.Para [ Node (_, _, il) ]) ] -> il
    | _ -> failwith "unexpected document"
  in
  assert (first (Doc.of_string ~dialect:(Dialect.with_wikilinks true Dialect.djot) src)
          = Inline.Wikilink (false, "a", Some "b"));
  assert (first (Doc.of_string src) <> Inline.Wikilink (false, "a", Some "b"))
