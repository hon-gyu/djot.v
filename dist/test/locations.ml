(* ai-disclosure: ai-generated *)

(* Source locations: node ranges, line positions, delimiting syntax and
   the parts of a node. Compared against locations.expected. *)

open Djot

let header s = Printf.printf "\n== %s\n" s

let print_range ?(lines = false) label d t =
  let line (n, start) = Printf.sprintf "%d (at %d)" n start in
  Printf.printf
    "%s%s%s\n"
    label
    (Outline.range d t)
    (if lines
     then
       Printf.sprintf
         ", lines %s to %s"
         (line (Textloc.first_line t))
         (line (Textloc.last_line t))
     else "")
;;

(* Block ranges. A heading opens a section. A block's range excludes
   its attribute lines; a div's and a code block's run to the closing
   fence. *)
let () =
  header "blocks";
  Outline.show "# hi\n\nbody\n";
  Outline.show "{#id}\n{.cls}\npara\n";
  Outline.show "{#i}\n::: warn\ninside\n:::\n";
  Outline.show "```py\nx = 1\n```\n"
;;

(* Line positions: a line number and the byte its line starts at. *)
let () =
  header "lines";
  List.iter
    (fun src ->
      let d = Doc.of_string ~locs:true src in
      List.iter
        (fun n -> print_range ~lines:true "block" d (Doc.textloc d n))
        (Doc.blocks d))
    [ "# hi\n\nbody\n"; "```py\nx = 1\n```\n" ]
;;

(* Inline ranges, containers before their contents. *)
let () =
  header "inlines";
  Outline.show "a [link](dest){.c} b";
  Outline.show "k [r][lbl] l";
  Outline.show "p [^fn] q";
  Outline.show "i ![alt](i.png) j";
  Outline.show "s [txt]{.c} t";
  Outline.show
    ~profile:(Profile.with_ext_wikilinks true Profile.djot)
    "p [[a|b]] ![[c]] q";
  Outline.show ~profile:(Profile.with_ext_dollar_math true Profile.djot) "a $x$ b";
  Outline.show ~profile:(Profile.with_ext_tags true Profile.djot) "p :kbd[a] q"
;;

(* A callout's title and a key's label are located like any other
   inline. *)
let () =
  header "extensions";
  let callouts = Profile.with_ext_callouts true Profile.djot in
  Outline.show ~profile:callouts "> [!warning]- Do not rename\n> body\n";
  Outline.show ~profile:callouts "> [!note] T  \n";
  Outline.show ~profile:(Profile.with_ext_keyed true Profile.djot) "> key: value\n"
;;

(* A node's delimiting syntax, in source order; an unclosed div has no
   closing fence. *)
let () =
  header "syntax";
  List.iter
    (fun src ->
      Printf.printf "\n%s\n" (Outline.quote src);
      let d = Doc.of_string ~locs:true src in
      List.iter
        (fun n ->
          List.iter
            (fun (r, t) ->
              print_range
                (match (r : Doc.syntax) with
                 | RAttrSpec -> "RAttrSpec"
                 | ROpenFence -> "ROpenFence"
                 | RCloseFence -> "RCloseFence")
                d
                t)
            (Doc.syntax_locs d n))
        (Doc.blocks d))
    [ "{#i}\n::: warn\ninside\n:::\n"; "```py\nx\n```\n"; "::: a\nx\n" ]
;;

(* The parts of a list, a definition list and a table. *)
let () =
  header "parts";
  List.iter
    (fun src ->
      Printf.printf "\n%s\n" (Outline.quote src);
      let d = Doc.of_string ~locs:true src in
      let loc label t = print_range label d t in
      List.iter
        (fun n ->
          match Doc.parts d n with
          | NoParts -> print_endline "NoParts"
          | Items l -> List.iter (loc "item") l
          | DefItems l ->
            List.iter
              (fun (i, t, df) ->
                loc "item" i;
                loc "  term" t;
                loc "  def" df)
              l
          | TableRows (cap, rows) ->
            Option.iter (loc "caption") cap;
            List.iter
              (fun (r, cells) ->
                loc "row" r;
                List.iter (loc "  cell") cells)
              rows)
        (Doc.blocks d))
    [ "- a\n- b\n"; ": t\n\n  d\n"; "| a | b |\n| 1 | 2 |\n^ cap\n" ]
;;

(* Every footnote definition's label is located. *)
let () =
  header "footnote labels";
  let d = Doc.of_string ~locs:true "[^a]\n\n[^a]: one\n\n> [^a]: two\n" in
  List.iter
    (fun n -> print_range ~lines:true "label" d (Doc.footnote_label_loc d n))
    (Doc.footnote_defs d)
;;

(* Building a range from two others. *)
let () =
  header "reloc";
  let d = Doc.of_string ~locs:true "a\n\nb\n" in
  match Doc.blocks d with
  | [ a; b ] ->
    let t = Textloc.reloc ~first:(Doc.textloc d a) ~last:(Doc.textloc d b) in
    print_range ~lines:true "reloc" d t;
    assert (
      t = Textloc.make ~first_byte:0 ~last_byte:3 ~first_line:(1, 0) ~last_line:(3, 3))
  | _ -> failwith "unexpected document"
;;

(* Without locations every range is none and there is no syntax. *)
let () =
  let d = Doc.of_string "# hi\n\n```\nx\n```\n" in
  assert (List.for_all (fun n -> Textloc.is_none (Doc.textloc d n)) (Doc.blocks d));
  assert (List.for_all (fun n -> Doc.syntax_locs d n = []) (Doc.blocks d))
;;
