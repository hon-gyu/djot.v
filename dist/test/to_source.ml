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
