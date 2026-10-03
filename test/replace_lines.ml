(* ai-disclosure: ai-generated *)

open Djot

let bytes t = Textloc.first_byte t, Textloc.last_byte t

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
                  assert (For_testing.kernel got = For_testing.kernel expected);
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
