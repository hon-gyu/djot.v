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
          let d = Source.of_string ~locs src in
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
                  let got = Source.doc (Source.replace_lines d ~first ~last s) in
                  assert (For_testing.kernel got = For_testing.kernel expected);
                  assert (Doc.footnote_defs got = Doc.footnote_defs expected);
                  assert (ranges got = ranges expected))
                news
            done
          done)
        docs)
    [ false; true ];
  match Source.replace_lines (Source.of_string "a\n") ~first:3 ~last:2 "b" with
  | _ -> failwith "a range past the end is refused"
  | exception Invalid_argument _ -> ()
;;

(* The reported range holds the edited lines, and the lines outside it
   are the same text before and after. *)
let () =
  let src = "a\n\nb\n\n- c\n\n```\nk\n```\n\nd\n" in
  let ls = Array.of_list (Kernel.Strings.split_lines src) in
  let n = Array.length ls in
  let d = Source.of_string src in
  for first = 1 to n + 1 do
    for last = first - 1 to n do
      List.iter
        (fun s ->
          let d', (c : Source.change) = Source.replace_lines_changed d ~first ~last s in
          let ls' = Array.of_list (Kernel.Strings.split_lines (Source.to_string d')) in
          let n' = Array.length ls' in
          assert (c.first <= first && last <= c.old_last);
          assert (c.first - 1 <= c.new_last && c.old_last <= n && c.new_last <= n');
          assert (Array.sub ls 0 (c.first - 1) = Array.sub ls' 0 (c.first - 1));
          assert (n - c.old_last = n' - c.new_last);
          assert (
            Array.sub ls c.old_last (n - c.old_last)
            = Array.sub ls' c.new_last (n' - c.new_last)))
        [ ""; "x\n"; "```\n"; "- z\n"; "# a\n\n" ]
    done
  done
;;

(* An edit that leaves the parser idle is confined to its piece, and the
   blocks around it are the old values. One that opens a fence runs on
   until the parser is idle again at the end of an old piece. *)
let () =
  let d = Source.of_string "a\n\nb\n\nc\n\n```\nk\n```\n\nd\n" in
  let d', (c : Source.change) = Source.replace_lines_changed d ~first:3 ~last:3 "x" in
  assert (c = { first = 3; old_last = 4; new_last = 4 });
  let old = For_testing.parsed (Source.doc d)
  and now = For_testing.parsed (Source.doc d') in
  assert (List.length old = List.length now);
  List.iteri (fun k b -> assert (b == List.nth now k = (k <> 1))) old;
  let _, (c : Source.change) = Source.replace_lines_changed d ~first:3 ~last:3 "```" in
  assert (c = { first = 3; old_last = 10; new_last = 10 });
  let _, (c : Source.change) = Source.replace_lines_changed d ~first:6 ~last:5 "new\n" in
  assert (c = { first = 5; old_last = 6; new_last = 7 })
;;

(* Replacing bytes gives the parse of the source with those bytes
   replaced, for every range. *)
let () =
  List.iter
    (fun locs ->
      List.iter
        (fun src ->
          let d = Source.of_string ~locs src in
          let n = String.length src in
          for first = 0 to n do
            for last = first - 1 to n - 1 do
              List.iter
                (fun s ->
                  let edited =
                    String.sub src 0 first ^ s ^ String.sub src (last + 1) (n - last - 1)
                  in
                  let expected = Doc.of_string ~locs edited in
                  let got, (c : Source.change) =
                    Source.replace_bytes_changed d ~first ~last s
                  in
                  assert (Source.to_string got = edited);
                  let got = Source.doc got in
                  assert (For_testing.kernel got = For_testing.kernel expected);
                  assert (Doc.footnote_defs got = Doc.footnote_defs expected);
                  assert (c.first >= 1 && c.old_last >= c.first - 1))
                [ ""; "x"; "\n"; "x\n"; "\n\n- z"; "```\n" ]
            done
          done)
        [ ""
        ; "a"
        ; "a\nb\n\n# h\n\n- x\n\n- y\nc\n\n```\nk\n```\n"
        ; "> q\r\n\r\n| a |\n\n- b"
        ])
    [ false; true ];
  match Source.replace_bytes (Source.of_string "ab") ~first:1 ~last:2 "" with
  | _ -> failwith "a range past the end is refused"
  | exception Invalid_argument _ -> ()
;;
