(* ai-disclosure: autonomous *)

(* The extracted parser as a filter: djot on stdin, HTML on stdout.

   Usage:
     convert             one document
     convert --batch     a framed batch, as `djotjs.mjs --batch` takes
     convert --time [N]  one document; the best of N (default 5) wall
                         times for the semantic and the located block parse

   The same interface djotjs.mjs has.  Probing a divergence means running
   both on the same bytes, and without this ours is the one that cannot
   be. *)

open Djot_test

let time n input =
  Printf.printf "== time: best of %d over %d bytes ==\n" n (String.length input);
  let time name f =
    let best = ref infinity in
    for _ = 1 to n do
      let t0 = Unix.gettimeofday () in
      ignore (Sys.opaque_identity (f input));
      let t1 = Unix.gettimeofday () in
      if t1 -. t0 < !best then best := t1 -. t0
    done;
    Printf.printf "%-22s %9.3f ms\n" name (!best *. 1000.)
  in
  time "parse_blocks" (fun s ->
    Djot.Step.parse_blocks Djot.Inline.djot_table Djot.Step.djot_bconfig
      Djot.Step.semantic_line_ix Djot.Ast.semantic_pos s);
  time "parse_blocks_located" (fun s ->
    Djot.Reparse.parse_blocks_located Djot.Inline.djot_table
      Djot.Step.djot_bconfig s)

let () =
  let input = In_channel.input_all stdin in
  match List.tl (Array.to_list Sys.argv) with
  | [] -> print_string (Djot.Html.convert input)
  | [ "--batch" ] ->
    print_string
      (Parsers.frame (List.map Djot.Html.convert (Parsers.unframe input)))
  | [ "--time" ] -> time 5 input
  | [ "--time"; n ] when int_of_string_opt n <> None ->
    time (int_of_string n) input
  | _ ->
    prerr_endline "usage: convert [--batch | --time [N]]";
    exit 2
