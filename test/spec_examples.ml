(* ai-disclosure: ai-generated *)

(* [spec_examples FILE.dj ...] prints SpecExamples.v: one Rocq
   [Example] per [example] block of the extension reference, stating that
   the block's source renders to the block's HTML under the extension's
   setting.

   The blocks are found by scanning lines, not by parsing djot: the
   parser must not be what decides which of its own examples are checked.
   No library, so that this builds before the development does. *)

let quote s = String.concat "\"\"" (String.split_on_char '"' s)
let text lines = String.concat "" (List.map (fun l -> l ^ "\n") lines)

let examples file =
  let name = Filename.chop_suffix (Filename.basename file) ".dj" in
  let ident = String.map (fun c -> if c = '-' then '_' else c) name in
  let lines = In_channel.with_open_bin file In_channel.input_lines in
  let count = ref 0 in
  let rec scan = function
    | [] -> ()
    | "``` example" :: rest -> block [] rest
    | _ :: rest -> scan rest
  and block source = function
    | "." :: rest -> expected (List.rev source) [] rest
    | "```" :: _ | [] -> failwith (file ^ ": an example without its \".\" line")
    | l :: rest -> block (l :: source) rest
  and expected source html = function
    | "```" :: rest ->
      incr count;
      Printf.printf
        "Example %s_%d :\n  renders Spec.%s\n\"%s\"\n\"%s\".\nProof. vm_compute. reflexivity. Qed.\n\n"
        ident
        !count
        ident
        (quote (text source))
        (quote (text (List.rev html)));
      scan rest
    | [] -> failwith (file ^ ": an example that is not closed")
    | l :: rest -> expected source (l :: html) rest
  in
  scan lines;
  if !count = 0 then failwith (file ^ ": no example")
;;

let () =
  print_string
    "(* Written from spec/*.dj by test/spec_examples.ml.  Not a source file. *)\n\n\
     From Stdlib Require Import String.\n\
     From DjotV Require Import Spec.\n\
     Local Open Scope string_scope.\n\n";
  List.iter examples (List.sort compare (List.tl (Array.to_list Sys.argv)))
;;
