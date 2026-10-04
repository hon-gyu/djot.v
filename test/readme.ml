(* ai-disclosure: ai-generated *)

(* [readme README.md] prints the README with its property tables written
   again from theories/Properties.v: the text between the two marker lines
   is replaced, the rest is kept.  The status is the one of the djot
   profile. *)

open Djot

let start = "<!-- properties: generated from theories/Properties.v -->"
let stop = "<!-- /properties -->"

let status (p : Properties.property) =
  let theorems =
    match p.p_theorems with
    | [] -> ""
    | ts -> ": " ^ String.concat ", " (List.map (Printf.sprintf "`%s`") ts)
  in
  match p.p_status Profile.djot_options with
  | Proved -> "proved" ^ theorems
  | Conditional c -> Printf.sprintf "conditional%s. %s" theorems c
  | Broken (reason, _) -> "broken. " ^ reason
  | Conjectured -> "conjectured"
  | Unknown -> "unknown"
  | Inapplicable why -> "inapplicable. " ^ why
;;

let tables () =
  let groups =
    List.fold_left
      (fun gs (p : Properties.property) ->
        if List.mem p.p_group gs then gs else gs @ [ p.p_group ])
      []
      Properties.all
  in
  let cell s = String.concat "\\|" (String.split_on_char '|' s) in
  let table g =
    Printf.printf "\n### %s\n\n| Property | Implication | Status |\n| --- | --- | --- |\n" g;
    List.iter
      (fun (p : Properties.property) ->
        if p.p_group = g
        then
          Printf.printf
            "| %s | %s | %s |\n"
            (cell p.p_statement)
            (cell p.p_implication)
            (cell (status p)))
      Properties.all
  in
  List.iter table groups;
  print_newline ()
;;

let () =
  let lines = In_channel.with_open_bin Sys.argv.(1) In_channel.input_lines in
  let rec keep = function
    | [] -> failwith "README.md: no properties marker"
    | l :: rest ->
      print_endline l;
      if l = start
      then (
        tables ();
        skip rest)
      else keep rest
  and skip = function
    | [] -> failwith "README.md: the properties marker is not closed"
    | l :: rest ->
      if l = stop
      then (
        print_endline l;
        List.iter print_endline rest)
      else skip rest
  in
  keep lines
;;
