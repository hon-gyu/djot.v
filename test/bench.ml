(* ai-disclosure: ai-generated *)

(* Scaling benchmark: generated input shapes at growing sizes, timed
   through the block and document parse and through `Html.convert`.

   Usage:
     bench                  every shape at 20 KB and 80 KB
     bench SHAPE ...        only the named shapes
     bench --sizes A,B,...  other sizes, in bytes

   `growth` is the last time over the one before it.  At 4x the size a
   linear cost grows about 4x and a quadratic one about 16x; rows past
   8x are marked.  A size whose convert time passes the budget stops
   that shape, so a quadratic shape reports what it reached rather than
   running for minutes.  Times depend on the build profile and machine;
   compare them only with each other. *)

let rep s n = String.concat "" (List.init (max 0 n) (fun _ -> s))

(* Cut into 78-byte lines, so that a shape measures paragraph-level cost
   and not the per-line one. *)
let wrap s =
  String.concat "\n"
    (List.init (String.length s / 78) (fun i -> String.sub s (i * 78) 78))

let shapes = [
  "paragraphs", "short paragraphs",
    (fun n -> rep "word word word word word word word.\n\n" (n / 36));
  "paragraph", "one paragraph of short lines",
    (fun n -> rep "word word word word word word word\n" (n / 35));
  "line", "one line of words",
    (fun n -> rep "word " (n / 5));
  "punctuation", "one line of period and letter pairs",
    (fun n -> rep ".a" (n / 2));
  "commas", "one line of words and commas",
    (fun n -> rep "word, " (n / 6));
  "candidates", "one line of failed autolink candidates",
    (fun n -> rep "<a " (n / 3));
  "verbatim", "code spans, wrapped",
    (fun n -> wrap (rep "`a" (n / 2)));
  "brackets", "unclosed [, wrapped",
    (fun n -> wrap (rep "[a" (n / 2)));
  "emphasis", "unclosed _, wrapped",
    (fun n -> wrap (rep "_a " (n / 3)));
  "links", "inline links, wrapped",
    (fun n -> wrap (rep "[a](b) " (n / 7)));
  "headings", "the same heading repeated",
    (fun n -> rep "# heading\n\n" (n / 11));
  "lists", "nested list items",
    (fun n ->
       String.concat ""
         (List.init (n / 40) (fun i -> String.make (2 * (i mod 20)) ' ' ^ "- a\n")));
  "table", "table rows",
    (fun n -> "| a | b |\n|---|---|\n" ^ rep "| x | y |\n" (n / 10));
]

let budget_ms = 5000.

(* Best of up to three runs, fewer when one run is already slow. *)
let time f x =
  let best = ref infinity and runs = ref 0 in
  while !runs < 3 && (!runs = 0 || !best < 200.) do
    let t0 = Unix.gettimeofday () in
    ignore (Sys.opaque_identity (f x));
    best := min !best ((Unix.gettimeofday () -. t0) *. 1000.);
    incr runs
  done;
  !best

let parse_doc s =
  Djot.Document.parse_doc Djot.Inline.djot_table Djot.Step.djot_bconfig
    Djot.Ast.semantic_pos s

let growth = function
  | a :: b :: _ when b > 0. -> Some (a /. b)
  | _ -> None

let run sizes (name, desc, gen) =
  Printf.printf "%s (%s)\n" name desc;
  let rec go parses converts = function
    | [] -> ()
    | n :: rest ->
      let s = gen n in
      let p = time parse_doc s and c = time Djot.Html.convert s in
      let g xs x =
        match growth (x :: xs) with
        | Some r -> Printf.sprintf "%5.1fx%s" r (if r > 8. then " !" else "  ")
        | None -> "        "
      in
      Printf.printf "  %8d B  parse %9.1f ms %s  convert %9.1f ms %s\n%!"
        (String.length s) p (g parses p) c (g converts c);
      if c > budget_ms then
        (if rest <> [] then Printf.printf "  (over %.0f ms budget, larger sizes skipped)\n" budget_ms)
      else go (p :: parses) (c :: converts) rest
  in
  go [] [] sizes

let () =
  let sizes = ref [ 20_000; 80_000 ] and only = ref [] in
  let rec args = function
    | [] -> ()
    | "--sizes" :: v :: rest ->
      sizes := List.map int_of_string (String.split_on_char ',' v);
      args rest
    | name :: rest when List.exists (fun (n, _, _) -> n = name) shapes ->
      only := name :: !only;
      args rest
    | a :: _ ->
      prerr_endline ("bench: unknown argument " ^ a ^ "; shapes: "
                     ^ String.concat " " (List.map (fun (n, _, _) -> n) shapes));
      exit 2
  in
  args (List.tl (Array.to_list Sys.argv));
  List.iter
    (fun ((name, _, _) as shape) ->
       if !only = [] || List.mem name !only then run !sizes shape)
    shapes
