(* ai-disclosure: autonomous *)

(* The inline grammar (`dev/InlineGrammar.v`) against the specification's
   reading (`ref_read`, `Precedence.v`), on paragraphs over the precedence
   alphabet.

   Usage:
     grammar [N] [--len L] [--seed S] [--verbose]

   The grammar is not proved equal to `valid`; this is what checks it.
   Every paragraph must have exactly one parse, with the pairs and the
   openers of `ref_read`.  Two pools: every one-line paragraph of up to L
   pieces (default 5) from a small set, then N random paragraphs of up to
   three lines of up to eight pieces from a larger one (default 5000).
   Exits nonzero on a difference and prints the first few. *)

module P = Djot.Precedence
module G = Djot_fixtures.InlineGrammar

let table = Djot.Inline.djot_table

(* Delimiters bare and braced, brackets with what may follow them,
   parens for destinations, escapes, backticks, and text. *)
let small = [| "_"; "*"; "{_"; "_}"; "["; "]"; "("; ")"; "a"; " "; "\\"; "`" |]

let pieces =
  [| "_"; "*"; "^"; "~"; "{_"; "_}"; "{*"; "*}"; "{="; "=}"; "{+"; "+}";
     "["; "]"; "]("; "]["; "("; ")"; "a"; "b"; " "; "\\"; "\\*"; "\\]";
     "\\("; "[a]("; "[a]["; "`"; "``"; "`a`"; "`*`"; "$"; "$`a`"; "$$`*`" |]

let sort_pairs m = List.sort compare m
let sort_os os = List.sort_uniq compare os

let bad = ref 0
let checked = ref 0

let check l =
  if List.for_all (P.over_alphabet table) l then begin
    incr checked;
    let ts = P.para_string l in
    let m, os = P.ref_read table ts in
    let ok =
      match G.grammar_read table ts with
      | [ (m', os') ] -> sort_pairs m = sort_pairs m' && sort_os os = sort_os os'
      | _ -> false
    in
    if not ok then begin
      incr bad;
      if !bad <= 5 then begin
        Printf.printf "--- %d parses:\n%s\n"
          (List.length (G.grammar_read table ts))
          (String.concat "\n" (List.map (Printf.sprintf "  %S") l))
      end
    end
  end

(* Every string of up to `len` pieces from `small`. *)
let exhaustive len =
  let rec go k acc =
    check [ acc ];
    if k < len then Array.iter (fun p -> go (k + 1) (acc ^ p)) small
  in
  go 0 ""

(* Kept short: the enumerator backtracks, and each opener with a closer
   of its kind ahead doubles its work, so a long line of mixed
   delimiters is exponential.  The exhaustive pool covers the small
   cases completely; this one reaches the pieces it leaves out. *)
let gen_line () =
  let n = Random.int 9 in
  String.concat "" (List.init n (fun _ -> pieces.(Random.int (Array.length pieces))))

let gen_para () = List.init (1 + Random.int 3) (fun _ -> gen_line ())

let () =
  let n = ref 5000 and len = ref 5 and seed = ref 7 and verbose = ref false in
  let rec args = function
    | [] -> ()
    | "--len" :: v :: rest -> len := int_of_string v; args rest
    | "--seed" :: v :: rest -> seed := int_of_string v; args rest
    | "--verbose" :: rest -> verbose := true; args rest
    | v :: rest -> n := int_of_string v; args rest
  in
  args (List.tl (Array.to_list Sys.argv));
  Random.init !seed;
  exhaustive !len;
  if !verbose then Printf.printf "exhaustive: %d paragraphs\n%!" !checked;
  for _ = 1 to !n do check (gen_para ()) done;
  Printf.printf "grammar against ref_read: %d paragraphs over the alphabet, %d differ\n"
    !checked !bad;
  exit (if !bad = 0 then 0 else 1)
