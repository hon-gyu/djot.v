(* ai-disclosure: autonomous *)

(* `parse (render d) = d` over every canonical document the enumerator
   accepts, in the extracted parser.  No other parser is consulted.

   Usage:
     roundtrip [--keyed | --wiki | --callouts] [DEPTH] [--report FILE] [--verbose]

   The plain pool is what `Generate.gen_roundtrip_1` and `gen_roundtrip_2`
   prove in the kernel at depths 1 and 2; its default depth is 3, which
   takes seconds here and about twenty minutes as `dev/check/Deep.v`.
   `--keyed` reads the pool with keyed blocks on (default depth 1), and
   `--wiki` the ordinary pool with wikilinks on plus each wikilink leaf in
   the containers (default depth 2), and `--callouts` the callout pool with
   callouts and wikilinks on (default depth 1); djot.js has none of these
   extensions.

   The pinned counts are the coverage witness: the fragment must grow when
   a construct lands, and a shrinking count is a regression that zero
   mismatches would not show.  Update the line when the fragment
   legitimately grows. *)

open Djot_test

let plain_counts = [ (1, 312); (2, 4385); (3, 57857) ]
let keyed_counts = [ (1, 7216); (2, 98980) ]
let wiki_counts = [ (1, 342); (2, 4415); (3, 57887) ]
let callout_counts = [ (1, 337); (2, 4410); (3, 57882) ]

let run ~pool depth r verbose =
  let t0 = Unix.gettimeofday () in
  let module G = Djot_fixtures.Generate in
  let name, accepted, lhs, counts =
    match pool with
    | `Plain -> "", G.accepted, G.rt_lhs, plain_counts
    | `Keyed -> "keyed ", G.keyed_accepted, G.keyed_rt_lhs, keyed_counts
    | `Wiki -> "wiki ", G.wiki_accepted, G.wiki_rt_lhs, wiki_counts
    | `Callouts -> "callout ", G.callout_accepted, G.callout_rt_lhs, callout_counts
  in
  let docs = accepted depth in
  let t1 = Unix.gettimeofday () in
  let total = ref 0 and bad = ref 0 in
  List.iter
    (fun c ->
      incr total;
      if lhs c <> G.rt_rhs c then begin
        incr bad;
        if verbose || !bad <= 5 then
          Report.out r "\n--- roundtrip mismatch %d\n%s\n" !bad
            (Djot_fixtures.Fixtures.render_cb c)
      end)
    docs;
  let t2 = Unix.gettimeofday () in
  Report.out r
    "\n== %sroundtrip: depth %d, %d documents, %.2fs enumerate, %.2fs check ==\n"
    name depth !total (t1 -. t0) (t2 -. t1);
  Report.out r "parse (render d) = d   ok %6d   mismatch %4d\n" (!total - !bad)
    !bad;
  let count_ok =
    match List.assoc_opt depth counts with
    | None -> Report.out r "(no pinned count for depth %d)\n" depth; true
    | Some n when n = !total -> true
    | Some n ->
      Report.out r "COUNT MOVED: expected %d accepted at depth %d, got %d\n" n
        depth !total;
      false
  in
  !bad = 0 && count_ok

let () =
  let pool = ref `Plain and depth = ref None in
  let report = ref "" and verbose = ref false in
  let rec args = function
    | [] -> ()
    | "--keyed" :: rest -> pool := `Keyed; args rest
    | "--wiki" :: rest -> pool := `Wiki; args rest
    | "--callouts" :: rest -> pool := `Callouts; args rest
    | "--report" :: v :: rest -> report := v; args rest
    | "--verbose" :: rest -> verbose := true; args rest
    | d :: rest when int_of_string_opt d <> None ->
      depth := int_of_string_opt d; args rest
    | a :: _ -> prerr_endline ("roundtrip: unknown argument " ^ a); exit 2
  in
  args (List.tl (Array.to_list Sys.argv));
  let depth =
    match !depth, !pool with
    | Some d, _ -> d
    | None, `Plain -> 3
    | None, `Keyed -> 1
    | None, `Wiki -> 2
    | None, `Callouts -> 1
  in
  let r = Report.create !report in
  let ok = run ~pool:!pool depth r !verbose in
  Report.save r;
  exit (if ok then 0 else 1)
