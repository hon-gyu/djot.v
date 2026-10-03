(* ai-disclosure: ai-generated *)

open Djot

let docs =
  [ ""
  ; "\n"
  ; "a"
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
  ; "# a\n\n# a\n\n## b\n\n- a\n- b\n\n::: d\nx\n:::\n"
  ; "> q\r\n\r\n| a |\r\n\r\n- b"
  ; "```\nopen\n\n"
  ]
;;

let feed_all feed t parts =
  List.fold_left
    (fun (acc, t) x ->
      let bs, t = feed t x in
      acc @ bs, t)
    ([], t)
    parts
;;

(* [s] cut into chunks of [k] bytes. *)
let chunks k s =
  let n = String.length s in
  List.init ((n + k - 1) / k) (fun i -> String.sub s (i * k) (min k (n - (i * k))))
;;

let same a b =
  For_testing.kernel a = For_testing.kernel b
  && Doc.source a = Doc.source b
  && Doc.footnote_defs a = Doc.footnote_defs b
;;

(* However the input is cut, the returned blocks followed by [peek] are
   the parse, each returned block was already in an earlier [peek], and
   [finish] is [Doc.of_string]. *)
let () =
  List.iter
    (fun locs ->
      List.iter
        (fun src ->
          let expected = Doc.of_string ~locs src in
          let check feed parts =
            let t = Stream.start ~locs () in
            let bs, t = feed_all feed t parts in
            assert (bs @ Stream.peek t = For_testing.parsed expected);
            let d = Stream.finish t in
            assert (same d expected);
            List.iter (fun b -> assert (Doc.textloc d b = Doc.textloc expected b)) bs
          in
          for k = 1 to String.length src + 1 do
            check Stream.feed_string (chunks k src)
          done;
          (* [feed_line] ends each line, so it matches when the source does. *)
          if src = "" || src.[String.length src - 1] = '\n'
          then check Stream.feed_line (Kernel.Strings.split_lines src))
        docs)
    [ false; true ]
;;

(* A returned block is never returned again, and the blocks returned so
   far stay a prefix of the parse of any longer input. *)
let () =
  let src = List.nth docs 3 in
  let whole = For_testing.parsed (Doc.of_string src) in
  let rec prefix a b =
    match a, b with
    | [], _ -> true
    | x :: a, y :: b -> x = y && prefix a b
    | _ :: _, [] -> false
  in
  ignore
    (List.fold_left
       (fun (acc, t) c ->
         let bs, t = Stream.feed_string t c in
         let acc = acc @ bs in
         assert (prefix acc whole);
         assert (acc @ Stream.peek t = For_testing.parsed (Stream.finish t));
         acc, t)
       ([], Stream.start ())
       (chunks 3 src))
;;

(* An earlier stream value can be continued again. *)
let () =
  let _, t = Stream.feed_string (Stream.start ()) "a\n\n" in
  let _, x = Stream.feed_string t "b\n" in
  let _, y = Stream.feed_string t "c\n" in
  assert (same (Stream.finish x) (Doc.of_string "a\n\nb\n"));
  assert (same (Stream.finish y) (Doc.of_string "a\n\nc\n"));
  assert (same (Stream.finish t) (Doc.of_string "a\n\n"))
;;

(* The finished document can be edited. *)
let () =
  let _, t = Stream.feed_string (Stream.start ()) "a\n\nb\n" in
  let d = Doc.replace_lines (Stream.finish t) ~first:3 ~last:3 "# c\n" in
  assert (same d (Doc.of_string "a\n\n# c\n"))
;;

(* A block is returned by the line that closes it, and the open one is
   in [peek]. *)
let () =
  let n (bs, t) = List.length bs, List.length (Stream.peek t), t in
  let t = Stream.start () in
  let r, p, t = n (Stream.feed_string t "a\nb") in
  assert ((r, p) = (0, 1));
  let r, p, t = n (Stream.feed_string t "\n\n- x\n") in
  assert ((r, p) = (1, 1));
  let r, p, t = n (Stream.feed_line t "") in
  assert ((r, p) = (0, 1));
  let r, p, _ = n (Stream.feed_line t "c") in
  assert ((r, p) = (1, 1))
;;
