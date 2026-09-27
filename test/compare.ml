(* ai-disclosure: ai-generated *)

(* Wall time of whole converter processes on the same documents, for
   comparing implementations rather than growth (for which see bench).

   Usage:
     compare NAME=CMD ...

   Each CMD reads djot on stdin and writes HTML on stdout.  The time is
   the best of three runs and includes process start, which the empty
   document shows on its own.  The documents are the two benchmark
   inputs the reference implementations ship, djot.js's readme.dj and
   djoths's m.dj, repeated, and one long line of mixed inline syntax. *)

open Djot_test

let rep s n = String.concat "" (List.init n (fun _ -> s))

let read path = In_channel.with_open_bin path In_channel.input_all

let documents () =
  let path parts = List.fold_left Filename.concat Parsers.root parts in
  let readme = read (path [ "djot.js"; "bench"; "readme.dj" ])
  and manual = read (path [ "djoths"; "benchmark"; "m.dj" ]) in
  let line n = rep "word _emph_ `code` [link](url) " (n / 32) ^ "\n" in
  [ "empty", "";
    "readme.dj", readme;
    "readme.dj x16", rep (readme ^ "\n") 16;
    "m.dj", manual;
    "m.dj x4", rep (manual ^ "\n") 4;
    "m.dj x16", rep (manual ^ "\n") 16;
    "line 80 KB", line 80_000;
    "line 320 KB", line 320_000 ]

let time argv input =
  let best = ref infinity in
  for _ = 1 to 3 do
    let t0 = Unix.gettimeofday () in
    (match Parsers.run_process argv input with
     | Ok _ -> ()
     | Error e -> failwith (argv.(0) ^ ": " ^ e));
    best := Float.min !best (Unix.gettimeofday () -. t0)
  done;
  !best

let () =
  let converters =
    List.tl (Array.to_list Sys.argv)
    |> List.map (fun a ->
         match String.index_opt a '=' with
         | Some i ->
           ( String.sub a 0 i,
             Array.of_list
               (String.split_on_char ' '
                  (String.sub a (i + 1) (String.length a - i - 1))) )
         | None -> failwith ("expected NAME=CMD, got " ^ a))
  in
  Printf.printf "%-14s %8s" "document" "KB";
  List.iter (fun (name, _) -> Printf.printf " %12s" name) converters;
  Printf.printf "   (ms, best of 3)\n%!";
  List.iter
    (fun (label, doc) ->
      Printf.printf "%-14s %8d" label (String.length doc / 1024);
      List.iter
        (fun (_, argv) -> Printf.printf " %12.0f%!" (time argv doc *. 1000.))
        converters;
      print_newline ())
    (documents ())
