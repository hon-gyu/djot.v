(* ai-disclosure: ai-generated *)

(* The input every subcommand reads, and how to parse and render it. Independent of
   the command line. *)

let ( let@ ) = ( @@ )

type from =
  [ `Djot
  | `Json
  ]

type input =
  { file : string (** ["-"] for stdin. *)
  ; from : from
  ; profile : Djot.Profile.t
  ; frontmatter : bool
  ; time : bool
  }

let read_file (file : string) : (string, string) result =
  try
    Ok
      (if file = "-"
       then In_channel.input_all stdin
       else In_channel.with_open_bin file In_channel.input_all)
  with
  | Sys_error e -> Error e
;;

(** [f ()], printing its wall-clock time to stderr as [label: N ms] when [on]. *)
let timed ~(on : bool) (label : string) (f : unit -> 'a) : 'a =
  if not on
  then f ()
  else (
    let t0 = Unix.gettimeofday () in
    let res = f () in
    let delta = (Unix.gettimeofday () -. t0) *. 1000. in
    Printf.eprintf "%s: %.1f ms\n%!" label delta;
    res)
;;

let parse ~(locs : bool) (i : input) : (Djot.Doc.t, string) result =
  let@ text = Result.bind (read_file i.file) in
  let@ () = timed ~on:i.time "parse" in
  (match i.from with
   | `Json -> Djot_json.of_string ~profile:i.profile text
   | `Djot ->
     (match
        Djot.Doc.of_string ~profile:i.profile ~locs ~frontmatter:i.frontmatter text
      with
      | doc -> Ok doc
      | exception Invalid_argument e -> Error e))
  |> Result.map_error (Printf.sprintf "%s: %s" i.file)
;;

(** Parses the input and prints [render doc]. *)
let run ?(locs : bool = false) (i : input) (render : Djot.Doc.t -> string) : int =
  match parse ~locs i with
  | Error e ->
    Printf.eprintf "djot: %s\n" e;
    1
  | Ok doc ->
    print_string (timed ~on:i.time "render" (fun () -> render doc));
    0
;;
