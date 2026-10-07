(* ai-disclosure: ai-generated *)

(* The input every subcommand reads, and the options that describe it. *)

(* Input
   ===== *)

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
    let r = f () in
    Printf.eprintf "%s: %.1f ms\n%!" label ((Unix.gettimeofday () -. t0) *. 1000.);
    r)
;;

let parse ~(locs : bool) (i : input) : (Djot.Doc.t, string) result =
  Result.bind (read_file i.file) (fun text ->
    timed ~on:i.time "parse" (fun () ->
      match i.from with
      | `Json -> Djot_json.of_string ~profile:i.profile text
      | `Djot ->
        (match
           Djot.Doc.of_string ~profile:i.profile ~locs ~frontmatter:i.frontmatter text
         with
         | doc -> Ok doc
         | exception Invalid_argument e -> Error e))
    |> Result.map_error (Printf.sprintf "%s: %s" i.file))
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

(* Options
   ======= *)

open Cmdliner
open Cmdliner.Term.Syntax

let s_syntax : string = "SYNTAX OPTIONS"

let file : string Term.t =
  let doc = "The input file. Reads from $(b,stdin) if none or $(b,-) is given." in
  Arg.(value & pos 0 string "-" & info [] ~doc ~docv:"FILE")
;;

let from : from Term.t =
  let doc =
    "The input format: $(b,djot), or $(b,json) as written by $(b,djot json). A JSON \
     document has no source locations."
  in
  let formats = [ "djot", `Djot; "json", `Json ] in
  Arg.(value & opt (enum formats) `Djot & info [ "f"; "from" ] ~doc ~docv:"FORMAT")
;;

let frontmatter : bool Term.t =
  let doc =
    "Read YAML frontmatter between two $(b,---) lines at the start of the input. Needs \
     the library to be built with the $(b,yaml) package."
  in
  Arg.(value & flag & info [ "frontmatter" ] ~doc)
;;

let time : bool Term.t =
  let doc = "Print parse and render times to $(b,stderr)." in
  Arg.(value & flag & info [ "time" ] ~doc)
;;

let locs : bool Term.t =
  let doc = "Include source locations." in
  Arg.(value & flag & info [ "l"; "locs" ] ~doc)
;;

(** [--profile], then one [--NAME] and [--no-NAME] pair per {!Djot.Profile.switches}. *)
let profile : Djot.Profile.t Term.t =
  let base : Djot.Profile.t Term.t =
    let doc =
      "The syntax to start from: $(b,djot), or $(b,markdown-like), which adds Markdown \
       spellings. The options below change it construct by construct."
    in
    let profiles = [ "djot", `Djot; "markdown-like", `Markdown_like ] in
    let+ p =
      Arg.(
        value
        & opt (enum profiles) `Djot
        & info [ "profile" ] ~doc ~docv:"PROFILE" ~docs:s_syntax)
    in
    match p with
    | `Djot -> Djot.Profile.djot
    | `Markdown_like -> Djot.Profile.markdown_like
  in
  let switch (s : Djot.Profile.Switch.t) : bool option Term.t =
    let name =
      String.map
        (function
          | '_' -> '-'
          | c -> c)
        (Djot.Profile.Switch.name s)
    in
    let what = Manpage.escape (Djot.Profile.Switch.doc s) in
    let on = Arg.info [ name ] ~docs:s_syntax ~doc:("Turn on: " ^ what ^ ".") in
    let off = Arg.info [ "no-" ^ name ] ~docs:s_syntax ~doc:("Turn off: " ^ what ^ ".") in
    Arg.(value & vflag None [ Some true, on; Some false, off ])
  in
  List.fold_left
    (fun acc s ->
       let+ p = acc
       and+ v = switch s in
       match v with
       | None -> p
       | Some b -> Djot.Profile.Switch.set s b p)
    base
    Djot.Profile.switches
;;

let input : input Term.t =
  let+ file
  and+ from
  and+ profile
  and+ frontmatter
  and+ time in
  { file; from; profile; frontmatter; time }
;;

let syntax_man : Manpage.block list =
  [ `S s_syntax
  ; `P
      "Options naming a construct turn it on or off. Those whose name starts with \
       $(b,ext-) are extensions to djot, off in the $(b,djot) profile."
  ]
;;
