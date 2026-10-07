(* ai-disclosure: ai-generated *)

(* The arguments the subcommands share. *)

open Cmdliner
open Cmdliner.Term.Syntax
open Common

let s_syntax : string = "SYNTAX OPTIONS"

let exits : Cmd.Exit.info list =
  Cmd.Exit.info 1 ~doc:"when the input cannot be read or parsed."
  :: List.filter
       (fun (e : Cmd.Exit.info) -> Cmd.Exit.info_code e <> Cmd.Exit.some_error)
       Cmd.Exit.defaults
;;

let file : string Term.t =
  let doc = "The input file. Reads from $(b,stdin) if none or $(b,-) is given." in
  let (arg : string Arg.t) = Arg.(pos 0 string "-" & info [] ~doc ~docv:"FILE") in
  Arg.(value arg)
;;

let from : from Term.t =
  let (doc : string) =
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
       spellings. The other options of this section change it construct by construct."
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
    let off =
      Arg.info [ "no-" ^ name ] ~docs:s_syntax ~doc:("Turn off: " ^ what ^ ".")
    in
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
