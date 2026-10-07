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

module P = Djot.Profile

(** What [describe] says of each profile, as a sentence of a manual. *)
let per_profile (describe : P.t -> string) : string =
  let said = List.map (fun (name, p) -> name, describe p) Syntax.profiles in
  String.capitalize_ascii
    (match said with
     | (_, v) :: rest when List.for_all (fun (_, v') -> v' = v) rest ->
       Printf.sprintf "%s in every profile." v
     | said ->
       List.map (fun (name, v) -> Printf.sprintf "%s in $(b,%s)" v name) said
       |> String.concat ", "
       |> Printf.sprintf "%s.")
;;

let env_syntax : Cmd.Env.info =
  let doc =
    "The syntax to start from when $(b,--profile) is not given, as words separated by \
     spaces: a profile first, then $(i,NAME) or $(b,no-)$(i,NAME) for a construct and \
     $(i,NAME)=$(i,SPELLING) for a delimiter, named as the options are. For example \
     $(b,markdown-like ext-wikilinks no-tables highlight===)."
  in
  Cmd.Env.info "DJOT_SYNTAX" ~doc
;;

(** [--profile], one [--NAME] and [--no-NAME] pair per {!Djot.Profile.switches}, and one
    [--NAME] per {!Djot.Profile.delimiters}. Without [--profile] the options edit what
    [DJOT_SYNTAX] gives. *)
let profile : P.t Term.t =
  let base : string option Term.t =
    let doc =
      "The syntax to start from: $(b,djot), or $(b,markdown-like), which adds Markdown \
       spellings. The other options of this section change it construct by construct."
    in
    let names = List.map (fun (name, _) -> name, name) Syntax.profiles in
    Arg.(
      value
      & opt (some (enum names)) None
      & info
          [ "profile" ]
          ~doc
          ~docv:"PROFILE"
          ~docs:s_syntax
          ~absent:"$(b,DJOT_SYNTAX) env, or $(b,djot)"
          ~doc_envs:[ env_syntax ])
  in
  let switch (s : P.Switch.t) : Syntax.edit Term.t =
    let name = Syntax.switch_name s in
    let what = Manpage.escape (P.Switch.doc s) in
    let on =
      let state p = if P.Switch.get s p then "on" else "off" in
      let doc = Printf.sprintf "Turn on: %s. %s" what (per_profile state) in
      Arg.info [ name ] ~docs:s_syntax ~doc
    in
    let off =
      let doc = Printf.sprintf "Turn off what $(b,--%s) turns on." name in
      Arg.info [ "no-" ^ name ] ~docs:s_syntax ~doc
    in
    let+ v = Arg.(value & vflag None [ Some true, on; Some false, off ]) in
    fun p -> Ok (Option.fold v ~none:p ~some:(fun b -> P.Switch.set s b p))
  in
  let delimiter (d : P.Delimiter.t) : Syntax.edit Term.t =
    let name = P.Delimiter.name d in
    let doc =
      let spelling p =
        Printf.sprintf
          "$(b,%s)"
          (Manpage.escape (Syntax.spelling_to_string (P.Delimiter.spelling d p)))
      in
      Printf.sprintf "How %s is written. %s" name (per_profile spelling)
    in
    let+ s =
      Arg.(
        value & opt (some string) None & info [ name ] ~docs:s_syntax ~docv:"SPELLING" ~doc)
    in
    Option.fold s ~none:Result.ok ~some:(Syntax.respell d)
  in
  let edit : Syntax.edit Term.t =
    List.fold_left
      (fun acc t ->
         let+ f = acc
         and+ g = t in
         fun p -> Result.bind (f p) g)
      (Term.const Result.ok)
      (List.map switch P.switches @ List.map delimiter P.delimiters)
  in
  Term.term_result' ~usage:true
  @@
  let+ env = Term.env
  and+ base
  and+ edit in
  let start : (P.t, string) result =
    match base, env "DJOT_SYNTAX" with
    | Some name, _ -> Ok (List.assoc name Syntax.profiles)
    | None, None -> Ok P.djot
    | None, Some words ->
      Result.map_error (Printf.sprintf "DJOT_SYNTAX: %s") (Syntax.of_words words)
  in
  Result.bind start edit
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
      "Options naming a construct turn it on or off, and say which profiles have it on. \
       Those whose name starts with $(b,ext-) are extensions to djot, off in the \
       $(b,djot) profile."
  ; `P
      "Options naming an inline delimiter take its $(i,SPELLING): the delimiter itself, \
       as in $(b,**), which also reads the braced form; the delimiter in braces, as in \
       $(b,{=}), to read only the braced form; or $(b,off)."
  ]
;;
