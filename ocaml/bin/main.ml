(* ai-disclosure: ai-generated *)

(* The djot command: djot to HTML, djot, JSON, or an indented tree. *)

open Cmdliner
open Cmdliner.Term.Syntax
open Cmd_common

let djot_cmd : int Cmd.t =
  let doc = "Render to djot" in
  let man : Manpage.block list =
    [ `S Manpage.s_description
    ; `P "$(cmd) writes the document back as djot source, in the syntax of the profile."
    ]
    @ syntax_man
  in
  let style : Djot.style Term.t =
    let doc =
      "How to write the source. $(b,safe) escapes text and braces delimiters so that the \
       result parses back to the same tree. $(b,naive) writes what a person would type \
       and need not parse back. $(b,checked) is $(b,naive) where that parses back to the \
       same tree, and $(b,safe) elsewhere."
    in
    let styles = [ "checked", `Checked; "safe", `Safe; "naive", `Naive ] in
    Arg.(value & opt (enum styles) `Checked & info [ "style" ] ~doc ~docv:"STYLE")
  in
  Cmd.make (Cmd.info "djot" ~doc ~man)
  @@ let+ i = input
     and+ style in
     run i (fun doc ->
       let s = Djot.Doc.to_string ~style doc in
       if s = "" || String.ends_with ~suffix:"\n" s then s else s ^ "\n")
;;

let ast_cmd : int Cmd.t =
  let doc = "Print the tree, one node per line" in
  let man : Manpage.block list =
    [ `S Manpage.s_description
    ; `P
        "$(cmd) prints the document as an indented tree in the form djot.js prints \
         with $(b,-t astpretty). With $(b,--locs), each node shows its source range as \
         $(i,line):$(i,column):$(i,byte) at both ends."
    ]
    @ syntax_man
  in
  Cmd.make (Cmd.info "ast" ~doc ~man)
  @@ let+ i = input
     and+ locs in
     run ~locs i Djot_json.to_ast_string
;;

let json_cmd : int Cmd.t =
  let doc = "Write the tree as JSON" in
  let man : Manpage.block list =
    [ `S Manpage.s_description
    ; `P
        "$(cmd) writes the document as JSON in the format of djot.js's AST, with the \
         additions listed in the documentation of the $(b,djot.json) library. \
         $(b,--from json) reads it back."
    ]
    @ syntax_man
  in
  let compact : bool Term.t =
    let doc = "Write the JSON on one line." in
    Arg.(value & flag & info [ "compact" ] ~doc)
  in
  Cmd.make (Cmd.info "json" ~doc ~man)
  @@ let+ i = input
     and+ locs
     and+ compact in
     let format = if compact then Jsont.Minify else Jsont.Indent in
     run ~locs i (fun doc -> Djot_json.to_string ~format doc ^ "\n")
;;

let cmd : int Cmd.t =
  let doc = "Process djot files" in
  let man : Manpage.block list =
    [ `S Manpage.s_description
    ; `P
        "$(cmd) parses djot with a parser extracted from a Rocq development and renders \
         it to HTML, djot, JSON, or an indented tree."
    ]
  in
  Cmd.group
    (Cmd.info "djot" ~version:"%%VERSION%%" ~doc ~man)
    [ Cmd_html.cmd; djot_cmd; ast_cmd; json_cmd ]

let () = exit (Cmd.eval' cmd)
