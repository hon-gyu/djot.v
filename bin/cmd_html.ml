(* ai-disclosure: ai-generated *)

(* The html subcommand. *)

open Cmd_common

(* Full page
   ========= *)

let html_escape (s : string) : string =
  let b = Buffer.create (String.length s) in
  String.iter
    (function
      | '&' -> Buffer.add_string b "&amp;"
      | '<' -> Buffer.add_string b "&lt;"
      | '>' -> Buffer.add_string b "&gt;"
      | '"' -> Buffer.add_string b "&quot;"
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b
;;

(** [--title], else a string [title] in the frontmatter, else the file name. *)
let page_title ~(title : string option) ~(file : string) (doc : Djot.Doc.t) : string =
  let of_frontmatter () : string option =
    Option.bind (Djot.Doc.frontmatter doc) (fun fm ->
      match List.assoc_opt "title" fm.fields with
      | Some (`String t) -> Some t
      | _ -> None)
  in
  let of_file () : string =
    if file = "-"
    then "Untitled"
    else String.capitalize_ascii (Filename.remove_extension (Filename.basename file))
  in
  match title with
  | Some t -> t
  | None -> Option.value (of_frontmatter ()) ~default:(of_file ())
;;

(** [inline_csss] are file contents. The built-in stylesheet is used when neither
    [csss] nor [inline_csss] is given. *)
let page
    ~(lang : string)
    ~(title : string)
    ~(csss : string list)
    ~(inline_csss : string list)
    (body : string)
  : string
  =
  let b = Buffer.create (String.length body + 4096) in
  let add : string -> unit = Buffer.add_string b in
  let style (css : string) : unit = add (Printf.sprintf "<style>\n%s</style>\n" css) in
  add "<!DOCTYPE html>\n";
  add (Printf.sprintf "<html lang=\"%s\">\n<head>\n" (html_escape lang));
  add "<meta charset=\"utf-8\">\n";
  add "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n";
  add (Printf.sprintf "<title>%s</title>\n" (html_escape title));
  if csss = [] && inline_csss = [] then style Builtin_css.s;
  List.iter
    (fun url ->
      add (Printf.sprintf "<link rel=\"stylesheet\" href=\"%s\">\n" (html_escape url)))
    csss;
  List.iter style inline_csss;
  add "</head>\n<body>\n";
  add body;
  add "</body>\n</html>\n";
  Buffer.contents b
;;

(* Command
   ======= *)

open Cmdliner
open Cmdliner.Term.Syntax

let cmd : int Cmd.t =
  let doc = "Render to HTML" in
  let man : Manpage.block list =
    [ `S Manpage.s_description
    ; `P
        "$(cmd) writes an HTML fragment, or with $(b,--doc) a complete page, to \
         $(b,stdout)."
    ; `Pre "$(cmd) $(b,--doc README.dj > README.html)"
    ]
    @ syntax_man
  in
  let docu : bool Term.t =
    let doc = "Write a complete HTML page rather than a fragment." in
    Arg.(value & flag & info [ "c"; "doc" ] ~doc)
  in
  let title : string option Term.t =
    let doc =
      "The page title with $(b,--doc). Defaults to the $(b,title) field of the \
       frontmatter, then to the file name."
    in
    Arg.(value & opt (some string) None & info [ "t"; "title" ] ~doc ~docv:"TITLE")
  in
  let lang : string Term.t =
    let doc = "The page language (BCP 47) with $(b,--doc)." in
    Arg.(value & opt string "en" & info [ "lang" ] ~doc ~docv:"LANG")
  in
  let csss : string list Term.t =
    let doc =
      "Link the stylesheet at $(docv) with $(b,--doc). Repeatable. The built-in \
       stylesheet is included only when neither this nor $(b,--inline-css) is given."
    in
    Arg.(value & opt_all string [] & info [ "css" ] ~doc ~docv:"URL")
  in
  let inline_csss : string list Term.t =
    let doc =
      "Include the content of $(docv) in a $(b,style) element with $(b,--doc). \
       Repeatable."
    in
    Arg.(value & opt_all file [] & info [ "inline-css" ] ~doc ~docv:"FILE.css")
  in
  Cmd.make (Cmd.info "html" ~doc ~man)
  @@ let+ i = input
     and+ docu
     and+ title
     and+ lang
     and+ csss
     and+ inline_csss in
     let read_all (files : string list) : (string list, string) result =
       List.fold_right
         (fun f acc -> Result.bind (read_file f) (fun s -> Result.map (List.cons s) acc))
         files
         (Ok [])
     in
     match read_all inline_csss with
     | Error e ->
       Printf.eprintf "djot: %s\n" e;
       1
     | Ok inline_csss ->
       run i (fun doc ->
         let body = Djot.Html.of_doc doc in
         if not docu
         then body
         else (
           let title : string = page_title ~title ~file:i.file doc in
           page ~lang ~title ~csss ~inline_csss body))
;;
