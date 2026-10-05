(* ai-disclosure: ai-generated *)

(* One request per run: the command and its options are the arguments, the
   input is on stdin and the result goes to stdout.  A request that fails
   writes its message to stderr and exits with 2.

     djot_wasi COMMAND [--locs] [--profile NAME] [--on SWITCH] [--off SWITCH]

   html      djot text to HTML
   ast       djot text to the JSON of Djot_json
   ast-html  that JSON to HTML
   ast-djot  that JSON to djot text *)

exception Failed of string

let fail fmt = Printf.ksprintf (fun s -> raise (Failed s)) fmt

let switch name =
  match
    List.find_opt (fun s -> Djot.Profile.Switch.name s = name) Djot.Profile.switches
  with
  | Some s -> s
  | None -> fail "unknown switch %S" name
;;

let base = function
  | "djot" -> Djot.Profile.djot
  | "markdown_like" -> Djot.Profile.markdown_like
  | name -> fail "unknown profile %S" name
;;

(* The options, left to right: a switch is set on the profile named before it. *)
let rec options profile locs = function
  | [] -> profile, locs
  | "--locs" :: rest -> options profile true rest
  | "--profile" :: name :: rest -> options (base name) locs rest
  | "--on" :: name :: rest ->
    options (Djot.Profile.Switch.set (switch name) true profile) locs rest
  | "--off" :: name :: rest ->
    options (Djot.Profile.Switch.set (switch name) false profile) locs rest
  | arg :: _ -> fail "unknown option %S" arg
;;

let of_json profile input =
  match Djot_json.of_string ~profile input with
  | Ok doc -> doc
  | Error e -> fail "%s" e
;;

let run command args input =
  let profile, locs = options Djot.Profile.djot false args in
  match command with
  | "html" -> Djot.Html.of_doc (Djot.Doc.of_string ~profile ~locs input)
  | "ast" -> Djot_json.to_string (Djot.Doc.of_string ~profile ~locs input)
  | "ast-html" -> Djot.Html.of_doc (of_json profile input)
  | "ast-djot" -> Djot.Doc.to_string (of_json profile input)
  | _ -> fail "unknown command %S" command
;;

let () =
  set_binary_mode_in stdin true;
  set_binary_mode_out stdout true;
  match Array.to_list Sys.argv with
  | _ :: command :: args ->
    (match run command args (In_channel.input_all stdin) with
     | output -> print_string output
     | exception Failed message ->
       prerr_string message;
       exit 2)
  | _ ->
    prerr_string "usage: djot_wasi COMMAND [OPTION]...";
    exit 2
;;
