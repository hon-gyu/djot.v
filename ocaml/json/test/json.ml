(* ai-disclosure: ai-generated *)

(* The JSON form of documents and trees. Compared against json.expected. *)

open Djot

let blocks = Jsont.list Djot_json.block

let extended =
  Profile.(
    djot
    |> with_ext_keyed true
    |> with_ext_callouts true
    |> with_ext_wikilinks true
    |> with_ext_tags true)
;;

let show ?(profile = Profile.djot) ?(locs = false) name src =
  Printf.printf "\n== %s\n" name;
  let d = Doc.of_string ~profile ~locs src in
  print_endline (Djot_json.to_string ~format:Jsont.Indent d)
;;

let () =
  show
    "document"
    "# A _title_\n\nSee [it][ref] and [^n]...\n\n[ref]: /url\n\n[^n]: A note.\n";
  show "identifiers" "# a\n\n{#a .c}\n# b\n\n> # a\n";
  show "bullet lists" "- a\n\n+ b\n";
  show "table" "| h |\n|--:|\n| 1 |\n^ cap\n";
  show
    ~profile:extended
    "extensions"
    "tags: [[page|alias]]\n\n> [!note]- A title\n\n::: aside\n:::\n";
  show ~locs:true "positions" "> a\n"
;;

(* Decoding what was encoded gives the same tree. *)
let () =
  let src =
    "{#x .c k=v}\n\
     # H\n\n\
     _e_ *s* {=m=} {+i+} {-d-} H~2~O a^2^ `v` $`m` $$`d` :sym: <http://a.b> <a@b.c> \
     [l](u) ![i](p) [r][] [sp]{.k} 'q' \"q\" `r`{=html} a\\ b [^n] [[w]] ![[e|a]]\\\n\
     next\n\n\
     ## Sub\n\n\
     1. a\n\n\
     - b\n\n\
    \  c\n\n\
     - [ ] t\n\n\
     : term\n\n\
    \  def\n\n\
     | h | i |\n\
     |:--|:-:|\n\
     | 1 | 2 |\n\
     ^ cap\n\n\
     ``` ocaml\n\
     code\n\
     ```\n\n\
     ``` =html\n\
     <b>\n\
     ```\n\n\
     > q\n\n\
     ::: warn\n\
     d\n\
     :::\n\n\
     ***\n\n\
     key: value\n\n\
     > [!tip]+ T\n\
     > body\n\n\
     [r]: /u\n\n\
     [^n]: note\n"
  in
  let d = Doc.of_string ~profile:extended src in
  let tree = Doc.blocks d in
  let json = Jsont_bytesrw.encode_string blocks tree |> Result.get_ok in
  assert (Jsont_bytesrw.decode_string blocks json = Ok tree)
;;

let () =
  Printf.printf "\n== errors\n";
  let decode json =
    match Jsont_bytesrw.decode_string blocks json with
    | Ok _ -> print_endline "ok"
    | Error e -> print_endline e
  in
  decode {|[{"tag":"para","children":[{"tag":"nope"}]}]|};
  decode {|[{"tag":"heading","children":[]}]|};
  decode {|[{"tag":"ext_keyed","label":[],"children":[]}]|}
;;
