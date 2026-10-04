(* ai-disclosure: ai-generated *)

(* Writes the static pages: [gen PAGES OUT].  A page is a djot file,
   rendered by the parser this site is about.  Three code block languages
   are filled in here:

   - [example]: the source, the HTML it renders to under the page's
     profile, and a link that opens it in the playground;
   - [properties]: the status of every property under the named profiles;
   - [versions]: the commits the site was built from.

   An extension page starts with a [profile: ...] line in the form
   [Spec.of_string] reads; its examples are parsed with that profile. *)

open Djot
open Site_common
module P = Djot_properties

let read path = In_channel.with_open_bin path In_channel.input_all

let write path s =
  let rec mkdir d =
    if not (Sys.file_exists d)
    then (
      mkdir (Filename.dirname d);
      Sys.mkdir d 0o755)
  in
  mkdir (Filename.dirname path);
  Out_channel.with_open_bin path (fun oc -> Out_channel.output_string oc s)
;;

let escape s =
  let b = Buffer.create (String.length s) in
  String.iter
    (function
      | '<' -> Buffer.add_string b "&lt;"
      | '>' -> Buffer.add_string b "&gt;"
      | '&' -> Buffer.add_string b "&amp;"
      | '"' -> Buffer.add_string b "&quot;"
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b
;;

let percent s =
  let b = Buffer.create (String.length s) in
  String.iter
    (function
      | ('A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '-' | '_' | '.' | '~') as c ->
        Buffer.add_char b c
      | c -> Printf.bprintf b "%%%02X" (Char.code c))
    s;
  Buffer.contents b
;;

let repo = "https://github.com/hon-gyu/djot.v"

let layout ~root ~title body =
  Printf.sprintf
    {|<!doctype html>
<html lang="en">
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>%s</title>
<link rel="stylesheet" href="%sstyle.css">
<header>
<a class="brand" href="%s">djot.v</a>
<nav>
<a href="%splayground/">Playground</a>
<a href="%sextensions/">Extensions</a>
<a href="%sapi/">OCaml API</a>
<a href="%s">Source</a>
</nav>
</header>
%s
<footer>
Built from <a href="%s/tree/%s">%s</a>.
Models the <a href="https://github.com/jgm/djot/blob/%s/doc/syntax.md">djot syntax reference at %s</a> (%s).
</footer>
</html>
|}
    (escape title)
    root
    (if root = "" then "./" else root)
    root
    root
    root
    repo
    body
    repo
    Versions.commit
    Versions.describe
    Versions.spec_commit
    (String.sub Versions.spec_commit 0 7)
    Versions.spec_date
;;

let status_cell : P.status -> string = function
  | Proved -> {|<td class="proved">proved</td>|}
  | Proved_with_caveat s ->
    Printf.sprintf {|<td class="caveat" title="%s">proved, with a caveat</td>|} (escape s)
  | Broken { reason; _ } ->
    Printf.sprintf {|<td class="broken" title="%s">broken</td>|} (escape reason)
  | Expected -> {|<td class="expected">expected, not proved</td>|}
  | Unknown -> {|<td class="unknown">no claim</td>|}
  | Not_applicable s -> Printf.sprintf {|<td class="na">%s</td>|} (escape s)
;;

let property_table ~all profiles =
  let differs p =
    List.exists (fun (_, q) -> P.status p q <> P.status p Profile.djot) profiles
  in
  let row p =
    Printf.sprintf
      "<tr><td>%s</td>%s</tr>"
      (escape (P.statement p))
      (String.concat "" (List.map (fun (_, q) -> status_cell (P.status p q)) profiles))
  in
  Printf.sprintf
    {|<table class="properties"><tr><th>Property</th>%s</tr>%s</table>|}
    (String.concat
       ""
       (List.map (fun (name, _) -> Printf.sprintf "<th>%s</th>" (escape name)) profiles))
    (String.concat "\n" (List.map row (List.filter (fun p -> all || differs p) P.all)))
;;

let versions () =
  Printf.sprintf
    {|<dl class="versions">
<dt>Syntax reference</dt><dd><a href="https://github.com/jgm/djot/blob/%s/doc/syntax.md">jgm/djot at %s</a>, %s</dd>
<dt>This project</dt><dd><a href="%s/tree/%s">%s</a></dd>
</dl>|}
    Versions.spec_commit
    (String.sub Versions.spec_commit 0 7)
    Versions.spec_date
    repo
    Versions.commit
    Versions.describe
;;

let example ~root profile src =
  let html = Html.of_doc (Doc.of_string ~profile src) in
  Printf.sprintf
    {|<div class="example">
<pre class="source"><code>%s</code></pre>
<pre class="rendered"><code>%s</code></pre>
<a href="%splayground/#profile=%s&amp;text=%s">Open in the playground</a>
</div>|}
    (escape src)
    (escape html)
    root
    (percent (Spec.to_string profile))
    (percent src)
;;

let named name =
  match List.assoc_opt name Spec.presets with
  | Some p -> name, p
  | None -> failwith (name ^ ": no such preset")
;;

(* The page's HTML, with the generated blocks filled in. *)
let render ~root profile src =
  let block _ (Node (_, _, b) : Block.t node) =
    let raw html = Mapper.ret (Node.make (Block.RawBlock ("html", html))) in
    match b with
    | CodeBlock ("example", s) -> raw (example ~root profile s)
    | CodeBlock ("versions", _) -> raw (versions ())
    | CodeBlock ("properties", s) ->
      raw
        (property_table
           ~all:true
           (List.map named (List.filter (( <> ) "") (String.split_on_char '\n' s))))
    | _ -> Mapper.default
  in
  Html.of_doc (Mapper.map_doc (Mapper.make ~block ()) (Doc.of_string src))
;;

let title src =
  match String.split_on_char '\n' src with
  | l :: _ when String.starts_with ~prefix:"# " l -> String.sub l 2 (String.length l - 2)
  | _ -> "djot.v"
;;

(* An extension page: its profile line, then djot. *)
let extension src =
  match String.index_opt src '\n' with
  | Some i when String.starts_with ~prefix:"profile: " src ->
    (match Spec.of_string (String.sub src 9 (i - 9)) with
     | Ok p -> p, String.sub src (i + 1) (String.length src - i - 1)
     | Error e -> failwith e)
  | _ -> failwith "an extension page starts with a profile: line"
;;

let () =
  let pages = Sys.argv.(1)
  and out = Sys.argv.(2) in
  let ( / ) = Filename.concat in
  let page ~root ~dst ?(after = "") profile src =
    write
      (out / dst)
      (layout
         ~root
         ~title:(title src)
         ("<main>\n" ^ render ~root profile src ^ after ^ "</main>"))
  in
  page ~root:"" ~dst:"index.html" Profile.djot (read (pages / "home.dj"));
  let names =
    Sys.readdir (pages / "extensions")
    |> Array.to_list
    |> List.filter (fun f -> Filename.check_suffix f ".dj" && f <> "index.dj")
    |> List.sort compare
  in
  let titles =
    List.map
      (fun f ->
        let profile, src = extension (read (pages / "extensions" / f)) in
        let name = Filename.chop_suffix f ".dj" in
        let after =
          "<h2>Properties</h2>\n\
           <p>What turning this on changes, against djot. Every property not listed keeps \
           its status.</p>\n"
          ^ property_table ~all:false [ "djot", Profile.djot; "with this extension", profile ]
        in
        page ~root:"../" ~dst:("extensions" / (name ^ ".html")) ~after profile src;
        Printf.sprintf {|<li><a href="%s.html">%s</a></li>|} name (escape (title src)))
      names
  in
  page
    ~root:"../"
    ~dst:("extensions" / "index.html")
    ~after:("<ul>\n" ^ String.concat "\n" titles ^ "\n</ul>\n")
    Profile.djot
    (read (pages / "extensions" / "index.dj"));
  write
    (out / "playground" / "index.html")
    (layout
       ~root:"../"
       ~title:"Playground"
       {|<main id="playground" class="wide"><noscript>The playground needs JavaScript.</noscript></main>
<script src="playground.js"></script>|})
;;
