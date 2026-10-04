(* ai-disclosure: ai-generated *)

(* Writes the static pages: [gen PAGES OUT].  A page is a djot file,
   rendered by the parser this site is about.  Four code block languages
   are filled in here:

   - [example]: the source, the HTML it renders to under a profile, and a
     link that opens it in the playground;
   - [changes]: the properties whose status a profile changes, against
     djot;
   - [properties]: the status of every property under the named profiles;
   - [versions]: the commits the site was built from.

   The extensions page is made of the files of [extensions/], in the
   order of their names.  Each starts with a [profile: ...] line in the
   form [Spec.of_string] reads, which is the profile of its [example] and
   [changes] blocks. *)

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

let github_mark =
  {|<svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true"><path fill="currentColor" d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27s1.36.09 2 .27c1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.01 8.01 0 0 0 16 8c0-4.42-3.58-8-8-8z"/></svg>|}
;;

(* The theme is the reader's choice if they made one, and the system's
   otherwise.  It is set before the page paints. *)
let theme_script =
  {|<script>
(function () {
  var root = document.documentElement, stored = null;
  try { stored = localStorage.getItem("theme"); } catch (e) {}
  root.dataset.theme = stored || (matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light");
  window.toggleTheme = function () {
    root.dataset.theme = root.dataset.theme === "dark" ? "light" : "dark";
    try { localStorage.setItem("theme", root.dataset.theme); } catch (e) {}
    window.dispatchEvent(new Event("themechange"));
  };
})();
</script>|}
;;

let layout ~root ~title body =
  String.concat
    ""
    [ {|<!doctype html>
<html lang="en">
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>|}
    ; escape title
    ; "</title>\n"
    ; theme_script
    ; Printf.sprintf
        {|
<link rel="stylesheet" href="%sstyle.css">
<header>
<a class="brand" href="%s">djot.v</a>
<nav>
<a href="%splayground/">Playground</a>
<a href="%sextensions/">Extensions</a>
<a href="%sapi/">OCaml API</a>
</nav>
<span class="tools">
<a class="github" href="%s">%s GitHub</a>
<button class="theme" onclick="toggleTheme()" aria-label="Switch between light and dark">Light / dark</button>
</span>
</header>
|}
        root
        (if root = "" then "./" else root)
        root
        root
        root
        repo
        github_mark
    ; body
    ; Printf.sprintf
        {|
<footer>
Built from <a href="%s/tree/%s">%s</a>.
Models the <a href="https://github.com/jgm/djot/blob/%s/doc/syntax.md">djot syntax reference at %s</a> (%s).
</footer>
</html>
|}
        repo
        Versions.commit
        Versions.describe
        Versions.spec_commit
        (String.sub Versions.spec_commit 0 7)
        Versions.spec_date
    ]
;;

let status_cell (s : P.status) : string =
  let note =
    match s with
    | Proved_with_caveat n | Not_applicable n | Broken { reason = n; _ } ->
      Printf.sprintf "<small>%s</small>" (escape n)
    | Proved | Expected | Unknown -> ""
  in
  Printf.sprintf {|<td class="status %s">%s%s</td>|} (Status.word s) (Status.word s) note
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

(* The page as a document, with the generated blocks filled in.  An
   [example] or [changes] block names its profile after a colon, as an
   index into [profiles]. *)
let document ~root ?(profiles = [||]) src =
  let profile lang =
    match String.index_opt lang ':' with
    | Some i -> profiles.(int_of_string (String.sub lang (i + 1) (String.length lang - i - 1)))
    | None -> Profile.djot
  in
  let block _ (Node (_, _, b) : Block.t node) =
    let raw html = Mapper.ret (Node.make (Block.RawBlock ("html", html))) in
    match b with
    | CodeBlock (lang, s) when String.starts_with ~prefix:"example" lang ->
      raw (example ~root (profile lang) s)
    | CodeBlock (lang, _) when String.starts_with ~prefix:"changes" lang ->
      raw
        (property_table
           ~all:false
           [ "djot", Profile.djot; "with this extension", profile lang ])
    | CodeBlock ("versions", _) -> raw (versions ())
    | CodeBlock ("properties", s) ->
      raw
        (property_table
           ~all:true
           (List.map named (List.filter (( <> ) "") (String.split_on_char '\n' s))))
    | _ -> Mapper.default
  in
  Mapper.map_doc (Mapper.make ~block ()) (Doc.of_string src)
;;

let title src =
  match String.split_on_char '\n' src with
  | l :: _ when String.starts_with ~prefix:"# " l -> String.sub l 2 (String.length l - 2)
  | _ -> "djot.v"
;;

(* An extension file as a part of the extensions page: its profile, and
   its text with every heading one level down, its [example] blocks
   naming profile [i], and its properties at the end. *)
let extension i src =
  let profile, lines =
    match String.split_on_char '\n' src with
    | l :: rest when String.starts_with ~prefix:"profile: " l ->
      (match Spec.of_string (String.sub l 9 (String.length l - 9)) with
       | Ok p -> p, rest
       | Error e -> failwith e)
    | _ -> failwith "an extension file starts with a profile: line"
  in
  let fenced = ref false in
  let line l =
    if String.starts_with ~prefix:"```" l
    then (
      fenced := not !fenced;
      if l = "``` example" then Printf.sprintf "``` example:%d" i else l)
    else if (not !fenced) && String.starts_with ~prefix:"#" l
    then "#" ^ l
    else l
  in
  ( profile
  , String.concat "\n" (List.map line lines)
    ^ Printf.sprintf
        "\n### Properties\n\n\
         What turning this on changes, against djot. Every property not listed keeps its \
         status.\n\n\
         ``` changes:%d\n\
         ```\n\n"
        i )
;;

(* The headings of levels 2 and 3, as a list of links. *)
let contents (d : Doc.t) =
  let rec sections (bs : Block.t node list) =
    List.concat_map
      (fun (Node (_, attrs, b) : Block.t node) ->
        match b with
        | Section (Node (_, _, Heading (level, text)) :: rest) ->
          (match Attr.id attrs with
           | Some id when level = 2 || level = 3 ->
             [ Printf.sprintf
                 {|<a class="level%d" href="#%s">%s</a>|}
                 level
                 (escape id)
                 (escape (Inline.to_plain_text text))
             ]
           | _ -> [])
          @ sections rest
        | _ -> [])
      bs
  in
  "<nav class=\"contents\">\n" ^ String.concat "\n" (sections (Doc.blocks d)) ^ "\n</nav>\n"
;;

let () =
  let pages = Sys.argv.(1)
  and out = Sys.argv.(2) in
  let ( / ) = Filename.concat in
  let page ~root ~dst src =
    write
      (out / dst)
      (layout
         ~root
         ~title:(title src)
         ("<main>\n" ^ Html.of_doc (document ~root src) ^ "</main>"))
  in
  page ~root:"" ~dst:"index.html" (read (pages / "home.dj"));
  page ~root:"../" ~dst:("api" / "index.html") (read (pages / "api.dj"));
  let parts =
    Sys.readdir (pages / "extensions")
    |> Array.to_list
    |> List.filter (fun f -> Filename.check_suffix f ".dj")
    |> List.sort compare
    |> List.mapi (fun i f -> extension i (read (pages / "extensions" / f)))
  in
  let src = String.concat "" (read (pages / "extensions.dj") :: List.map snd parts) in
  let d = document ~root:"../" ~profiles:(Array.of_list (List.map fst parts)) src in
  write
    (out / "extensions" / "index.html")
    (layout
       ~root:"../"
       ~title:(title src)
       ("<div class=\"with-contents\">\n<main>\n"
        ^ Html.of_doc d
        ^ "</main>\n"
        ^ contents d
        ^ "</div>"));
  write
    (out / "playground" / "index.html")
    (layout
       ~root:"../"
       ~title:"Playground"
       {|<main id="playground" class="wide"><noscript>The playground needs JavaScript.</noscript></main>
<script src="playground.js"></script>|})
;;
