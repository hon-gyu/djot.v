(* ai-disclosure: ai-generated *)

(* Writes the static pages: [gen PAGES EXTENSIONS OUT].  A page is a djot file,
   rendered by the parser this site is about.  Four code block languages
   are filled in here:

   - [example]: a source and its HTML, as the extension reference writes
     them, with a link that opens the source in the playground;
   - [changes]: the properties whose status a profile changes, against
     djot;
   - [properties]: the status of every property under the named profiles;
   - [versions]: the version, the syntax reference it models, and the
     commit the site was built from.

   The extensions page is made of the files of the directory EXTENSIONS,
   the extension reference (theories/spec), in the order of their
   names.  A file's setting is the one of its name in
   theories/Spec.v. *)

open Djot
open Site_common
module P = Djot.Kernel.Properties

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
<link rel="stylesheet" href="%stheme.css">
<link rel="stylesheet" href="%sstyle.css">
<header>
<a class="brand" href="%s">djot.v</a>
<nav>
<a href="%splayground/">Playground</a>
<a href="%sextensions/">Extensions</a>
<a href="%sapi/">API</a>
</nav>
<span class="tools">
<a class="github" href="%s">%s GitHub</a>
<button class="theme" onclick="toggleTheme()" aria-label="Switch between light and dark">Light / dark</button>
</span>
</header>
|}
        root
        root
        (if root = "" then "./" else root)
        root
        root
        root
        Links.repo
        github_mark
    ; body
    ; Printf.sprintf
        {|
<footer>
djot.v %s, built from <a href="%s">%s</a> (%s).
Models the <a href="https://github.com/jgm/djot/blob/%s/doc/syntax.md">djot syntax reference at %s</a> (%s).
</footer>
</html>
|}
        Versions.version
        Links.tree
        Versions.describe
        Versions.commit_date
        Versions.spec_commit
        (String.sub Versions.spec_commit 0 7)
        Versions.spec_date
    ]
;;

let status_cell (s : P.status) : string =
  let note =
    match s with
    | Conditional n | Inapplicable n | Broken (n, _) ->
      Printf.sprintf "<small>%s</small>" (escape n)
    | Proved | Conjectured | Unknown -> ""
  in
  Printf.sprintf {|<td class="status %s">%s%s</td>|} (P.status_name s) (P.status_name s) note
;;

let property_table ~all profiles =
  let differs p =
    List.exists (fun (_, q) -> p.P.p_status (Profiles.options q) <> p.P.p_status (Profiles.options Profile.djot)) profiles
  in
  let row p =
    Printf.sprintf
      "<tr><td>%s</td>%s</tr>"
      (escape (p.P.p_statement))
      (String.concat "" (List.map (fun (_, q) -> status_cell (p.P.p_status (Profiles.options q))) profiles))
  in
  Printf.sprintf
    {|<table class="properties"><tr><th>Property</th>%s</tr>%s</table>|}
    (String.concat
       ""
       (List.map (fun (name, _) -> Printf.sprintf "<th>%s</th>" (escape name)) profiles))
    (String.concat "\n" (List.map row (List.filter (fun p -> all || differs p) P.all)))
;;

(* What each status word means, shown above a full table. *)
let legend =
  {|<dl class="legend">
<dt class="proved">proved</dt><dd>The theorems hold for the profile.</dd>
<dt class="conditional">conditional</dt><dd>They hold under a condition on the document, stated below the status.</dd>
<dt class="broken">broken</dt><dd>The property fails for the profile, for the reason stated.</dd>
<dt class="conjectured">conjectured</dt><dd>Believed to hold, and not proved for the profile.</dd>
<dt class="unknown">unknown</dt><dd>No claim either way.</dd>
<dt class="inapplicable">inapplicable</dt><dd>The property is about a construct that is switched off.</dd>
</dl>
|}
;;

let versions () =
  Printf.sprintf
    {|<dl class="versions">
<dt>Version</dt><dd>%s</dd>
<dt>Syntax reference</dt><dd><a href="https://github.com/jgm/djot/blob/%s/doc/syntax.md">jgm/djot at %s</a>, %s</dd>
<dt>Built from</dt><dd><a href="%s">%s</a>, %s</dd>
</dl>|}
    Versions.version
    Versions.spec_commit
    (String.sub Versions.spec_commit 0 7)
    Versions.spec_date
    Links.tree
    Versions.describe
    Versions.commit_date
;;

(* An example of the extension reference: its source, a line with a
   period, and its HTML.  The HTML is the reference's own, which the
   Rocq build has checked against the parser. *)
let example ~root profile block =
  let rec split source = function
    | "." :: html -> List.rev source, html
    | l :: rest -> split (l :: source) rest
    | [] -> failwith "an example without its \".\" line"
  in
  let source, html = split [] (String.split_on_char '\n' block) in
  let src = String.concat "" (List.map (fun l -> l ^ "\n") source) in
  Printf.sprintf
    {|<div class="example">
<pre class="source"><code>%s</code></pre>
<pre class="rendered"><code>%s</code></pre>
<a href="%splayground/#profile=%s&amp;text=%s">Open in the playground</a>
</div>|}
    (escape src)
    (escape (String.concat "\n" html))
    root
    (percent (Profiles.to_string profile))
    (percent src)
;;

let named name =
  match List.assoc_opt name Profiles.presets with
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
        (legend
         ^ property_table
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

(* A file of the extension reference as a part of the extensions page:
   its setting, and its text with every heading one level down, its
   [example] blocks naming profile [i], and its properties at the end. *)
let extension i file =
  let name = Filename.chop_suffix (Filename.basename file) ".dj" in
  let profile =
    match Option.bind (List.assoc_opt name Kernel.Spec.all) Profile.of_kernel with
    | Some p -> p
    | None -> failwith (name ^ ": no setting of that name in theories/Spec.v")
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
  , String.concat "\n" (List.map line (String.split_on_char '\n' (read file)))
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

(* A property that names a theorem the development does not have is a
   mistake in the property list. *)
let () =
  List.iter
    (fun p ->
      List.iter
        (fun t ->
          if Links.theorem t = None
          then failwith (Printf.sprintf "%s: no theorem named %s" (p.P.p_id) t))
        (p.P.p_theorems))
    P.all
;;

let () =
  let pages = Sys.argv.(1)
  and extensions = Sys.argv.(2)
  and out = Sys.argv.(3) in
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
    Sys.readdir extensions
    |> Array.to_list
    |> List.filter (fun f -> Filename.check_suffix f ".dj")
    |> List.sort compare
    |> List.mapi (fun i f -> extension i (extensions / f))
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
