(* ai-disclosure: ai-generated *)

(* A parsed tree printed one node per line, indented by depth. With
   locations, each node shows its inclusive byte range and the source it
   covers. A lowercase line is a grouping with no node of its own. *)

open Djot

type item =
  | I of Inline.t node
  | B of Block.t node
  | Group of string * item list

let inlines = List.map (fun n -> I n)
let blocks = List.map (fun n -> B n)

(* A string literal that leaves non-ASCII bytes as they are. *)
let quote s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (fun c ->
      if c = '"' || c = '\\' || Char.code c < 0x20
      then Buffer.add_string b (String.escaped (String.make 1 c))
      else Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b
;;

let target : Inline.target -> string = function
  | Direct s -> "(Direct " ^ quote s ^ ")"
  | Reference s -> "(Reference " ^ quote s ^ ")"
;;

let inline_label : Inline.t -> string * item list = function
  | Str s -> "Str " ^ quote s, []
  | Emph l -> "Emph", inlines l
  | Strong l -> "Strong", inlines l
  | Highlight l -> "Highlight", inlines l
  | Insert l -> "Insert", inlines l
  | Delete l -> "Delete", inlines l
  | Superscript l -> "Superscript", inlines l
  | Subscript l -> "Subscript", inlines l
  | Verbatim s -> "Verbatim " ^ quote s, []
  | Symbol s -> "Symbol " ^ quote s, []
  | Math (_, s) -> "Math " ^ quote s, []
  | Link (l, t) -> "Link " ^ target t, inlines l
  | Image (l, t) -> "Image " ^ target t, inlines l
  | Span (name, l) -> "Span " ^ quote name, inlines l
  | FootnoteReference s -> "FootnoteReference " ^ quote s, []
  | UrlLink s -> "UrlLink " ^ quote s, []
  | EmailLink s -> "EmailLink " ^ quote s, []
  | RawInline (f, s) -> Printf.sprintf "RawInline %s %s" (quote f) (quote s), []
  | NonBreakingSpace -> "NonBreakingSpace", []
  | Quoted (_, l) -> "Quoted", inlines l
  | SoftBreak -> "SoftBreak", []
  | HardBreak -> "HardBreak", []
  | Ext_wikilink (embed, t, alias) ->
    let alias = Option.fold ~none:"" ~some:(fun a -> " " ^ quote a) alias in
    ( Printf.sprintf "Ext_wikilink%s %s%s" (if embed then " embed" else "") (quote t) alias
    , [] )
;;

let block_label : Block.t -> string * item list = function
  | Para l -> "Para", inlines l
  | Section l -> "Section", blocks l
  | Heading (n, l) -> Printf.sprintf "Heading %d" n, inlines l
  | BlockQuote l -> "BlockQuote", blocks l
  | CodeBlock (lang, s) -> Printf.sprintf "CodeBlock %s %s" (quote lang) (quote s), []
  | Div (name, l) -> "Div " ^ quote name, blocks l
  | OrderedList (_, _, its) ->
    "OrderedList", List.map (fun l -> Group ("item", blocks l)) its
  | BulletList (_, its) -> "BulletList", List.map (fun l -> Group ("item", blocks l)) its
  | TaskList (_, its) -> "TaskList", List.map (fun (_, l) -> Group ("item", blocks l)) its
  | DefinitionList (_, its) ->
    ( "DefinitionList"
    , List.map
        (fun (t, d) ->
          Group ("item", [ Group ("term", inlines t); Group ("def", blocks d) ]))
        its )
  | ThematicBreak -> "ThematicBreak", []
  | Table (cap, rows) ->
    let row r =
      Group ("row", List.map (fun (Block.Cell (_, _, l)) -> Group ("cell", inlines l)) r)
    in
    ( "Table"
    , (if cap = [] then [] else [ Group ("caption", inlines cap) ]) @ List.map row rows )
  | RawBlock (f, s) -> Printf.sprintf "RawBlock %s %s" (quote f) (quote s), []
  | FootnoteDef (label, l) -> "FootnoteDef " ^ quote label, blocks l
  | RefDef (label, dest) -> Printf.sprintf "RefDef %s %s" (quote label) (quote dest), []
  | Ext_keyed (label, b) -> "Ext_keyed", [ Group ("label", inlines label); B b ]
  | Ext_callout (kind, fold, title, body) ->
    let fold =
      match fold with
      | None -> ""
      | Some Block.FoldExpanded -> " FoldExpanded"
      | Some FoldCollapsed -> " FoldCollapsed"
    in
    ( Printf.sprintf "Ext_callout %s%s" (quote kind) fold
    , Group ("title", inlines title) :: blocks body )
;;

(* [first-last "covered source"], or nothing without locations. *)
let range d t =
  if Textloc.is_none t
  then ""
  else (
    let f = Textloc.first_byte t
    and l = Textloc.last_byte t in
    match Doc.source d with
    | Some src -> Printf.sprintf " %d-%d %s" f l (quote (String.sub src f (l - f + 1)))
    | None -> Printf.sprintf " %d-%d" f l)
;;

let rec print_item d depth it =
  let pad = String.make (2 * depth) ' ' in
  let node label n kids =
    Printf.printf "%s%s%s\n" pad label (range d (Doc.textloc d n));
    List.iter (print_item d (depth + 1)) kids
  in
  match it with
  | I n ->
    let label, kids = inline_label (Node.content n) in
    node label n kids
  | B n ->
    let label, kids = block_label (Node.content n) in
    node label n kids
  | Group (name, kids) ->
    Printf.printf "%s%s\n" pad name;
    List.iter (print_item d (depth + 1)) kids
;;

let print_blocks d bs = List.iter (fun n -> print_item d 0 (B n)) bs

(* The blocks, then the footnote definitions. *)
let print d =
  print_blocks d (Doc.blocks d);
  print_blocks d (Doc.footnote_defs d)
;;

(* The source as a header, then its parse with locations. *)
let show ?(profile = Profile.djot) src =
  Printf.printf "\n%s\n" (quote src);
  print (Doc.of_string ~profile ~locs:true src)
;;
