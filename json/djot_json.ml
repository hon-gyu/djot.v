(* ai-disclosure: ai-generated *)

open Djot
module O = Jsont.Object
module C = Jsont.Object.Case

let error fmt = Jsont.Error.msgf Jsont.Meta.none fmt

(* Shared pieces
   ============= *)

(* An object as its members, in order. *)
let assoc ~kind (t : 'a Jsont.t) : (string * 'a) list Jsont.t =
  let enc f l acc = List.fold_left (fun acc (k, v) -> f Jsont.Meta.none k v acc) acc l in
  let mems =
    O.Mems.map
      t
      ~dec_empty:(fun () -> [])
      ~dec_add:(fun _ k v acc -> (k, v) :: acc)
      ~dec_finish:(fun _ acc -> List.rev acc)
      ~enc:{ O.Mems.enc }
  in
  O.map ~kind Fun.id |> O.keep_unknown mems ~enc:Fun.id |> O.finish
;;

let attrs : Attr.t Jsont.t = assoc ~kind:"attributes" Jsont.string

(* djot.js's [pos]: one-based lines and columns, zero-based offsets, the
   end included.  Columns and offsets count bytes. *)
let pos : Textloc.t Jsont.t =
  let point =
    O.map ~kind:"source location" (fun line col offset -> line, col, offset)
    |> O.mem "line" Jsont.int ~enc:(fun (l, _, _) -> l)
    |> O.mem "col" Jsont.int ~enc:(fun (_, c, _) -> c)
    |> O.mem "offset" Jsont.int ~enc:(fun (_, _, o) -> o)
    |> O.finish
  in
  let enc (line, line_start) byte = line, byte - line_start + 1, byte in
  let dec (l, c, o) (l', c', o') =
    Textloc.make
      ~first_byte:o
      ~last_byte:o'
      ~first_line:(l, o - c + 1)
      ~last_line:(l', o' - c' + 1)
  in
  O.map ~kind:"pos" dec
  |> O.mem "start" point ~enc:(fun t -> enc (Textloc.first_line t) (Textloc.first_byte t))
  |> O.mem "end" point ~enc:(fun t -> enc (Textloc.last_line t) (Textloc.last_byte t))
  |> O.finish
;;

(* Where a node is in its document. *)
type loc = { loc : 'a. 'a node -> Textloc.t }

(* A node: its tag and the members of that tag's case, then the members
   every node has.  A decoded node has no position. *)
let node ~kind (l : loc) cases enc_case : 'a node Jsont.t =
  let pos_of n =
    let t = l.loc n in
    if Textloc.is_none t then None else Some t
  in
  O.map ~kind (fun content attrs _pos -> Node.make ~attrs content)
  |> O.case_mem "tag" Jsont.string cases ~tag_to_string:Fun.id ~enc:Node.content ~enc_case
  |> O.mem "attributes" attrs ~dec_absent:Attr.empty ~enc:Node.attrs ~enc_omit:(( = ) [])
  |> O.opt_mem "pos" pos ~enc:pos_of
  |> O.finish
;;

(* A node with one tag. *)
let fixed l tag obj : 'a node Jsont.t =
  let c = C.map tag obj ~dec:Fun.id in
  node ~kind:tag l [ C.make c ] (C.value c)
;;

let empty = String.equal ""
let no_members : unit Jsont.t = O.map () |> O.finish

let text : string Jsont.t =
  O.map Fun.id |> O.mem "text" Jsont.string ~enc:Fun.id |> O.finish
;;

let children list = O.map Fun.id |> O.mem "children" list ~enc:Fun.id |> O.finish

(* A div or a span: its name, left out when empty, and its children. *)
let named list =
  O.map (fun name kids -> name, kids)
  |> O.mem "name" Jsont.string ~dec_absent:"" ~enc:fst ~enc_omit:empty
  |> O.mem "children" list ~enc:snd
  |> O.finish
;;

let formatted : (string * string) Jsont.t =
  O.map (fun format text -> format, text)
  |> O.mem "format" Jsont.string ~enc:fst
  |> O.mem "text" Jsont.string ~enc:snd
  |> O.finish
;;

(* Inlines
   ======= *)

let inline_at (l : loc) : Inline.t node Jsont.t =
  let rec t =
    lazy
      (let inlines = Jsont.list (Jsont.rec' t) in
       let kids = children inlines in
       let linked =
         let dec dest reference kids =
           match dest, reference with
           | Some d, _ -> kids, Inline.Direct d
           | None, Some r -> kids, Inline.Reference r
           | None, None -> error "a link or image has a destination or a reference"
         in
         O.map dec
         |> O.opt_mem "destination" Jsont.string ~enc:(function
           | _, Inline.Direct d -> Some d
           | _, Inline.Reference _ -> None)
         |> O.opt_mem "reference" Jsont.string ~enc:(function
           | _, Inline.Reference r -> Some r
           | _, Inline.Direct _ -> None)
         |> O.mem "children" inlines ~enc:fst
         |> O.finish
       in
       let symbol = O.map Fun.id |> O.mem "alias" Jsont.string ~enc:Fun.id |> O.finish in
       let wikilink =
         O.map (fun embed target alias -> embed, target, alias)
         |> O.mem "embed" Jsont.bool ~enc:(fun (e, _, _) -> e)
         |> O.mem "target" Jsont.string ~enc:(fun (_, t, _) -> t)
         |> O.opt_mem "alias" Jsont.string ~enc:(fun (_, _, a) -> a)
         |> O.finish
       in
       let open Inline in
       let str = C.map "str" text ~dec:(fun s -> Str s) in
       let emph = C.map "emph" kids ~dec:(fun k -> Emph k) in
       let strong = C.map "strong" kids ~dec:(fun k -> Strong k) in
       let mark = C.map "mark" kids ~dec:(fun k -> Highlight k) in
       let insert = C.map "insert" kids ~dec:(fun k -> Insert k) in
       let delete = C.map "delete" kids ~dec:(fun k -> Delete k) in
       let superscript = C.map "superscript" kids ~dec:(fun k -> Superscript k) in
       let subscript = C.map "subscript" kids ~dec:(fun k -> Subscript k) in
       let verbatim = C.map "verbatim" text ~dec:(fun s -> Verbatim s) in
       let symb = C.map "symb" symbol ~dec:(fun s -> Symbol s) in
       let inline_math = C.map "inline_math" text ~dec:(fun s -> Math (InlineMath, s)) in
       let display_math =
         C.map "display_math" text ~dec:(fun s -> Math (DisplayMath, s))
       in
       let link = C.map "link" linked ~dec:(fun (k, tgt) -> Link (k, tgt)) in
       let image = C.map "image" linked ~dec:(fun (k, tgt) -> Image (k, tgt)) in
       let span = C.map "span" (named inlines) ~dec:(fun (n, k) -> Span (n, k)) in
       let footnote_reference =
         C.map "footnote_reference" text ~dec:(fun s -> FootnoteReference s)
       in
       let url = C.map "url" text ~dec:(fun s -> UrlLink s) in
       let email = C.map "email" text ~dec:(fun s -> EmailLink s) in
       let raw_inline =
         C.map "raw_inline" formatted ~dec:(fun (f, s) -> RawInline (f, s))
       in
       let non_breaking_space =
         C.map "non_breaking_space" no_members ~dec:(fun () -> NonBreakingSpace)
       in
       let single_quoted =
         C.map "single_quoted" kids ~dec:(fun k -> Quoted (SingleQuotes, k))
       in
       let double_quoted =
         C.map "double_quoted" kids ~dec:(fun k -> Quoted (DoubleQuotes, k))
       in
       let soft_break = C.map "soft_break" no_members ~dec:(fun () -> SoftBreak) in
       let hard_break = C.map "hard_break" no_members ~dec:(fun () -> HardBreak) in
       let ext_wikilink =
         C.map "ext_wikilink" wikilink ~dec:(fun (e, t, a) -> Ext_wikilink (e, t, a))
       in
       let enc_case = function
         | Str s -> C.value str s
         | Emph k -> C.value emph k
         | Strong k -> C.value strong k
         | Highlight k -> C.value mark k
         | Insert k -> C.value insert k
         | Delete k -> C.value delete k
         | Superscript k -> C.value superscript k
         | Subscript k -> C.value subscript k
         | Verbatim s -> C.value verbatim s
         | Symbol s -> C.value symb s
         | Math (InlineMath, s) -> C.value inline_math s
         | Math (DisplayMath, s) -> C.value display_math s
         | Link (k, tgt) -> C.value link (k, tgt)
         | Image (k, tgt) -> C.value image (k, tgt)
         | Span (n, k) -> C.value span (n, k)
         | FootnoteReference s -> C.value footnote_reference s
         | UrlLink s -> C.value url s
         | EmailLink s -> C.value email s
         | RawInline (f, s) -> C.value raw_inline (f, s)
         | NonBreakingSpace -> C.value non_breaking_space ()
         | Quoted (SingleQuotes, k) -> C.value single_quoted k
         | Quoted (DoubleQuotes, k) -> C.value double_quoted k
         | SoftBreak -> C.value soft_break ()
         | HardBreak -> C.value hard_break ()
         | Ext_wikilink (e, t, a) -> C.value ext_wikilink (e, t, a)
       in
       let cases =
         [ C.make str
         ; C.make emph
         ; C.make strong
         ; C.make mark
         ; C.make insert
         ; C.make delete
         ; C.make superscript
         ; C.make subscript
         ; C.make verbatim
         ; C.make symb
         ; C.make inline_math
         ; C.make display_math
         ; C.make link
         ; C.make image
         ; C.make span
         ; C.make footnote_reference
         ; C.make url
         ; C.make email
         ; C.make raw_inline
         ; C.make non_breaking_space
         ; C.make single_quoted
         ; C.make double_quoted
         ; C.make soft_break
         ; C.make hard_break
         ; C.make ext_wikilink
         ]
       in
       node ~kind:"inline" l cases enc_case)
  in
  Lazy.force t
;;

(* Blocks
   ====== *)

open Block

let tight : list_spacing Jsont.t =
  Jsont.map
    Jsont.bool
    ~dec:(fun b -> if b then Tight else Loose)
    ~enc:(function
      | Tight -> true
      | Loose -> false)
;;

(* A numeral between its delimiters: ["1."], ["a)"], ["(I)"]. *)
let ordered_style : (ordered_list_style * ordered_list_delim) Jsont.t =
  let numerals =
    [ Decimal, "1"; LetterLower, "a"; LetterUpper, "A"; RomanLower, "i"; RomanUpper, "I" ]
  in
  let delims =
    [ RightPeriod, ("", "."); RightParen, ("", ")"); LeftRightParen, ("(", ")") ]
  in
  Jsont.enum
    ~kind:"ordered list style"
    (List.concat_map
       (fun (s, n) -> List.map (fun (d, (o, c)) -> o ^ n ^ c, (s, d)) delims)
       numerals)
;;

let align : align Jsont.t =
  Jsont.enum
    ~kind:"alignment"
    [ "default", AlignDefault
    ; "left", AlignLeft
    ; "right", AlignRight
    ; "center", AlignCenter
    ]
;;

(* A list: its spacing and its items. *)
let spaced item =
  O.map (fun sp items -> sp, items)
  |> O.mem "tight" tight ~enc:fst
  |> O.mem "children" (Jsont.list item) ~enc:snd
  |> O.finish
;;

let labelled name value =
  O.map (fun label v -> label, v)
  |> O.mem "label" Jsont.string ~enc:fst
  |> O.mem name value ~enc:snd
  |> O.finish
;;

(* The two children of a definition list item. *)
type def_part =
  | Term of Inline.t node list
  | Definition of t node list

(* The children of a table. *)
type table_part =
  | Caption of Inline.t node list
  | Row of cell node list

(* The blocks that [keep] holds for are the ones written. *)
let block_list ?keep (block : t node Jsont.t) : t node list Jsont.t =
  match keep with
  | None -> Jsont.list block
  | Some keep -> Jsont.map (Jsont.list block) ~dec:Fun.id ~enc:(List.filter keep)
;;

let block_at ?keep (l : loc) (inline : Inline.t node Jsont.t) : t node Jsont.t =
  let inlines = Jsont.list inline in
  let plain k = Inline.to_plain_text k in
  let rec t =
    lazy
      (let blocks = block_list ?keep (Jsont.rec' t) in
       let heading =
         O.map (fun level _plain kids -> level, kids)
         |> O.mem "level" Jsont.int ~enc:fst
         |> O.mem "plain" Jsont.string ~dec_absent:"" ~enc:(fun (_, k) -> plain k)
         |> O.mem "children" inlines ~enc:snd
         |> O.finish
       in
       let code =
         O.map (fun lang text -> lang, text)
         |> O.mem "lang" Jsont.string ~dec_absent:"" ~enc:fst ~enc_omit:empty
         |> O.mem "text" Jsont.string ~enc:snd
         |> O.finish
       in
       let item = fixed l "list_item" (children blocks) in
       let ordered =
         let dec (ol_style, ol_delim) ol_start sp items =
           { ol_style; ol_delim; ol_start }, sp, items
         in
         O.map dec
         |> O.mem "style" ordered_style ~enc:(fun (a, _, _) -> a.ol_style, a.ol_delim)
         |> O.mem "start" Jsont.int ~enc:(fun (a, _, _) -> a.ol_start)
         |> O.mem "tight" tight ~enc:(fun (_, sp, _) -> sp)
         |> O.mem "children" (Jsont.list item) ~enc:(fun (_, _, items) -> items)
         |> O.finish
       in
       let task_item =
         let checkbox = Jsont.enum [ "checked", Complete; "unchecked", Incomplete ] in
         O.map (fun status kids -> status, kids)
         |> O.mem "checkbox" checkbox ~enc:fst
         |> O.mem "children" blocks ~enc:snd
         |> O.finish
         |> fixed l "task_list_item"
       in
       let def_item =
         let part =
           let term = C.map "term" (children inlines) ~dec:(fun k -> Term k) in
           let definition =
             C.map "definition" (children blocks) ~dec:(fun k -> Definition k)
           in
           node ~kind:"definition list item part" l [ C.make term; C.make definition ]
           @@ function
           | Term k -> C.value term k
           | Definition k -> C.value definition k
         in
         let dec = function
           | [ Node (p, a, Term term); Node (p', a', Definition def) ] ->
             Node (p, a, term), Node (p', a', def)
           | _ -> error "a definition list item holds a term, then a definition"
         in
         let enc (Node (p, a, term), Node (p', a', def)) =
           [ Node (p, a, Term term); Node (p', a', Definition def) ]
         in
         O.map dec
         |> O.mem "children" (Jsont.list part) ~enc
         |> O.finish
         |> fixed l "definition_list_item"
       in
       let table =
         let cell =
           let dec head align kids =
             Cell ((if head then HeadCell else BodyCell), align, kids)
           in
           O.map dec
           |> O.mem "head" Jsont.bool ~enc:(fun (Cell (ty, _, _)) -> ty = HeadCell)
           |> O.mem "align" align ~enc:(fun (Cell (_, al, _)) -> al)
           |> O.mem "children" inlines ~enc:(fun (Cell (_, _, k)) -> k)
           |> O.finish
           |> fixed l "cell"
         in
         let row =
           (* A row is a head row when its cells are head cells. *)
           let head cells =
             cells <> []
             && List.for_all
                  (fun c -> Node.content c |> fun (Cell (ty, _, _)) -> ty = HeadCell)
                  cells
           in
           O.map (fun _head cells -> cells)
           |> O.mem "head" Jsont.bool ~dec_absent:false ~enc:head
           |> O.mem "children" (Jsont.list cell) ~enc:Fun.id
           |> O.finish
         in
         let part =
           let caption = C.map "caption" (children inlines) ~dec:(fun k -> Caption k) in
           let row = C.map "row" row ~dec:(fun cells -> Row cells) in
           node ~kind:"table part" l [ C.make caption; C.make row ]
           @@ function
           | Caption k -> C.value caption k
           | Row cells -> C.value row cells
         in
         let rows =
           List.map (function
             | Node (p, a, Row cells) -> Node (p, a, cells)
             | Node (_, _, Caption _) -> error "a table's caption is its first child")
         in
         let dec = function
           | Node (p, a, Caption k) :: parts -> Node (p, a, k), rows parts
           | parts -> Node.make [], rows parts
         in
         let enc (Node (p, a, k), rows) =
           Node (p, a, Caption k)
           :: List.map (fun (Node (p, a, cells)) -> Node (p, a, Row cells)) rows
         in
         O.map dec |> O.mem "children" (Jsont.list part) ~enc |> O.finish
       in
       let keyed =
         let dec _plain label = function
           | [ b ] -> label, b
           | _ -> error "a keyed block holds one block"
         in
         O.map dec
         |> O.mem "plain" Jsont.string ~dec_absent:"" ~enc:(fun (label, _) -> plain label)
         |> O.mem "label" inlines ~enc:fst
         |> O.mem "children" blocks ~enc:(fun (_, b) -> [ b ])
         |> O.finish
       in
       let callout =
         let fold = Jsont.enum [ "expanded", FoldExpanded; "collapsed", FoldCollapsed ] in
         O.map (fun kind fold title body -> kind, fold, title, body)
         |> O.mem "kind" Jsont.string ~enc:(fun (k, _, _, _) -> k)
         |> O.opt_mem "fold" fold ~enc:(fun (_, f, _, _) -> f)
         |> O.mem "title" inlines ~enc:(fun (_, _, t, _) -> t)
         |> O.mem "children" blocks ~enc:(fun (_, _, _, b) -> b)
         |> O.finish
       in
       let para = C.map "para" (children inlines) ~dec:(fun k -> Para k) in
       let section = C.map "section" (children blocks) ~dec:(fun k -> Section k) in
       let heading = C.map "heading" heading ~dec:(fun (lvl, k) -> Heading (lvl, k)) in
       let block_quote =
         C.map "block_quote" (children blocks) ~dec:(fun k -> BlockQuote k)
       in
       let code_block =
         C.map "code_block" code ~dec:(fun (lang, s) -> CodeBlock (lang, s))
       in
       let div = C.map "div" (named blocks) ~dec:(fun (n, k) -> Div (n, k)) in
       let ordered_list =
         C.map "ordered_list" ordered ~dec:(fun (a, sp, items) ->
           OrderedList (a, sp, items))
       in
       let bullet_list =
         C.map "bullet_list" (spaced item) ~dec:(fun (sp, items) ->
           BulletList (sp, items))
       in
       let task_list =
         C.map "task_list" (spaced task_item) ~dec:(fun (sp, items) ->
           TaskList (sp, items))
       in
       let definition_list =
         C.map "definition_list" (spaced def_item) ~dec:(fun (sp, items) ->
           DefinitionList (sp, items))
       in
       let thematic_break =
         C.map "thematic_break" no_members ~dec:(fun () -> ThematicBreak)
       in
       let table = C.map "table" table ~dec:(fun (cap, rows) -> Table (cap, rows)) in
       let raw_block = C.map "raw_block" formatted ~dec:(fun (f, s) -> RawBlock (f, s)) in
       let footnote =
         C.map "footnote" (labelled "children" blocks) ~dec:(fun (label, k) ->
           FootnoteDef (label, k))
       in
       let reference =
         C.map "reference" (labelled "destination" Jsont.string) ~dec:(fun (label, d) ->
           RefDef (label, d))
       in
       let ext_keyed =
         C.map "ext_keyed" keyed ~dec:(fun (label, b) -> Ext_keyed (label, b))
       in
       let ext_callout =
         C.map "ext_callout" callout ~dec:(fun (k, f, t, b) -> Ext_callout (k, f, t, b))
       in
       let enc_case = function
         | Para k -> C.value para k
         | Section k -> C.value section k
         | Heading (lvl, k) -> C.value heading (lvl, k)
         | BlockQuote k -> C.value block_quote k
         | CodeBlock (lang, s) -> C.value code_block (lang, s)
         | Div (n, k) -> C.value div (n, k)
         | OrderedList (a, sp, items) -> C.value ordered_list (a, sp, items)
         | BulletList (sp, items) -> C.value bullet_list (sp, items)
         | TaskList (sp, items) -> C.value task_list (sp, items)
         | DefinitionList (sp, items) -> C.value definition_list (sp, items)
         | ThematicBreak -> C.value thematic_break ()
         | Table (cap, rows) -> C.value table (cap, rows)
         | RawBlock (f, s) -> C.value raw_block (f, s)
         | FootnoteDef (label, k) -> C.value footnote (label, k)
         | RefDef (label, d) -> C.value reference (label, d)
         | Ext_keyed (label, b) -> C.value ext_keyed (label, b)
         | Ext_callout (k, f, t, b) -> C.value ext_callout (k, f, t, b)
       in
       let cases =
         [ C.make para
         ; C.make section
         ; C.make heading
         ; C.make block_quote
         ; C.make code_block
         ; C.make div
         ; C.make ordered_list
         ; C.make bullet_list
         ; C.make task_list
         ; C.make definition_list
         ; C.make thematic_break
         ; C.make table
         ; C.make raw_block
         ; C.make footnote
         ; C.make reference
         ; C.make ext_keyed
         ; C.make ext_callout
         ]
       in
       node ~kind:"block" l cases enc_case)
  in
  Lazy.force t
;;

(* Trees and documents
   =================== *)

let no_loc = { loc = (fun _ -> Textloc.none) }
let inline = inline_at no_loc
let block = block_at no_loc inline

(* The footnote definitions, last closed first: the order the document
   pass assigns them in, reversed. *)
let footnote_defs_closing (d : Doc.t) : Block.t node list =
  let block f acc n =
    match Node.content n with
    | Block.FootnoteDef (_, k) ->
      Folder.ret (n :: List.fold_left (Folder.fold_block f) acc k)
    | _ -> Folder.default
  in
  Folder.fold_doc (Folder.make ~block ()) [] d
;;

(* Encoding only: a [Doc.t] is not built from blocks.  Definitions are
   listed in [references] and [footnotes] and left out of the blocks. *)
let doc (d : Doc.t) : Doc.t Jsont.t =
  let l = { loc = (fun n -> Doc.textloc d n) } in
  let keep n =
    match Node.content n with
    | RefDef _ | FootnoteDef _ -> false
    | _ -> true
  in
  let block = block_at ~keep l (inline_at l) in
  let defs = assoc ~kind:"definitions" block in
  let reference (label, (dest, attrs)) = label, Node.make ~attrs (RefDef (label, dest)) in
  (* An entry is the definition node its blocks came from, so it has that
     node's attributes and position. *)
  let footnotes d =
    let defs = footnote_defs_closing d in
    let defines label n =
      match Node.content n with
      | Block.FootnoteDef (l, _) -> Kernel.Ast.normalize_label l = label
      | _ -> false
    in
    List.map (fun (label, _) -> label, List.find (defines label) defs) (Doc.footnotes d)
  in
  O.enc_only ~kind:"doc" ()
  |> O.mem "tag" Jsont.string ~enc:(Fun.const "doc")
  |> O.mem "references" defs ~enc:(fun d -> List.map reference (Doc.references d))
  |> O.mem "autoReferences" defs ~enc:(fun d ->
    List.map reference (Doc.auto_references d))
  |> O.mem "footnotes" defs ~enc:footnotes
  |> O.mem "children" (block_list ~keep block) ~enc:Doc.blocks
  |> O.finish
;;

let of_doc (d : Doc.t) : Jsont.json =
  match Jsont.Json.encode' (doc d) d with
  | Ok json -> json
  | Error e -> invalid_arg (Jsont.Error.to_string e)
;;

let to_string ?(format = Jsont.Minify) (d : Doc.t) : string =
  match Jsont_bytesrw.encode_string ~format (doc d) d with
  | Ok s -> s
  | Error e -> invalid_arg e
;;
