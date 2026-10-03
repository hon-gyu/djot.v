(*---------------------------------------------------------------------------
   Copyright (c) 2021 The cmarkit programmers. All rights reserved.
   Copyright (c) 2026 hon-gyu. All rights reserved.
   SPDX-License-Identifier: MIT AND ISC
  ---------------------------------------------------------------------------*)

(* The module types are modeled on cmarkit's; see LICENSE-cmarkit. The
   implementation is not derived from cmarkit: it calls the Rocq-extracted
   kernel. 
   
   Other deviation:
   - No [Meta.t]. [Attr.t] is used instead.
*)

module Kernel = Djot_kernel
module K = Kernel

module Attr = struct
  type t = (string * string) list

  let empty : t = []
  let find (k : string) (a : t) : string option = K.Ast.alist_lookup k a
  let id (a : t) : string option = find "id" a

  let classes (a : t) : string list =
    match find "class" a with
    | None -> []
    | Some s -> List.filter (( <> ) "") (String.split_on_char ' ' s)
  ;;

  let key_values (a : t) : (string * string) list =
    List.filter (fun (k, _) -> k <> "id" && k <> "class") a
  ;;

  let is_key (k : string) : bool = k <> "" && String.for_all K.Attributes.is_key_char k

  let set (k : string) (v : string) (a : t) : t option =
    if is_key k then Some (K.Ast.Attr.set k v a) else None
  ;;

  let add_class (c : string) (a : t) : t option =
    if K.Attributes.class_word_ok c then Some (K.Ast.Attr.add_class c a) else None
  ;;

  let set_exn k v a =
    match set k v a with
    | Some a -> a
    | None -> invalid_arg "Attr.set_exn: not a key"
  ;;

  let add_class_exn c a =
    match add_class c a with
    | Some a -> a
    | None -> invalid_arg "Attr.add_class_exn: not a class name"
  ;;

  let to_string : t -> string = K.Attributes.attr_spec

  (** Whitespace runs in a value collapse to one space, 
      so [of_string (to_string a) <> a].  *)
  let of_string (s : string) : t option =
    let n = String.length s in
    if n = 0 || s.[0] <> '{'
    then None
    else (
      let p, rest = K.Attributes.afeed (String.sub s 1 (n - 1)) K.Attributes.ap_init in
      if K.Attributes.ap_done p && rest = "" then Some p.ap_attrs else None)
  ;;
end

type 'a node = 'a K.Ast.node = Node of K.Ast.pos * Attr.t * 'a

module Node = struct
  let make ?(attrs : Attr.t = []) x : 'a node = Node (K.Ast.NoPos, attrs, x)

  let attrs : 'a node -> Attr.t = function
    | Node (_, a, _) -> a
  ;;

  let content : 'a node -> 'a = function
    | Node (_, _, x) -> x
  ;;
end

module Inline = struct
  type math_style = K.Ast.math_style =
    | DisplayMath
    | InlineMath

  type target = K.Ast.target =
    | Direct of string
    | Reference of string

  type quote_type = K.Ast.quote_type =
    | SingleQuotes
    | DoubleQuotes

  type t = K.Ast.inline =
    | Str of string
    | Emph of t node list
    | Strong of t node list
    | Highlight of t node list
    | Insert of t node list
    | Delete of t node list
    | Superscript of t node list
    | Subscript of t node list
    | Verbatim of string
    | Symbol of string
    | Math of math_style * string
    | Link of t node list * target
    | Image of t node list * target
    | Span of string * t node list
    | FootnoteReference of string
    | UrlLink of string
    | EmailLink of string
    | RawInline of string * string
    | NonBreakingSpace
    | Quoted of quote_type * t node list
    | SoftBreak
    | HardBreak
    | Ext_wikilink of bool * string * string option

  let to_plain_text (ns : t node list) : string =
    String.concat "" (List.map (fun n -> K.Document.inline_text (Node.content n)) ns)
  ;;
end

module Block = struct
  type list_spacing = K.Ast.list_spacing =
    | Tight
    | Loose

  type ordered_list_style = K.Ast.ordered_list_style =
    | Decimal
    | LetterUpper
    | LetterLower
    | RomanUpper
    | RomanLower

  type ordered_list_delim = K.Ast.ordered_list_delim =
    | RightPeriod
    | RightParen
    | LeftRightParen

  type ordered_list_attributes = K.Ast.ordered_list_attributes =
    { ol_style : ordered_list_style
    ; ol_delim : ordered_list_delim
    ; ol_start : int
    }

  type task_status = K.Ast.task_status =
    | Complete
    | Incomplete

  type align = K.Ast.align =
    | AlignLeft
    | AlignRight
    | AlignCenter
    | AlignDefault

  type cell_type = K.Ast.cell_type =
    | HeadCell
    | BodyCell

  type cell = K.Ast.cell = Cell of cell_type * align * Inline.t node list

  type callout_fold = K.Ast.callout_fold =
    | FoldExpanded
    | FoldCollapsed

  type t = K.Ast.block =
    | Para of Inline.t node list
    | Section of t node list
    | Heading of int * Inline.t node list
    | BlockQuote of t node list
    | CodeBlock of string * string
    | Div of string * t node list
    | OrderedList of ordered_list_attributes * list_spacing * t node list list
    | BulletList of list_spacing * t node list list
    | TaskList of list_spacing * (task_status * t node list) list
    | DefinitionList of list_spacing * (Inline.t node list * t node list) list
    | ThematicBreak
    | Table of Inline.t node list * cell list list
    | RawBlock of string * string
    | FootnoteDef of string * t node list
    | RefDef of string * string
    | Ext_keyed of Inline.t node list * t node
    | Ext_callout of string * callout_fold option * Inline.t node list * t node list
end

module Textloc = struct
  type byte_pos = int
  type line_pos = int * byte_pos

  type t =
    { first_byte : byte_pos
    ; last_byte : byte_pos
    ; first_line : line_pos
    ; last_line : line_pos
    }

  let first_byte t = t.first_byte
  let last_byte t = t.last_byte
  let first_line t = t.first_line
  let last_line t = t.last_line

  let make ~first_byte ~last_byte ~first_line ~last_line =
    { first_byte; last_byte; first_line; last_line }
  ;;

  let none = { first_byte = -1; last_byte = -1; first_line = -1, -1; last_line = -1, -1 }
  let is_none t = t.first_byte < 0
  let is_empty t = t.first_byte > t.last_byte

  let reloc ~first ~last =
    { first with last_byte = last.last_byte; last_line = last.last_line }
  ;;

  let pp : Format.formatter -> t -> unit =
    fun ppf t ->
    if is_none t
    then Format.pp_print_string ppf "<none>"
    else
      Format.fprintf
        ppf
        "%d.%d-%d.%d"
        (fst t.first_line)
        (t.first_byte - snd t.first_line)
        (fst t.last_line)
        (t.last_byte - snd t.last_line)
  ;;

  (* Strings.resolve_spot, over an array: the list lookup is linear in
     the line index. *)
  let resolve_spot (lines : K.Strings.source_line array) (p : K.Ast.spot) =
    if p.spot_line >= Array.length lines
    then None
    else (
      let l = lines.(p.spot_line) in
      if p.spot_rem > l.source_line_length
      then None
      else (
        let col = l.source_line_length - p.spot_rem in
        Some (l.source_line_start + col, p.spot_line, col)))
  ;;

  let line_pos lines i = i + 1, lines.(i).K.Strings.source_line_start

  (* A stop at the start of a line ends the range on the line before. *)
  let of_span lines (s : K.Ast.span) =
    match resolve_spot lines s.span_start, resolve_spot lines s.span_stop with
    | Some (a, la, _), Some (b, lb, cb) ->
      let lb = if cb = 0 && b > a && lb > la then lb - 1 else lb in
      { first_byte = a
      ; last_byte = b - 1
      ; first_line = line_pos lines la
      ; last_line = line_pos lines lb
      }
    | _ -> none
  ;;
end

module Profile = struct
  type t = K.Profile.profile

  let djot = K.Profile.djot_profile
  let markdown_like = K.Profile.markdown_like_profile
  let with_footnotes = K.Profile.with_footnotes

  (* The inline switches are the ones proved to keep a table admissible
     (InlineTable.v, `*_preserves_admissible`). *)
  let inline f b (p : t) = { p with profile_inline = f b p.profile_inline }
  let block f b (p : t) = { p with profile_block = f b p.profile_block }
  let with_smart_typography = inline K.InlineTable.with_smart_typography
  let with_raw_inline = inline K.InlineTable.with_raw_inline
  let with_math = inline K.InlineTable.with_math
  let with_inline_attrs = inline K.InlineTable.with_inline_attrs
  let with_ext_wikilinks = inline K.InlineTable.with_wikilinks
  let with_ext_dollar_math = inline K.InlineTable.with_dollar_math
  let with_tables = block K.Step.with_tables
  let with_divs = block K.Step.with_divs
  let with_tasks = block K.Step.with_tasks
  let with_raw_blocks = block K.Step.with_raw_blocks
  let with_deflists = block K.Step.with_deflists
  let with_block_attrs = block K.Step.with_block_attrs
  let with_heading_continuation = block K.Step.with_heading_continuation
  let with_ext_keyed = block K.Step.with_keyed
  let with_ext_callouts = block K.Step.with_callouts
  let with_ext_tags = K.Profile.with_tags
end

module Doc = struct
  type t =
    { kernel : K.Ast.doc
    ; footnote_defs : Block.t node list
    ; lines : K.Strings.source_line array option
    ; source : (string * K.Reparse.piece list) option
        (* The source and its pieces, for [replace_lines]. *)
    ; profile : Profile.t
    }

  (* The definitions the document pass takes out of the tree, in source
     order. *)
  let rec collect_footnote_defs acc (Node (_, _, b) as n) =
    let bl acc l = List.fold_left collect_footnote_defs acc l in
    match (b : Block.t) with
    | FootnoteDef (_, l) -> bl (n :: acc) l
    | Section l | BlockQuote l | Div (_, l) | Ext_callout (_, _, _, l) -> bl acc l
    | OrderedList (_, _, its) | BulletList (_, its) -> List.fold_left bl acc its
    | TaskList (_, its) -> List.fold_left (fun acc (_, it) -> bl acc it) acc its
    | DefinitionList (_, its) -> List.fold_left (fun acc (_, it) -> bl acc it) acc its
    | Ext_keyed (_, b) -> collect_footnote_defs acc b
    | Para _ | Heading _ | CodeBlock _ | ThematicBreak | Table _ | RawBlock _ | RefDef _
      -> acc
  ;;

  let make ~profile ~lines ~source pos bs =
    { kernel = K.Document.doc_pass pos bs
    ; footnote_defs = List.rev (List.fold_left collect_footnote_defs [] bs)
    ; lines
    ; source
    ; profile
    }
  ;;

  (* The fold step the pieces are cut with, and its finish. *)
  let fold_step ~locs (p : Profile.t) =
    let { K.Profile.profile_inline = table; profile_block = bconfig } = p in
    if locs
    then K.Reparse.loc_step table bconfig, K.Step.finish table bconfig K.Ast.located_pos
    else K.Reparse.sem_step table bconfig, K.Step.finish table bconfig K.Ast.semantic_pos
  ;;

  let of_pieces ~profile ~locs src ps =
    if locs
    then
      make
        ~profile
        ~lines:(Some (Array.of_list (K.Strings.line_table src)))
        ~source:(Some (src, ps))
        K.Ast.located_pos
        (K.Reparse.assemble 0 ps)
    else
      make
        ~profile
        ~lines:None
        ~source:(Some (src, ps))
        K.Ast.semantic_pos
        (K.Reparse.pieces_tree ps)
  ;;

  let of_string ?(profile = Profile.djot) ?(locs = false) s =
    let stp, fin = fold_step ~locs profile in
    of_pieces ~profile ~locs s (K.Reparse.pieces stp fin (K.Strings.split_lines s))
  ;;

  let of_blocks ?(profile = Profile.djot) bs =
    make ~profile ~lines:None ~source:None K.Ast.semantic_pos bs
  ;;

  (* The byte where zero-based line [k] starts, or the length when [k] is
     the number of lines. *)
  let line_start src k =
    let rec go i k =
      if k = 0
      then i
      else (
        match String.index_from_opt src i '\n' with
        | Some j -> go (j + 1) (k - 1)
        | None -> String.length src)
    in
    go 0 k
  ;;

  (* [src] with zero-based lines [f] to [l] replaced by [s], newlines
     added where [s] would otherwise join a neighbouring line. *)
  let edit_source src f l s =
    let a = line_start src f
    and b = line_start src (l + 1) in
    let pre = String.sub src 0 a
    and post = String.sub src b (String.length src - b) in
    let ends_nl x = x <> "" && x.[String.length x - 1] = '\n' in
    let mid =
      if s = ""
      then ""
      else (
        let s = if post <> "" && not (ends_nl s) then s ^ "\n" else s in
        if pre <> "" && not (ends_nl pre) then "\n" ^ s else s)
    in
    pre ^ mid ^ post
  ;;

  (* The edit widens to the pieces holding lines [first] to [last]; the
     lines of those pieces outside the range go back in around [s]. *)
  let replace_lines d ~first ~last s =
    let src, ps =
      match d.source with
      | Some x -> x
      | None -> invalid_arg "Doc.replace_lines: not made by of_string"
    in
    let n = List.length ps in
    let pa = Array.of_list ps in
    let starts = Array.make (n + 1) 0 in
    Array.iteri
      (fun k p -> starts.(k + 1) <- starts.(k) + List.length p.K.Reparse.piece_lines)
      pa;
    let f = first - 1
    and l = last - 1 in
    if f < 0 || l < f - 1 || l >= starts.(n)
    then invalid_arg "Doc.replace_lines: range outside the document";
    let rec holding k = if k < n && starts.(k + 1) <= f then holding (k + 1) else k in
    let rec after k = if k < n && starts.(k) <= l then after (k + 1) else k in
    let i = holding 0 in
    let j = max i (after 0) in
    let before =
      if i < j
      then List.filteri (fun k _ -> starts.(i) + k < f) pa.(i).K.Reparse.piece_lines
      else []
    in
    let behind =
      if i < j
      then
        List.filteri (fun k _ -> starts.(j - 1) + k > l) pa.(j - 1).K.Reparse.piece_lines
      else []
    in
    let locs = Option.is_some d.lines in
    let stp, fin = fold_step ~locs d.profile in
    of_pieces
      ~profile:d.profile
      ~locs
      (edit_source src f l s)
      (K.Reparse.splice stp fin ps i j (before @ K.Strings.split_lines s @ behind))
  ;;

  let source d = Option.map fst d.source
  let blocks d = d.kernel.doc_blocks
  let footnotes d = d.kernel.doc_footnotes
  let footnote_defs d = d.footnote_defs
  let footnote d l = K.Ast.alist_lookup (K.Ast.normalize_label l) (footnotes d)
  let references d = d.kernel.doc_references

  let reference d l =
    K.Ast.lookup_reference l (d.kernel.doc_references @ d.kernel.doc_auto_references)
  ;;

  let textloc d (Node (p, _, _)) =
    match d.lines, p with
    | Some lines, K.Ast.SomePos p -> Textloc.of_span lines p.node_span
    | _ -> Textloc.none
  ;;

  (* A definition's range starts at its [[^]. *)
  let footnote_label_loc d n =
    match n with
    | Node (_, _, Block.FootnoteDef (label, _)) ->
      let l = textloc d n in
      if Textloc.is_none l
      then Textloc.none
      else (
        let first_byte = l.first_byte + 2 in
        Textloc.make
          ~first_byte
          ~last_byte:(first_byte + String.length label - 1)
          ~first_line:l.first_line
          ~last_line:l.first_line)
    | Node _ -> Textloc.none
  ;;

  type syntax = K.Ast.syntax_role =
    | RAttrSpec
    | ROpenFence
    | RCloseFence

  type parts =
    | NoParts
    | Items of Textloc.t list
    | DefItems of (Textloc.t * Textloc.t * Textloc.t) list
    | TableRows of Textloc.t option * (Textloc.t * Textloc.t list) list

  let provenance d (Node (p, _, _)) =
    match d.lines, p with
    | Some lines, K.Ast.SomePos p -> Some (lines, p)
    | _ -> None
  ;;

  let syntax_locs d n =
    match provenance d n with
    | Some (lines, p) ->
      (* Recorded as the parser settles them: a block's attribute spec
           comes after its fences. *)
      List.map (fun (r, s) -> r, Textloc.of_span lines s) p.syntax_spans
      |> List.stable_sort (fun (_, a) (_, b) ->
        compare a.Textloc.first_byte b.Textloc.first_byte)
    | None -> []
  ;;

  let parts d n =
    match provenance d n with
    | None -> NoParts
    | Some (lines, p) ->
      let loc = Textloc.of_span lines in
      (match p.part_spans with
       | K.Ast.PNone -> NoParts
       | PItems items -> Items (List.map loc items)
       | PDefItems items ->
         DefItems (List.map (fun ((i, t), d) -> loc i, loc t, loc d) items)
       | PTable (cap, rows) ->
         TableRows
           (Option.map loc cap, List.map (fun (r, cs) -> loc r, List.map loc cs) rows))
  ;;

  let kernel d = d.kernel
end

(* Both traversals match every constructor by name, leaves included, so a
   constructor added in Rocq fails to compile here until it is placed. *)

module Mapper = struct
  type 'a filter_map = 'a option

  type 'a result =
    [ `Default
    | `Map of 'a
    ]

  let default = `Default
  let delete : 'a result = `Map None
  let ret (x : 'a) : 'a filter_map result = `Map (Some x)

  type t =
    { inline : t -> Inline.t node -> Inline.t node filter_map result
    ; block : t -> Block.t node -> Block.t node filter_map result
    }

  type 'a mapper = t -> 'a -> 'a filter_map result

  let make
    ?(inline : Inline.t node mapper = fun _ _ -> `Default)
    ?(block : Block.t node mapper = fun _ _ -> `Default)
    ()
    =
    { inline; block }
  ;;

  let rec map_inline m n =
    match m.inline m n with
    | `Map r -> r
    | `Default -> Some (inline_children m n)

  and map_inlines m ns = List.filter_map (map_inline m) ns

  and inline_children m (Node (p, a, x)) : Inline.t node =
    let k = map_inlines m in
    let x : Inline.t =
      match x with
      | Emph l -> Emph (k l)
      | Strong l -> Strong (k l)
      | Highlight l -> Highlight (k l)
      | Insert l -> Insert (k l)
      | Delete l -> Delete (k l)
      | Superscript l -> Superscript (k l)
      | Subscript l -> Subscript (k l)
      | Link (l, t) -> Link (k l, t)
      | Image (l, t) -> Image (k l, t)
      | Span (n, l) -> Span (n, k l)
      | Quoted (q, l) -> Quoted (q, k l)
      | ( Str _
        | Verbatim _
        | Symbol _
        | Math _
        | FootnoteReference _
        | UrlLink _
        | EmailLink _
        | Ext_wikilink _
        | RawInline _
        | NonBreakingSpace
        | SoftBreak
        | HardBreak ) as x -> x
    in
    Node (p, a, x)
  ;;

  let rec map_block m n =
    match m.block m n with
    | `Map r -> r
    | `Default -> block_children m n

  and map_blocks m ns = List.filter_map (map_block m) ns

  and block_children m (Node (p, a, x)) : Block.t node option =
    let il = map_inlines m
    and bl = map_blocks m in
    let cell (Block.Cell (t, al, l)) = Block.Cell (t, al, il l) in
    let x : Block.t option =
      match x with
      | Para l -> Some (Para (il l))
      | Section l -> Some (Section (bl l))
      | Heading (lvl, l) -> Some (Heading (lvl, il l))
      | BlockQuote l -> Some (BlockQuote (bl l))
      | Div (n, l) -> Some (Div (n, bl l))
      | OrderedList (o, sp, its) -> Some (OrderedList (o, sp, List.map bl its))
      | BulletList (sp, its) -> Some (BulletList (sp, List.map bl its))
      | TaskList (sp, its) -> Some (TaskList (sp, List.map (fun (s, it) -> s, bl it) its))
      | DefinitionList (sp, its) ->
        Some (DefinitionList (sp, List.map (fun (t, it) -> il t, bl it) its))
      | Table (cap, rows) -> Some (Table (il cap, List.map (List.map cell) rows))
      | FootnoteDef (l, bs) -> Some (FootnoteDef (l, bl bs))
      | Ext_keyed (l, b) ->
        Option.map (fun b -> Block.Ext_keyed (il l, b)) (map_block m b)
      | Ext_callout (kind, fold, title, body) ->
        Some (Ext_callout (kind, fold, il title, bl body))
      | (CodeBlock _ | ThematicBreak | RawBlock _ | RefDef _) as x -> Some x
    in
    Option.map (fun x -> Node (p, a, x)) x
  ;;

  let map_doc (m : t) (d : Doc.t) : Doc.t =
    let k = d.kernel in
    { d with
      kernel =
        { k with
          doc_blocks = map_blocks m k.doc_blocks
        ; doc_footnotes = List.map (fun (l, bs) -> l, map_blocks m bs) k.doc_footnotes
        }
    }
  ;;
end

module Folder = struct
  type 'a result =
    [ `Default
    | `Fold of 'a
    ]

  let default = `Default
  let ret x = `Fold x

  type 'a t =
    { inline : 'a t -> 'a -> Inline.t node -> 'a result
    ; block : 'a t -> 'a -> Block.t node -> 'a result
    }

  type ('a, 'b) folder = 'b t -> 'b -> 'a -> 'b result

  let make
    ?(inline : (Inline.t node, 'a) folder = fun _ _ _ -> `Default)
    ?(block : (Block.t node, 'a) folder = fun _ _ _ -> `Default)
    ()
    =
    { inline; block }
  ;;

  let rec fold_inline (f : 'a t) (acc : 'a) (n : Inline.t node) : 'a =
    match f.inline f acc n with
    | `Fold acc -> acc
    | `Default ->
      let k = List.fold_left (fold_inline f) acc in
      (match Node.content n with
       | Emph l
       | Strong l
       | Highlight l
       | Insert l
       | Delete l
       | Superscript l
       | Subscript l
       | Link (l, _)
       | Image (l, _)
       | Span (_, l)
       | Quoted (_, l) -> k l
       | Str _
       | Verbatim _
       | Symbol _
       | Math _
       | FootnoteReference _
       | UrlLink _
       | EmailLink _
       | Ext_wikilink _
       | RawInline _
       | NonBreakingSpace
       | SoftBreak
       | HardBreak -> acc)
  ;;

  let rec fold_block (f : 'a t) (acc : 'a) (n : Block.t node) : 'a =
    match f.block f acc n with
    | `Fold acc -> acc
    | `Default ->
      let il acc l = List.fold_left (fold_inline f) acc l in
      let bl acc l = List.fold_left (fold_block f) acc l in
      (match Node.content n with
       | Para l | Heading (_, l) -> il acc l
       | Section l | BlockQuote l | Div (_, l) | FootnoteDef (_, l) -> bl acc l
       | OrderedList (_, _, its) | BulletList (_, its) -> List.fold_left bl acc its
       | TaskList (_, its) -> List.fold_left (fun acc (_, it) -> bl acc it) acc its
       | DefinitionList (_, its) ->
         List.fold_left (fun acc (t, it) -> bl (il acc t) it) acc its
       | Table (cap, rows) ->
         let cell acc (Block.Cell (_, _, l)) = il acc l in
         let acc = List.fold_left (List.fold_left cell) acc rows in
         il acc cap
       | Ext_keyed (l, b) -> fold_block f (il acc l) b
       | Ext_callout (_, _, title, body) -> bl (il acc title) body
       | CodeBlock _ | ThematicBreak | RawBlock _ | RefDef _ -> acc)
  ;;

  let fold_doc (f : 'a t) (acc : 'a) (d : Doc.t) : 'a =
    let bl acc l = List.fold_left (fold_block f) acc l in
    List.fold_left
      (fun acc (_, bs) -> bl acc bs)
      (bl acc (Doc.blocks d))
      (Doc.footnotes d)
  ;;
end

module Html = struct
  type t = K.Html.helt =
    | HText of string
    | HRaw of string
    | HVoid of string * bool * Attr.t
    | HElem of string * int * Attr.t * t list

  let tree (d : Doc.t) = K.Html.html_tree d.kernel
  let (to_string : t list -> string) = K.Html.serialize_flat
  let of_doc (d : Doc.t) = K.Html.render_html d.kernel
end

module Source = struct
  let of_blocks ?(profile = Profile.djot) (bs : Block.t node list) =
    K.Render.render_djot profile.K.Profile.profile_inline profile.profile_block bs
  ;;

  let of_inlines ?(profile = Profile.djot) (ils : Inline.t node list) =
    String.concat "\n" (K.InlineView.inline_lines profile.K.Profile.profile_inline ils "")
  ;;

  let of_doc (d : Doc.t) =
    K.Render.render_doc d.profile.profile_inline d.profile.profile_block d.kernel
  ;;
end
