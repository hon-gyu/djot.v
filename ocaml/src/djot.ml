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

  let kvs (a : t) : (string * string) list =
    List.filter (fun (k, _) -> k <> "id" && k <> "class") a
  ;;

  let is_valid : t -> bool = K.Attributes.attr_ok
  let is_key : string -> bool = K.Attributes.key_ok
  let is_class : string -> bool = K.Attributes.class_word_ok

  let is_valid_strict : t -> bool =
    fun a -> is_valid a && List.for_all (fun c -> is_class c) (classes a)
  ;;

  let set (k : string) (v : string) (a : t) : t option =
    if is_key k then Some (K.Ast.Attr.set k v a) else None
  ;;

  let set_id (id : string) (a : t) : t = K.Ast.Attr.set "id" id a

  let add_class (c : string) (a : t) : t option =
    if is_class c then Some (K.Ast.Attr.add_class c a) else None
  ;;

  let remove : string -> t -> t = K.Ast.Attr.remove

  let set_classes (cs : string list) (a : t) : t option =
    if List.for_all is_class cs then Some (K.Ast.Attr.set_classes cs a) else None
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

  let set_classes_exn cs a =
    match set_classes cs a with
    | Some a -> a
    | None -> invalid_arg "Attr.set_classes_exn: not a class name"
  ;;

  let to_string : t -> string = K.Attributes.attr_spec

  (** Whitespace runs in a value collapse to one space, so [of_string (to_string a) <> a]. *)
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

module Profile = struct
  type t = K.Profile.options

  let djot = K.Profile.djot_options
  let markdown_like = K.Profile.markdown_like_options
  let table (p : t) = p.o_inline
  let of_kernel (o : t) = if K.InlineTable.dconfig_ok o.o_inline then Some o else None
  let bconfig = K.Profile.bconfig_of

  module Switch = struct
    type profile = t

    type t =
      { name : string
      ; doc : string
      ; get : profile -> bool
      ; set : bool -> profile -> profile
      }

    let name s = s.name
    let doc s = s.doc
    let is_extension s = not (s.get djot)
    let get s = s.get
    let set s = s.set
  end

  (* The inline switches are the ones proved to keep a table admissible
     (InlineTable.v, `*_preserves_admissible`). *)
  let inline name doc get f : Switch.t =
    { name
    ; doc
    ; get = (fun p -> get p.K.Profile.o_inline)
    ; set = (fun b p -> { p with o_inline = f b p.o_inline })
    }
  ;;

  open K.InlineTable

  let footnotes =
    inline
      "footnotes"
      "[^a] and [^a]: ..."
      (fun t -> t.dc_footnotes)
      with_inline_footnotes
  ;;

  let smart_typography =
    inline
      "smart_typography"
      "dashes and ellipses"
      (fun t -> t.dc_smart_typography)
      with_smart_typography
  ;;

  let raw_inline =
    inline "raw_inline" "`x`{=html}" (fun t -> t.dc_raw_inline) with_raw_inline
  ;;

  let math = inline "math" "$`x` and $$`x`" (fun t -> t.dc_math) with_math

  let inline_attrs =
    inline
      "inline_attrs"
      "{...} after an inline, and [text]{...}"
      (fun t -> t.dc_attrs)
      with_inline_attrs
  ;;

  let ext_wikilinks =
    inline
      "ext_wikilinks"
      "[[target|alias]] and ![[target]]"
      (fun t -> t.dc_wikilinks)
      with_wikilinks
  ;;

  let ext_dollar_math =
    inline
      "ext_dollar_math"
      "$x$, $$x$$ and $`x`$"
      (fun t -> t.dc_dollar_math)
      with_dollar_math
  ;;

  let ext_tags =
    inline "ext_tags" "::: name and :name[...]" (fun t -> t.dc_tags) with_inline_tags
  ;;

  let tables : Switch.t =
    { name = "tables"
    ; doc = "pipe tables"
    ; get = (fun p -> p.o_tables)
    ; set = (fun b p -> { p with o_tables = b })
    }
  ;;

  let divs : Switch.t =
    { name = "divs"
    ; doc = "::: fenced divs"
    ; get = (fun p -> p.o_divs)
    ; set = (fun b p -> { p with o_divs = b })
    }
  ;;

  let tasks : Switch.t =
    { name = "tasks"
    ; doc = "- [ ] task list items"
    ; get = (fun p -> p.o_tasks)
    ; set = (fun b p -> { p with o_tasks = b })
    }
  ;;

  let raw_blocks : Switch.t =
    { name = "raw_blocks"
    ; doc = "code blocks with an =format info string"
    ; get = (fun p -> p.o_raw_blocks)
    ; set = (fun b p -> { p with o_raw_blocks = b })
    }
  ;;

  let deflists : Switch.t =
    { name = "deflists"
    ; doc = ": definition lists"
    ; get = (fun p -> p.o_deflists)
    ; set = (fun b p -> { p with o_deflists = b })
    }
  ;;

  let block_attrs : Switch.t =
    { name = "block_attrs"
    ; doc = "an attribute line {...} before a block"
    ; get = (fun p -> p.o_block_attrs)
    ; set = (fun b p -> { p with o_block_attrs = b })
    }
  ;;

  let heading_continuation : Switch.t =
    { name = "heading_continuation"
    ; doc = "a heading's text continues onto the following lines"
    ; get = (fun p -> p.o_heading_continuation)
    ; set = (fun b p -> { p with o_heading_continuation = b })
    }
  ;;

  let ext_keyed : Switch.t =
    { name = "ext_keyed"
    ; doc = "label: content"
    ; get = (fun p -> p.o_keyed)
    ; set = (fun b p -> { p with o_keyed = b })
    }
  ;;

  let ext_callouts : Switch.t =
    { name = "ext_callouts"
    ; doc = "> [!kind] on the first line of a block quote"
    ; get = (fun p -> p.o_callouts)
    ; set = (fun b p -> { p with o_callouts = b })
    }
  ;;

  let ext_setext_headings : Switch.t =
    { name = "ext_setext_headings"
    ; doc = "a paragraph underlined with = or --"
    ; get = (fun p -> p.o_setext)
    ; set = (fun b p -> { p with o_setext = b })
    }
  ;;

  let ext_list_interrupts : Switch.t =
    { name = "ext_list_interrupts"
    ; doc = "a list starts on the line after paragraph text"
    ; get = (fun p -> p.o_list_interrupts)
    ; set = (fun b p -> { p with o_list_interrupts = b })
    }
  ;;

  let switches =
    [ footnotes
    ; smart_typography
    ; raw_inline
    ; math
    ; inline_attrs
    ; tables
    ; divs
    ; tasks
    ; raw_blocks
    ; deflists
    ; block_attrs
    ; heading_continuation
    ; ext_wikilinks
    ; ext_dollar_math
    ; ext_keyed
    ; ext_callouts
    ; ext_tags
    ; ext_setext_headings
    ; ext_list_interrupts
    ]
  ;;

  let with_footnotes = footnotes.set
  let with_smart_typography = smart_typography.set
  let with_raw_inline = raw_inline.set
  let with_math = math.set
  let with_inline_attrs = inline_attrs.set
  let with_tables = tables.set
  let with_divs = divs.set
  let with_tasks = tasks.set
  let with_raw_blocks = raw_blocks.set
  let with_deflists = deflists.set
  let with_block_attrs = block_attrs.set
  let with_heading_continuation = heading_continuation.set
  let with_ext_wikilinks = ext_wikilinks.set
  let with_ext_dollar_math = ext_dollar_math.set
  let with_ext_keyed = ext_keyed.set
  let with_ext_callouts = ext_callouts.set
  let with_ext_tags = ext_tags.set
  let with_ext_setext_headings = ext_setext_headings.set
  let with_ext_list_interrupts = ext_list_interrupts.set

  let pp_fields ppf fields =
    Format.pp_open_vbox ppf 0;
    Format.pp_print_list
      ~pp_sep:Format.pp_print_cut
      (fun ppf (name, v) -> Format.fprintf ppf "%s: %s" name v)
      ppf
      fields;
    Format.pp_close_box ppf ()
  ;;

  module Delimiter = struct
    type profile = t

    type syntax =
      [ `Off
      | `Braced
      | `Bare
      ]

    type t =
      { name : string
      ; row : dstyle
      }

    let name d = d.name

    let spelling d (p : profile) : char * int * syntax =
      let t = table p in
      ( t.dc_char d.row
      , t.dc_width d.row
      , match t.dc_syntax d.row with
        | DOff -> `Off
        | DBraced -> `Braced
        | DBare | DBareAfterBreak -> `Bare )
    ;;
  end

  let emph : Delimiter.t = { name = "emph"; row = DEmph }
  let strong : Delimiter.t = { name = "strong"; row = DStrong }
  let superscript : Delimiter.t = { name = "superscript"; row = DSuper }
  let subscript : Delimiter.t = { name = "subscript"; row = DSub }
  let highlight : Delimiter.t = { name = "highlight"; row = DMark }
  let insert : Delimiter.t = { name = "insert"; row = DInsert }
  let delete : Delimiter.t = { name = "delete"; row = DDelete }
  let delimiters = [ emph; strong; superscript; subscript; highlight; insert; delete ]

  (* The quote rows have no setter: what an unmatched quote leaves behind
     is part of the row. *)
  let rows =
    delimiters @ [ { name = "single_quote"; row = DSQuote }; { name = "double_quote"; row = DDQuote } ]
  ;;

  let refusal c : drow_refusal -> string = function
    | RWidth -> "the width must be at least 1"
    | RNotPunct -> Printf.sprintf "%C is not ASCII punctuation" c
    | RReserved -> Printf.sprintf "%C is taken by other syntax" c
    | RDecay -> "an unmatched delimiter must leave something behind"
    | RBareHyphen -> "a bare delimiter cannot be a hyphen"
    | RTaken row ->
      let r = List.find (fun (r : Delimiter.t) -> r.row = row) rows in
      Printf.sprintf "%C is already the %s delimiter" c r.name
  ;;

  let with_delimiter (d : Delimiter.t) c ~width (syntax : Delimiter.syntax) (p : t) =
    let entry =
      { de_char = c
      ; de_width = width
      ; de_syntax =
          (match syntax with
           | `Off -> DOff
           | `Braced -> DBraced
           | `Bare -> DBare)
      ; de_decay = DDSelf
      }
    in
    match drow_update_refusal (table p) d.row entry with
    | None -> Ok { p with o_inline = update_drow d.row entry (table p) }
    | Some r -> Error (refusal c r)
  ;;

  let delimiter_fields (p : t) =
    let t = table p in
    let delim (d : Delimiter.t) =
      let s = d.row in
      let run = String.make (t.dc_width s) (t.dc_char s) in
      ( d.name
      , match t.dc_syntax s with
        | DOff -> "off"
        | DBraced -> run ^ " braced"
        | DBare -> run ^ " bare"
        | DBareAfterBreak -> run ^ " bare after a break" )
    in
    List.map delim rows
  ;;

  let pp_delimiters ppf p = pp_fields ppf (delimiter_fields p)

  let equal (p : t) (q : t) =
    delimiter_fields p = delimiter_fields q
    && List.for_all (fun (s : Switch.t) -> s.get p = s.get q) switches
  ;;

  let pp ppf (p : t) =
    let switch (s : Switch.t) = s.name, if s.get p then "on" else "off" in
    pp_fields ppf (delimiter_fields p @ List.map switch switches)
  ;;
end

type style =
  [ `Safe
  | `Checked
  | `Naive
  ]

(* Source in a [style], from the two forms the kernel writes. *)
module Styled = struct
  let tree (p : Profile.t) (s : string) : K.Ast.doc =
    K.Document.parse_doc (Profile.table p) (Profile.bconfig p) K.Ast.semantic_pos s
  ;;

  (* The naive parts, top-level blocks or one run of inlines, where the whole
     still parses as the safe parts do. When it does not, a part goes back to
     the safe form if it parses differently alone or after the part before it,
     and when that is not enough every part does. *)
  let checked profile ~sep (safe : string list) (naive : string list) : string =
    let join = String.concat sep in
    let same a b = tree profile a = tree profile b in
    let all_safe = join safe in
    let target = tree profile all_safe in
    let all_naive = join naive in
    if tree profile all_naive = target
    then all_naive
    else (
      let pick (prev, acc) p w =
        let ok =
          same w p
          &&
          match prev with
          | None -> true
          | Some (prev_safe, prev_chosen) ->
            same (join [ prev_chosen; w ]) (join [ prev_safe; p ])
        in
        let chosen = if ok then w else p in
        Some (p, chosen), chosen :: acc
      in
      let _, picked = List.fold_left2 pick (None, []) safe naive in
      let mixed = join (List.rev picked) in
      if tree profile mixed = target then mixed else all_safe)
  ;;

  (* [Render.sep_lines] puts one blank line between blocks. *)
  let blocks (style : style) (profile : Profile.t) (bs : K.Ast.block node list) : string =
    let table = Profile.table profile in
    let config = Profile.bconfig profile in
    let safe = K.Render.render_djot table config in
    let naive = K.Readable.readable_djot table config in
    match style with
    | `Safe -> safe bs
    | `Naive -> naive bs
    | `Checked ->
      let each f = List.map (fun b -> f [ b ]) bs in
      checked profile ~sep:"\n\n" (each safe) (each naive)
  ;;

  let inlines (style : style) (profile : Profile.t) (ils : K.Ast.inline node list)
    : string
    =
    let table = Profile.table profile in
    let safe = String.concat "\n" (K.InlineView.inline_lines table ils "") in
    let naive () = String.concat "\n" (K.Readable.readable_inline_lines table ils) in
    match style with
    | `Safe -> safe
    | `Naive -> naive ()
    | `Checked -> checked profile ~sep:"" [ safe ] [ naive () ]
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

  let to_string ?(profile = Profile.djot) ?(style = `Checked) (ils : t node list) : string =
    Styled.inlines style profile ils
  ;;

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
    | OrderedList of ordered_list_attributes * list_spacing * t node list node list
    | BulletList of char * list_spacing * t node list node list
    | TaskList of list_spacing * (task_status * t node list) node list
    | DefinitionList of
        list_spacing * (Inline.t node list node * t node list node) node list
    | ThematicBreak
    | Table of Inline.t node list node * cell node list node list
    | RawBlock of string * string
    | FootnoteDef of string * t node list
    | RefDef of string * string
    | Ext_keyed of Inline.t node list * t node
    | Ext_callout of string * callout_fold option * Inline.t node list * t node list

  let to_string ?(profile = Profile.djot) ?(style = `Checked) (bs : t node list) : string =
    Styled.blocks style profile bs
  ;;
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

module Doc = struct
  type t =
    { kernel : K.Ast.doc
    ; lines : K.Strings.source_line array option
    ; profile : Profile.t
    }

  let pass ~profile ~lines pos bs =
    { kernel = K.Document.doc_pass pos bs; lines; profile }
  ;;

  let make ?(profile = Profile.djot) (bs : Block.t node list) : t =
    pass ~profile ~lines:None K.Ast.semantic_pos (K.Document.unsection bs)
  ;;

  (* The fold step the pieces are cut with, and its finish. *)
  let fold_step ~locs (p : Profile.t) =
    let table = Profile.table p
    and bconfig = Profile.bconfig p in
    if locs
    then K.Reparse.loc_step table bconfig, K.Step.finish table bconfig K.Ast.located_pos
    else K.Reparse.sem_step table bconfig, K.Step.finish table bconfig K.Ast.semantic_pos
  ;;

  let of_pieces ~profile ~locs src ps =
    if locs
    then
      pass
        ~profile
        ~lines:(Some (Array.of_list (K.Strings.line_table src)))
        K.Ast.located_pos
        (K.Reparse.assemble 0 ps)
    else pass ~profile ~lines:None K.Ast.semantic_pos (K.Reparse.pieces_tree ps)
  ;;

  let pieces_of_string ~profile ~locs (s : string) : K.Reparse.piece list =
    let stp, fin = fold_step ~locs profile in
    K.Reparse.pieces stp fin (K.Strings.split_lines s)
  ;;

  let of_string ?(profile = Profile.djot) ?(locs = false) (s : string) : t =
    of_pieces ~profile ~locs s (pieces_of_string ~profile ~locs s)
  ;;

  let to_string ?(style = `Checked) (d : t) : string =
    Styled.blocks style d.profile (K.Render.doc_source_blocks d.kernel)
  ;;

  let blocks (d : t) : Block.t node list = d.kernel.doc_blocks
  let footnotes (d : t) : (string * Block.t node list) list = d.kernel.doc_footnotes

  let footnote (d : t) (l : string) : Block.t node list option =
    K.Ast.alist_lookup (K.Ast.normalize_label l) (footnotes d)
  ;;

  let references (d : t) : (string * (string * Attr.t)) list = d.kernel.doc_references

  let auto_references (d : t) : (string * (string * Attr.t)) list =
    d.kernel.doc_auto_references
  ;;

  let auto_identifiers (d : t) : string list = d.kernel.doc_auto_identifiers

  let reference (d : t) (l : string) : (string * Attr.t) option =
    K.Ast.lookup_reference l (references d @ auto_references d)
  ;;

  let textloc (d : t) (node : 'a node) : Textloc.t =
    match node with
    | Node (p, _, _) ->
      (match d.lines, p with
       | Some lines, K.Ast.SomePos p -> Textloc.of_span lines p.node_span
       | _ -> Textloc.none)
  ;;

  type syntax = K.Ast.syntax_role =
    | RAttrSpec
    | ROpenFence
    | RCloseFence

  let provenance d (Node (p, _, _)) =
    match d.lines, p with
    | Some lines, K.Ast.SomePos p -> Some (lines, p)
    | _ -> None
  ;;

  let syntax_locs (d : t) (n : 'a node) : (syntax * Textloc.t) list =
    match provenance d n with
    | Some (lines, p) ->
      (* Recorded as the parser settles them: a block's attribute spec
           comes after its fences. *)
      List.map (fun (r, s) -> r, Textloc.of_span lines s) p.syntax_spans
      |> List.stable_sort (fun (_, a) (_, b) ->
        compare a.Textloc.first_byte b.Textloc.first_byte)
    | None -> []
  ;;
end

module Source = struct
  type t =
    { text : string
    ; pieces : K.Reparse.piece list (* The parse of [text], for the edits. *)
    ; doc : Doc.t
    }

  let of_pieces ~profile ~locs text pieces =
    { text; pieces; doc = Doc.of_pieces ~profile ~locs text pieces }
  ;;

  let of_string ?(profile = Profile.djot) ?(locs = false) (s : string) : t =
    of_pieces ~profile ~locs s (Doc.pieces_of_string ~profile ~locs s)
  ;;

  let to_string (t : t) : string = t.text
  let doc (t : t) : Doc.t = t.doc

  (* The byte where zero-based line [k] starts, or the length when [k] is
     the number of lines. *)
  let line_start (src : string) (k : int) : int =
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
  let edit_source (src : string) (f : int) (l : int) (s : string) : string =
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

  type change =
    { first : int
    ; old_last : int
    ; new_last : int
    }

  (* The splice keeps the pieces it does not parse as the values they
     were, so the pieces two lists share at each end are the kept ones.
     The pieces shared at the start are counted up to the first [f] lines
     only, which places an edit that changes no piece at the edit. *)
  let change_of f old_ps new_ps =
    let lines n p = n + List.length p.K.Reparse.piece_lines in
    let rec shared limit n a b =
      match a, b with
      | x :: a, y :: b when x == y && lines n x <= limit -> shared limit (lines n x) a b
      | _ -> n, a, b
    in
    let pre, a, b = shared f 0 old_ps new_ps in
    let _, a, b = shared max_int 0 (List.rev a) (List.rev b) in
    { first = pre + 1
    ; old_last = List.fold_left lines pre a
    ; new_last = List.fold_left lines pre b
    }
  ;;

  (* The edit widens to the pieces holding lines [first] to [last]; the
     lines of those pieces outside the range go back in around [s]. *)
  let replace_lines_changed (t : t) ~first ~last (s : string) : t * change =
    let src = t.text
    and ps = t.pieces in
    let n = List.length ps in
    let pa = Array.of_list ps in
    let starts = Array.make (n + 1) 0 in
    Array.iteri
      (fun k p -> starts.(k + 1) <- starts.(k) + List.length p.K.Reparse.piece_lines)
      pa;
    let f = first - 1
    and l = last - 1 in
    if f < 0 || l < f - 1 || l >= starts.(n)
    then invalid_arg "Source.replace_lines: range outside the source";
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
    let profile = t.doc.profile
    and locs = Option.is_some t.doc.lines in
    let stp, fin = Doc.fold_step ~locs profile in
    let ps' =
      K.Reparse.splice stp fin ps i j (before @ K.Strings.split_lines s @ behind)
    in
    of_pieces ~profile ~locs (edit_source src f l s) ps', change_of f ps ps'
  ;;

  let replace_lines t ~first ~last s = fst (replace_lines_changed t ~first ~last s)

  (* The edit widens to whole lines: from the start of the line holding
     byte [first] to the end of the line holding the byte after [last],
     which the edit joins to what comes before it. *)
  let replace_bytes_changed (t : t) ~first ~last (s : string) : t * change =
    let src = t.text in
    let n = String.length src in
    let a = first
    and b = last + 1 in
    if a < 0 || b < a || b > n
    then invalid_arg "Source.replace_bytes: range outside the source";
    let la =
      match if a = 0 then None else String.rindex_from_opt src (a - 1) '\n' with
      | Some k -> k + 1
      | None -> 0
    in
    let lb =
      match if b = n then None else String.index_from_opt src b '\n' with
      | Some k -> k + 1
      | None -> n
    in
    let newlines i j =
      let c = ref 0 in
      for k = i to j - 1 do
        if src.[k] = '\n' then incr c
      done;
      !c
    in
    let first_line = newlines 0 la + 1 in
    let count = newlines la lb + if lb > la && src.[lb - 1] <> '\n' then 1 else 0 in
    replace_lines_changed
      t
      ~first:first_line
      ~last:(first_line + count - 1)
      (String.sub src la (a - la) ^ s ^ String.sub src b (lb - b))
  ;;

  let replace_bytes t ~first ~last s = fst (replace_bytes_changed t ~first ~last s)
end

module Stream = struct
  type t =
    { profile : Profile.t
    ; locs : bool
    ; chunks : string list (* The input so far, last chunk first. *)
    ; partial : string list (* The unfinished line's parts, last first. *)
    ; pieces : K.Reparse.piece list (* The finished pieces, last first. *)
    ; offset : int (* The lines in [pieces]. *)
    ; pending : K.Reparse.pending
    ; ids : K.Document.id_state (* After the blocks returned. *)
    }

  let start ?(profile = Profile.djot) ?(locs = false) () =
    { profile
    ; locs
    ; chunks = []
    ; partial = []
    ; pieces = []
    ; offset = 0
    ; pending = K.Reparse.fresh
    ; ids = K.Document.id_state_init
    }
  ;;

  let rec drop n l =
    match l with
    | _ :: rest when n > 0 -> drop (n - 1) rest
    | _ -> l
  ;;

  (* The blocks of the piece being read that [feed] has not returned yet,
     placed where the piece starts. *)
  let unreturned t bs =
    let bs = drop (List.length t.pending.K.Reparse.pend_blocks) bs in
    K.Document.Ids.of_list
      (if t.locs then K.Ast.Shift.of_blocks t.offset bs else bs)
      t.ids
  ;;

  (* One whole line. A line that leaves the fold idle ends the piece. *)
  let line t l =
    let stp, _ = Doc.fold_step ~locs:t.locs t.profile in
    match K.Reparse.cut stp [ l ] t.pending with
    | [], p ->
      let ids, bs = unreturned t p.K.Reparse.pend_blocks in
      bs, { t with pending = p; ids }
    | c :: _, p ->
      let ids, bs = unreturned t c.K.Reparse.piece_blocks in
      ( bs
      , { t with
          pieces = c :: t.pieces
        ; offset = t.offset + List.length c.K.Reparse.piece_lines
        ; pending = p
        ; ids
        } )
  ;;

  let feed_string t s =
    let t = { t with chunks = s :: t.chunks } in
    let rec go acc t = function
      | [] -> acc, t
      | [ last ] -> acc, if last = "" then t else { t with partial = last :: t.partial }
      | part :: rest ->
        let bs, t = line t (String.concat "" (List.rev (part :: t.partial))) in
        go (List.rev_append bs acc) { t with partial = [] } rest
    in
    let acc, t = go [] t (String.split_on_char '\n' s) in
    List.rev acc, t
  ;;

  let feed_line t l = feed_string t (l ^ "\n")

  (* The pieces as if input ended here: the unfinished line, if it has
     bytes, is the last line. *)
  let ended t =
    let stp, fin = Doc.fold_step ~locs:t.locs t.profile in
    let cs, p =
      match t.partial with
      | [] -> [], t.pending
      | parts -> K.Reparse.cut stp [ String.concat "" (List.rev parts) ] t.pending
    in
    cs @ K.Reparse.close fin p
  ;;

  let peek t = snd (unreturned t (K.Reparse.pieces_tree (ended t)))

  let finish t =
    Source.of_pieces
      ~profile:t.profile
      ~locs:t.locs
      (String.concat "" (List.rev t.chunks))
      (List.rev_append t.pieces (ended t))
  ;;

  module Sections = struct
    type event =
      | Enter of Attr.t
      | Item of Block.t node
      | Leave

    (* The levels of the open sections, innermost first. *)
    type t = int list

    let start = []

    let step t (Node (p, a, b) as n) =
      match (b : Block.t) with
      | Heading (lvl, _) ->
        let rec leave acc = function
          | l :: rest when lvl <= l -> leave (Leave :: acc) rest
          | t -> acc, t
        in
        let left, t = leave [] t in
        left @ [ Enter a; Item (Node (p, [], b)) ], lvl :: t
      | _ -> [ Item n ], t
    ;;

    let finish t = List.map (fun _ -> Leave) t
  end
end

module For_testing = struct
  let kernel (d : Doc.t) = d.kernel
  let parsed (s : Source.t) = K.Reparse.pieces_tree s.pieces
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
    (* Items, rows, cells and captions keep their position and attributes. *)
    let on f (Node (p, a, x)) = Node (p, a, f x) in
    let cell = on (fun (Block.Cell (t, al, l)) -> Block.Cell (t, al, il l)) in
    let x : Block.t option =
      match x with
      | Para l -> Some (Para (il l))
      | Section l -> Some (Section (bl l))
      | Heading (lvl, l) -> Some (Heading (lvl, il l))
      | BlockQuote l -> Some (BlockQuote (bl l))
      | Div (n, l) -> Some (Div (n, bl l))
      | OrderedList (o, sp, its) -> Some (OrderedList (o, sp, List.map (on bl) its))
      | BulletList (c, sp, its) -> Some (BulletList (c, sp, List.map (on bl) its))
      | TaskList (sp, its) ->
        Some (TaskList (sp, List.map (on (fun (s, it) -> s, bl it)) its))
      | DefinitionList (sp, its) ->
        Some (DefinitionList (sp, List.map (on (fun (t, d) -> on il t, on bl d)) its))
      | Table (cap, rows) -> Some (Table (on il cap, List.map (on (List.map cell)) rows))
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
    let pos = if Option.is_some d.lines then K.Ast.located_pos else K.Ast.semantic_pos in
    let bs = map_blocks m (K.Render.doc_source_blocks d.kernel) in
    { d with kernel = K.Document.doc_pass pos (K.Document.unsection bs) }
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
       | OrderedList (_, _, its) | BulletList (_, _, its) ->
         List.fold_left (fun acc it -> bl acc (Node.content it)) acc its
       | TaskList (_, its) ->
         List.fold_left (fun acc it -> bl acc (snd (Node.content it))) acc its
       | DefinitionList (_, its) ->
         List.fold_left
           (fun acc it ->
             let t, d = Node.content it in
             bl (il acc (Node.content t)) (Node.content d))
           acc
           its
       | Table (cap, rows) ->
         let cell acc c =
           match Node.content c with
           | Block.Cell (_, _, l) -> il acc l
         in
         let acc =
           List.fold_left (fun acc r -> List.fold_left cell acc (Node.content r)) acc rows
         in
         il acc (Node.content cap)
       | Ext_keyed (l, b) -> fold_block f (il acc l) b
       | Ext_callout (_, _, title, body) -> bl (il acc title) body
       | CodeBlock _ | ThematicBreak | RawBlock _ | RefDef _ -> acc)
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

  let of_blocks (bs : Block.t node list) =
    K.Html.render_html (K.Document.doc_pass K.Ast.semantic_pos bs)
  ;;
end
