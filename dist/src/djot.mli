(*---------------------------------------------------------------------------
   Copyright (c) 2021 The cmarkit programmers. All rights reserved.
   Copyright (c) 2026 hon-gyu. All rights reserved.
   SPDX-License-Identifier: MIT AND ISC
  ---------------------------------------------------------------------------*)

(* The module types are modeled on cmarkit's; see LICENSE-cmarkit. The
   implementation is not derived from cmarkit: it calls the Rocq-extracted
   kernel. *)

(** Djot documents: parse, traverse, render.

    The tree types are the extracted ones from {!Kernel}, re-exported with
    their constructors, so a value from the kernel and a value from this
    module are the same value.  Every syntax extension is a constructor
    defined in the Rocq development; there are no extension points here. *)

module Kernel = Djot_kernel

(** {1 Attributes} *)

module Attr : sig
  type t = (string * string) list
  (** In source order.  All classes live in one ["class"] entry,
      space-separated. *)

  val empty : t
  val find : string -> t -> string option
  val id : t -> string option
  val classes : t -> string list

  val key_values : t -> (string * string) list
  (** The entries other than ["id"] and ["class"]. *)
end

(** {1 Nodes} *)

type 'a node = 'a Kernel.Ast.node = Node of Kernel.Ast.pos * Attr.t * 'a
(** A tree element: its source position (see {!Doc.textloc}), its
    attributes, and its contents. *)

module Node : sig
  val make : ?attrs:Attr.t -> 'a -> 'a node
  (** A node with no source position. *)

  val attrs : 'a node -> Attr.t
  val contents : 'a node -> 'a
end

(** {1 Inlines} *)

module Inline : sig
  type math_style = Kernel.Ast.math_style = DisplayMath | InlineMath
  type target = Kernel.Ast.target = Direct of string | Reference of string
  type quote_type = Kernel.Ast.quote_type = SingleQuotes | DoubleQuotes

  type t = Kernel.Ast.inline =
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
    | Span of t node list
    | FootnoteReference of string
    | UrlLink of string
    | EmailLink of string
    | Ext_wikilink of bool * string * string option
        (** An extension: [Ext_wikilink (embed, target, alias)], both strings
            as written. *)
    | RawInline of string * string
    | NonBreakingSpace
    | Quoted of quote_type * t node list
    | SoftBreak
    | HardBreak

  val to_plain_text : t node list -> string
  (** The text a heading identifier is derived from. *)
end

(** {1 Blocks} *)

module Block : sig
  type list_spacing = Kernel.Ast.list_spacing = Tight | Loose

  type ordered_list_style = Kernel.Ast.ordered_list_style =
    | Decimal
    | LetterUpper
    | LetterLower
    | RomanUpper
    | RomanLower

  type ordered_list_delim = Kernel.Ast.ordered_list_delim =
    | RightPeriod
    | RightParen
    | LeftRightParen

  type ordered_list_attributes = Kernel.Ast.ordered_list_attributes = {
    ol_style : ordered_list_style;
    ol_delim : ordered_list_delim;
    ol_start : int;
  }

  type task_status = Kernel.Ast.task_status = Complete | Incomplete

  type align = Kernel.Ast.align =
    | AlignLeft
    | AlignRight
    | AlignCenter
    | AlignDefault

  type cell_type = Kernel.Ast.cell_type = HeadCell | BodyCell

  type cell = Kernel.Ast.cell =
    | Cell of cell_type * align * Inline.t node list

  type callout_fold = Kernel.Ast.callout_fold = FoldExpanded | FoldCollapsed

  type t = Kernel.Ast.block =
    | Para of Inline.t node list
    | Section of t node list
        (** a heading (the first child) and the blocks up to the next heading of
            the same or a higher level. The heading's id is on the
            section node. *)
    | Heading of int * Inline.t node list
    | BlockQuote of t node list
    | CodeBlock of string * string
    | Div of t node list
    | OrderedList of ordered_list_attributes * list_spacing * t node list list
    | BulletList of list_spacing * t node list list
    | TaskList of list_spacing * (task_status * t node list) list
    | DefinitionList of list_spacing * (Inline.t node list * t node list) list
    | ThematicBreak
    | Table of Inline.t node list * cell list list
        (** Caption, then rows.  An empty caption is no caption. *)
    | RawBlock of string * string
    | FootnoteDef of string * t node list
        (** Moved into {!Doc.footnotes} by the document pass. *)
    | RefDef of string * string
    | Ext_keyed of Inline.t node list * t node
        (** An extension: [label: content]. *)
    | Ext_callout of string * callout_fold option * Inline.t node list * t node list
        (** Kind, fold marker, inline title, and body. *)
end

(** {1 Source locations} *)

module Textloc : sig
  type byte_pos = int
  (** Zero-based. *)

  type line_pos = int * byte_pos
  (** A one-based line number and the byte position of the line's first
      byte. *)

  type t

  val none : t
  val is_none : t -> bool

  val is_empty : t -> bool
  (** [last_byte] is [first_byte - 1]. *)

  val first_byte : t -> byte_pos

  val last_byte : t -> byte_pos
  (** Inclusive. *)

  val first_line : t -> line_pos
  val last_line : t -> line_pos

  val v :
    first_byte:byte_pos ->
    last_byte:byte_pos ->
    first_line:line_pos ->
    last_line:line_pos ->
    t

  val reloc : first:t -> last:t -> t
  (** From the start of [first] to the end of [last]. *)

  val pp : Format.formatter -> t -> unit
end

(** {1 Profiles} *)

module Profile : sig
  type t
  (** The syntax a parse accepts.  Start from a named profile and switch
      constructs on or off. *)

  val djot : t
  (** djot as specified.  The extensions are off. *)

  val markdown_like : t
  (** djot with Markdown spellings added: strong as [**], dollar math,
      setext headings, sublists without a blank line, one-line ATX
      headings.  Not CommonMark. *)

  (** {2 djot constructs}  All on in {!djot}. *)

  val with_footnotes : bool -> t -> t
  (** References [[^a]] and definitions [[^a]: ...] together. *)

  val with_smart_typography : bool -> t -> t
  (** Dashes and ellipses. *)

  val with_raw_inline : bool -> t -> t
  (** [`x`{=html}]. *)

  val with_math : bool -> t -> t
  (** [$`x`] and [$$`x`]. *)

  val with_inline_attrs : bool -> t -> t
  (** [{...}] after an inline, and spans [[text]{...}]. *)

  val with_tables : bool -> t -> t
  val with_divs : bool -> t -> t
  val with_tasks : bool -> t -> t

  val with_raw_blocks : bool -> t -> t
  (** Code blocks with an [=format] info string. *)

  val with_deflists : bool -> t -> t

  val with_block_attrs : bool -> t -> t
  (** An attribute line [{...}] before a block. *)

  val with_heading_continuation : bool -> t -> t
  (** A heading's text continues onto the following lines; off in
      {!markdown_like}. *)

  (** {2 Extensions}  All off in {!djot}. *)

  val with_ext_wikilinks : bool -> t -> t
  (** [[[target|alias]]] and [![[target]]] ({!Inline.Ext_wikilink}). *)

  val with_ext_dollar_math : bool -> t -> t
  (** [$x$], [$$x$$] and [$`x`$], read as {!Inline.Math}; on in
      {!markdown_like}.  Independent of {!with_math}. *)

  val with_ext_keyed : bool -> t -> t
  (** [label: content] ({!Block.Ext_keyed}). *)

  val with_ext_callouts : bool -> t -> t
  (** Callouts with a header on the first line of a block quote. Off by default. *)
end

(** {1 Documents} *)

module Doc : sig
  type t

  val of_string : ?profile:Profile.t -> ?locs:bool -> string -> t
  (** Parse, then run the document pass: headings get identifiers and
      open sections, footnote and reference definitions move into side
      tables.  [locs] (default [false]) records source positions. *)

  val of_blocks : ?profile:Profile.t -> Block.t node list -> t
  (** Run the document pass over parsed blocks.  The result has no
      source, so {!textloc} is {!Textloc.none} throughout.  [profile]
      (default {!Profile.djot}) is the syntax {!Source.of_doc} writes. *)

  val replace_lines : t -> first:int -> last:int -> string -> t
  (** [replace_lines d ~first ~last s] is {!of_string}, with [d]'s
      profile and [locs], of [d]'s source with lines [first] to [last]
      (one-based, inclusive) replaced by [s].  [last = first - 1] inserts
      before line [first].  A newline is added after [s] when it does
      not end with one and lines follow it.

      The parse is kept in pieces cut where the block parser is idle,
      each parsed with its lines numbered from its first.  Only the
      pieces from the edit to the next such point are parsed again; the
      ones after it keep their blocks and are shifted to their new
      first line (Reparse.v, [splice_pieces], [replace_reuses]).  The
      document pass runs over the whole result.

      Raises [Invalid_argument] if [d] was made by {!of_blocks}, or the
      range is not within [d]'s lines. *)

  val blocks : t -> Block.t node list

  val footnotes : t -> (string * Block.t node list) list
  (** One entry per normalized label, holding the blocks of the last
      definition with that label, as djot.js resolves references. *)

  val footnote_defs : t -> Block.t node list
  (** Every {!Block.FootnoteDef} of the parse in source order, repeated
      labels included, with its label as written and its blocks.  Taken
      from the parse, so {!Mapper.map_doc} leaves them as they were. *)

  val footnote : t -> string -> Block.t node list option

  val references : t -> (string * (string * Attr.t)) list
  (** Explicit reference definitions: label, destination, attributes. *)

  val reference : t -> string -> (string * Attr.t) option
  (** A label's destination, from an explicit definition or else from a
      heading. *)

  val textloc : t -> 'a node -> Textloc.t
  (** {!Textloc.none} unless the document was parsed with [~locs:true] and
      the node came from that parse. *)

  val footnote_label_loc : t -> Block.t node -> Textloc.t
  (** The label of a {!Block.FootnoteDef}, between [[^] and [\]].
      {!Textloc.none} for any other node and under the same conditions
      as {!textloc}. *)

  type syntax = Kernel.Ast.syntax_role =
    | RAttrSpec  (** An attribute spec [{...}]. *)
    | ROpenFence  (** A code block's or div's opening fence line. *)
    | RCloseFence  (** Its closing fence line, absent when unclosed. *)

  val syntax_locs : t -> 'a node -> (syntax * Textloc.t) list
  (** The node's delimiting syntax, in source order.  Empty under the
      same conditions as {!textloc}. *)

  (** The ranges of the parts of a node that are not nodes themselves,
      parallel to its children. *)
  type parts =
    | NoParts
    | Items of Textloc.t list
        (** A list's items.  A task list's include the checkbox. *)
    | DefItems of (Textloc.t * Textloc.t * Textloc.t) list
        (** A definition list's items: the item, its term, its
            definition. *)
    | TableRows of Textloc.t option * (Textloc.t * Textloc.t list) list
        (** A table's caption, then each row and its cells. *)

  val parts : t -> 'a node -> parts
  (** {!NoParts} under the same conditions as {!textloc}. *)

  val kernel : t -> Kernel.Ast.doc
end

(** {1 Traversals} *)

module Mapper : sig
  type 'a filter_map = 'a option
  type 'a result = [ `Default | `Map of 'a ]

  val default : 'a result
  (** Keep the node and map its children. *)

  val delete : 'a filter_map result
  val ret : 'a -> 'a filter_map result

  type t
  type 'a mapper = t -> 'a -> 'a filter_map result

  val make :
    ?inline:Inline.t node mapper -> ?block:Block.t node mapper -> unit -> t

  val map_inline : t -> Inline.t node -> Inline.t node filter_map

  val map_block : t -> Block.t node -> Block.t node filter_map
  (** A {!Block.Ext_keyed} whose block is deleted is deleted. *)

  val map_doc : t -> Doc.t -> Doc.t
  (** The blocks, then each footnote's blocks.  The side tables and the
      source are kept. *)
end

module Folder : sig
  type 'a result = [ `Default | `Fold of 'a ]

  val default : 'a result
  (** Fold the node's children. *)

  val ret : 'a -> 'a result

  type 'a t
  type ('a, 'b) folder = 'b t -> 'b -> 'a -> 'b result

  val make :
    ?inline:(Inline.t node, 'a) folder ->
    ?block:(Block.t node, 'a) folder ->
    unit ->
    'a t

  val fold_inline : 'a t -> 'a -> Inline.t node -> 'a
  val fold_block : 'a t -> 'a -> Block.t node -> 'a

  val fold_doc : 'a t -> 'a -> Doc.t -> 'a
  (** The blocks, then each footnote's blocks.  Children are visited in
      source order. *)
end

(** {1 HTML} *)

module Html : sig
  type t = Kernel.Html.helt =
    | HText of string  (** Escaped when serialized. *)
    | HRaw of string  (** Written as is. *)
    | HVoid of string * bool * Attr.t
        (** [HVoid (tag, self_closing, attrs)]: no closing tag. *)
    | HElem of string * int * Attr.t * t list
        (** [HElem (tag, newlines, attrs, children)].  [newlines] is 2 for
            a newline after both tags, 1 after the closing tag only, 0 for
            neither. *)

  val tree : Doc.t -> t list
  (** The output before serialization, for post-processing. *)

  val to_string : t list -> string
  val of_doc : Doc.t -> string
end

(** {1 Djot source} *)

module Source : sig
  val of_doc : Doc.t -> string
  (** The document as djot source, in the syntax of the profile it was
      parsed with.  A heading id the parser would derive again is left
      out.  Parsing the result with that profile gives the same tree, up
      to source positions, except that:
      - footnote definitions come after the blocks;
      - whitespace runs in attribute values collapse to one space;
      - a span with no attributes, an empty block quote, an empty table
        and an empty definition item read back as something else;
      - two adjacent bullet lists read back as one, since the tree does
        not keep the marker;
      - a [|] in a table cell's text splits the cell.
      Roundtrip.v proves the round trip for a fragment of documents;
      beyond it this is tested, not proved. *)
end
