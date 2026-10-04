(*---------------------------------------------------------------------------
   Copyright (c) 2021 The cmarkit programmers. All rights reserved.
   Copyright (c) 2026 hon-gyu. All rights reserved.
   SPDX-License-Identifier: MIT AND ISC
  ---------------------------------------------------------------------------*)

(* The module types are modeled on cmarkit's; see LICENSE-cmarkit. The
   implementation is not derived from cmarkit: it calls the Rocq-extracted
   kernel. *)

(** Djot documents: parse, traverse, render.

    The tree types are the extracted ones from {!Kernel}, re-exported with their
    constructors, so a value from the kernel and a value from this module are the same
    value. Every syntax extension is a constructor defined in the Rocq development; there
    are no extension points here. *)

module Kernel = Djot_kernel

(** {1 Attributes} *)

module Attr : sig
  (** Key/value pairs in source order. ["id"] holds the identifier; ["class"] holds every
      class, space-separated. *)
  type t = (string * string) list

  val empty : t
  val find : string -> t -> string option
  val id : t -> string option
  val classes : t -> string list

  (** The entries other than ["id"] and ["class"]. *)
  val kvs : t -> (string * string) list

  (** Whether a string can be a key: one or more of [a-z], [A-Z], [0-9], [-], [_], [:]. *)
  val is_key : string -> bool

  (** Whether a string can be one class name: one or more of [a-z], [A-Z], [0-9], [-],
      [_], [:]. *)
  val is_class : string -> bool

  (** Whether every key satisfies {!is_key} and none repeats.

      Lenient about invalid class names, [is_class] is not guaranteed

      Holds for parsed attributes and the results of {!set} and {!add_class}. *)
  val is_valid : t -> bool

  (** {!is_valid} and every class satisfies {!is_class}. *)
  val is_valid_strict : t -> bool

  (** [None] if [k] is not a valid key.

      Position: the value is replaced in place if [k] is already present, otherwise added
      at the end. *)
  val set : string -> string -> t -> t option

  val set_id : string -> t -> t

  (** [None] if not a valid class. *)
  val add_class : string -> t -> t option

  val remove : string -> t -> t

  (** [None] if not a valid class. *)
  val set_classes : string list -> t -> t option

  val set_exn : string -> string -> t -> t
  val add_class_exn : string -> t -> t
  val set_classes_exn : string list -> t -> t

  (** The attributes in djot syntax, [{#id .class key="value"}]; [""] for {!empty}. *)
  val to_string : t -> string

  (** Parses djot attribute syntax, [{...}], [None] if not a valid attribute syntax. *)
  val of_string : string -> t option
end

(** {1 Profiles} *)

module Profile : sig
  (** The syntax a parse accepts. Start from a named profile and switch constructs on or
      off. *)
  type t

  (** djot as specified. The extensions are off. *)
  val djot : t

  (** djot with Markdown spellings added: strong as [**], dollar math, setext headings,
      sublists without a blank line, one-line ATX headings. Not CommonMark. *)
  val markdown_like : t

  (** {2 djot constructs}
      All on in {!djot}. *)

  (** References [[^a]] and definitions [[^a]: ...] together. *)
  val with_footnotes : bool -> t -> t

  (** Dashes and ellipses. *)
  val with_smart_typography : bool -> t -> t

  (** [`x`{=html}]. *)
  val with_raw_inline : bool -> t -> t

  (** [$`x`] and [$$`x`]. *)
  val with_math : bool -> t -> t

  (** [{...}] after an inline, and spans [[text]{...}]. *)
  val with_inline_attrs : bool -> t -> t

  val with_tables : bool -> t -> t
  val with_divs : bool -> t -> t
  val with_tasks : bool -> t -> t

  (** Code blocks with an [=format] info string. *)
  val with_raw_blocks : bool -> t -> t

  val with_deflists : bool -> t -> t

  (** An attribute line [{...}] before a block. *)
  val with_block_attrs : bool -> t -> t

  (** A heading's text continues onto the following lines; off in {!markdown_like}. *)
  val with_heading_continuation : bool -> t -> t

  (** {2 Extensions}
      All off in {!djot}. *)

  (** [[[target|alias]]] and [![[target]]] ({!Inline.Ext_wikilink}). *)
  val with_ext_wikilinks : bool -> t -> t

  (** [$x$], [$$x$$] and [$`x`$], read as {!Inline.Math}; on in {!markdown_like}.
      Independent of {!with_math}. *)
  val with_ext_dollar_math : bool -> t -> t

  (** [label: content] ({!Block.Ext_keyed}). *)
  val with_ext_keyed : bool -> t -> t

  (** Callouts with a header on the first line of a block quote. Off by default. *)
  val with_ext_callouts : bool -> t -> t

  (** Custom tag names: [::: name] names a {!Block.Div} and [:name[...]] a {!Inline.Span}.
      Both spellings move together. *)
  val with_ext_tags : bool -> t -> t

  (** A setext heading: a paragraph underlined with [=] (level 1) or two or more [-]
      (level 2). On in {!markdown_like}. *)
  val with_ext_setext_headings : bool -> t -> t

  (** A bullet, or an ordered marker numbered [1], starts a list on the line after
      paragraph text, with no blank line between. On in {!markdown_like}. *)
  val with_ext_list_interrupts : bool -> t -> t

  (** One [name: value] line per inline delimiter, giving its characters and how it is
      written, e.g. [strong: ** bare] or [highlight: = braced]. *)
  val pp_delimiters : Format.formatter -> t -> unit

  (** The lines of {!pp_delimiters}, then one [name: value] line per switch above, named
      as the switch without [with_]. *)
  val pp : Format.formatter -> t -> unit
end

(** {1 Nodes} *)

type 'a node = 'a Kernel.Ast.node =
  | Node of Kernel.Ast.pos * Attr.t * 'a
  (** A tree element: source position (see {!Doc.textloc}), attributes, and contents. *)

module Node : sig
  (** A node with no source position. *)
  val make : ?attrs:Attr.t -> 'a -> 'a node

  val attrs : 'a node -> Attr.t
  val content : 'a node -> 'a
end

(** {1 Writing source} *)

(** How a tree is written as djot source by [to_string].
    - [`Safe]: text is escaped and delimiters are braced by fixed rules, so that the
      result parses back to the tree. Fast, and not what a person would type: [3\:1],
      [{_a_}].
    - [`Naive]: the text a person would type, for a tree built by hand. Nothing is
      escaped, emphasis and quotes are written without braces where they read back as
      such, table columns are padded, and a blank line inside a container is empty. Text
      is written as it is, so a paragraph holding [- x] reads back as a list and [a*b*c]
      as strong emphasis.
    - [`Checked]: [`Naive] wherever that parses to the same tree as [`Safe] does, and
      [`Safe] for the top-level blocks where it does not. The result always parses as the
      [`Safe] one. Costs two parses of the result, more when blocks differ. *)
type style =
  [ `Safe
  | `Checked
  | `Naive
  ]

(** {1 Inlines} *)

module Inline : sig
  type math_style = Kernel.Ast.math_style =
    | DisplayMath
    | InlineMath

  type target = Kernel.Ast.target =
    | Direct of string
    | Reference of string

  type quote_type = Kernel.Ast.quote_type =
    | SingleQuotes
    | DoubleQuotes

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
    | Span of string * t node list
    (** The string is a name, written [:name[...]], an extension
        ({!Profile.with_ext_tags}); empty means unnamed. *)
    | FootnoteReference of string
    | UrlLink of string
    | EmailLink of string
    | RawInline of string * string
    | NonBreakingSpace
    | Quoted of quote_type * t node list
    | SoftBreak
    | HardBreak
    | Ext_wikilink of bool * string * string option
    (** An extension: [Ext_wikilink (embed, target, alias)], both strings as written. *)

  (** The text a heading identifier is derived from. *)
  val to_plain_text : t node list -> string

  (** The inlines as djot source, as they are written inside a paragraph, a soft or hard
      break ending a line.
      @param profile the syntax to write; default {!Profile.djot}
      @param style default [`Checked], which reads the inlines as one paragraph *)
  val to_string : ?profile:Profile.t -> ?style:style -> t node list -> string
end

(** {1 Blocks} *)

module Block : sig
  type list_spacing = Kernel.Ast.list_spacing =
    | Tight
    | Loose

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

  type ordered_list_attributes = Kernel.Ast.ordered_list_attributes =
    { ol_style : ordered_list_style
    ; ol_delim : ordered_list_delim
    ; ol_start : int
    }

  type task_status = Kernel.Ast.task_status =
    | Complete
    | Incomplete

  type align = Kernel.Ast.align =
    | AlignLeft
    | AlignRight
    | AlignCenter
    | AlignDefault

  type cell_type = Kernel.Ast.cell_type =
    | HeadCell
    | BodyCell

  type cell = Kernel.Ast.cell = Cell of cell_type * align * Inline.t node list

  type callout_fold = Kernel.Ast.callout_fold =
    | FoldExpanded
    | FoldCollapsed

  type t = Kernel.Ast.block =
    | Para of Inline.t node list
    | Section of t node list
    (** a heading (the first child) and the blocks up to the next heading of the same or a
        higher level. The heading's id is on the section node. *)
    | Heading of int * Inline.t node list
    | BlockQuote of t node list
    | CodeBlock of string * string
    | Div of string * t node list
    (** The string is a name, written [::: name] where djot reads a class, an extension
        ({!Profile.with_ext_tags}); empty means unnamed. *)
    | OrderedList of ordered_list_attributes * list_spacing * t node list node list
    (** Each item is a node, with its own location. *)
    | BulletList of char * list_spacing * t node list node list
    (** The character is the marker the items are written with: [-], [+] or [*], or [:]
        where definition lists are off. *)
    | TaskList of list_spacing * (task_status * t node list) node list
    | DefinitionList of
        list_spacing * (Inline.t node list node * t node list node) node list
    (** Each item holds its term and its definition. *)
    | ThematicBreak
    | Table of Inline.t node list node * cell node list node list
    (** Caption, then rows of cells. A caption with no inlines is no caption. *)
    | RawBlock of string * string
    | FootnoteDef of string * t node list
    (** A definition stays where it was written; {!Doc.footnotes} is collected from
        these. *)
    | RefDef of string * string
    | Ext_keyed of Inline.t node list * t node (** An extension: [label: content]. *)
    | Ext_callout of string * callout_fold option * Inline.t node list * t node list
    (** Kind, fold marker, inline title, and body. *)

  (** The blocks as djot source, for the source of one node or of a mapped tree. Unlike
      {!Doc.to_string}, a heading's identifier is always written as an attribute.
      @param profile the syntax to write; default {!Profile.djot}
      @param style default [`Checked] *)
  val to_string : ?profile:Profile.t -> ?style:style -> t node list -> string
end

(** {1 Source locations} *)

module Textloc : sig
  (** Zero-based. *)
  type byte_pos = int

  (** A one-based line number and the byte position of the line's first byte. *)
  type line_pos = int * byte_pos

  type t

  val first_byte : t -> byte_pos

  (** Inclusive. *)
  val last_byte : t -> byte_pos

  val first_line : t -> line_pos
  val last_line : t -> line_pos
  val none : t
  val is_none : t -> bool

  (** [last_byte] is [first_byte - 1]. *)
  val is_empty : t -> bool

  val make
    :  first_byte:byte_pos
    -> last_byte:byte_pos
    -> first_line:line_pos
    -> last_line:line_pos
    -> t

  (** The range from [first]'s first byte to [last]'s last byte *)
  val reloc : first:t -> last:t -> t

  val pp : Format.formatter -> t -> unit
end

(** {1 Documents} *)

(** A parsed document: its blocks, and the footnotes and references they define.

    A document does not keep the text it was parsed from. To edit a document's text and
    parse only what the edit affects, use {!Source}. *)
module Doc : sig
  type t

  (** Parses a djot text.

      Each heading gets an identifier and is wrapped, with the blocks under it, in a
      {!Block.Section}. Footnote and reference definitions stay in the blocks, and are
      also collected by label in {!footnotes} and {!references}.

      @param profile the syntax to accept; default {!Profile.djot}
      @param locs whether to record source positions, see {!textloc}; default [false] *)
  val of_string : ?profile:Profile.t -> ?locs:bool -> string -> t

  (** The document as djot source, in the syntax of the profile it was parsed with. An
      identifier in {!auto_identifiers} is not written.

      With [`Safe] or [`Checked], parsing the result with that profile gives the same
      tree, up to source positions, except that:
      - whitespace runs in attribute values collapse to one space;
      - a span with no attributes, an empty block quote, an empty table and an empty
        definition item read back as something else;
      - two adjacent bullet lists with the same marker read back as one;
      - a [|] in a table cell's text splits the cell.

      The round trip is proved in Rocq for a fragment of documents written with [`Safe];
      beyond it this is tested, not proved.

      With [`Naive] the result need not parse back to the same tree; see {!style}.

      @param style default [`Checked] *)
  val to_string : ?style:style -> t -> string

  val blocks : t -> Block.t node list

  (** The footnotes: one entry per label, with the blocks of its definition as they are
      in {!blocks}. A definition written inside another is in that one's blocks and has
      an entry of its own.

      Two labels are the same when they are equal once each run of whitespace is replaced
      by one space, so [[^a  b]] and [[^a b]] are one footnote and [[^a]] and [[^A]] are
      two. When a label is defined more than once, the entry holds the last definition;
      every definition is in {!blocks}. *)
  val footnotes : t -> (string * Block.t node list) list

  (** The blocks of the footnote with this label, compared as in {!footnotes}. *)
  val footnote : t -> string -> Block.t node list option

  (** Explicit reference definitions: label, destination, attributes. *)
  val references : t -> (string * (string * Attr.t)) list

  (** One reference per heading: the heading's text as label, and its identifier after a
      [#] as destination. *)
  val auto_references : t -> (string * (string * Attr.t)) list

  (** The identifiers derived from a heading's text, in document order; an identifier a
      heading was written with is not listed. Going through the headings and sections in
      document order, the first one with the next listed identifier is the one it was
      derived for. *)
  val auto_identifiers : t -> string list

  (** A label's destination, from an explicit definition or else from a heading. *)
  val reference : t -> string -> (string * Attr.t) option

  (** {!Textloc.none} unless the document was parsed with [~locs:true] and the node came
      from that parse. A list item spans from its marker to its last content, a table row
      its line, a cell from its leading [|], a caption from its [^], a footnote definition
      from its [[^]. *)
  val textloc : t -> 'a node -> Textloc.t

  type syntax = Kernel.Ast.syntax_role =
    | RAttrSpec (** Attributes in braces, [{...}]. *)
    | ROpenFence (** A code block's or div's opening fence line. *)
    | RCloseFence (** Its closing fence line, absent when unclosed. *)

  (** The node's delimiting syntax, in source order. Empty under the same conditions as
      {!textloc}. *)
  val syntax_locs : t -> 'a node -> (syntax * Textloc.t) list
end

(** {1 Editable sources} *)

(** A djot text together with its parse, for texts that change.

    An edit gives a new source whose document equals {!Doc.of_string} on the edited text,
    parsing again only the part of the text the edit can affect. A value of type {!t} is
    immutable: the source before an edit stays valid.

    Edit the source, not the document: {!doc} is always the parse of {!to_string}, so a
    document changed with {!Mapper.map_doc} has to be mapped again after an edit. To make
    a changed document the text to edit, start a new source from {!Doc.to_string}. *)
module Source : sig
  type t

  (** [of_string s] is the source with text [s]. [profile] and [locs] are as in
      {!Doc.of_string}, and hold for every edit of this source. *)
  val of_string : ?profile:Profile.t -> ?locs:bool -> string -> t

  (** The text. {!Doc.textloc} of {!doc} gives byte ranges in it. *)
  val to_string : t -> string

  (** The parse of the text, equal to {!Doc.of_string} on {!to_string}. *)
  val doc : t -> Doc.t

  (** [replace_lines t ~first ~last s] is [t] with lines [first] to [last] of its text
      replaced by [s]. Lines are counted from one and both ends are included, so
      [~first:2 ~last:3] replaces two lines.

      With [last = first - 1] no line is replaced and [s] is inserted before line [first]:
      [~first:1 ~last:0] inserts at the start, and with [n] lines in the text
      [~first:(n + 1) ~last:n] appends. This is the empty range of {!Textloc.is_empty}.

      [s] is taken as whole lines: a newline is added where [s] would otherwise join a
      neighbouring line.

      @raise Invalid_argument if the range is outside the text's lines. *)
  val replace_lines : t -> first:int -> last:int -> string -> t

  (** [replace_bytes t ~first ~last s] is [t] with bytes [first] to [last] of its text
      replaced by exactly [s]. Bytes are counted from zero and both ends are included, as
      in {!Textloc}. With [last = first - 1] no byte is replaced and [s] is inserted
      before byte [first].

      @raise Invalid_argument if the range is outside the text. *)
  val replace_bytes : t -> first:int -> last:int -> string -> t

  (** The lines an edit parsed again, one-based and inclusive: lines [first] to [old_last]
      of the text before the edit, which are lines [first] to [new_last] of the text after
      it. A last line of [first - 1] is an empty range. The range holds the edited lines
      and can be wider.

      The lines outside it were not parsed: the blocks they give are the ones of the
      document before the edit, with the positions of those after the range moved.
      Identifiers, sections, footnotes and references are still worked out over the whole
      document, so outside the range an edit can change the suffix of a repeated heading
      identifier, where a section ends, and what {!Doc.reference} and {!Doc.footnote}
      answer. *)
  type change =
    { first : int
    ; old_last : int
    ; new_last : int
    }

  (** {!replace_lines}, with the lines it parsed again. *)
  val replace_lines_changed : t -> first:int -> last:int -> string -> t * change

  (** {!replace_bytes}, with the lines it parsed again. *)
  val replace_bytes_changed : t -> first:int -> last:int -> string -> t * change
end

(** {1 Streaming} *)

module Stream : sig
  (** A parse fed its input in parts. Blocks are returned as the input closes them, and
      {!finish} gives the source, and with it the document.

      - The blocks are top level and in source order.
      - They differ from {!Doc.blocks} in one way: a heading is not wrapped in a
        {!Block.Section} (see {!Sections}). *)
  type t

  val start : ?profile:Profile.t -> ?locs:bool -> unit -> t

  (** Feed bytes: any part of the input, holding several lines or part of one.

      @return
        the blocks closed by the lines this completes. Bytes after the last newline are
        held until their line ends. *)
  val feed_string : t -> string -> Block.t node list * t

  (** [feed_line t l] is [feed_string t (l ^ "\n")]. *)
  val feed_line : t -> string -> Block.t node list * t

  (** held blocks that would be returned if the input ended here. *)
  val peek : t -> Block.t node list

  (** The source of all the input fed, equal to {!Source.of_string} on its concatenation.
      Every block returned by a feed, followed by {!peek}, is the parse its document was
      built from. With [locs], {!Doc.textloc} of that document locates the returned
      blocks. *)
  val finish : t -> Source.t

  (** The sections {!Doc.blocks} nests the blocks in, as events over the returned blocks:
      a heading leaves every open section of its level or deeper and enters its own. *)
  module Sections : sig
    type event =
      | Enter of Attr.t
      (** A section starts. The attributes are its heading's, identifier included; the
          heading follows as an {!Item} without them. *)
      | Item of Block.t node
      | Leave (** The innermost open section ends. *)

    (** The open sections. *)
    type t

    val start : t

    (** The events of one block. *)
    val step : t -> Block.t node -> event list * t

    (** End of input: one {!Leave} per open section. *)
    val finish : t -> event list
  end
end

(** /**)

module For_testing : sig
  (** The document without its line table, so that two parses compare with [=]. *)
  val kernel : Doc.t -> Kernel.Ast.doc

  (** The blocks of a source's pieces, before identifiers and sections. An edit keeps
      the values of the pieces it does not parse again. *)
  val parsed : Source.t -> Block.t node list
end

(** /**)

(** {1 Traversals} *)

module Mapper : sig
  type 'a filter_map = 'a option

  type 'a result =
    [ `Default
    | `Map of 'a
    ]

  (** Keep the node and map its children. *)
  val default : 'a result

  val delete : 'a filter_map result
  val ret : 'a -> 'a filter_map result

  type t
  type 'a mapper = t -> 'a -> 'a filter_map result

  val make : ?inline:Inline.t node mapper -> ?block:Block.t node mapper -> unit -> t
  val map_inline : t -> Inline.t node -> Inline.t node filter_map

  (** A {!Block.Ext_keyed} whose block is deleted is deleted. *)
  val map_block : t -> Block.t node -> Block.t node filter_map

  (** Maps the blocks. {!Doc.footnotes} is collected again from the result, so it follows
      a definition that was mapped or deleted. {!Doc.references} and what
      {!Doc.reference} answers stay as they were.

      The result is not tied to any text: an edit of the {!Source} the document came from
      gives the parse of the edited text, without the map. *)
  val map_doc : t -> Doc.t -> Doc.t
end

module Folder : sig
  type 'a result =
    [ `Default
    | `Fold of 'a
    ]

  (** Fold the node's children. *)
  val default : 'a result

  val ret : 'a -> 'a result

  type 'a t
  type ('a, 'b) folder = 'b t -> 'b -> 'a -> 'b result

  val make
    :  ?inline:(Inline.t node, 'a) folder
    -> ?block:(Block.t node, 'a) folder
    -> unit
    -> 'a t

  val fold_inline : 'a t -> 'a -> Inline.t node -> 'a

  (** Children are visited in source order. To fold a document, fold its {!Doc.blocks}:
      a footnote's blocks are there, under its {!Block.FootnoteDef}. *)
  val fold_block : 'a t -> 'a -> Block.t node -> 'a
end

(** {1 HTML} *)

module Html : sig
  type t = Kernel.Html.helt =
    | HText of string (** Escaped when serialized. *)
    | HRaw of string (** Written as is. *)
    | HVoid of string * bool * Attr.t
    (** [HVoid (tag, self_closing, attrs)]: no closing tag. *)
    | HElem of string * int * Attr.t * t list
    (** [HElem (tag, newlines, attrs, children)]. [newlines] is 2 for a newline after both
        tags, 1 after the closing tag only, 0 for neither. *)

  (** The output before serialization, for post-processing. *)
  val tree : Doc.t -> t list

  val to_string : t list -> string
  val of_doc : Doc.t -> string

  (** The HTML of blocks that are not in a document, such as a tree built in code or the
      blocks {!Stream} returns. Headings get identifiers and sections, and footnotes and
      references are resolved among these blocks, as {!Doc.of_string} does for a text.

      The blocks must have no {!Block.Section}. For a parsed document use {!of_doc}. *)
  val of_blocks : Block.t node list -> string
end
