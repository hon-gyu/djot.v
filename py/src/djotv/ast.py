# ai-disclosure: ai-generated
"""The tree of a djot document.

One class per node of the JSON the OCaml library writes, which is djot.js's AST
with a few additions (see `Djot_json` there).  A field has the name of its JSON
member, and a class the name of its tag in camel case: `block_quote` is
`BlockQuote`.

Every node has `attributes`, and a `pos` when the document was parsed with
`locs=True`.  The identifier a heading or a section was given, rather than
written with, is in `auto_attributes`.
"""

from __future__ import annotations

from dataclasses import dataclass, field, fields
from typing import Any, ClassVar, Literal, cast

type Align = Literal["default", "left", "right", "center"]
type Checkbox = Literal["checked", "unchecked"]
type Fold = Literal["expanded", "collapsed"]
type OrderedListStyle = Literal[
    "1.", "1)", "(1)", "a.", "a)", "(a)", "A.", "A)", "(A)", "i.", "i)", "(i)", "I.", "I)", "(I)"
]  # fmt: skip

type Inline = (
    Str | Emph | Strong | Mark | Insert | Delete | Superscript | Subscript | Verbatim
    | Symb | InlineMath | DisplayMath | Link | Image | Span | FootnoteReference | Url
    | Email | RawInline | NonBreakingSpace | SingleQuoted | DoubleQuoted | SoftBreak
    | HardBreak | ExtWikilink
)  # fmt: skip

type Block = (
    Para | Section | Heading | BlockQuote | CodeBlock | Div | OrderedList | BulletList
    | TaskList | DefinitionList | ThematicBreak | Table | RawBlock | Footnote
    | Reference | ExtKeyed | ExtCallout
)  # fmt: skip


# Positions
# =========


@dataclass(slots=True, frozen=True)
class Point:
    """A place in the source: `line` and `col` from one, `offset` from zero.

    Columns and offsets count bytes of the UTF-8 text.
    """

    line: int
    col: int
    offset: int


@dataclass(slots=True, frozen=True)
class Pos:
    """The source a node was read from, `end` being its last byte."""

    start: Point
    end: Point


# Nodes
# =====


@dataclass(slots=True, kw_only=True, repr=False)
class Node:
    tag: ClassVar[str]

    attributes: dict[str, str] = field(default_factory=dict[str, str])
    auto_attributes: dict[str, str] = field(default_factory=dict[str, str])
    pos: Pos | None = None

    def __repr__(self) -> str:
        """The fields that say something: `pos`, and an empty or absent one, are left out."""
        shown = [
            f"{f.name}={value!r}"
            for f in fields(self)[3:] + fields(self)[:2]
            if (value := getattr(self, f.name)) not in (None, "", [], {})
        ]
        return f"{type(self).__name__}({', '.join(shown)})"

    def to_json(self) -> dict[str, Any]:
        """The node as the JSON object it is read from."""
        out: dict[str, Any] = {"tag": self.tag}
        for f in fields(self):
            value = getattr(self, f.name)
            if f.name == "attributes":
                if value:
                    out["attributes"] = dict(value)
            elif f.name == "auto_attributes":
                if value:
                    out["autoAttributes"] = dict(value)
            elif f.name == "pos":
                if value is not None:
                    out["pos"] = {
                        "start": _point_to_json(value.start),
                        "end": _point_to_json(value.end),
                    }
            elif f.name in ("name", "lang") and value == "":
                # Left out when empty, as the OCaml library writes them.
                pass
            elif isinstance(value, list):
                out[f.name] = [child.to_json() for child in cast(list[Node], value)]
            elif value is not None:
                out[f.name] = value
        return out


def _point_to_json(point: Point) -> dict[str, int]:
    return {"line": point.line, "col": point.col, "offset": point.offset}


# Inlines
# -------


@dataclass(slots=True, repr=False)
class Str(Node):
    tag: ClassVar[str] = "str"
    text: str


@dataclass(slots=True, repr=False)
class Emph(Node):
    tag: ClassVar[str] = "emph"
    children: list[Inline] = field(default_factory=list[Inline])


@dataclass(slots=True, repr=False)
class Strong(Node):
    tag: ClassVar[str] = "strong"
    children: list[Inline] = field(default_factory=list[Inline])


@dataclass(slots=True, repr=False)
class Mark(Node):
    tag: ClassVar[str] = "mark"
    children: list[Inline] = field(default_factory=list[Inline])


@dataclass(slots=True, repr=False)
class Insert(Node):
    tag: ClassVar[str] = "insert"
    children: list[Inline] = field(default_factory=list[Inline])


@dataclass(slots=True, repr=False)
class Delete(Node):
    tag: ClassVar[str] = "delete"
    children: list[Inline] = field(default_factory=list[Inline])


@dataclass(slots=True, repr=False)
class Superscript(Node):
    tag: ClassVar[str] = "superscript"
    children: list[Inline] = field(default_factory=list[Inline])


@dataclass(slots=True, repr=False)
class Subscript(Node):
    tag: ClassVar[str] = "subscript"
    children: list[Inline] = field(default_factory=list[Inline])


@dataclass(slots=True, repr=False)
class Verbatim(Node):
    tag: ClassVar[str] = "verbatim"
    text: str


@dataclass(slots=True, repr=False)
class Symb(Node):
    """A symbol, written `:alias:`."""

    tag: ClassVar[str] = "symb"
    alias: str


@dataclass(slots=True, repr=False)
class InlineMath(Node):
    tag: ClassVar[str] = "inline_math"
    text: str


@dataclass(slots=True, repr=False)
class DisplayMath(Node):
    tag: ClassVar[str] = "display_math"
    text: str


@dataclass(slots=True, repr=False)
class Link(Node):
    """A link to `destination`, or to the definition labelled `reference`."""

    tag: ClassVar[str] = "link"
    children: list[Inline] = field(default_factory=list[Inline])
    destination: str | None = None
    reference: str | None = None


@dataclass(slots=True, repr=False)
class Image(Node):
    """An image at `destination`, or at the definition labelled `reference`."""

    tag: ClassVar[str] = "image"
    children: list[Inline] = field(default_factory=list[Inline])
    destination: str | None = None
    reference: str | None = None


@dataclass(slots=True, repr=False)
class Span(Node):
    """`name` is that of `:name[...]`, an extension; empty when unnamed."""

    tag: ClassVar[str] = "span"
    children: list[Inline] = field(default_factory=list[Inline])
    name: str = ""


@dataclass(slots=True, repr=False)
class FootnoteReference(Node):
    """`text` is the label of the footnote."""

    tag: ClassVar[str] = "footnote_reference"
    text: str


@dataclass(slots=True, repr=False)
class Url(Node):
    tag: ClassVar[str] = "url"
    text: str


@dataclass(slots=True, repr=False)
class Email(Node):
    tag: ClassVar[str] = "email"
    text: str


@dataclass(slots=True, repr=False)
class RawInline(Node):
    tag: ClassVar[str] = "raw_inline"
    format: str
    text: str


@dataclass(slots=True, repr=False)
class NonBreakingSpace(Node):
    tag: ClassVar[str] = "non_breaking_space"


@dataclass(slots=True, repr=False)
class SingleQuoted(Node):
    tag: ClassVar[str] = "single_quoted"
    children: list[Inline] = field(default_factory=list[Inline])


@dataclass(slots=True, repr=False)
class DoubleQuoted(Node):
    tag: ClassVar[str] = "double_quoted"
    children: list[Inline] = field(default_factory=list[Inline])


@dataclass(slots=True, repr=False)
class SoftBreak(Node):
    tag: ClassVar[str] = "soft_break"


@dataclass(slots=True, repr=False)
class HardBreak(Node):
    tag: ClassVar[str] = "hard_break"


@dataclass(slots=True, repr=False)
class ExtWikilink(Node):
    """An extension: `[[target|alias]]`, or `![[...]]` when `embed`."""

    tag: ClassVar[str] = "ext_wikilink"
    target: str
    embed: bool = False
    alias: str | None = None


# Blocks
# ------


@dataclass(slots=True, repr=False)
class Para(Node):
    tag: ClassVar[str] = "para"
    children: list[Inline] = field(default_factory=list[Inline])


@dataclass(slots=True, repr=False)
class Section(Node):
    """A heading, its first child, and the blocks up to the next heading of the
    same or a higher level.  The heading's identifier is on the section."""

    tag: ClassVar[str] = "section"
    children: list[Block] = field(default_factory=list[Block])


@dataclass(slots=True, repr=False)
class Heading(Node):
    """`plain` is the text an identifier is derived from.  It is written for a
    reader and not read back."""

    tag: ClassVar[str] = "heading"
    level: int
    children: list[Inline] = field(default_factory=list[Inline])
    plain: str = ""


@dataclass(slots=True, repr=False)
class BlockQuote(Node):
    tag: ClassVar[str] = "block_quote"
    children: list[Block] = field(default_factory=list[Block])


@dataclass(slots=True, repr=False)
class CodeBlock(Node):
    tag: ClassVar[str] = "code_block"
    text: str
    lang: str = ""


@dataclass(slots=True, repr=False)
class Div(Node):
    """`name` is that of `::: name`, an extension; empty when unnamed."""

    tag: ClassVar[str] = "div"
    children: list[Block] = field(default_factory=list[Block])
    name: str = ""


@dataclass(slots=True, repr=False)
class ListItem(Node):
    tag: ClassVar[str] = "list_item"
    children: list[Block] = field(default_factory=list[Block])


@dataclass(slots=True, repr=False)
class OrderedList(Node):
    """`style` is the numeral between its delimiters, `start` the first number."""

    tag: ClassVar[str] = "ordered_list"
    children: list[ListItem] = field(default_factory=list[ListItem])
    style: OrderedListStyle = "1."
    start: int = 1
    tight: bool = True


@dataclass(slots=True, repr=False)
class BulletList(Node):
    """`style` is the marker: `-`, `+` or `*`."""

    tag: ClassVar[str] = "bullet_list"
    children: list[ListItem] = field(default_factory=list[ListItem])
    style: str = "-"
    tight: bool = True


@dataclass(slots=True, repr=False)
class TaskListItem(Node):
    tag: ClassVar[str] = "task_list_item"
    checkbox: Checkbox
    children: list[Block] = field(default_factory=list[Block])


@dataclass(slots=True, repr=False)
class TaskList(Node):
    tag: ClassVar[str] = "task_list"
    children: list[TaskListItem] = field(default_factory=list[TaskListItem])
    tight: bool = True


@dataclass(slots=True, repr=False)
class Term(Node):
    tag: ClassVar[str] = "term"
    children: list[Inline] = field(default_factory=list[Inline])


@dataclass(slots=True, repr=False)
class Definition(Node):
    tag: ClassVar[str] = "definition"
    children: list[Block] = field(default_factory=list[Block])


@dataclass(slots=True, repr=False)
class DefinitionListItem(Node):
    """Two children: the term, then the definition."""

    tag: ClassVar[str] = "definition_list_item"
    children: list[Term | Definition] = field(default_factory=list[Term | Definition])


@dataclass(slots=True, repr=False)
class DefinitionList(Node):
    tag: ClassVar[str] = "definition_list"
    children: list[DefinitionListItem] = field(default_factory=list[DefinitionListItem])
    tight: bool = True


@dataclass(slots=True, repr=False)
class ThematicBreak(Node):
    tag: ClassVar[str] = "thematic_break"


@dataclass(slots=True, repr=False)
class Cell(Node):
    tag: ClassVar[str] = "cell"
    children: list[Inline] = field(default_factory=list[Inline])
    head: bool = False
    align: Align = "default"


@dataclass(slots=True, repr=False)
class Row(Node):
    """`head` says whether the cells are head cells.  It is written for a
    reader and not read back: each cell says so itself."""

    tag: ClassVar[str] = "row"
    children: list[Cell] = field(default_factory=list[Cell])
    head: bool = False


@dataclass(slots=True, repr=False)
class Caption(Node):
    tag: ClassVar[str] = "caption"
    children: list[Inline] = field(default_factory=list[Inline])


@dataclass(slots=True, repr=False)
class Table(Node):
    """The caption, which a parsed table always has, then the rows.  A caption
    with no children is no caption."""

    tag: ClassVar[str] = "table"
    children: list[Caption | Row] = field(default_factory=list[Caption | Row])


@dataclass(slots=True, repr=False)
class RawBlock(Node):
    tag: ClassVar[str] = "raw_block"
    format: str
    text: str


@dataclass(slots=True, repr=False)
class Footnote(Node):
    """The definition of the footnote labelled `label`."""

    tag: ClassVar[str] = "footnote"
    label: str
    children: list[Block] = field(default_factory=list[Block])


@dataclass(slots=True, repr=False)
class Reference(Node):
    """The definition of the link reference labelled `label`."""

    tag: ClassVar[str] = "reference"
    label: str
    destination: str


@dataclass(slots=True, repr=False)
class ExtKeyed(Node):
    """An extension: `label: content`, the content being the one child.

    `plain` is the text of the label.  It is written for a reader and not read
    back.
    """

    tag: ClassVar[str] = "ext_keyed"
    label: list[Inline] = field(default_factory=list[Inline])
    children: list[Block] = field(default_factory=list[Block])
    plain: str = ""


@dataclass(slots=True, repr=False)
class ExtCallout(Node):
    """An extension: a callout of some `kind`, with its fold marker if it has
    one, its title and its body."""

    tag: ClassVar[str] = "ext_callout"
    kind: str
    title: list[Inline] = field(default_factory=list[Inline])
    children: list[Block] = field(default_factory=list[Block])
    fold: Fold | None = None


# Documents
# =========


@dataclass(slots=True)
class Doc:
    """A document: its blocks, and its definitions by label.

    The definitions are left out of `children`, as in djot.js.
    `auto_references` has one entry per heading, for `[Heading][]`.  It is
    written for a reader and not read back.
    """

    tag: ClassVar[str] = "doc"

    children: list[Block] = field(default_factory=list[Block])
    references: dict[str, Reference] = field(default_factory=dict[str, Reference])
    auto_references: dict[str, Reference] = field(default_factory=dict[str, Reference])
    footnotes: dict[str, Footnote] = field(default_factory=dict[str, Footnote])

    def to_json(self) -> dict[str, Any]:
        def table(defs: dict[str, Any]) -> dict[str, Any]:
            return {label: node.to_json() for label, node in defs.items()}

        return {
            "tag": self.tag,
            "references": table(self.references),
            "autoReferences": table(self.auto_references),
            "footnotes": table(self.footnotes),
            "children": [child.to_json() for child in self.children],
        }

    @classmethod
    def from_json(cls, json: dict[str, Any]) -> Doc:
        """The document a `doc` object describes.

        Raises `ValueError` for an object that is not one the OCaml library
        writes.
        """
        if json.get("tag") != cls.tag:
            raise ValueError('a document has the tag "doc"')

        def table(name: str) -> dict[str, Any]:
            return {
                label: node_from_json(node)
                for label, node in json.get(name, {}).items()
            }

        return cls(
            children=[node_from_json(child) for child in json.get("children", [])],
            references=table("references"),
            auto_references=table("autoReferences"),
            footnotes=table("footnotes"),
        )


# Reading JSON
# ============

_CLASSES: dict[str, type[Node]] = {
    cls.tag: cls
    for cls in (
        Str, Emph, Strong, Mark, Insert, Delete, Superscript, Subscript, Verbatim, Symb,
        InlineMath, DisplayMath, Link, Image, Span, FootnoteReference, Url, Email,
        RawInline, NonBreakingSpace, SingleQuoted, DoubleQuoted, SoftBreak, HardBreak,
        ExtWikilink,
        Para, Section, Heading, BlockQuote, CodeBlock, Div, ListItem, OrderedList,
        BulletList, TaskListItem, TaskList, Term, Definition, DefinitionListItem,
        DefinitionList, ThematicBreak, Cell, Row, Caption, Table, RawBlock, Footnote,
        Reference, ExtKeyed, ExtCallout,
    )
}  # fmt: skip


def _point(json: dict[str, int]) -> Point:
    return Point(json["line"], json["col"], json["offset"])


def node_from_json(json: dict[str, Any]) -> Any:
    """The node a JSON object describes, of the class its tag names.

    Raises `ValueError` for an object that is not one the OCaml library writes.
    """
    tag = json.get("tag")
    cls = _CLASSES.get(tag)  # type: ignore[arg-type]
    if cls is None:
        raise ValueError(f"unknown node tag {tag!r}")
    members: dict[str, Any] = {}
    for name, value in json.items():
        if name == "tag":
            pass
        elif name == "attributes":
            members["attributes"] = value
        elif name == "autoAttributes":
            members["auto_attributes"] = value
        elif name == "pos":
            members["pos"] = Pos(_point(value["start"]), _point(value["end"]))
        elif isinstance(value, list):
            # A member that is a list is a list of nodes.
            children = cast(list[dict[str, Any]], value)
            members[name] = [node_from_json(child) for child in children]
        else:
            members[name] = value
    try:
        return cls(**members)
    except TypeError as error:
        raise ValueError(f"a {tag!r} node: {error}") from None
