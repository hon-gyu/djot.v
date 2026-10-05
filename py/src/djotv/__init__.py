# ai-disclosure: ai-generated
"""djot, parsed and rendered by the parser of djot.v.

The parser is written and verified in Rocq, extracted to OCaml, and compiled
from there to WebAssembly; this package runs it in Wasmtime.

    >>> import djotv
    >>> djotv.to_html("*hi*")
    '<p><strong>hi</strong></p>\\n'
    >>> djotv.parse("*hi*").children
    [Para(children=[Strong(children=[Str(text='hi')])])]
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Literal

from . import ast
from ._runtime import DjotError, run
from .ast import Doc

__all__ = ["DjotError", "Doc", "Profile", "ast", "parse", "to_djot", "to_html"]


@dataclass(frozen=True, slots=True)
class Profile:
    """The syntax a parse accepts: a named profile with constructs switched.

    `djot` is djot as specified.  `markdown_like` adds Markdown spellings:
    strong as `**`, dollar math, setext headings, sublists without a blank
    line.  It is not CommonMark.

    A switch has the name of its `Djot.Profile.with_` function in the OCaml
    library: `tables`, `footnotes`, `ext_wikilinks`, `ext_callouts`.  The
    extensions are off in both profiles.

        Profile(switches={"ext_wikilinks": True, "tables": False})
    """

    base: Literal["djot", "markdown_like"] = "djot"
    switches: dict[str, bool] = field(default_factory=dict)

    def _options(self) -> list[str]:
        options = ["--profile", self.base]
        for name, on in self.switches.items():
            options += ["--on" if on else "--off", name]
        return options


def _options(profile: Profile | None) -> list[str]:
    return [] if profile is None else profile._options()


def parse(text: str, *, profile: Profile | None = None, locs: bool = False) -> Doc:
    """The tree of a djot text.

    With `locs`, every node has the `pos` it was read from.
    """
    options = _options(profile) + (["--locs"] if locs else [])
    return Doc.from_json(json.loads(run("ast", options, text)))


def to_html(source: str | Doc, *, profile: Profile | None = None) -> str:
    """The HTML of a djot text, or of a tree."""
    if isinstance(source, Doc):
        return run("ast-html", _options(profile), json.dumps(source.to_json()))
    return run("html", _options(profile), source)


def to_djot(doc: Doc, *, profile: Profile | None = None) -> str:
    """A tree as djot text, in the syntax of `profile`.

    Parsing the result with that profile gives the same tree, up to positions
    and the exceptions `Djot.Doc.to_string` lists in the OCaml library.
    """
    return run("ast-djot", _options(profile), json.dumps(doc.to_json()))
