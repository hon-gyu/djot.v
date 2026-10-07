# ai-disclosure: ai-generated
# pyright: reportPrivateUsage=false
import doctest
import json
import threading
from typing import Any, cast

import pytest

import djotv
from djotv import DjotError, Profile, _options, ast
from djotv._runtime import run

# A text with every node the parser makes.
EVERYTHING = """\
{#top .a key="v"}
# Heading _emph_ *strong*

A {=mark=} {+insert+} {-delete-} x^sup^ H~2~O `verb` :smile: $`x` $$`y`
[link](http://e.x) [ref][r] ![img](i.png) [span]{.c} :tag[named] note[^n]
<http://u.rl> <me@e.mail> `<b>`{=html} non\\ breaking 'single' "double"\\
hard [[wiki|alias]] ![[embed]] %{ hole }

> quote

``` py
code
```

```
plain
```

::: warning
div
:::

::: note-name
named div
:::

1. one
2. two

(a) loose

(b) item

- bullet

- [ ] todo
- [x] done

term

: definition

* * *

| h | i |
|:--|--:|
| a | b |
^ caption

``` =html
<hr>
```

[r]: http://ref.x

[^n]: A note.

key: keyed

> [!tip]- Title
> callout
"""

EXTENSIONS = Profile(
    switches={
        "ext_wikilinks": True,
        "ext_keyed": True,
        "ext_callouts": True,
        "ext_tags": True,
        "ext_holes": True,
    }
)


def tags(json_value: Any) -> set[str]:
    found: set[str] = set()
    if isinstance(json_value, list):
        for child in cast(list[Any], json_value):
            found |= tags(child)
    elif isinstance(json_value, dict):
        members = cast(dict[str, Any], json_value)
        for child in members.values():
            found |= tags(child)
        tag = members.get("tag")
        if isinstance(tag, str):
            found.add(tag)
    return found


def para(text: str, *, profile: Profile | None = None, locs: bool = False) -> ast.Para:
    (block,) = djotv.parse(text, profile=profile, locs=locs).children
    assert isinstance(block, ast.Para)
    return block


@pytest.mark.parametrize("locs", [False, True])
def test_tree_is_the_json(locs: bool):
    options = _options(EXTENSIONS) + (["--locs"] if locs else [])
    written = json.loads(run("ast", options, EVERYTHING))
    doc = djotv.parse(EVERYTHING, profile=EXTENSIONS, locs=locs)
    assert doc.to_json() == written


def test_every_class_is_read():
    written = json.loads(run("ast", _options(EXTENSIONS), EVERYTHING))
    assert tags(written) - {"doc"} == set(ast._CLASSES)


def test_html():
    assert djotv.to_html("*hi*") == "<p><strong>hi</strong></p>\n"
    assert djotv.to_html("x — ü") == "<p>x — ü</p>\n"


def test_html_of_a_tree():
    doc = djotv.parse(EVERYTHING, profile=EXTENSIONS)
    assert djotv.to_html(doc, profile=EXTENSIONS) == djotv.to_html(
        EVERYTHING, profile=EXTENSIONS
    )


def test_djot_of_a_tree_parses_back():
    doc = djotv.parse(EVERYTHING, profile=EXTENSIONS)
    again = djotv.parse(djotv.to_djot(doc, profile=EXTENSIONS), profile=EXTENSIONS)
    assert djotv.to_html(again, profile=EXTENSIONS) == djotv.to_html(
        doc, profile=EXTENSIONS
    )


def test_a_built_tree():
    doc = ast.Doc(
        children=[
            ast.Para(
                children=[ast.Str("a "), ast.Emph(children=[ast.Str("b")])],
                attributes={"class": "c"},
            )
        ]
    )
    assert djotv.to_html(doc) == '<p class="c">a <em>b</em></p>\n'
    assert djotv.to_djot(doc) == "{.c}\na _b_"


def test_match():
    (block,) = djotv.parse("[a](b)").children
    match block:
        case ast.Para(children=[ast.Link(destination=destination)]):
            assert destination == "b"
        case _:
            raise AssertionError(block)


def test_pos():
    strong = para("é *b*", locs=True).children[1]
    assert strong.pos == ast.Pos(ast.Point(1, 4, 3), ast.Point(1, 6, 5))
    assert djotv.parse("x").children[0].pos is None


def test_repr():
    assert repr(djotv.parse("*hi*").children[0]) == (
        "Para(children=[Strong(children=[Str(text='hi')])])"
    )


def test_profile():
    assert para("[[w]]").children[0] == ast.Str("[[w]]")
    wikilinks = Profile(switches={"ext_wikilinks": True})
    assert para("[[w]]", profile=wikilinks).children == [ast.ExtWikilink("w")]
    assert "<strong>" in djotv.to_html("**x**", profile=Profile("markdown_like"))
    assert "<table>" not in djotv.to_html(
        "| a |\n", profile=Profile(switches={"tables": False})
    )


def test_errors():
    with pytest.raises(DjotError, match="unknown switch"):
        djotv.to_html("x", profile=Profile(switches={"nope": True}))
    with pytest.raises(DjotError, match="nested too deeply"):
        djotv.to_html("> " * 5000 + "x")
    with pytest.raises(ValueError, match="unknown node tag"):
        ast.node_from_json({"tag": "nope"})


def test_threads():
    results: list[bool] = []

    def work(i: int):
        results.append(djotv.to_html(f"*{i}*") == f"<p><strong>{i}</strong></p>\n")

    threads = [threading.Thread(target=work, args=(i,)) for i in range(8)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    assert results == [True] * 8


def test_doctests():
    assert doctest.testmod(djotv).failed == 0
