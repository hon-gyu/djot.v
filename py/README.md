<!-- ai-disclosure: ai-generated -->

# djotv

[djot](https://djot.net) for Python, parsed and rendered by the parser of
djot.v: written and verified in Rocq, extracted to OCaml, and compiled from
there to WebAssembly.  The package is pure Python and runs the module in
[Wasmtime](https://wasmtime.dev), so it needs no OCaml and installs the same
wheel everywhere Wasmtime does.

```python
import djotv
from djotv import ast

djotv.to_html("*hi*")  # '<p><strong>hi</strong></p>\n'

doc = djotv.parse("# Title\n\nSee [the site](https://djot.net).\n", locs=True)
match doc.children[0].children[1]:
    case ast.Para(children=[_, ast.Link(destination=url) as link, _]):
        print(url, link.pos.start.line)  # https://djot.net 3

djotv.to_html(doc)  # the HTML of a tree
djotv.to_djot(doc)  # a tree as djot text
```

The tree is typed: `djotv.ast` has one dataclass per node, and `ast.Block` and
`ast.Inline` are the unions of them.  The classes mirror the JSON the OCaml
library writes, which is djot.js's AST with a few additions; `to_json` and
`Doc.from_json` convert to and from it.

A `Profile` chooses the syntax, as `Djot.Profile` does in OCaml:

```python
from djotv import Profile

djotv.parse("[[page]]", profile=Profile(switches={"ext_wikilinks": True}))
djotv.to_html("**strong**", profile=Profile("markdown_like"))
```

## How it runs

The module is a WASI command.  Each call is one run of it: the command and its
options as arguments, the text on stdin, the result on stdout.  OCaml values
are WasmGC references, which a host cannot build, so text is all that crosses
and a tree crosses as JSON.

- The first call in a process compiles the module, about 0.7 s once per
  machine.  Wasmtime caches the result, and later processes load it in about
  60 ms.
- A call costs about 1 ms before any parsing.
- Parsing runs at roughly 0.7 MB/s, some twenty times slower than the native
  OCaml library.  Most of that is Wasmtime's default collector, which
  wasmtime-py does not let a caller change.
- A document nested some two thousand levels deep exhausts the WebAssembly
  stack and raises `DjotError`.

## Development

`src/djotv/djot.wasm` is built from `wasi/` at the root of the repository by
`make py-wasm` there, in an opam switch with the `ocaml/` package's dependencies and
`wasm_of_ocaml-compiler`.  `make check-py` runs the tests.
