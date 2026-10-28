<!-- ai-disclosure: ai-generated -->

# djotv

[djot](https://djot.net) for JavaScript, parsed and rendered by the parser of
djot.v: written and verified in Rocq, extracted to OCaml, and compiled from
there to JavaScript with js_of_ocaml.  It is one CommonJS module with no
dependencies.  Loaded by a script tag instead, it puts `parse`, `toHtml` and
`toDjot` on the global object.

```js
const djotv = require("djotv");

djotv.toHtml("*hi*"); // '<p><strong>hi</strong></p>\n'

const doc = djotv.parse("# Title\n\nSee [the site](https://djot.net).\n", { locs: true });
doc.children[0].children[1].children[1].destination; // 'https://djot.net'

djotv.toHtml(doc); // the HTML of a tree
djotv.toDjot(doc); // a tree as djot text
```

The tree is the JSON the OCaml library writes, which is djot.js's AST with a
few additions.  `index.d.ts` types the functions and the options; a node is
typed only by its `tag`.

A profile chooses the syntax, as `Djot.Profile` does in OCaml:

```js
djotv.parse("[[page]]", { profile: { switches: { ext_wikilinks: true } } });
djotv.toHtml("**strong**", { profile: { base: "markdown_like" } });
```

`toDjot` takes a `style`.  The default, `irredundant`, writes every backslash
and brace the parse needs and no other, and is the slowest: on a 140 KB
document, parsing takes about 50 ms, `irredundant` about 0.8 s and `checked`
about 0.15 s.  `index.d.ts` describes the four styles.

A failure throws an `Error`: an unknown switch, profile or style, a tree the
OCaml library cannot read, or a document nested too deeply for the stack.

## Installation

The package is not on npm.  Build it from the repository, pack it, and install
the tarball:

```sh
git clone https://github.com/hon-gyu/djot.v
cd djot.v
make js-pkg
cd js && npm pack  # writes djotv-0.1.0.tgz

# in your project
npm install /path/to/djot.v/js/djotv-0.1.0.tgz
```

`make js-pkg` needs the build environment described under Development.

## Development

`djotv.js` is built from `djotv.ml` by `make js-pkg` at the root of the
repository, in an environment with the `ocaml/` package's dependencies, brr and
`js_of_ocaml-compiler`.  `make check-js` runs the tests.
