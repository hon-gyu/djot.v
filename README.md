# djot

A djot parser and HTML renderer extracted from
[djot.v](https://github.com/hon-gyu/djot.v), a djot parser written and
verified in Rocq. The goals behind djot's design (no backtracking,
container uniformity, local interpretation, safe rewrapping) are proved
there as theorems about the parser; this directory
carries only the OCaml the extraction produces, plus a thin hand-written
API over it, so building it needs no Rocq installation.

```ocaml
let doc = Djot.Doc.of_string ~locs:true "# hi\n\n*strong* and [a](b)\n"
let html = Djot.Html.of_doc doc
```

The API follows [cmarkit](https://erratique.ch/software/cmarkit)'s shape
(`Doc`, `Block`, `Inline`, `Textloc`, `Mapper`, `Folder`, `Html`).  cmarkit
is under the ISC license; its notice is in `LICENSE-cmarkit.md`.  The
differences:

- The tree types are the extracted ones, re-exported with their
  constructors.  Every element is a `'a node = Node of pos * attrs * 'a`.
- The types are closed.  Syntax extensions are constructors defined in
  Rocq and named `Ext_*` (`Inline.Ext_wikilink`, `Block.Ext_keyed`); there are no extension
  hooks.
- There is no layout information.  The locations of fences, attribute
  specs, list items and table cells are available instead, through
  `Doc.syntax_locs` and `Doc.parts`.
- A node's location needs its document: `Doc.textloc doc node`.  Parse
  with `~locs:true` to record locations.
- The document pass groups each heading and the blocks under it into a
  `Block.Section`, which carries the heading's id.
- `Html.tree` returns the output tree before serialization, for
  post-processing; `Html.to_string` serializes it.

The syntax a parse accepts is a `Djot.Profile.t`: `Profile.djot` or
`Profile.markdown_like`, adjusted per construct with `Profile.with_tables`,
`Profile.with_footnotes` and so on.  The extensions are off in both and
switch on with `Profile.with_ext_wikilinks` and `Profile.with_ext_keyed`.

The extracted modules are the `djot.kernel` library (`Djot.Kernel`).
They mirror the Rocq ones and speak the extracted representation, with
numbers as OCaml `int`.  `test/api.ml` tests the hand-written API,
which the Rocq proofs do not cover.

`kernel/` is generated.  Change `theories/` upstream and re-run extraction;
edits made there are overwritten.
