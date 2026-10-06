# djot

A djot parser and HTML renderer extracted from
[djot.v](https://github.com/hon-gyu/djot.v), a djot parser written and
verified in Rocq. The goals behind djot's design (no backtracking,
container uniformity, local interpretation, safe hard-wrapping) are proved
there as theorems about the parser; this directory
carries only the OCaml the extraction produces, plus a thin hand-written
API over it, so building it needs no Rocq installation.

```ocaml
let doc = Djot.Doc.of_string ~locs:true "# hi\n\n*strong* and [a](b)\n"
let html = Djot.Html.of_doc doc
```

The package is not on opam (yet).  The repository's `ocaml` branch holds this
directory at its root.

The API follows [cmarkit](https://erratique.ch/software/cmarkit)'s shape
(`Doc`, `Block`, `Inline`, `Textloc`, `Mapper`, `Folder`, `Html`).  cmarkit
is under the ISC license; its notice is in `LICENSE-cmarkit.md`.  The
differences:

- The tree types are the extracted ones, re-exported with their
  constructors.  Every element is a `'a node = Node of pos * attrs * 'a`.
- The types are closed.  Syntax extensions are constructors defined in
  Rocq and named `Ext_*` (`Inline.Ext_wikilink`, `Block.Ext_keyed`,
  `Block.Ext_callout`); there are no extension
  hooks.
- There is no layout information.  The locations of fences and
  attribute specs are available instead, through `Doc.syntax_locs`.
- List items, definition terms and definitions, table rows, cells and
  captions are nodes, as in djot.js, so each has a location.
- A node's location needs its document: `Doc.textloc doc node`.  Parse
  with `~locs:true` to record locations.
- Parsing groups each heading and the blocks under it into a
  `Block.Section`, which carries the heading's id.
- `Html.tree` returns the output tree before serialization, for
  post-processing; `Html.to_string` serializes it.
- `Doc.to_string` renders a document back to djot, where cmarkit has a
  CommonMark renderer.  `Block.to_string` and `Inline.to_string` do the
  same for part of a tree.
- `Doc.make` gives the document of blocks built in code, with ids,
  sections and definitions resolved as for a parsed text.
  `Html.of_blocks` renders such blocks directly.
- A `Source.t` is a text together with its parse, for texts that change.
  `Source.replace_lines` and `Source.replace_bytes` edit the text,
  parsing again only the part the edit can affect, and `Source.doc`
  gives the document.  The `_changed` variants also return the lines
  that were parsed again.  A `Doc.t` does not keep its text.
- `Stream` parses input fed in lines or in arbitrary chunks, returning
  each top-level block when the input closes it; `Stream.finish` gives
  the source, and `Source.doc` its document.

The `djot.json` library writes a document as JSON in the format of
djot.js's AST, for checking a document's shape with JSON Schema or `jq`,
and reads one back.
It is built when [jsont](https://erratique.ch/software/jsont) and bytesrw
are installed; `Djot_json` lists what it adds to djot.js's format and
where it differs.

```ocaml
let json = Djot_json.to_string (Djot.Doc.of_string "# hi\n")
```

With `~frontmatter:true`, `Doc.of_string`, `Source.of_string` and
`Stream.start` read YAML frontmatter, a mapping between two `---` lines
at the start of the text, and parse the rest as djot.
This needs the [yaml](https://github.com/avsm/ocaml-yaml) package and
raises `Invalid_argument` when the library was built without it.
The frontmatter is read in OCaml, outside the extracted parser, so the
theorems say nothing about it; `Djot.Frontmatter` gives the rule.

```ocaml
let doc = Djot.Doc.of_string ~frontmatter:true "---\ntitle: hi\n---\n# hi\n"
let title =
  Option.bind (Djot.Doc.frontmatter doc) (fun fm -> List.assoc_opt "title" fm.fields)
```

The syntax a parse accepts is a `Djot.Profile.t`: `Profile.djot` or
`Profile.markdown_like`, adjusted per construct with `Profile.with_tables`,
`Profile.with_footnotes` and so on.  The extensions are off in both and
switch on with `Profile.with_ext_wikilinks`, `Profile.with_ext_keyed`, and
`Profile.with_ext_callouts`.

The `djot` command is built when cmdliner and `djot.json` are available.
Its subcommands `html`, `djot`, `json` and `ast` render a file, or stdin,
to HTML, djot, djot.js's JSON AST, and an indented tree.  `--from json`
reads the JSON back, `html --doc` writes a complete page, and the profile
switches are options such as `--no-tables` and `--ext-wikilinks`;
`djot --help` lists them.

```sh
djot html --doc --frontmatter notes.dj > notes.html
djot json notes.dj | jq '...' | djot html --from json
```

The extracted modules are the `djot.kernel` library (`Djot.Kernel`).
They mirror the Rocq ones and speak the extracted representation, with
numbers as OCaml `int`.  `test/api.ml` tests the hand-written API,
which the Rocq proofs do not cover.

`kernel/` is generated.  Change `theories/` upstream and re-run extraction;
edits made there are overwritten.
