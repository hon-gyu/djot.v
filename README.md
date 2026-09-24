<!-- ai-disclosure: autonomous -->

# djot

A djot parser extracted from the Rocq development in
[djot.v](https://github.com/hon-gyu/djot.v).  The roundtrip and
well-formedness properties it satisfies are proved there; this directory
carries only the OCaml the extraction produces, so building it needs no
Rocq installation.

```ocaml
let html = Djot.Html.convert "# hi\n\n*strong* and [a](b)\n"
```

`Djot.Html.convert : string -> string` is the intended entry point.  The
deeper modules mirror the Coq ones and are usable, but they speak the
extracted representation: numbers are the unary `Djot.Datatypes.nat`.

For source locations, call `Djot.Step.parse_blocks_located` or
`Djot.Document.parse_doc_located` with `Djot.Inline.djot_table` and
`Djot.Step.djot_bconfig`.  Nodes carry `Djot.Ast.SomePos`; resolve its
`node_span` using `Djot.Strings.resolve_span (line_table source)`.  The
resolved endpoints contain zero-based byte offsets, line indices, and
byte columns.  `check/located.ml` exercises these entry points as a
separate package consumer.

Wikilinks (`[[target|alias]]`, `![[target]]`) are off in djot's table.
Pass `Djot.InlineTable.with_wikilinks true Djot.InlineTable.djot_config` as the
table to switch them on; they parse to `Djot.Ast.Wikilink (embed,
target, alias)` with both strings as written.

`src/` is generated.  Change `theories/` upstream and run `make dist`;
edits made here are overwritten.
