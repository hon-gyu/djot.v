---
ai-disclosure: ai-generated
---
# JSON output: gaps against djot.js's AST

`djot.json` (`ocaml/json`) writes a document in the format of djot.js's AST.
The aim is that deleting the keys we add leaves djot.js's output. These
are the places where that fails, each because the tree does not hold what
djot.js writes. Recorded 2026-10-04.

## To do

| Gap | djot.js | Ours | What closing it needs |
| --- | ------- | ---- | --------------------- |
| Smart punctuation | a `smart_punctuation` node with the source (`--`, `...`, an unmatched quote) | part of a `str`, as the rendered character | an inline constructor carrying its source; see "smart punctuation contributes its rendering" in `djotjs-divergences.md` for the cost |
| Derived identifiers | a derived section id is under `autoAttributes`, a written one under `attributes` | always under `attributes` | the document pass recording which ids it derived; `doc_auto_identifiers` lists every used id, written ones included |
| Bullet list `style` | the marker, `-`, `+` or `*` | absent | the marker on `BulletList`; the same field would remove the round-trip exception that two adjacent bullet lists read back as one |

## Not a gap in the tree

`pos` has djot.js's shape with two differences in its values.

- Columns and offsets count bytes; djot.js counts UTF-16 code units. The
  two agree on ASCII text. Converting needs the text, which a `Doc.t`
  does not keep and a `Source.t` does.
- A node's range is the one `Doc.textloc` gives, by the rules of
  `260916.plan.source-locations.md`, which differ from djot.js's (a
  block's range there usually includes its trailing newline).
