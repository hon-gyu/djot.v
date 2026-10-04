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
| Bullet list `style` | the marker, `-`, `+` or `*` | absent | the marker on `BulletList`; the same field would remove the round-trip exception that two adjacent bullet lists read back as one |

## Closed

### Derived identifiers (2026-10-04)

`doc_auto_identifiers` now lists the ids the document pass derived, in
document order, and no written one. Going through the headings and
sections in document order, the first with the next listed id is the one
it was derived for: a derived id differs from every id before its
heading, so a written id that repeats it comes later.

- `of_doc` writes a listed id under `autoAttributes`.
- `Doc.to_string` leaves out exactly the listed ids
  (`Render.drop_auto_ids`). Before, it left an id out when it equalled
  what the heading's text gives, which dropped a written `{#My-title}`
  above `# My title` and wrote out a derived `My-title-1`.

Not proved: that taking the listed ids off gives back the tree before
the pass. `Document.pass_erase` says so only for input with no written
heading id. The cases are kernel-checked examples
(`Render.render_doc_keeps_written_id` and the two after it,
`Document.written_id_repeats_derived`).

## Not a gap in the tree

`pos` has djot.js's shape with two differences in its values.

- Columns and offsets count bytes; djot.js counts UTF-16 code units. The
  two agree on ASCII text. Converting needs the text, which a `Doc.t`
  does not keep and a `Source.t` does.
- A node's range is the one `Doc.textloc` gives, by the rules of
  `260916.plan.source-locations.md`, which differ from djot.js's (a
  block's range there usually includes its trailing newline).
