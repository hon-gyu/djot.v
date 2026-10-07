---
ai-disclosure: ai-generated
---
# Holes

The extension is implemented, and its rules are stated in
`theories/spec/holes.dj`. That file is the reference from now on. This
note is the work log behind it: what was built, where it departs from
[[261007.plan.holes]], and what is still open. It is not updated when
the rules change.

Status: **implemented** (2026-10-07), v1, on branch `hy/holes`. The
setting, scanner states, proofs, extraction, the OCaml switch
`Profile.with_ext_holes` and the Python `ast.ExtHole` are built.
`dev/check/Hole.v` pins every decision, and the roundtrip test has a
holes pool (`make roundtrip-holes`).

## What was built

- `Ast.Hole (s : string)`, an inline leaf. `Document` and
  `reference_text` read it as contributing no text; HTML writes
  `<code data-hole="">s</code>`; the djot renderer writes `%{`, the
  payload through `hole_src`, then `}`.
- `dc_holes` in the inline table, `with_holes`, and `holes_enabled`.
  `%` is dispatched only after the table lookup, so a table that spells
  a row with `%` keeps it and has no holes. `drow_ok` was left alone;
  no table in the repository uses `%`.
- Two scanner states. `IPercent` holds a `%` until the next byte, as
  `IBang` holds a `!`. `IHole depth esc src txt sh o` is the candidate:
  `src` is the raw source since `%{`, decoded by `hole_text` only at the
  close, so the located start is computed from the source length as
  dollar math's is.
- `needs_escape` claims `%` while holes are on, so canonical text never
  spells `%{`. The roundtrip theorem is stated for every table, so it
  covers the holes table with no new case. `in_alphabet` excludes `%`
  under holes, which keeps the precedence theorem's alphabet free of it.
- Proof work, by file: `Wf.v` (the invariant and its preservation
  through step, break, resolve and finish), `InlineBuffer.v` (the buffer
  simulation), `InlineLocated.v` (erasure), `InlineSpans.v` (the span
  invariant), `InlineInvert.v` (commutation with an output prefix, and
  `ilead_plain`), `InlinePrecedence.v` (`ilead_text`). About 380 lines
  of theory against dollar math's 760; no new canonical constructor was
  needed, as for math.

## Where it departs from the plan

**The candidate is nested, not a frame stack.** The plan's "Linear
time" section proposed a stack of frames with one shared depth so that
open holes cost one step per byte. Step 0 measured the existing
scanner first: nested link destinations already chain their ordinary
readings the same way, and `[a](b` repeated is superlinear today
(`convert --time`: 0.25 s at 1000 repetitions, 24 s at 8000). Holes
were built in the `IDollarMath` shape, which the proofs could follow
case by case. The two shapes give the same results; only the cost
differs.

Measured through the Python package (wasm), holes on:

| input | n = 250 | 500 | 1000 |
| --- | --- | --- | --- |
| `%{ x ` repeated | 0.50 s | 2.2 s | 9.4 s |
| the same, holes off | 7 ms | 12 ms | 19 ms |
| `%{` repeated | | 13 ms (1000) | 54 ms (4000) |

`%{` repeated stays linear because the `{` after each `%` starts an
attribute candidate whose ordinary reading resolves the next `%` to
text. `%{ x ` defeats that, and each open hole adds a link to the chain.
The frame stack remains the fix; it changes the state's shape and so
the five proof files above.

**D6 was amended in review: an empty hole is a hole.** As first built,
an empty or blank payload fell back to the ordinary reading, in which
`{}` is an empty attribute block that djot drops, so `%{}` rendered as
`%`, not as the text the plan said. Review chose the simpler rule
instead: the matching `}` always closes a hole, and `%{}` is `Hole ""`
for the consumer to reject. The check and its case in each proof were
deleted.

**D10 has no code.** The block hole is the consumer's reading of a code
block in language `%`, so nothing in the parser changed for it.

## Found on the way

- `ocaml/kernel` had not been regenerated for `1e74e28` (destination
  escapes). The kernel commit on this branch carries that change too,
  and `ocaml/test/to_source.expected` moved with it.
- The wasm build refuses a paragraph of about 2000 inline nodes or more
  ("nested too deeply"), with or without holes: `*y* ` repeated 2000
  times fails on main. Not a holes issue; noted because the timing runs
  hit it.
- The test-suite diff against expected HTML has the same two
  mismatches as main.

## Open

1. The baseline table checked against djot.js (its `lib/` was not built
   in this checkout).
2. The frame stack, if linear cost on hostile input matters before the
   destination chain is fixed too.
3. `hole_src` escapes every brace, so a payload with balanced braces
   renders as `%{ \{x\} }`. Leaving balanced braces bare is a renderer
   refinement for [[261007.plan.irredundant-escapes]].
4. Kinds (`%*{`, `%?{`), holes in attribute values, and an evaluator,
   all out of v1 by the plan.
