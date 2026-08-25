# djot.v

A verified [djot](https://djot.net) parser in Rocq. 

## Layout

- `theories/` — the Gallina development (theory name `DjotV`).
  `Line.v` classifies a line, `Parser.v` steps the block state machine,
  `Render.v` prints a canonical document, `Roundtrip.v` relates them,
  `Document.v` is the whole-document pass, `Html.v` the HTML converter,
  `Generate.v` a typed enumerator that checks the roundtrip by
  computation. `Spike.v` is the Phase 0 fuel-vs-measure spike, kept as a
  record of that decision.
- `harness/` — extraction (`Extract.v` → `core.ml`) and the OCaml
  differential test runner.
- `djot.js/`, `djoths/` — submodules: the two oracle implementations.
- `reference/` — spec and rationale documents.
- `.project/` — plan, oracle-disagreement log, reports.

## Requirements

- opam switch with Rocq 9.x, dune ≥ 3.20, and the `coq` compatibility
  package (dune's Coq mode still invokes `coqc`): `opam install coq`
- node ≥ 17 (djot.js oracle), GHC + cabal (djoths oracle)

## Documentation

Build the reader-facing Rocqdoc site with:

```sh
make doc
open _build/doc/index.html
```