# djot.v

A verified [djot](https://djot.net) parser in Rocq. Research plan:
`.project/260802-plan.ai-generated.md`; background:
`reference/Formalizing djot in Rocq.v2.md`.

## Layout

- `theories/` — the Gallina development (theory name `DjotV`).
  Currently the Phase 0 toy fragment (paragraphs) plus `Spike.v`, the
  fuel-vs-measure spike for `many`-style combinators.
- `harness/` — extraction (`Extract.v` → `core.ml`) and the OCaml
  differential test runner.
- `djot.js/`, `djoths/` — submodules: the two oracle implementations.
- `reference/` — spec and rationale documents.
- `.project/` — plan, oracle-disagreement log, reports.

## Requirements

- opam switch with Rocq 9.x, dune ≥ 3.20, and the `coq` compatibility
  package (dune's Coq mode still invokes `coqc`): `opam install coq`
- node ≥ 17 (djot.js oracle), GHC + cabal (djoths oracle)

## Use

```
make oracles    # one-time: build djot.js (npm) and djoths (cabal)
make build      # dune build: theory, proofs, extraction, harness
make test       # three-way differential run over the djot.js corpus
make baseline   # oracle-vs-oracle report -> baseline-report.txt
```

The harness compares the extracted Gallina parser against both oracles on
djot.js's `.test` corpus. Cases with `p`/`a` options (sourcepos, AST
output) are skipped; filter cases are dropped. Mismatches are data, not
failures — the exit code is nonzero only on engine errors.

Select engines or files:

```
dune exec harness/main.exe -- --engines gallina,djotjs --verbose \
  djot.js/test/para.test
```

## Editor

VsRocq (vsrocq-language-server is installed in the switch). `_CoqProject`
maps both the sources and dune's compiled `.vo` files:

```
-R theories DjotV
-R _build/default/theories DjotV
```

Run `dune build` first so inter-file `Require`s resolve in the editor.
