---
ai-disclosure: ai-generated
date: 2026-08-02
---
# Handover: djot.v state as of 2026-08-02

Where the verified-djot project stands after its first working day, for
whoever (human or agent) picks it up next. The research background is
`reference/Formalizing djot in Rocq.v2.md`; the staged plan is
`.project/260802-plan.ai-generated.md`. This file records what actually
exists, how to drive it, and what to watch out for.

## Status at a glance

- Phase 0 (infrastructure) **done**; Phase 1 (wf AST, renderer, roundtrip)
  **core done**, growing construct by construct.
- Parser covers: paragraphs, thematic breaks, fenced code/raw blocks.
- Theorems, all axiom-free (`Print Assumptions` closed), zero `Admitted`:
  - `wf_parse` (Wf.v): every parser output is well-formed, for all inputs.
  - `roundtrip_blocks` (Roundtrip.v): `parse (render (doc_of_cblocks cbs))
    = doc_of_cblocks cbs` — exact equality on canonical blocks.
  - `many_fuel_stable` (Spike.v): the Spike A verdict — fuel + discharge
    lemmas, not well-founded recursion.
- Differential corpus (djot.js's 287 usable cases): gallina 38, djot.js
  287 (its own corpus), djoths 262. The 25 djoths divergences are
  adjudicated in `.project/oracle-disagreements.md` — djot.js is the sole
  authority (upstream README: djoths is not kept up to date).
- Corpus numbers are a health check, not the goal — the standing priority
  is good code and proof engineering over conformance chasing.

## How to drive it

```
make build      # dune build: theory, proofs, extraction, harness
make test       # three-way differential run over djot.js/test/*.test
make baseline   # oracle-vs-oracle report -> .project/baseline-report.txt
make oracles    # one-time: npm build djot.js, cabal build djoths
```

Selective runs: `dune exec harness/main.exe -- --engines gallina --verbose
djot.js/test/para.test`. Mismatches are data (exit 0); only engine errors
fail. Cases with `p`/`a` options are skipped; `!`-filter cases dropped.

Editor: VsRocq; `_CoqProject` maps both `theories/` and
`_build/default/theories` to `DjotV` — run `dune build` first so
inter-file `Require`s resolve.

## Architecture (the part worth internalizing)

Dependency chain, one concern per file:

```
Strings.v   byte-string utilities + all their lemmas (split/join inversion)
  └ Line.v      line_kind classifier — THE prefix-determinism seam
      └ Parser.v    fold over classified lines; pstate = PPara | PFence;
                    equation lemmas are the proof interface
          ├ Wf.v        wf predicate + state_wf invariant + wf_parse
          ├ Html.v      HTML renderer (djot.js serialization is authority)
          └ Render.v    cblock canonical view + cb_ok renderability
              └ Roundtrip.v  split_render / parse_sep / render agreement
```

Load-bearing decisions:

- **Proofs never unfold the parser.** Wf/Roundtrip only rewrite with
  Parser.v's equation lemmas (`parse_lines_text`, `_cont_seed`,
  `_para_seed`, `_fence_*`). This is why re-proving after refactors has
  been mechanical. Keep it that way.
- **Renderability is phrased through the classifier**: a canonical
  paragraph's first line must `classify` as `KText`; interior lines merely
  nonblank (= the no-interruption rule); last line pre-stripped. A
  canonical code block's content must not close a 3-backtick fence.
  Canonicality-in-the-hypothesis is what makes roundtrip *exact* equality
  with no quotient.
- **Fence content is never classified** — only close-tested. Verbatimness
  is structural, not a side condition.
- The split/join inversion needs only: all lines newline-free, final line
  nonempty. (Weakened for blank code-content lines; don't re-strengthen.)

## The extension recipe (proven twice: thematic breaks, code fences)

To add a block construct:

1. `Line.v` — recognizer + `line_kind` case (+ canonical-form lemmas).
2. `Parser.v` — parser branch + its equation/seed lemmas.
3. `Wf.v` — case in `parse_lines_wf` (and `wf_block` if new AST shape).
4. `Render.v` — `cblock` constructor, canonical rendering, `cb_ok`.
5. `Roundtrip.v` — one case each in `cb_ok_lines_ok`, `parse_sep`,
   `render_djot_cblocks`.

## Rocq gotchas already paid for (do not rediscover)

- `destruct ... eqn:` substitutes in **hypotheses too** (Rocq 9) — drop
  follow-up rewrites that expect the term still there.
- `simpl` over-reduces: it unfolds `Ascii.eqb` on literals into bit
  matches and nested-inductive definitions into un-unifiable match
  towers. Use definitional equation lemmas + targeted `rewrite`, or `cbn
  [whitelist]`. When a rewrite fails mysteriously, the head is often an
  `app` that needs `cbn [app]` to become a `cons`.
- With `string_scope` open, `++` on lists silently parses as
  `String.append` — annotate list appends `%list`.
- Literal-headed appends make associativity definitional ("``` ++ x`"
  reduces), which lets 256-way ascii destructs close by `reflexivity`
  (`fence_block_wf`, `render_fence_block`).
- Debugging: replay a failing rewrite chain in a scratch `.v` against
  `_build/default/theories` with `match goal with |- ?G => idtac G end`.

## Toolchain facts

- opam switch `rocq-9`; the `coq` compat package provides `coqc` shims for
  dune's Coq mode and **pinned Rocq 9.2.0 down to 9.1.1** (acceptable; be
  aware before upgrading).
- Dune stanzas need explicit `(theories Stdlib)`.
- djoths's executable is `djoths`, not `djot`; locate with
  `cabal list-bin exe:djoths` (bare `djot` hits a cabal bug).
- djot.js oracle = `harness/oracles/djotjs.mjs` over the built
  `djot.js/lib`.

## Open threads, in rough priority order

1. **Next construct — pick one:**
   - *Block quotes*: first true container; starts turning `pstate` into
     the Phase 2 container stack. Structurally the most valuable.
   - *Headings*: forces the whole-document auto-identifier/section pass —
     the first thing that must live outside the locality boundary (keep it
     a separate pass after `parse_lines`; do not thread it through the
     fold).
2. **SPEC-GAP findings** (also in oracle-disagreements.md): tilde fences
   are undocumented in the prose spec; table separator-cell trimming is
   ambiguous (djot.js does not trim). The formalized spec decides both
   djot.js's way; consider filing upstream doc issues.
3. **Indented code fences**: recognizer accepts leading ws but content is
   not de-indented (djot.js strips the fence's indent). Known-incomplete;
   revisit when containers introduce indent handling properly.
4. **Inline parsing** is untouched: paragraphs are Str/SoftBreak only.
   Phase 3 formalizes djot.js's opener-stack single pass (not djoths's
   backtracking combinators) — see the plan.
5. **Deferred render details**: HTML for lists/tables/headings are TODO
   stubs in Html.v; raw block passthrough is html-only.
6. Corpus gains now come mostly from constructs with inline content, so
   expect the number to plateau until Phase 3 starts.

## File-by-file (theories/)

| File | Contents | Key theorem/lemma |
|---|---|---|
| Strings.v | ws/blank, rev, split/join + inversion | `split_join_line`, `join_nl_last` |
| Line.v | `line_kind`, thematic + fence recognizers | `classify_backtick_fence` |
| Parser.v | `pstate`, `parse_lines`, equations, examples | `parse_lines_para_seed`, `_fence_seed` |
| Ast.v | full AST (djoths AST.hs transcription) | — |
| Wf.v | wf predicate, canonicality, `state_wf` | `wf_parse` |
| Render.v | `cblock`, `cb_ok`, djot renderer | — |
| Roundtrip.v | split/parse/render agreement | `roundtrip_blocks` |
| Html.v | HTML renderer (djot.js-faithful) | — |
| Spike.v | Spike A: fuel + discharge lemmas | `many_fuel_stable` |

Commit history tells the story: `7104129` scaffold → `c220897`
adjudication → `420fa7c` AST → `87db4d6` wf → `542e493` roundtrip →
`fc1237a` restructure/classifier/thematic → `376ea05` code fences.
