---
ai-disclosure: ai-generated
date: 2026-08-05
---
# Handover: djot.v state as of 2026-08-05

Where the verified-djot project stands, for whoever (human or agent)
picks it up next. The research background is
`reference/Formalizing djot in Rocq.v2.md`; the staged plan is
`.project/260802-plan.ai-generated.md`. This file records what actually
exists, how to drive it, and what to watch out for.

## Status at a glance

- Phase 0 (infrastructure) **done**; Phase 1 (wf AST, renderer, roundtrip)
  **core done**, growing construct by construct.
- Parser covers: paragraphs, thematic breaks, fenced code/raw blocks,
  **block quotes** (nested, with lazy continuation), **headings**
  (multi-line, interruptible; no section/id pass yet).
- Theorems, all axiom-free (`Print Assumptions` closed), zero `Admitted`:
  - `wf_parse` (Wf.v): every parser output is well-formed, for all inputs.
  - `wf_complete_false` (Wf.v): wf is *not* the image of `parse_doc` — the
    gap is construct coverage, not a missing wf condition.
  - `roundtrip_blocks` (Roundtrip.v): `parse (render (doc_of_cblocks cbs))
    = doc_of_cblocks cbs` — exact equality on canonical blocks.
  - `quote_uniformity` (Parser.v): prefixing every line with `"> "` parses
    to that document wrapped in a quote. No hypotheses, every construct.
    This is Phase 2's uniformity statement, arriving early.
  - `many_fuel_stable` (Spike.v): the Spike A verdict — fuel + discharge
    lemmas, not well-founded recursion.
- Differential corpus (djot.js's 287 usable cases): gallina 47, djot.js
  287 (its own corpus), djoths 262. The 25 djoths divergences are
  adjudicated in `.project/oracle-disagreements.md` — djot.js is the sole
  authority (upstream README: djoths is not kept up to date).
- Corpus numbers are a health check, not the goal — the standing priority
  is good code and proof engineering over conformance chasing.
  `block_quote.test` is 12/15; the 3 misses need inline emphasis and
  heading ids, and the block structure is right in all of them.
  Headings moved the number by zero on purpose: their HTML cannot match
  djot.js until section wrapping and auto-identifiers exist.

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
      └ Parser.v    step (per-line transition) + finish; parse_lines folds
                    them; pstate = PPara | PFence | PQuote (container
                    stack); equation lemmas are the proof interface
          ├ Wf.v        wf predicate + state_wf invariant + wf_parse
          ├ Html.v      HTML renderer (djot.js serialization is authority)
          └ Render.v    cblock canonical view + cb_ok + line renderer
              └ Roundtrip.v  split_render / parse_cblock / render agreement
```

Load-bearing decisions:

- **Proofs never unfold the parser.** Wf/Roundtrip only rewrite with
  Parser.v's equation lemmas (`step_*`, `parse_lines_step`,
  `parse_lines_text`, `_cont_seed`, `_para_seed`, `_fence_*`). This is
  why re-proving after refactors has been mechanical. Keep it that way.
- **The state is a container stack, and `step` is its transition.** This
  is deliberately Phase 2's `BlockSpec` shape (`continue`/`close`/
  `finalize` rolled into one function) so that phase is a refactor of a
  working design, not a rewrite.
- **Nesting and uniformity come from re-entering `classify`.** A quote
  strips its prefix and runs `step` on the enclosed line, so a
  container's contents take the same path as the top level. That is
  what makes `quote_uniformity` hypothesis-free — and what a new
  container should copy.
- **Fuel exists but never escapes.** Quote descent recurses on the
  *line*, not the state, so it is not structural. `step_fuel` takes
  fuel; `step` fixes it at the line's length (enough by
  `classify_quote_length`) and `step_fuel_enough` discharges it. No
  statement outside Parser.v mentions fuel — keep it that way when the
  next container lands.
- **The djot renderer is line-valued** (`render_block_lines`), because
  block structure *is* line structure: a quote's rendering is its
  contents' lines with a prefix. `sep_lines` is the one layout function,
  shared by documents and container contents.
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

## The extension recipe (proven four times: thematic breaks, code fences, block quotes, headings)

To add a block construct:

1. `Line.v` — recognizer + `line_kind` case (+ canonical-form lemmas).
2. `Parser.v` — `step` branch + its equation/seed lemmas.
3. `Wf.v` — case in `step_fuel_wf` (and `wf_block` if new AST shape),
   plus the matching case in `step_fuel_supported`.
4. `Render.v` — `cblock` constructor, `cb_lines`/`cb_ast`/`cb_ok` case,
   `render_block_lines` case.
5. `Roundtrip.v` — one case each in `cb_ok_lines_ok`, `parse_cblock`,
   `render_cb_lines`.

For a *container* specifically, add to that: a `pstate` constructor, its
cases in `finish`/`lazy_ok`/`feed_lazy`, and the `state_wf` clause.
Block quotes are the worked example throughout.

## Rocq gotchas already paid for (do not rediscover)

- `destruct ... eqn:` substitutes in **hypotheses too** (Rocq 9) — drop
  follow-up rewrites that expect the term still there.
- `simpl` over-reduces: it unfolds `Ascii.eqb` on literals into bit
  matches and nested-inductive definitions into un-unifiable match
  towers. Use definitional equation lemmas + targeted `rewrite`, or `cbn
  [whitelist]`. When a rewrite fails mysteriously, the head is often an
  `app` that needs `cbn [app]` to become a `cons`.
- With `string_scope` open, `++` on lists silently parses as
  `String.append` — annotate list appends `%list`. The reverse bites too:
  a `%list` annotation scopes the *whole* expression, so a string `++`
  inside a lambda under it needs its own `%string`.
- **Mutual `Fixpoint ... with ...` is rejected** for both `block` (through
  `list (node block)`) and `cblock` (through `list cblock`): the cross-call
  argument is not a subterm of the *other* function's principal argument.
  Verified, not assumed. Hence the hand-inlined fixpoints everywhere, each
  paired with an equation lemma proved by `change` + induction, and
  `cblock_ind2` for the induction the generated principle cannot do.
- `rewrite last_map` needs the default to match syntactically; `last l d`
  is default-independent on nonempty `l` (`last_default`) — rewrite with
  that first.
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

1. **The whole-document pass.** Headings parse but produce no `Section`
   wrapping and no `id`s. Both are order-dependent computations over the
   finished block list — level-driven section nesting, and identifier
   dedup with `-1`/`-2` suffixes. Reference definitions and footnotes
   want the same pass (they are block syntax that produces no block, only
   side-table entries), so build it once for all four. It must sit
   *after* `parse_lines`, never inside the fold: that separation is what
   Phase 3's locality theorem depends on.
   Note djot.js only wraps sections at the top level — inside a quote a
   heading gets a bare `<h1 id=...>`. Check that before designing.

2. **Lists** — the last real container, and bigger than the plan's
   one-liner. Budget it as four sub-problems, not one:
   - indent-based continuation (`indent > list.indent`, or blank), which
     is what finally forces an indent notion on `pstate`;
   - `list` + `list_item` as *two* nested containers;
   - tight/loose, which is a stateful rule: a blank line sets a flag on
     the enclosing list, and any later event that is not a list boundary
     turns the list loose (djot.js `parse.ts` ~line 1237). Our fold can
     carry this in `PList` state since the list is only emitted on close
     — no retroactivity needed.
   - marker styles and their narrowing across items (`i.` is roman *and*
     alpha until a sibling disambiguates). The plan already files this
     under Phase 3's "small combinatorial specs"; it can be deferred by
     doing bullet lists first.
3. **SPEC-GAP findings** (also in oracle-disagreements.md): tilde fences
   are undocumented in the prose spec; table separator-cell trimming is
   ambiguous (djot.js does not trim). The formalized spec decides both
   djot.js's way; consider filing upstream doc issues.
4. **Indentation is the one known-incomplete area.** Two instances:
   - Indented code fences: the recognizer accepts leading ws but content
     is not de-indented (djot.js strips the fence's indent).
   - Block quotes strip `>` plus *at most one* whitespace, so `>     a`
     keeps four spaces where djot.js's `skipSpace` drops them for
     paragraph (Inline) content while *preserving* relative indent for
     verbatim (Text) content. The current rule is right for `"> "` and
     for fence content, wrong for over-indented paragraph lines.
   - Headings strip the hashes plus at most one whitespace, so `#   a`
     has the same over-indent behaviour as `>   a`.
   Both want the same fix: an indent notion on the container stack, which
   is what lists will force. Deliberately not patched piecemeal.

5. **Empty containers sit outside the canonical view.** `>` parses to
   `BlockQuote []` and `#` to `Heading _ []` (both correct — djot.js
   agrees, and `wf_block` allows them), but `cb_ok` rejects both because
   neither has a rendering to invert. Harmless today; revisit if the
   roundtrip fragment is ever claimed to be the parser's whole image.
7. **Inline parsing** is untouched: paragraphs are Str/SoftBreak only.
   Phase 3 formalizes djot.js's opener-stack single pass (not djoths's
   backtracking combinators) — see the plan.
8. **Deferred render details**: HTML for lists/tables/headings are TODO
   stubs in Html.v; raw block passthrough is html-only.
9. Corpus gains now come mostly from constructs with inline content, so
   expect the number to plateau until Phase 3 starts.

## File-by-file (theories/)

| File | Contents | Key theorem/lemma |
|---|---|---|
| Strings.v | ws/blank, rev, split/join + inversion | `split_join_line`, `split_join_nl` |
| Line.v | `line_kind`, thematic/fence/quote/heading recognizers | `classify_canonical_heading`, `classify_quote_length` |
| Parser.v | `pstate` stack, `step`/`finish`, equations, examples | `quote_uniformity`, `step_fuel_enough` |
| Ast.v | full AST (djoths AST.hs transcription) | — |
| Wf.v | wf predicate, canonicality, `state_wf` | `wf_parse`, `wf_complete_false` |
| Render.v | `cblock`, `cb_ok`, `render_block_lines`, `cblock_ind2` | — |
| Roundtrip.v | split/parse/render agreement | `roundtrip_blocks` |
| Html.v | HTML renderer (djot.js-faithful) | — |
| Spike.v | Spike A: fuel + discharge lemmas | `many_fuel_stable` |

Commit history tells the story: `7104129` scaffold → `c220897`
adjudication → `420fa7c` AST → `87db4d6` wf → `542e493` roundtrip →
`fc1237a` restructure/classifier/thematic → `376ea05` code fences →
`2b9eccd` wf completeness → `1fb1a1f` container stack + block quotes →
`1978716` quote roundtrip + line renderer → `b54876a` headings.
