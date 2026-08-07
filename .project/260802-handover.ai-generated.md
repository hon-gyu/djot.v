---
ai-disclosure: ai-generated
date: 2026-08-07
authors: [claude/opus-5, claude/sonnet-5]
---
# Handover: djot.v state as of 2026-08-07

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
  (multi-line, interruptible), **bullet lists** (indent-based
  continuation, tight/loose, nesting), and the **whole-document pass**
  over the finished block list: auto-identifiers, implicit heading
  references, level-driven section nesting.
- Theorems, all axiom-free (`Print Assumptions` closed), zero `Admitted`:
  - `wf_parse` (Wf.v): every output of the line fold is well-formed, for
    all inputs.
  - `wf_doc_pass` / `wf_parse_doc` (Wf.v): the whole-document pass carries
    well-formedness through, so the guarantee still covers the real entry
    point. The section half needs a stack invariant (every open section's
    accumulator is nonempty, because it starts with its own heading);
    the identifier half needs `Ast.block_ind2`.
  - `wf_complete_false` (Wf.v): wf is *not* the image of `parse_blocks` —
    the gap is construct coverage, not a missing wf condition. The
    counterexample is a `Section`, which the line fold cannot emit
    (sections only come from the document pass, which runs after it).
  - `roundtrip_blocks` (Roundtrip.v): `parse_blocks (render_djot
    (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs` — exact equality on
    canonical blocks, at the line-fold layer. Carries a `no_nested_list
    cbs` hypothesis alongside `cb_ok`: `CList` exists as a canonical
    construct (`Render.v`, with a fully-proven `cb_ok`/`lines_ok`
    fragment and the hard supporting lemma `parse_cblock_pad`), but
    `parse_cblock`'s own item-sequencing induction for it isn't proven
    yet, so lists are excluded from this theorem specifically — see
    `.project/260807-list-roundtrip-indent-shift.ai-generated.md` for
    exactly what's left and why the rest didn't need re-deriving.
  - `pass_erase` (Document.v): the whole-document pass adds only
    structure erasure recovers — `undo_pass (doc_blocks (doc_pass bs))
    = bs` for input the pass has not already run on (`pristine`: no
    sections, no heading carrying an explicit id). Two halves:
    `undo_sectionize` is unconditional (sectionize only wraps), and
    `undo_assign_ids` is where `pristine` is actually needed.
  - `roundtrip_doc` (Roundtrip.v): the roundtrip at the real entry point
    — render, `parse_doc`, `undo_pass`, and you are back at the same
    blocks.
  - `quote_uniformity` (Parser.v): prefixing every line with `"> "` parses
    to that document wrapped in a quote. No hypotheses, every construct.
    This is Phase 2's uniformity statement, arriving early.
  - `many_fuel_stable` (Spike.v): the Spike A verdict — fuel + discharge
    lemmas, not well-founded recursion.
- Differential corpus (djot.js's 287 usable cases): gallina 75, djot.js
  287 (its own corpus), djoths 262. The 25 djoths divergences are
  adjudicated in `.project/oracle-disagreements.md` — djot.js is the sole
  authority (upstream README: djoths is not kept up to date).
- Corpus numbers are a health check, not the goal — the standing priority
  is good code and proof engineering over conformance chasing.
  `block_quote.test` is 13/15; both misses need inline emphasis.
  `headings.test` is 13/18; the remaining misses need block attributes
  (`{#id}`), footnotes, and inline links — the over-indentation miss is
  fixed (thread 2, done).
  `lists.test` is 16/33. The over-indentation misses are fixed; almost
  everything left is ordered-list markers (`1.`, `(a)`, roman numerals —
  Phase 3's combinatorial specs, thread 3), plus two loose-list misses
  that are an `<li><p>` HTML-rendering gap (thread 8), unrelated to
  indentation.

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
                    them; parse_blocks is the entry point; pstate = PPara
                    | PHeading | PFence | PQuote (container stack);
                    equation lemmas are the proof interface
          ├ Document.v  the whole-document pass: parse_doc = doc_pass ∘
          │             parse_blocks; ids, auto-references, sections
          │   ├ Wf.v      wf predicate + state_wf + wf_parse + wf_parse_doc
          │   └ Html.v    HTML renderer (djot.js serialization is authority)
          └ Render.v    cblock canonical view + cb_ok + line renderer
              └ Roundtrip.v  split_render / parse_cblock / render agreement
```

Two entry points, deliberately: `Parser.parse_blocks : string -> blocks`
is the line fold and the layer every structural theorem is stated
against; `Document.parse_doc : string -> doc` composes the pass on top
and is what Html.convert and the harness use.

Load-bearing decisions:

- **Proofs never unfold the parser.** Wf/Roundtrip only rewrite with
  Parser.v's equation lemmas (`step_*`, `parse_lines_step`,
  `parse_lines_text`, `_cont_seed`, `_para_seed`, `_fence_*`). This is
  why re-proving after refactors has been mechanical. Keep it that way.
- **The state is a container stack, and `step` is its transition.** This
  is deliberately Phase 2's `BlockSpec` shape (`continue`/`close`/
  `finalize` rolled into one function) so that phase is a refactor of a
  working design, not a rewrite.
- **Every state answers a line one of two ways: continue, or
  close-and-reopen.** `close_reopen st opened` is that second answer,
  shared by every state — `finish` supplies finalize, `open_kind` the
  reopening. A new container writes its *continuation* rule and inherits
  the rest. The one exception is `PFence`, which consumes its closing
  line rather than reprocessing it; that is what verbatim means.
- **The two wrappers take the opening already computed.** `close_reopen`
  and `open_quote` are deliberately not recursive: an earlier attempt
  made the opener mutually recursive with `step_fuel`, which cost a
  second unit of fuel per nesting level and broke `step`'s bound of
  `S (String.length l)` — `> > deep` no longer had enough. Fuel must
  decrement exactly once per level. `step_fuel_stable` is what catches
  this; if it starts failing after a change here, that is the reason.
- **Nesting and uniformity come from re-entering `classify`.** A quote
  strips its prefix and runs `step` on the enclosed line, so a
  container's contents take the same path as the top level. That is
  what makes `quote_uniformity` hypothesis-free — and what a new
  container should copy.
- **Fuel exists but never escapes, and its measure is two-part.** A
  quote descent shortens the *line* (`classify_quote_length`); a list
  item's content line is handed to the inner container *unchanged* and
  shortens the *state* instead. So the measure is
  `String.length l + pstate_depth st`, and `step` fixes fuel at `S` of
  it. A new container that descends without consuming a prefix must keep
  `pstate_depth` honest. `step_fuel_stable` / `step_fuel_enough`
  discharge it; no statement outside Parser.v mentions fuel — keep it
  that way.
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
- **Tight/loose is an event rule, not a tree rule.** djot.js arms a
  `blanklines` flag on a blank line and loosens the list at the next
  event that is neither a blank nor a list boundary (parse.ts ~1237).
  So `- a`, blank, `  - b` stays *tight*, even though a blank separates
  the item's two children — the next event opens a list. The textbook
  "blank line between block children" rule gets that case wrong. The
  flags live in `list_state` because a list is only emitted when it
  closes, so nothing is revised retroactively.
- **A list marker never interrupts an open paragraph**, same as every
  other block opener. `- a` / `  - b` is one item whose paragraph runs
  on, not a nested list — nesting needs the blank line first. This kills
  a whole class of interaction before it starts.
- **The pass is erasable, and that is a standing obligation.**
  `Document.undo_pass` inverts it, and `pass_erase` says so. Anything
  new added to the pass must either extend `undo_pass` or be shown not
  to touch the block tree — otherwise `roundtrip_doc` silently stops
  covering it. Note `undo_pass` strips the id *before* handing a
  section's attributes back to its heading; that ordering is what lets
  one traversal undo both halves.
- **The whole-document pass is a separate file, run after the fold.**
  Anything order-dependent over the finished block list lives in
  Document.v: identifier uniqueness, implicit heading references, section
  nesting — and reference definitions and footnotes when they land, since
  they are the same shape (block syntax producing no block, only
  side-table entries). Keeping it out of the fold is what Phase 3's
  locality theorem needs. Sectioning is top-level only, matching djot.js;
  identifiers are assigned everywhere and share one counter.
- **`Ast.block_ind2` is the induction principle for the AST.** Rocq's
  generated `block_ind` will not descend through `list (node block)`, so
  every proof over blocks needs it. Its list/table cases carry no
  hypothesis for the blocks they hold — unsound to use there, and
  unprovable rather than silently wrong, which is the point.
- **Recursion over the AST goes on `block`, not `node block`.** The guard
  checker will not follow `list (node block)` from a `node block`
  argument, so `Html.render_block` and `Document.assign_ids` both take the
  payload with the node's attributes passed alongside. Learned twice;
  reach for this shape first.
- **Fence content is never classified** — only close-tested. Verbatimness
  is structural, not a side condition.
- The split/join inversion needs only: all lines newline-free, final line
  nonempty. (Weakened for blank code-content lines; don't re-strengthen.)

## The extension recipe (proven four times: thematic breaks, code fences, block quotes, headings)

A construct with a whole-document component adds a sixth step: its case
in Document.v, plus the matching wf-preservation lemma in Wf.v's
"whole-document pass" section.

To add a block construct:

1. `Line.v` — recognizer + `line_kind` case (+ canonical-form lemmas).
2. `Parser.v` — `step` branch + its equation/seed lemmas. A container
   writes only its continuation rule; `close_reopen` handles the rest.
3. `Wf.v` — case in `step_fuel_wf` (and `wf_block` if new AST shape),
   plus the matching case in `step_fuel_supported`, `finish_wf`,
   `feed_lazy_wf` and their `_supported` twins.
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
- **`cbn` on a recursive definition reduces the recursive call too**, so
  an induction hypothesis about it stops matching. This is the same trap
  as `simpl` over-reducing, and the same fix: an equation lemma per
  branch (`close_ge_singleton`/`close_ge_cons`, `stack_erase_cons`,
  `sect_ok_cons`), rewritten with rather than computed through. Watch for
  it whenever a definition has both a `[x]` and an `x :: rest` pattern —
  `cbn` will happily unfold two levels.
- Debugging: replay a failing rewrite chain in a scratch `.v` against
  `_build/default/theories` with `match goal with |- ?G => idtac G end`.
  The rocq-mcp server's *interactive* tools (`rocq_start`, `rocq_check`,
  `rocq_step_multi`) need `pet`/coq-lsp, which is not installed here —
  they return `reason: "unavailable"`. Only `rocq_compile_file` works,
  which is what `dune build` already gives you.

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

1. **Two loose ends around the document pass.**
   - `unique_id`'s fuel has no discharge lemma. The argument is in the
     comment (n taken ids, n+2 distinct candidates); proving it needs
     pigeonhole plus injectivity of `nat_str`, and would buy the real
     statement — the assigned identifier is fresh. Compare
     `Parser.step_fuel_enough`.
   - `Ast.block_ind2` has no induction hypotheses for the list and table
     constructors. Mechanical to fill in; do it when lists land, not
     before.

2. **Indentation — done.** `open_kind`'s `KText` case, the `PPara`
   continuation branch, and `push_text` (which covers both `PHeading`'s
   own KText branch and its KHeading-continuation branch) now
   `drop_leading_ws` the line before storing it, matching djot.js's
   unconditional `skipSpace` before inline content. One fix, because
   quotes and lists both re-enter `step` on their enclosed line through
   a fresh `PPara []` — the strip happens once, at that shared seam, and
   covers all four faces (top-level paragraphs, quotes, headings, list
   items) without touching Line.v or the container states themselves.
   `line_ok` (Strings.v) gained a third conjunct,
   `String.eqb (drop_leading_ws l) l`, so `para_ok`/`heading_ok`
   (Render.v, unchanged — both already route through `line_ok`) now
   reject the leading-whitespace lines the parser can no longer produce;
   `Roundtrip.v`'s seed lemmas carry a `map drop_leading_ws` that
   collapses back to the identity via the new
   `forallb_line_ok_map_drop_leading_ws`. Fence content is untouched —
   verbatim stays verbatim.

3. **Lists, the parts deliberately left out.**
   - `CList` now exists (`Render.v`), with `cb_lines`/`cb_ast`/`cb_ok`
     fully proven (`cb_ok_lines_ok` covers it) and the hard supporting
     lemma for item content (`parse_cblock_pad`, Roundtrip.v) proven and
     axiom-free. What's still missing is `parse_cblock`'s own item-
     sequencing induction (open on a marker, thread tight/loose through
     a run of siblings, close) — `roundtrip_blocks`/`roundtrip_doc`
     carry a `no_nested_list` hypothesis excluding `CList` until that
     lands. Precise remaining shape, and why two exclusion predicates
     (`list_content_safe`, `no_nested_list`) exist and how to retire
     them: `.project/260807-list-roundtrip-indent-shift.ai-generated.md`.
   - Nested lists specifically need one more theorem beyond that
     (an indent-shift argument through `PList`'s step lemmas) — same doc,
     "Finding 1."
   - Ordered lists: markers whose style is ambiguous until a sibling
     disambiguates (`i.` is roman *and* alpha). Filed under Phase 3's
     "small combinatorial specs". `Line.list_marker` handles bullets
     only, and says so.
   - `list` and `list_item` are one `PList` constructor rather than two
     nested containers. They only differ when a sibling marker arrives,
     which the single constructor handles directly; split them if
     ordered lists or definition lists make it pay.
4. **SPEC-GAP findings** (also in oracle-disagreements.md): tilde fences
   are undocumented in the prose spec; table separator-cell trimming is
   ambiguous (djot.js does not trim). The formalized spec decides both
   djot.js's way; consider filing upstream doc issues.
5. **Indented code fences.** The recognizer accepts leading whitespace
   on a fence opener, but content is not de-indented (djot.js strips the
   fence's own indent from each content line). Deliberately not folded
   into thread 2's fix: fence content is verbatim by design (never
   classified), so this wants its own indent-tracking rule, not
   `drop_leading_ws`.

6. **Empty containers sit outside the canonical view.** `>` parses to
   `BlockQuote []` and `#` to `Heading _ []` (both correct — djot.js
   agrees, and `wf_block` allows them), but `cb_ok` rejects both because
   neither has a rendering to invert. Harmless today; revisit if the
   roundtrip fragment is ever claimed to be the parser's whole image.
7. **Inline parsing** is untouched: paragraphs are Str/SoftBreak only.
   Phase 3 formalizes djot.js's opener-stack single pass (not djoths's
   backtracking combinators) — see the plan.
8. **Deferred render details**: HTML for lists and tables are TODO stubs
   in Html.v; raw block passthrough is html-only. Block attributes now
   render on every tag (`render_attrs`), but nothing except the pass
   produces them — `{#id}` block-attribute syntax is unparsed.
9. Corpus gains now come mostly from constructs with inline content, so
   expect the number to plateau until Phase 3 starts.

## File-by-file (theories/)

| File        | Contents                                                     | Key theorem/lemma                               |
| ----------- | ------------------------------------------------------------ | ----------------------------------------------- |
| Strings.v   | ws/blank, rev, split/join + inversion                        | `split_join_line`, `split_join_nl`              |
| Line.v      | `line_kind`, thematic/fence/quote/heading/bullet recognizers | `classify_quote_length`, `classify_list_length` |
| Parser.v    | `pstate` stack, `step`/`finish`, equations, examples         | `quote_uniformity`, `step_fuel_enough`          |
| Html.v      | HTML renderer, incl. tight/loose list items                  | —                                               |
| Ast.v       | full AST (djoths AST.hs transcription)                       | `block_ind2`                                    |
| Document.v  | ids, auto-references, sections; `parse_doc`; erasure         | `pass_erase`, `undo_sectionize`                 |
| Wf.v        | wf predicate, canonicality, `state_wf`, pass preservation    | `wf_parse`, `wf_parse_doc`, `wf_complete_false` |
| Render.v    | `cblock`, `cb_ok`, `render_block_lines`, `cblock_ind2`       | —                                               |
| Roundtrip.v | split/parse/render agreement                                 | `roundtrip_blocks`, `roundtrip_doc`             |
| Spike.v     | Spike A: fuel + discharge lemmas                             | `many_fuel_stable`                              |

Commit history tells the story: `7104129` scaffold → `c220897`
adjudication → `420fa7c` AST → `87db4d6` wf → `542e493` roundtrip →
`fc1237a` restructure/classifier/thematic → `376ea05` code fences →
`2b9eccd` wf completeness → `1fb1a1f` container stack + block quotes →
`1978716` quote roundtrip + line renderer → `b54876a` headings →
whole-document pass (sections, identifiers, implicit references) →
erasure + doc-level roundtrip → `close_reopen`/`open_quote` factoring →
bullet lists.
