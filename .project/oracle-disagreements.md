# Oracle disagreements

Append-only adjudication log: cases where djoths's output differs from
djot.js's expected corpus output (djot.js passes its own corpus 287/287, so
"expected" and "djot.js" coincide on this corpus).

Baseline established 2026-08-02 with `make baseline`
(djot.js @ v0.3.2 submodule, djoths @ 0.1.4.1 submodule; 287 cases run,
6 skipped for `p`/`a` options, filter cases dropped).
Full diffs: `.project/baseline-report.txt` (regenerate with `make baseline`).

Context for adjudication (djot README): current development is focused on
djot.js; djot.lua and probably djoths are not kept up to date with the
latest syntax changes. So "djoths-outdated" is the expected default verdict,
and djot.js is the authority wherever the two disagree.

Verdict legend:

- `render-only` — same parse, different HTML serialization; irrelevant to
  the parser formalization, but pick djot.js's serialization for ours.
- `djoths-outdated` — parse-level divergence where djoths implements an
  older syntax behavior; follow djot.js.
- `djoths-bug` — violates the prose spec directly.
- `SPEC-GAP` — the prose syntax reference is silent or ambiguous on the
  point; the corpus is the only authority. These are exactly the corners a
  formalized spec must decide explicitly — collect them as input to Phase 1+.

## Adjudicated 2026-08-02

| Case | Verdict | Notes |
|---|---|---|
| attributes.test:145 | render-only | HTML attribute *ordering* (`id key class` vs `class key id`); merged attributes identical |
| attributes.test:253 | djoths-outdated | failed multi-line block attribute (`{%`…) must fall back to a single paragraph including following lines; djoths splits it |
| attributes.test:327 | djoths-outdated | `<` not allowed in identifier: djot.js rejects `{#a<b}` as attribute → literal text; djoths accepts. Same root cause as spans.test:21/27 |
| attributes.test:346 | djoths-outdated | unclosed block attribute `{a=x` + next line: falls back to one merged paragraph in djot.js |
| attributes.test:362 | djoths-outdated | same, and the fallback paragraph cannot be interrupted — `# non-heading` stays paragraph text in djot.js; djoths parses a heading. Touches the no-paragraph-interruption invariant |
| block_quote.test:117 | render-only | djot.js emits no `<section>` wrapper for headings inside block quotes; djoths wraps. (Section-wrapping is a render policy, but it feeds auto-id assignment — see headings.test:138) |
| code_blocks.test:1 | djoths-outdated + SPEC-GAP | djot.js accepts `~~~` code fences; the prose syntax reference only documents backtick fences. Prose spec is behind the reference implementation |
| definition_lists.test:6 | djoths-outdated | definition content after blank line renders loose (`<dd><p>…`) in djot.js; djoths renders tight. Tightness computation for definition lists |
| definition_lists.test:113 | djoths-outdated | same tightness divergence |
| escapes.test:30 | djoths-outdated | `\` before end-of-input (no newline) is a hard break in djot.js; literal `\` in djoths |
| footnotes.test:1 | djoths-bug | second reference to the same note must not repeat `id="fnref1"` (duplicate DOM ids); djoths repeats it |
| footnotes.test:74 | djoths-bug | same duplicate-id issue for self-referencing notes |
| headings.test:36 | djoths-outdated | empty `#` continuation line inside a multi-line heading: djot.js joins with single newline; djoths keeps a blank line |
| headings.test:59 | djoths-outdated | auto-identifier for empty heading: djot.js `s-1`; djoths `sec`. Algorithm changed |
| headings.test:138 | djoths-outdated | uniqueness-suffix assignment order (`Foo-bar-1`/`-2` swapped); djot.js assigns in document order of the *headings* |
| headings.test:163 | djoths-bug | prose spec states `# Introduction[^1]` yields id `Introduction`; djoths yields `Introduction-1` |
| links_and_images.test:183 | djoths-outdated | reference definition with trailing junk (`"title"`) is invalid in djot.js → literal paragraph + targetless `<a>foo</a>`; djoths concatenates junk into the URL |
| links_and_images.test:192 | djoths-outdated | same with ` extra` (spec: no chunk of the URL may contain internal whitespace) |
| spans.test:21 | djoths-outdated | `{#a<b}` rejected as attribute → whole thing literal (no span); djoths accepts |
| spans.test:27 | djoths-outdated | same with inline formatting inside the brackets |
| spans.test:33 | djoths-outdated | unclosed attribute after `]`: djot.js → all literal; djoths emits an attribute-less `<span>` |
| tables.test:111 | djoths-outdated + SPEC-GAP | `| --- |` (spaces around dashes) is NOT a separator line in djot.js — cells render as em-dashes; djoths trims cells and sees a separator. The prose spec ("every cell consists of a sequence of one or more `-`") doesn't state whether cells are trimmed first; corpus says no trimming |
| task_lists.test:1 | render-only | task item HTML: djot.js plain `<input disabled>`; djoths `<label>` + li class. Parse identical |
| task_lists.test:17 | render-only | same |
| task_lists.test:38 | render-only | same (also confirms `-`/`+`/`*` marker change splits lists — both agree on the parse) |

## Consequences for the formalization

- Two SPEC-GAP findings so far — tilde fences (undocumented) and table
  separator-cell trimming (ambiguous). The relational spec must decide both;
  decide them djot.js's way and note the prose-spec deviation.
- attributes.test:362 is a live example of the paragraph-non-interruption
  invariant interacting with attribute-fallback — a good early test case for
  the Phase 2 prefix-determinism statement.
- Render-only rows mean the Phase 1 HTML renderer must copy djot.js's
  serialization choices (attribute order, section-wrapping policy, task-item
  markup), not djoths's, to keep the harness diff clean.
