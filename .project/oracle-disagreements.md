---
ai-disclosure: autonomous
---
# Oracle disagreements

Append-only adjudication log: cases where djoths's output differs from
djot.js's expected corpus output (djot.js passes its own corpus 287/287, so
"expected" and "djot.js" coincide on this corpus).

Baseline established 2026-08-02 with `make baseline`
(djot.js @ v0.3.2 submodule, djoths @ 0.1.4.1 submodule; 287 cases run,
6 skipped for `p`/`a` options, filter cases dropped).
Full diffs: `baseline-report.txt` (regenerate with `make baseline`).

Context for adjudication (djot README): current development is focused on
djot.js; djot.lua and probably djoths are not kept up to date with the
latest syntax changes. So "djoths-outdated" is the expected default verdict,
and djot.js is the authority wherever the two disagree.

**What counts as authority here.** The engines and the syntax reference
say what the language *is*. The rationale
(`reference/djot-repo-readme.md` §Rationale, and behind it
`reference/beyond-markdown.md`) says what it is *for*: it decides cases
where the first three conflict or go silent on *why*, which is how the
`djotjs-bug` verdict below was reached. Note the ordering of the two
rationale sources. The README is the djot project's own and states
consequences directly; beyond-markdown is a 2017 essay predating djot,
and parts of it were dropped. Checked 2026-08-09: its tightness rule
(`:254`) is *existential* where the syntax reference's is universal, and
on its own worked example both engines contradict it. Cite the rationale
for principles, never for behaviour.

Verdict legend:

- `render-only` — same parse, different HTML serialization; irrelevant to
  the parser formalization, but pick djot.js's serialization for ours.
- `djoths-outdated` — parse-level divergence where djoths implements an
  older syntax behavior; follow djot.js.
- `djoths-bug` — violates the prose spec directly.
- `djotjs-bug` — djot.js contradicts the prose where djoths follows it.
  Rare, and it overrides the "djot.js is the authority" default above,
  which exists because djoths lags on syntax *changes* — not because
  djot.js cannot have a plain bug.
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

## Adjudicated 2026-08-08 — ours

First entry where *our* parser is the odd one out; the log's original
framing (djoths vs djot.js) assumed the Gallina parser had no opinion yet.

| Case | Verdict | Notes |
|---|---|---|
| `- - b` / `  - c` | **our bug** | A list nested on its parent's marker line: both oracles read one outer item containing a two-item inner list; ours reads a one-item inner list and swallows `- c` as that item's content |

Root cause: `step_fuel` descends into a marker's residue with
`step_fuel n' rest (PPara [])`, so a nested `open_list` records
`indent_of rest` — an indent measured in the *residue's* coordinates, not
the line's. For `- - b` the inner list is recorded at indent 0 though its
marker sits at column 2, and the continuation `  - c` (indent 2) then
tests as *content* of the inner item rather than a sibling of it. Both
oracles measure the nested marker's absolute column.

Fix shape: thread a column offset through `step_fuel`, added at the two
places indentation is consulted (`open_list (off + indent_of l)` and the
`Nat.ltb (ls_indent ls) (off + indent_of l)` routing test), and grown by
the consumed prefix length at each descent through a quote prefix or a
list marker. Padding the residue back out with spaces instead would break
the termination measure, which is line length plus stack depth.

Consequence worth noting: this bug is also why `Parser.pad_nested_list_unshifted`
holds. With the offset threaded, a nested list's recorded indent becomes
`off + indent_of rest`, and an ambient pad grows `off` by exactly the pad
length — so the uniform shift that `step_pad` currently cannot state for
nested lists becomes true. The proof obstacle recorded in
`260807.list-roundtrip-indent-shift.autonomous.md` is a symptom of this
bug, not an inherent difficulty.

### Also ours: tightness of an item holding a nested list

| Case | Verdict | Notes |
|---|---|---|
| `- a` / blank / `  - b` | **was our bug (renderer side); fixed** | Both oracles report the outer list **tight**; our parser agrees. `Render.item_forces_loose` used to disagree, declaring any multi-block item loose, so `cb_ok` rejected the spacing that actually parses back |

Root cause: djot.js excludes a `+list` event from spending a blank line
into looseness, which `Parser.list_content` already encodes. The
renderer-side predicate did not mirror it.

**Resolved.** `item_forces_loose` is now `lines_loose` over the item's
own rendered lines (`dc13c4b`), so it reads the same rule off the same
lines the parser scans, rather than counting blocks. With nested lists
admitted to the fragment the case is live and it agrees:
`item_forces_loose ["a"; ""; "- b"] = false`, `cb_ok` accepts the
`Tight` spelling, and it roundtrips. `Roundtrip.nested_list_after_para_roundtrip`
pins it.

---

## Adjudicated 2026-08-09 — the generated corpus

First run of `make generated`: 671 enumerated `cb_ok` documents through
all three engines, exact HTML, djot.js as reference. Two causes account
for every diff (a crude classifier put 202 on tightness, 118 on heading
ids, 57 on both, and 1 unclassified — that last one is the two
compounded, not a third cause).

Note the denominator that matters for reading these numbers: **djoths
disagrees with djot.js on 314 of the same 671 documents.** This corpus
lands in contested territory by construction — it enumerates shapes
rather than sampling documents anyone wrote — so "gallina mismatches
djot.js 378 times" is not 378 bugs.

| Case | Verdict | Notes |
|---|---|---|
| `- a` / blank / `- - n` | **djotjs-bug (probable)** | Tightness of a list whose next item, after a blank, *begins with a nested list marker*. djot.js: **tight**. djoths: **loose**, and so do we. The prose says loose. Evidence below; 259 of 671 documents |
| `> # h`, `- # h` | **our gap** | A heading inside a container gets no identifier from us. Both oracles give it one and disagree only on the mechanism — djot.js `<h1 id="h">`, djoths `<section id="h"><h1>h</h1></section>`. Ours: bare `<h1>h</h1>`. 175 of 671 documents |

### Tightness after a blank before a nested marker

**The prose decides this one, against djot.js.** From
`reference/djot-syntax-reference.md`:

> A list is classed as *tight* if it does not contain blank lines between
> items, or between blocks inside an item. Blank lines at the start or end
> of a list do not count against tightness.

In `- a` / blank / `- - n` the blank sits between two items of the outer
list. It is not at the start or end of any list: the inner list begins
after the `- ` on the following line, so the blank is outside it
entirely. No exemption applies, and the outer list is loose. djoths says
loose; we say loose; djot.js says tight.

Four further facts, each checked 2026-08-09, that make this look like an
artifact rather than a decision:

1. **The suppression is specific to lists.** Put a quote, a heading, or a
   code block in the second item instead and djot.js returns loose. Only
   a nested list suppresses it. A principled "the blank belongs to the
   following container" rule would not distinguish them.
2. **It is local to the adjacent blank.** `- a` / blank / `- b` / blank /
   `- - n` comes back loose from both engines, so djot.js is not
   blanket-suppressing; only the blank immediately before the
   list-opening item is swallowed.
3. **djot.js's own corpus never exercises the shape.** Zero of its 26
   test files contain an item, a blank, and then an item beginning with a
   nested marker. The behaviour is untested upstream, not pinned.
4. **The mechanism is visible.** djot.js emits a `blankline` match and
   excludes a following `+list` event from spending it. That exclusion is
   wanted for the *intra-item* case below; here the same code path fires
   at a sibling boundary, where the blank is unambiguously between items.

**Standing rule overridden.** This log's default is that djot.js is the
authority wherever the two differ, on the grounds that djoths lags. That
presumption is about djoths being behind on syntax changes; here djoths
matches the written spec and djot.js does not, so it does not apply.

**Not to be confused with the intra-item case.** `- a` / blank /
`  - b` — nested list *indented inside the same item* — is called tight
by both engines, and by us. Read against the syntax reference alone this
looks like an unexplained deviation (the blank is between blocks inside
an item), and an earlier revision of this entry logged it as a SPEC-GAP
on the grounds that the boundary of the deviation was unwritten.

It is not unwritten. `reference/djot-repo-readme.md:117-138` states it
outright: a sublist "must always be preceded by a blank line", and
"(This blank line doesn't count against 'tightness.')". It also gives
the derivation: goal 7 (hard-wrap friendliness) forces block elements
not to interrupt paragraphs, which forces the blank before a sublist,
which is why that blank is exempt. A decided case with a stated reason,
not a gap.

That is also what bounds the exemption, and what sharpens the bug: it
reaches exactly as far as the requirement that creates it. Nothing
requires a blank before a sibling item; `- a` / `- - n` with no blank
parses fine, and djot.js's output for it is byte-identical to its output
for the witness. djot.js applies the exemption where its justification
does not reach, discarding a blank the author chose to write.

**Side-by-side**: `djotjs-list-tightness-bug.html` renders the witness and
the three controls with both engines' actual output; open it in a browser.

**Action**: worth reporting upstream with the witness above. We keep our
behaviour meanwhile — it matches the prose and djoths, and changing it
would mean restating `Parser.list_uniformity`'s spacing clause, not
patching a case.

### Headings inside containers

This one is ours regardless of how the oracles' disagreement resolves,
since we emit no identifier at all. `Document.v`'s whole-document pass
builds sections and assigns ids only at the top level; nothing descends
into a `BlockQuote` or a list item.

Consequence for the roundtrip: none today. `cb_ast` builds bare `mk`
nodes, `roundtrip_doc` is stated modulo `undo_pass`, and
`blocks_of_cblocks_pristine` says the fragment carries no ids for the
erasure to take back — so the theorem is untouched by this. It is a
conformance gap in the HTML converter, not a soundness problem, and it
is exactly the class a roundtrip theorem cannot see.
