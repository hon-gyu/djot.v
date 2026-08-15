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

### Ours: tight rendering does not reach inside a nested container

Found 2026-08-14, when the reference leaves enlarged the generated corpus.
**All 255** of that corpus's mismatches are this shape, and the smallest
witness needs no blank line at all:

```
- > a
```

djot.js emits `<li><blockquote>a</blockquote></li>`; we emit
`<li><blockquote><p>a</p></blockquote></li>`.

**It is the renderer, not the parser.** The first reading of this entry
blamed `Step.list_open` for arming the list's blank flag through a quote.
That was wrong, and `parse_blocks` says so: on `- > a` / `  > ` / `  > t`
our list is already `Tight`, agreeing with both oracles, and we still
print the `<p>`. djot.js's `tight` is a *renderer state variable*
(html.ts:140-150): `renderChildren` sets it on any node carrying a
`tight` field and restores it on exit, so it stays set through a
blockquote or a div and every `para` below a tight item renders bare
until another list resets it. `Html.render_block`'s `render_tight`
instead strips `<p>` from an item's *direct* children only.

**Fixed 2026-08-14.** `Html.render_block` now takes the flag as an
argument, containers pass it through and items set it. Generated corpus
2830 -> **3022** of 3085; the file corpus and `make shape` do not move,
since no corpus case puts a paragraph inside a container inside a tight
item.

### Fixed: a blank inside a still-open div in a list item

The **63** generated mismatches the renderer fix left were all one shape:

```
- :::
  a

  t
  :::
```

djot.js called the outer list tight, we called it `Loose`. djot.js runs
container `continue`s before the blankline handler, so what the handler
sees is the stack *after* this line's containers have closed: a div
survives a blank and is the tip, and no list is armed. A block quote does
*not* survive a prefix-less blank, which is why `- > a` / blank / `  t`
is loose in both engines -- the quote has closed by the time the blank is
handled.

`Step.step` decided this from `list_open inner`, which asks only whether
a *list* is open. The replacement, `blank_absorbed`, asks whether
anything the item still has open takes the blank first: a div, a code
block, a nested list and an unfinished attribute spec all absorb it; a
block quote, a heading and a reference definition do not. Stated that way
it is still a predicate on the state *before* the descent, so
`step_list_blank` kept its shape and the cost was a rename plus the
`PQuote` line -- the "test the state after" framing in the note this
replaces would have needed a `pad_safe` hypothesis `list_loose_of_pad`
does not have.

Each of the six containers was pinned against the oracle before the
predicate was written, and `list_open` is now dead. Generated corpus
3022/3085 -> **3067** of 3094 (the pool grew because `cb_ok` admits more
spacings once `item_forces_loose` changes).

### Still ours: a div's closing line does not arm the enclosing list

The **27** that remain are the complementary shape, and unlike the family
above they need no blank line at all:

```
- :::
  a
  :::
- t
```

djot.js calls this list loose. `isBlank` is computed *after* the
container closers have eaten the line (block.ts:1051), so a `:::` that
closes a div leaves nothing at the tip and fires the same `blankline`
event an empty line does. A fence closer does not: the code block
consumes its closer inside its own `continue`, before that test. Hence
`- ```/a/```/- b` is tight and `- :::/a/:::/- b` is loose -- verified
against the oracle both ways.

This one is genuinely expensive, and the price was measured rather than
guessed. Making a *nonblank* line arm `ls_blanks` falsifies
`scan_list_content_nonblank` and `scan_list_content_blanks_last`, and the
`ls_blanks ls = false` precondition of `parse_list_tail` /
`parse_item_and_tail` is *used* (two `rewrite Hblanks` collapse the loose
formula), not merely carried -- so all three statements have to carry the
incoming flag into their conclusions. Worse, it breaks `roundtrip_blocks`
as it stands: a canonical `CList Tight [[CDiv [...]]; [...]]` renders
exactly the shape above and would parse back `Loose`, so `cb_ok`'s
spacing clause needs a new conjunct for "this item's lines end with the
flag armed" alongside `seps_loosen`.

So the fix is: generalize the three `ListUniformity` statements over
`ls_blanks ls`, add the conjunct to `cb_ok`, then `div_closer` in `step`
is two lines. It is a step of its own, and the 27 are its measurement.

### Ours: a spec with nothing to attach to keeps its source

`{#id} at beginning` and `[link](url){}`. djot.js drops a spec that
attaches to nothing; we drop it only when there is pending text to have
attached to, and otherwise keep its source as literal text.

Two reasons, and only the first is about fidelity. A spec that ate the
whole scan would leave a paragraph or heading with no inlines, which
`wf_block` excludes and `parse_inline_line_nonempty` denies -- the same
shape as the blank-line-in-a-paragraph case above, where djot.js is happy
to build something the canonical AST cannot hold.

The second is structural and is why the test is on pending text rather
than on "has anything been emitted", which would be the faithful
question. `oout_app` appends a previous line's output *underneath* the
current scan, and it is how a multi-line paragraph is decomposed
(`para_inlines_cons2_closed`). Emptiness of the emitted output is
therefore not stable under it, so `istep_out_app` would be false; pending
text is stable. The same fact is what defers attaching a spec to a
preceding *node* (`*e*{.a}`), which needs the emitted output and so needs
an invariant saying the unstable states are unreachable.

Three corpus cases, all in `attributes.test`.

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

## Adjudicated 2026-08-09 — a blank at the end of a nested list

Found by `make shape` (`lists.test:242`, `lists.test:308`), which had not
been read case by case before. Both are pure tightness: the tree shape
matches, only the `<p>` wrapping differs.

| Case | Verdict | Notes |
|---|---|---|
| `- - b` / blank / `- d` | **ours** | Both oracles: **tight**. Us: **loose**. The prose agrees with the oracles |

**Minimal witness**, three lines:

```
- - b

- d
```

The blank is at the *end of the inner list*, and simultaneously between
two items of the outer list. The syntax reference:

> Blank lines at the start or end of a list do not count against
> tightness.

The exemption applies to the inner list, which consumes the blank, so
nothing is left to count against the outer one. Both oracles do this. We
count it against the outer list and return `Loose`.

**Distinct from the entry above, and it resolves the other way.** There
the blank *precedes* an item that opens a list (`- a` / blank / `- - n`),
and it is outside the inner list entirely — djoths sides with us and
djot.js does not. Here the blank *follows* an item that ends with a list,
it is inside the inner list's end, and **both** oracles side against us.
The two shapes look alike and must not be merged.

### The boundary, measured

Six controls, all three engines, 2026-08-09. Only the first diverges.

| # | Shape | djot.js | djoths | ours |
|---|---|---|---|---|
| A | `- a` / blank / `  - b` / blank / `- d` | tight | tight | **loose** |
| B | same, no blank before the sibling | tight | tight | tight |
| C | `- a` / `  - b` / blank / `- d` (no blank, so `- b` is lazy text) | loose | loose | loose |
| D | `- a` / blank / `  - b` (no sibling) | tight | tight | tight |
| E | quote in place of the sublist | loose | loose | loose |
| F | paragraph in place of the sublist | loose | loose | loose |

E and F bound it: the exemption is specific to a *list* closing, and does
not reach through a quote that contains one. A further control, `- a` /
blank / `  - b` / blank / `  t` / blank / `- d`, is loose everywhere —
the blank before `t` is spent by `t`, so only the list-closing blank is
exempt.

### The mechanism, both sides

djot.js, `src/parse.ts:1237-1258`:

```js
if (!/^[+-]list/.test(annot) && ln.data.blanklines) { ln.data.tight = false; }
if (!/^[-+]list_item$/.test(annot)) { ln.data.blanklines = false; }
```

The first regex has no `_item` and no anchor at the end, so it matches
`-list` — the event that *closes* the inner list — as well as `+list`.
The second then clears the pending blank, because `-list` is not a
`list_item` boundary. By the time `- d`'s content is handled there is no
blank outstanding. So the "blank at the end of a list" exemption is not a
special case in djot.js; it falls out of the close event being a list
event. The entry above is the same two lines firing where the
justification does not reach; this entry is the same two lines firing
where it does.

Ours, `theories/Parser.v`: the `KBlank` branch of the `PList` case in
`step_fuel` applies `list_blank ls` to the outer list *and* recurses into
`inner`, so one blank arms every open list at once. `list_next` then
spends the outer list's flag at the sibling marker. djot.js's `blankline`
handler picks exactly one list node — the innermost — which is the rule
we are missing. `list_content`'s existing `KList` exemption is the other
half of the same idea, already implemented.

### What it cost us, and the fix

`cb_ok` accepted the deviant spelling, so this was inside the proven
fragment rather than outside it: `roundtrip_doc` quantified over an AST
that no djot source denotes. The roundtrip could not see it, for the same
reason it cannot see the heading-id gap — it relates our parser to our
renderer, and the two agreed with each other.

**Fixed 2026-08-09.** One guard in the parser, mirrored twice on the
predicate side.

`Parser.list_open` asks whether a list is open *directly* in a state, with
no container in between, and `step`'s `KBlank` branch in the `PList` case
arms this list only when `list_open inner` is false:

```coq
let ls' := if list_open inner then ls else list_blank ls in
```

Because the branch recurses into `inner`, this arms exactly the innermost
open list — which is what djot.js's `blankline` handler does by selecting
one node from the container stack. `list_open` needs no recursion:
`PQuote` and `PList` are the only nesting constructors, and shape L above
says the exemption must *not* reach through a quote.

Three definitions had to learn the same thing, all of them scans that were
flat and are now threaded with the item's own parse state:

- `lines_loose` gained a `pstate` argument — contrary to what an earlier
  revision of this entry claimed, it was wrong too. `["- b"; ""; "t"]`
  leaves its enclosing list tight and `["a"; ""; "t"]` does not, and a
  scan that sees only `classify` cannot tell them apart.
- `scan_list_content` likewise, with `scan_loose_eq` as the bridge: the
  scan carries the state padded into the enclosing item and `lines_loose`
  carries it bare, and `pad_state_list_open` says `list_open` cannot tell
  those apart.
- `list_spacing_of`'s and `cb_ok`'s "a multi-item list may always be
  spelled `Loose`" disjunct became `seps_loosen`: a separator loosens only
  when the item before it does not end with an open list
  (`ends_open_list L = list_open (snd (run_lines L (PPara [])))`).

Checked by computation before any proof work — 2220 enumerated
(spacing, items) pairs, zero disagreements between `list_uniformity`'s two
sides — and then proved. No `Admitted`.

**Effect.** The fragment shed the unreachable inhabitants and gained the
reachable ones it had been rejecting: `accepted` went 59/671/7151 to
53/593/6437 at depths 1–3, every one still checked to roundtrip by full
AST equality. `make shape` went 220/287 to 222/287, the two cases being
`lists.test:242` and `:308`. On the generated corpus, mismatches against
djot.js went 378/671 to 252/593.

`Generate.nested_list_end_blank_tight`, `..._loose_rejected` and
`..._lines` pin the corrected behaviour; `nested_loose_promotes_outer`
changed verdict with it, and its comment records why.

### Correction to the entry above

That entry says two causes account for every diff in the generated run.
Three did. Re-classifying the 378 gallina-vs-djot.js mismatches by whether
the outputs differ only in `<p>` wrapping, then by input shape:

| Bucket | Before the fix | After |
|---|---|---|
| tightness, logged shape only | 34 | 34 |
| tightness, **this** shape only | 45 | **0** |
| tightness, both shapes present | 46 | 12 |
| heading ids and everything else | 253 | 206 |

The classifier is crude — it matches input shapes with a regex and cannot
split the "both" bucket — but the zero is the decisive number: every
document whose only tightness-relevant shape was this one now agrees. What
remains is the logged djot.js bug, which we deliberately do not follow.

The lesson is in the denominator, not the fix. The generated run contained
45 clean instances of this cause and reported them as a different one,
because the run was classified by the causes already known. It was found
instead by reading `make shape` output case by case — which nobody had
done, because 220/287 looked like it was all unimplemented constructs.

## Adjudicated 2026-08-09 — the fenced-div class token

Found while implementing divs (`.project/260809.container-uniformity.md`,
option A). The two oracles disagree on what may follow the opening fence.

| Case | Verdict | Notes |
|---|---|---|
| `:::a!` / `x` | **djot.js** | djot.js: a paragraph, no div at all. djoths: a div with class `a!` |

djot.js's opener is `pattDivFenceStart` followed by `pattDivFenceEnd =
([\w_-]*)[ \t]*\r?\n` (`block.ts:55-56`). The pattern is anchored and
must match through end of line, so a character outside `[\w_-]` makes the
whole opener fail and the line stays text. djoths takes the rest of the
line as the class without constraining it.

We follow djot.js: `Line.is_class_char` is `[0-9A-Za-z_-]`, and
`div_open` returns `None` when what follows the class token is not blank.
The reference prose says "optionally a class name" without saying what a
class name may contain, so this is a gap in the prose rather than a bug
in either implementation — the same shape as the tilde-fence and
table-trimming SPEC-GAPs.

Pinned as the last case of the div probe set.

## Adjudicated 2026-08-09 — a blank line inside a block attribute spec

Found while implementing block attributes. Not a disagreement between the
oracles — they agree — but a place where *we* deliberately differ, which
this log is also where the previous "ours" entries live.

| Case | Verdict | Notes |
|---|---|---|
| `{#i` / `··` / `··}` / `Hi` | agreed, we match | The blank line is indented past the opener, so it continues the spec; both oracles and we give `<p id="i">Hi</p>` |
| `{#i` / `··` / `··<}` / `Hi` | **we differ, on purpose** | The spec fails at `<`. djot.js reproduces the lines it ate as a paragraph *including the blank*: `<p>{#i\n\n<}\nHi</p>`. We drop the blank: `<p>{#i\n<}\nHi</p>` |

The first row is the surprise and it is worth stating: djot.js runs every
open container's `continue` on every line, blank lines included, and a
blank line's `this.indent` is its whole length. So a sufficiently
indented blank line is a continuation line for an attribute spec, not a
paragraph break. Nothing in the corpus covers it.

The second row is the cost of that. `block.ts:569-572` pushes each
continuation line's slice before feeding it, so a blank line becomes part
of the paragraph the failed spec turns into. A paragraph carrying a blank
line is exactly what `Wf.wf_block` excludes, and for a reason that is not
bookkeeping: it does not round-trip. Rendering such a paragraph and
parsing it back splits it in two, so admitting it would make
`parse (render d) = d` false for a document the parser can produce.
`Parser.push_text` is what drops the line, and the divergence is confined
to specs that both span a blank line and then fail.

Pinned as `Parser.parse_attr_blank_continues_spec` and
`Parser.parse_attr_failed_after_blank_drops_it`.

## Adjudicated 2026-08-10 — a blank before an item that opens a list

Ours, found by the generated corpus and invisible to the 287-case one.

| Case | djot.js | ours (before) | Verdict |
|---|---|---|---|
| `- a` / blank / `- b` | loose | loose | agree |
| `- a` / blank / `- - n` | **tight** | loose | **our bug, fixed** |
| `- a` / blank / `- > q` | loose | loose | agree |

djot.js excludes a `+list` event from spending a blank line into
looseness (parse.ts ~1237). `Parser.list_content` already encoded that
for the lines *inside* an item. The separator blank between two items is
spent by the *next item's first line*, and `list_next` did not have the
rule there — so an item whose content opens a nested list wrongly
loosened the enclosing list.

The fix is not confined to the parser, and that is the interesting part.
`seps_loosen` — the renderer-facing predicate that `list_uniformity`
carries — asked only whether the item *before* a separator ends with a
list still open (the trailing-blank exemption). A separator now has two
conjuncts, one from each side, so it became a pairwise scan over adjacent
items rather than an `existsb` over `removelast`. `list_loose_of` gained
the same conjunct for the first separator.

Consequence worth recording: `cb_ok` accepts strictly fewer `Loose`
spellings, because a list whose next item opens with a marker genuinely
cannot round-trip as `Loose` — both its spellings parse back `Tight`.
The generated corpus shrank from 888 documents to 796 for that reason,
and `check/Deep.v`'s depth-3 counts went `(68, 888, 11368)` to
`(65, 796, 9511)`.

### Still open, same area: a div in an item loosens the list

Found while checking the residue; pre-existing, not caused by the above.

| Case | djot.js | ours |
|---|---|---|
| `- :::` / `  a` / `  :::` / `- t` | **loose** | tight |
| `- > q` / `- t` | tight | tight |
| `- :::` / `  a` / `  :::` (one item) | tight | tight |

No blank line anywhere, and a quote in the same position does not do it.
**Diagnosed 2026-08-14**: a div's closing line is itself a `blankline`
event, because `isBlank` is computed after the closers have eaten the
line. See "Still ours: a div's closing line does not arm the enclosing
list" above, which carries the mechanism, the proof cost and the current
count (27, up from 12 because the pool grew).

## Adjudicated 2026-08-10 — an ordered list starting at 0

Found while measuring ordered-list coverage, not by the harness: the
corpus has no such document and the generated pool starts its decimal
kinds at 1.

| `0. a` / `1. b` | output |
| --- | --- |
| djot.js | `<ol>` |
| djoths | `<ol start="0">` |
| ours | `<ol start="0">` |

The two oracles disagree, so by the rule in
[[project-engineering-lessons#Ask the oracle]] this is a log entry rather
than a judgement call. `<ol>` with no attribute means start 1, so djot.js
is reading `0.` as 1 or suppressing the attribute below 1; djoths takes
the numeral at face value and so do we.

**Not acted on.** Nothing in the formalization turns on it: `cb_ok`
accepts `LKDecimal d 0`, and `roundtrip_blocks` is `parse (render d) = d`,
an internal property that holds either way. Only the HTML writer would
change, and only for start 0. Recorded so that a future HTML conformance
pass finds it already diagnosed rather than as a fresh mismatch.

## Adjudicated 2026-08-13 — ours: constructs inside an unterminated destination

Found by the corpus on the step that wired direct links: it is the one
case `links_and_images.test` scored worse on, against +11 elsewhere.

| `[unclosed](hello *a` / `b*` | output |
| --- | --- |
| djot.js, djoths | `[unclosed](hello <strong>a\nb</strong>` |
| ours | `[unclosed](hello *a\nb*` |

**Ours, deliberately, and confined to exactly this shape.** djot.js does
not have a destination *mode*: it keeps every matcher running inside
`](` and calls `strMatches` over the region only when the balanced `)`
arrives (`inline.ts:470`), turning whatever was matched into literal
text retroactively. So when the destination *does* close, its content is
literal either way and we agree; we differ only when a `](` never finds
its `)`, because then djot.js keeps the matches it made and we have
never made any.

Matching it is not a formalization question -- nothing in `wf_block` or
the roundtrip forbids it, and the canonical view will never produce such
a document -- it is a cost question. Our destination accumulates literal
text, and djot.js can afford not to because it holds the subject string
and can re-slice it; we do not keep source text for classified nodes, so
to match we would have to run the ordinary scan *and* accumulate the
source alongside it, then throw one of the two away at the close. That
is `strMatches` as a third retroactive disposition on top of the two
[[260811.inline-parser]] §2.2 already names, and it belongs with
footnote references and spans rather than with direct links.

**Consequence for the canonical view.** `ci_ok` must exclude a
destination whose text could open anything -- the delimiters, the
backtick, `[` -- which the destination's own escaping already handles,
since `\_` and `` \` `` decode the same way in both engines. So the
divergence is unreachable from a canonical document and stays a corpus
fidelity gap only.

## Adjudicated 2026-08-15 — ours: a spec with nothing before it

djot.js's `-attributes` handler asks for the tip of the current
container and returns without doing anything when there is none
(`tip === topContainer()`, parse.ts:452). The spec's own source is
already gone by then -- it was consumed by the attribute parser -- so it
vanishes.

| `{#i} x` | output |
| --- | --- |
| djot.js | `<p> x</p>` |
| ours | `<p>{#i} x</p>` |

**Ours, and this one is forced.** The deciding input is not that case
but `# {#i}`, where the spec is the heading's entire content. djot.js
renders `<h1></h1>`. A block with no children is not in `wf_block`, and
`parse_inline_line_nonempty` -- which `para_inlines_nonempty` and
through it every `wf_block` obligation on paragraphs and headings rests
on -- says a nonblank line yields at least one inline. Dropping the spec
would falsify it for the string `{#i}`.

This is the [[project-engineering-lessons]] clause on unrepresentable
oracle behaviour, and the answer to its question is yes: matching would
break a theorem about output the parser can reach. So we keep the source
as text, and the divergence is confined to a spec that has *neither*
pending text nor a node before it in the same scan -- `iattr_attach`'s
last branch, and the only one that does not consult `oattach`.

**What is not divergent.** Everything else in the family now matches:
`*e*{.a}` and `[l](u){}` attach to the node, `x{.a}{.b}` merges,
`foo {.a}` drops the spec because the text ends in whitespace, and
`foo bar{.a}` splits at the last space. The remaining `attributes.test`
gaps are a spec crossing a line break and `{% %}` comments, neither of
which is about attachment.

## Adjudicated 2026-08-15 — ours: constructs inside an unclosed `[^`

djot.js decides note-ness at the `]`, by reading the byte after the
opener (`inline.ts:361`). Until then the `^` is an ordinary superscript
opener and everything between is scanned normally; the note branch
destroys those matches only when the `]` actually arrives. So a `[^`
that never closes leaves the superscript standing.

| `[^a^b` | output |
| --- | --- |
| djot.js | `[<sup>a</sup>b` |
| ours | `[^a^b` |

**Ours, and confined to exactly that shape.** We decide at the `^`,
because the label is *source* and we keep no source beside classified
nodes -- the same constraint that made the destination accumulate text
rather than run `strMatches`. Whenever the `]` arrives the two agree,
since djot.js then discards everything it scanned in between and reads
the same source slice we accumulated. They differ only when a `[^`
finds no `]` in the paragraph.

This is the [[project-engineering-lessons]] "matchable, but only at a
price" clause, and the price is the one that clause names: matching
would mean running the ordinary scan *and* accumulating source
alongside it, then discarding one at the `]`. Unreachable from a
canonical document -- `needs_escape` claims both `[` and `^`, so
`escape_str` never emits the pair bare.

**A near miss worth recording.** `[^a[^b]]` looked like a third
behaviour: djot.js labels it `a[^b`, using the *outer* opener, where
`[[^a]]` and `x[y[^a]z]w` both use the inner one. Tracing the openers
byte by byte showed it is not a footnote rule at all -- the second `^`
closes the superscript the first one opened, and `clearOpeners(1, 4)`
drops the bracket opener nested inside it. Our `oclose` abandons frames
it walks past for the same reason, so we agree without special-casing
anything.
