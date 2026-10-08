---
ai-disclosure: autonomous
---
# djot.js divergences

Append-only adjudication log: where our parser's output differs from
djot.js's, and what we did about each case. djot.js is the implementation
we conform to; an entry says whether the difference is ours to fix, ours
by choice (and why), or djot.js's.

Entries up to 2026-09-24 also adjudicate djoths against djot.js; djoths was
dropped from the harness then. The baseline below was made with a recipe
that no longer exists (`make baseline`: djot.js and djoths against the
expected corpus output).

Baseline established 2026-08-02
(djot.js @ v0.3.2 submodule, djoths @ 0.1.4.1 submodule; 287 cases run,
6 skipped for `p`/`a` options, filter cases dropped).

Context for adjudication (djot README): current development is focused on
djot.js; djot.lua and probably djoths are not kept up to date with the
latest syntax changes. So "djoths-outdated" is the expected default verdict,
and djot.js is the authority wherever the two disagree.

**What counts as authority here.** The engines and the syntax reference
say what the language *is*. The rationale
([djot README §Rationale](https://github.com/jgm/djot#rationale), and behind it
[Beyond Markdown](https://johnmacfarlane.net/beyond-markdown.html)) says what it is *for*: it decides cases
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

**The prose decides this one, against djot.js.** From the
[syntax reference](https://github.com/jgm/djot/blob/main/doc/syntax.md):

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

It is not unwritten. [djot's rationale](https://github.com/jgm/djot#rationale) states it
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

Narrowed 2026-09-30: a blank at the end of an item no longer stays in a
div left open; see "Closed 2026-09-30 -- SPEC-GAP: whether a div left
open at the end of an item holds the blank after it".

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

### Fixed: a div's closing line arms the enclosing list

Reversed 2026-09-29, to follow the syntax reference: see "Closed
2026-09-29 -- djotjs-bug: a div's closing fence loosens a list".

The **42** that remained were the complementary shape, and unlike the
family above they need no blank line at all:

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

**Fixed 2026-08-22.** `Step.div_closer` is the predicate, read off the
state before the descent for the reason `blank_absorbed` is: `step` is
deterministic, so whether the line closes the div is a fact about the
state it arrives at. The generated corpus went 42 -> 0 and the whole
family is gone.

The price forecast here was half right. `scan_list_content_nonblank` and
`scan_list_content_after_blank` were indeed falsified -- and both turned
out to have no users at all, so they were deleted rather than
generalized. `scan_list_content_blanks_last` was falsified and *is* used;
what replaced it is `lines_gap`, the companion fold to `lines_loose`,
plus one conjunct on `item_ok`. The three `ls_blanks ls = false`
preconditions never had to move, because `item_ok` now guarantees them.

### Still ours: a list whose item ends with a div closer is not canonical

What the fix above cost, and the residue it leaves. `item_ok` asks
`negb (item_gap L)` of *every* item, including the last -- where nothing
follows to spend the gap, so the condition is not needed. It is asked
there anyway because the alternative is positional, and positional is
what the fold below would have to become.

So these two are outside the canonical view although their renderings
round-trip:

| shape | why it is fine in reality |
|---|---|
| `CList Tight [[CDiv [...]]]` | one item; `finish` never reads `ls_blanks` |
| `CList Loose [[CDiv [...]]; [...]]` | already loose, so the gap changes nothing |

Measured: the accepted pool went 34496 -> 31272 at depth 3, and part of
that is correct (a `Tight` list with a div-ending item in a non-final
position is genuinely unreachable now). `Roundtrip.div_ending_item_excluded`
pins the boundary and its deletion is what will confirm the fix.

The obligation that stopped it. `list_loose_of` is an `existsb
item_loose` over the items; the truth is a fold carrying the gap across
each marker:

```
loose_0 = false,  gap_0 = false
loose_{i+1} = loose_i || (gap_i && negb (starts_list L_i)) || item_loose L_i
gap_{i+1}   = item_gap L_i
```

which is exactly the recurrence `parse_item_and_tail_narrow`'s `Hloose1`
already proves one step of. Turning `list_loose_of` into that fold
changes the loose formula in `parse_list_tail` and `parse_item_and_tail`
-- where the two `rewrite Hblanks` currently collapse it -- and then
`cb_ok`'s spacing clause and `items_force_loose` follow. A step of its
own, and the 3224 excluded documents are its measurement.

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

Reversed 2026-09-29, to follow the syntax reference: see "Closed
2026-09-29 -- djotjs-bug: a blank before a nested list or an empty last
item does not loosen".

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
and `dev/check/Deep.v`'s depth-3 counts went `(68, 888, 11368)` to
`(65, 796, 9511)`.

### Still open, same area: a div in an item loosens the list

Found while checking the residue; pre-existing, not caused by the above.

| Case | djot.js | ours |
|---|---|---|
| `- :::` / `  a` / `  :::` / `- t` | **loose** | tight |
| `- > q` / `- t` | tight | tight |
| `- :::` / `  a` / `  :::` (one item) | tight | tight |

No blank line anywhere, and a quote in the same position does not do it.
**Diagnosed 2026-08-14, fixed 2026-08-22**: a div's closing line is
itself a `blankline` event, because `isBlank` is computed after the
closers have eaten the line. See "Fixed: a div's closing line arms the
enclosing list" above, which carries the mechanism and what the fix cost
the canonical view.

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
[[project-engineering-lessons#Ask djot.js]] this is a log entry rather
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
which is about attachment. *(Both closed 2026-08-22; see the entry on an
unclosed spec below, which is what is left of them.)*

*Amended 2026-08-22, when attachment moved to `oresolve`.* The
divergence is no longer "no scope output and no pending text before it"
but the narrower "nothing before it **in its own scope** once that scope
has resolved". `{#i} x` and `x` / `{.a}` still keep their source, and so
does `a *{.c}b*`, where the spec is the first thing inside a `Strong`
that closes — dropping it there would leave an empty container, which
`wf_inline` excludes and `oclose` refuses to build. What is no longer
divergent is everything where an *unfinished* opener sits in front: `a
*b{.c}o` now attributes `*b`, because by resolution time the `*` is
text.

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

## Adjudicated 2026-08-21 — ours: smart punctuation contributes its rendering

| input | verdict | note |
| ----- | ------- | ---- |
| `![a'b](u)` | **we differ, to be closed** | djot.js `alt="a'b"`, ours `alt="a’b"` |
| `# head'ing` | **we differ, to be closed** | djot.js `id="head'ing"`, ours `id="head’ing"` |
| `![a...b](u)` | same family | djot.js `alt="a...b"`, ours `alt="a…b"` |
| `![a---b](u)` | same family | djot.js `alt="a---b"`, ours `alt="a—b"` |

djot's AST models every piece of smart punctuation as
`SmartPunctuation {type, text}` where `text` is the *source*, so
`getStringContent` — which computes an image's `alt` and a heading's
implicit id — replays what the author typed. We have no such node: an
unmatched quote decays to its curly character through `ddecay`'s
`DDPair`, and an ellipsis or a dash run is written into the text buffer
by `IPeriod` and `IDash`. All four are therefore `Str` nodes holding the
rendered character, and the rendered character is what reaches `alt` and
the id.

The divergence dates from smart quotes, not from dashes; it is recorded
now because dashes and ellipsis made it a family rather than a case.
**Boundary**: the two agree everywhere the punctuation is rendered, and
differ only where a *string* is read back off the tree — image alt text
and implicit heading identifiers. Nothing else consults
`inline_text` on these nodes.

Matching would mean an AST node carrying its own source, which is the
[[project-engineering-lessons#When it is representable, but only at a
price]] clause: the price is a constructor plus a field on every
traversal, and the reachable set is smart punctuation inside a link
label or a heading. Unreachable from a canonical document either way,
since `escape_str` claims `'`, `"`, `-` and `.`.

**Revised 2026-10-04.** The verdict above was about cost, and the rows
said "on purpose" where no reason to prefer our output was given. The
decision now is to follow djot.js: `alt` and a derived id read what the
author typed. An id then does not change when the punctuation map does,
and it stays typeable. This waits for the node, which is planned
together with a user-provided punctuation map; see "Smart punctuation:
the plan" in `json-gaps.md`. Until then the rows above still describe
what we output.

## Adjudicated 2026-08-21 — ours: a failed autolink candidate is flat

| input | djot.js | ours |
| ----- | ------- | ---- |
| `<_a_>` | `&lt;<em>a</em>&gt;` | `&lt;_a_&gt;` |
| `` <a`b`c> `` | `` &lt;a<code>b</code>c&gt; `` | `` &lt;a`b`c&gt; `` |
| `<a[b](c)>` | `&lt;a<a href="c">b</a>&gt;` | `&lt;a[b](c)&gt;` |
| `<a\ b>` | `&lt;a&nbsp;b&gt;` | `&lt;a\ b&gt;` |
| `<a{.x}>` | `<span class="x">&lt;a</span>&gt;` | `&lt;a{.x}&gt;` |

djot.js decides an autolink with a *regex lookahead*: `pattAutolink`
(`inline.ts:85`) is matched at the `<`, and only if it matches and the
captured region passes one of the two tests does the scanner skip the
region (`inline.ts:262-280`). When the lookahead fails, the `<` becomes
a `str` and the scanner **returns to the byte after it**, so the region
is read a second time, now as ordinary inline content.

**Boundary, and it is a clean one: the two agree whenever the candidate
succeeds.** Nothing inside a successful autolink is dispatched on either
side -- djot.js never scanned it, we accumulated it raw -- which is why
`` <a:b`c> `` links to ``a:b`c`` in both. They differ only on a region
that is bracketed by `<` and `>` on one line, contains no whitespace,
fails both the email and the url test, *and* contains something the
inline layer would otherwise recognize.

**Ours, because the alternative is the second read.** That second read
is what `iscan_str_no_reread` says this scanner does not do, and unlike
the attribute reparse it cannot be confined to a shorter slice with
recognition disabled: a delimiter opened inside the region may close
outside it (`<_a>b_` is one emphasis to djot.js), so it is a rewind of
the whole scan rather than a sub-parse. Nor can the region be scanned
speculatively inside a scope: an unclosed verbatim in it would swallow
the `>` that decides the question, and `` <a:b`c> `` is exactly that
shape *and* a case the two agree on today.

Unreachable from a canonical document: `escape_str` claims the `<`, so a
`Str` renders one as `\<` and no canonical rendering spells a candidate
it did not mean.

## Adjudicated 2026-08-22 — ours: a caption with no table

| Input | djot.js | ours (and djoths) |
|---|---|---|
| `^ cap` alone | *nothing at all* | `<p>^ cap</p>` |
| `^ cap` / `\| a \|` | *nothing at all* | one paragraph of both lines |
| `\| a \|` / blank / `p` / blank / `^ cap` | table, `<p>p</p>` | the same, plus `<p>^ cap</p>` |

djot.js has a top-level `caption` container (`block.ts:236-260`): `^`
plus a space opens it anywhere a block may start, it continues while the
line is nonblank -- so it swallows the lines after it, a table's rows
included -- and at `-caption` it is merged into the preceding sibling
*only if that sibling is a table* (`parse.ts:1048-1069`). Otherwise the
container is popped and its content is dropped, which is why a caption
in the wrong place deletes itself and everything it ate.

**Ours, and the reason is that the oracle's answer is not
representable.** There is no AST for "a block that renders as nothing",
and inventing one would put a node in `wf_block` that no rendering can
produce -- the clause from
[[project-engineering-lessons#When djot.js's answer is
unrepresentable]]. Dropping the lines silently is worse than diverging:
a document that renders empty is the one failure mode a reader cannot
diagnose.

**Confined by construction rather than by a special case.** `^` is not a
`line_kind` here: `Line.caption_open` is consulted by the table's
continuation rule and nowhere else, so there is no caption container to
be in the wrong place. The cost is exactly the three rows above; where a
table does precede, the two agree, blank lines between them included.

## Adjudicated 2026-08-22 — djot.js: a `dd` has no tightness of its own

| Input | djot.js (and ours) | djoths |
|---|---|---|
| `: a` / blank / `  d` | `<dd>\n<p>d</p>\n</dd>` | `<dd>\nd\n</dd>` |
| two items, a blank between | agree | agree |
| `- : t` / blank / `    d` / `- x` | agree, both bare | agree |

djot.js's `definition_list` node carries **no `tight` field**, where
`bullet_list`, `ordered_list` and `task_list` all do
(`parse.ts:824-857`), and `renderChildren` overrides the renderer's
`tight` flag only for a node that has one (`html.ts:140-148`).  So a
`dd` renders at whatever tightness is *in force*: `<p>`-wrapped at top
level, bare inside a tight bullet item.  djoths computes a
`ListSpacing` for the `dl` (`AST.hs:263`) and renders on it, which is
why it differs on the commonest shape of all and agrees once a blank
line between items makes both answers Loose.

**djot.js, and the corpus pins it** (`definition_lists.test:6` and `:113`
are two of the eleven djoths mismatches).  `Html.render_block` renders a
definition at the incoming `tight` and never reads `DefinitionList`'s
`sp`.

**The field stays anyway, and not out of deference to djoths.**  The
canonical view spells a list as `CList k sp items` and
`render_cb_lines` says the renderer recovers `cb_lines` from `cb_ast`;
drop `sp` and a Loose and a Tight definition list render to different
lines and the same AST, so `cb_ast` stops being injective and the
theorem is false.  The field is unobservable in HTML and pinned by the
roundtrip, which is a sharper statement than either oracle makes.

**A consequence worth naming, since it looks like a bug.**  A blank
line inside a definition does *not* loosen an enclosing bullet list:
djot.js's blankline handler arms the tip container or its parent
(`parse.ts:1197-1205`), which inside a definition is the `dl`, whose
flag `-list` then discards.  `- : t` / blank / `    d` / `- x` is
therefore a tight bullet list in both oracles.  We get this for free
because a definition list *is* a list here too --
`Line.is_bullet` claims `:` and `Step.list_block` picks the node from
the style set, exactly as `-list` does.

## Adjudicated 2026-08-22 — djot.js: how a task item renders

| Input | djot.js (and ours) | djoths |
|---|---|---|
| `- [x] b` | `<li>\n<input disabled="" type="checkbox" checked=""/>\nb\n</li>` | `<li class="checked">\n<label><input type="checkbox" checked="" />b</label>\n</li>` |

djoths puts the status on the `<li>` as a class and wraps the content in
a `<label>`; djot.js emits a bare `disabled` input ahead of the content
and leaves the `<li>` plain (`html.ts:219-229`).  The *parse* agrees on
every case probed -- same items, same statuses, same list boundaries --
so this is a rendering divergence and nothing more.  djot.js is the
authority and `task_lists.test` pins it; three of the twenty-five djoths
mismatches in the exact-HTML run are these.

**Worth recording for the shape it shares with the definition list.**
Both constructs are one arm of djot.js's single list spec, and in both
the second oracle's HTML differs while its parse does not.  Where the
`dl` disagreement is about a *field* (djoths computes a spacing we
cannot observe), this one is about tags alone.

## Adjudicated 2026-08-22 — ours: an unclosed inline attribute spec

A spec now crosses a line break. djot.js scans the newline as an
ordinary byte of the subject and hands it to the attribute machine like
any other (`inline.ts:770-808`), and the machine treats it as
whitespace, so `hi{#id .class` / `key="value"}` is one spec and
`Foo bar {% c` / `d %} baz.` is one comment. We do the same: `ibreak`
feeds `nl_char` to `iattr_feed` rather than resolving the state to text,
which is what `ISpan` already did for a bracketed span's spec. Two
`attributes.test` cases (`:80`, `:282`) and the corpus went 278 to 280.

What does not follow is the *failure* path.

| `x{a="*b*"` | output |
| --- | --- |
| djot.js | `x{a=“<strong>b</strong>”` |
| ours | `x{a="*b*"` |

djot.js is speculative with backtracking here: while a spec is open it
buffers the slices it fed the machine, and when the spec fails or the
paragraph ends inside one it replays those slices through the *inline*
scanner with attributes switched off (`reparseAttributes`,
`inline.ts:637`). So a quote inside a dead spec turns smart, and a
delimiter inside one can close a scope opened before the `{`:
`*a{b="c*d` is `<strong>a{b=“c</strong>d`.

**Ours, and the reason is the scan's shape rather than a theorem.** Our
`IAttr` accumulates the spec's source and never scans it, so there is
nothing to replay; matching would mean resuming the scanner on bytes it
has already dispatched, which is what `iscan_str_fuel` certifies it does
not do. It is not the "run the ordinary scan *and* accumulate source"
price the direct link and the `[^` label declined — it is one level
worse, because the replay reaches scopes outside the spec and so cannot
be a subordinate scan either.

**Boundary.** The two agree on every spec that *closes*, whatever it
contains, since a closed spec's source is consumed by the machine on
both sides. They differ only on a spec that never closes and whose
source holds a byte an inline scan would have claimed — and the machine
admits an arbitrary byte in exactly two states, a quoted value and a
comment, so `{#id` and `{.class` and `{key=bare` are all agreed even
unclosed. Unreachable from a canonical document: `needs_escape` claims
`{`, so `escape_str` never emits one bare.

**What did change on our side of the failure path.** The literal
fallback now goes through `bsplit_nl`, the destination's rule, so the
breaks a dead spec spanned come back as `SoftBreak`s instead of newlines
inside a `Str`. Same HTML either way, which is why nothing measured it;
the point is that a `Str` holding a newline does not survive a reparse,
so it should not be in an AST we claim to round-trip. `bspan_lit` had
the same hole — a bracketed span's spec has crossed breaks since it was
written — and it is fixed here too.

## Adjudicated 2026-08-22 — ours: a spec inside a bracket that decays

Attachment now runs after the scan (`oresolve`), so an opener that never
closed is text before a spec asks what is in front of it. A bracket is
the one opener where that is still decided too early.

| `[a{.c}b] c` | output |
| --- | --- |
| djot.js | `<span class="c">[a</span>b] c` |
| ours | `[<span class="c">a</span>b] c` |

**Ours, and the reason is where `bclose` sits.** A `]` has to hand
`IClosed` the label's children *already resolved*, because the next byte
decides whether they become a link's, an image's, a span's, or literal
text — and three of those four are nodes that need `inlines`. So a spec
inside the label settles at the `]`, before it is known whether the `[`
will become text. Matching djot.js would mean carrying unresolved items
through `bclose` and resolving a second time on the literal path, which
is the retroactive disposition the destination
(`links_and_images:220`) and the `[^` label already declined.

**Boundary.** The two agree on every bracket that becomes a node, which
is every bracket followed by `(`, `[` or `{`. They differ only on one
that decays to text and contains a spec. Unreachable from a canonical
document: `needs_escape` claims `[` and `{`.

`Inline.attr_inside_a_decaying_bracket` pins it, and its deletion is
what would confirm a fix.

## Correction 2026-08-23 — to *a spec with nothing before it*

That entry gives two reasons where only one holds. "A block with no
children is not in `wf_block`" is true of `Para` and `Section`, whose
cases carry `nonempty`, and **false of `Heading`**, whose case is

```coq
| Heading level ils => Nat.leb 1 level && wf_inlines ils
```

with no nonemptiness obligation at all. `parse_blocks "#"` gives
`Heading 1 []` and `wf_parse` covers it, so djot.js's `<h1></h1>` is not
unrepresentable on that ground.

The verdict is unchanged, because the other reason is the real one and
is exact: `parse_inline_line_nonempty` says a *nonblank* line yields at
least one inline, and `{#i}` is nonblank. Dropping the spec would
falsify it whatever block the line sits in, which is also why the
divergence is not specific to headings.

Worth keeping the distinction: an empty heading is fine, an empty
*rendering of a nonblank line* is not.

## Correction 2026-08-23 — two reasons attached to the wrong thing

Found by re-running every `ours` entry's inputs against the current
build and djot.js. **Every verdict stands and every boundary sentence
checks out** -- the destination that closes, the `[^` that closes, the
autolink that succeeds, the spec that closes, the unclosed spec with no
quoted value, the bracket that becomes a node, and the caption preceded
by a table with or without a blank line all agree, exactly as claimed.
What did not survive is two pieces of supporting reasoning.

**1. The destination's unreachability is not `ci_ok`'s doing.**
*2026-08-13* says "`ci_ok` must exclude a destination whose text could
open anything". It does not: its only condition there is

```coq
| CILink _ kids dst => (no_nl dst && go kids && sep kids)%bool
```

The escaping is `escape_dest`, applied by `ci_src` when the destination
is *written*. And the simpler fact makes the point without either: the
divergence needs a `](` that never finds its `)`, and the canonical
renderer always closes a destination. Unreachability is immediate from
the renderer's shape, so the conclusion holds a fortiori.

**2. The empty-container reason belongs to a different input.** The
*2026-08-15* amendment cites `a *{.c}b*` and says "dropping it there
would leave an empty container". It would not -- djot.js gives
`<strong>b</strong>`, since `b` is still in the scope. That input
diverges for the plain reason, nothing before the spec in its own scope.

The input the empty-container reason is about is `a *{.c}*`, where
djot.js really does emit `<strong></strong>`. There matching is not
declined but unavailable, `wf_inline` excluding an empty `Strong`.
`Inline.attr_alone_in_a_closing_scope` now pins it beside
`attr_first_in_a_closing_scope`, which is the pair the distinction
needed.

**One row is incomplete rather than wrong.** *2026-08-15* gives djot.js's
`# {#i}` as `<h1></h1>`; the whole output is
`<section id="s-1">\n<h1></h1>\n</section>`, the section taking a
generated identifier because the heading has no text to make one from.
Ours is `<section id="i">\n<h1>{#i}</h1>\n</section>`. The divergence
reaches the identifier, not only the heading.

## Fixed 2026-09-05 — an escaped backtick in a table row

Found while asking what a rename may write into a destination (the former
`Site.dest_backtick_breaks_row`), not by the corpus: at the time no generated
document put a backtick in a table cell, so the shape below was unreachable
from the generator even though the corrected `cb_ok` admits it.

```
| a\`b |
```

djot.js reads that as a table row whose one cell renders `` a`b ``. Before
the repair we read it as `KText`:

```coq
Compute classify "| a\`b |".        (* KText  -- djot.js: a row *)
Compute classify "| a`b |".         (* KText  -- djot.js agrees   *)
Compute classify "| a\`b\`c |".     (* KRow   -- djot.js agrees   *)
```

The first result is now `KRow`; the other two controls remain unchanged.

The second line is the control and it is why this is narrow rather than
a disagreement about verbatim: an *unescaped* odd backtick really does
open a verbatim span that swallows the closing bar, and both engines
make the line a paragraph. The divergence is only about the escape.
`Line.row_cells` moved `vb_step` on every backtick it saw; the inline
scanner honoured a preceding `\` and the row scanner did not, so the two
disagreed about where the cell ended.

**Verdict: ours, and it was a bug rather than a choice.** No theorem
rested on it and no `wf_block` condition excluded the row, so the
argument of *When the oracle's answer is unrepresentable* does not
apply -- the row is representable and we simply did not build it.

**The repair.** Outside verbatim, `row_cells` now consumes a backslash
and its following byte together, matching the inline scanner's escape
parity. Inside verbatim the backslash stays literal, so it cannot protect
a closing backtick run. An escaped final bar is also rejected rather than
mistaken for the row closer.

Before the edit, a five-character alphabet probe (`a`, space, `\`, `` ` ``,
`|`) enumerated all 19,531 bar-wrapped lines through interior length six.
The repaired scanner makes 1,178 of them rows, rejects 2,074 false rows
whose final bar was escaped, and changes the cell split of 12 surviving
rows. Focused one-, two- and three-backslash controls match djot.js.

**What changed for the caller.** A rename may write a backtick into a
destination when the surrounding block otherwise remains canonical.
`Site.dest_backtick_breaks_row` has become `dest_backtick_row_ok`; the
bar counterexample remains, because destinations do not escape bars.

## Reclassified 2026-09-06 — three exact-HTML differences remain open

The earlier entries correctly reproduce djot.js and locate each
divergence, but they treated canonical unreachability or proof cost as
enough to close a difference. Those facts bound impact; they do not
establish conformance to the designated oracle.

`attributes.test:89` can follow djot.js by allowing an unattached spec to
produce no inline. `parse_inline_line_nonempty` must then exclude that
recovery case, and the block parser must omit an empty paragraph rather
than emit `Para []`. `attributes.test:95` can follow djot.js by allowing
the marker to disappear against the preceding `SoftBreak`;
`oresolve_app` and `para_inlines_cons2_closed` then need a side condition
excluding a pending attribute whose attachment depends on the appended
prefix. Canonical callers already avoid both shapes. Neither change
requires source replay.

`links_and_images.test:220` can also remain single-pass. The destination
state can retain both the ordinary inline interpretation and the exact
candidate source, choosing the source when `)` arrives and the inline
interpretation at end of input. This adds state and proof obligations,
but does not feed any byte through tokenization twice.

**Revised status.** Those three cases are open conformance work, not
intentional semantics. `attributes.test:370` remains the sole intentional
exact-HTML divergence: djot.js's failed-spec recovery calls
`reparseAttributes` on already-consumed source, directly conflicting
with `iscan_str_no_reread`. All four remain unreachable from canonical
renderer output and therefore do not threaten roundtrip.

## Reclassified 2026-09-06 — `attributes:370` is open too

The preceding correction still inferred too much from djot.js's
implementation. `reparseAttributes` does backtrack: it buffers a failed
attribute region and submits it to the inline scanner again. But the
observable result does not require that algorithm.

A parser can initialize an ordinary-inline shadow from the state before
`{` and advance it beside the attribute candidate on each new byte. If
the spec closes, it selects the attribute branch. If the candidate dies
at end of input, it selects the already-current shadow, which has turned
quotes smart and allowed delimiters to interact with scopes opened before
the `{`. No byte is replayed.

**Revised status.** `attributes.test:370` is an open conformance gap.
All four exact-HTML differences are now open and none requires weakening
the no-backtracking goal. See [[no-backtracking]] for the interpretation
that distinguishes an oracle implementation's replay from behaviour
that inherently requires replay.

## Closed 2026-09-08 — `attributes:89` and `attributes:95`, and what they cost

Both cases were one arm of `oattach_list`. A spec with nothing before it
and a spec sitting on a `SoftBreak` were the same disposition -- put the
source back as text -- and they had to stay the same disposition,
because the head below a waiting spec is a `SoftBreak` exactly when an
`oout_app` splice put a previous line there. Distinguishing them would
have made attachment see the splice, which every `_app` lemma denies.
Dropping the spec in both arms keeps them one case and follows djot.js,
so the two were one edit, not the two of unequal cost the reclassified
entry above described.

**What the earlier entry got wrong.** It priced `attributes:95` as a side
condition on `oresolve_app` and `para_inlines_cons2_closed`, reasoning
that letting a spec disappear against a `SoftBreak` makes resolution
sensitive to whether the paragraph is scanned whole or split at that
line. It does not: djot.js attaches to the break node, where the spec
renders as nothing, and *dropping* is the same observable. Both
decompositions then answer with nothing, and the lemma stands unchanged.

**What it did cost.** `oattach_list` can now return `[]`, so a nonblank
line can yield no inlines. That falsified `parse_inline_line_nonempty`
and the whole `iscan_productive` family behind it -- 700 lines, deleted.
Its consumers were three `wf_block` clauses asking a construct to be
nonempty: `Para`, `Keyed`'s label, and a `Table`'s caption.

The first two were relaxed rather than guarded, and that is the part
worth recording. `wf_block` is not the roundtrip domain -- `roundtrip_
blocks` quantifies over `cblocks_ok`, and `wf_complete_false` says
outright that `wf_block` does not characterize parser output. So the
question the lessons file poses (*would matching falsify `parse (render
d) = d` for a `d` the parser can reach?*) answers no here, and the oracle
wins: djot.js emits `<p></p>` for `{.a}{.b}` and `<strong></strong>` for
`*{.a}*`, and now so do we. The caption keeps its clause -- `Some []`
is a second spelling of `None`, which is a canonicity condition and not
a rendering one -- so `caption_of` tests the inlines rather than the
lines.

Relaxing rather than guarding also settled a case no guard would have:

```
{#i}
{.a}{.b}

x
```

djot.js gives the pending `{#i}` to the empty paragraph
(`<p id="i"></p>`, then `<p>x</p>`). A parser that omitted the empty
paragraph would have carried the pending set past the blank to `x`, and
`step_empty_carriable` -- the lemma that says a state emitting nothing
can still carry pending attributes -- would have become false with no
cheap repair.

**Fallout, and it is a regression.** `attributes.test:253` was matching
by accident and no longer does. The corpus number is 283 -> 284, not
285.

```
{%
SPDX-FileCopyrightText: 2025
%}

Hello.
```

djot.js renders the three lines as a literal paragraph; we now render
`<p></p>`, because the block attribute machine fails on them, retracts
to a paragraph of the lines it ate, and the *inline* machine then reads
`{%`..`%}` as a comment spec that closes, attaches to nothing and is
dropped. Both engines drop such a spec inline (`x{% c` / `%}y` is `xy`
in djot.js), so the difference is that djot.js never inline-parses those
lines at all: the source a block-attribute candidate consumed comes back
as literal text. Two adjacent probes pin the shape -- `{#i` / `*a*` and
`{a=x` / `*b*}` both still match, because there the re-parse happens to
reproduce the source.

**Verdict: ours, open.** This is the block-level member of the
recovery-of-consumed-source family that `attributes:370` and
`links_and_images:220` are the inline members of, and it wants the same
answer: a candidate advanced beside an ordinary shadow, with the shadow
chosen when the candidate dies. It is not a reason to keep the source in
`oattach_list`, which was fixing the wrong layer.

**Also removed.** `OMark` carried the spec's source for the dropped
disposition alone, so the field went with it, and with it
`ilist_ok`'s `nonempty_str src` clause and `iattr_mark`'s brace
reconstruction. `state_wf`'s `forallb nonblank` clauses had no consumer
left once `Para` lost its nonemptiness obligation, so `PPara`,
`PHeading`'s accumulator, `PAttr`'s slices, `PTable`'s caption lines and
`PKey`'s two strings carry nothing now. Net -845 lines.

## Probed 2026-09-08 — what `attributes:253` actually needs

Ten minutes against `block.ts:533-596` and djot.js, before designing
anything. Three results.

**Our continuation rule is already djot.js's.** The block attribute
container requires `this.indent > container.extra.indent` of a
continuation line, which is `Nat.ltb aind (off + indent_of l)`. A
multi-line spec succeeds on both sides when its later lines are indented
(`{#i` / `  .c}` / `x`, `{%` / `  c` / `  %}` / `x`) and fails on both
when they are not. Nothing to change there.

**The whole difference is one flag.** On failure djot.js calls
`para.inlineParser.reparseAttributes()` over the slices it accumulated:
the consumed source goes through the inline scanner with attribute
recognition *disabled*, and the paragraph resumes with it enabled. We
re-scan the same slices with attributes on. Every probe where the
re-scan reproduces the source agrees (`{#i` / `*a*`, `{a=x` / `hello`);
`:253` differs because `{%`..`%}` re-scans into a comment spec that
closes and is dropped.

One probe was a red herring and is worth recording so it is not chased
again: `{a=x` / `*b*}` renders literally on both sides, which looked
like the recovery suppressing emphasis. It is not -- `q` / `*b*}` is
literal too. A `*` closer followed by `}` simply cannot close.

**The cheap fix does not exist.** Escaping the slices' braces so an
ordinary scan reads them literally is not attributes-off:
`ibrace_step` consults `dstyle_of` before `inline_attrs_enabled`, so
attributes-off still opens `{-`, `{+` and every other marked delimiter,
while `\{` would not. And `with_inline_attrs false` cannot be applied to
the whole paragraph, because only the slices are attributes-off.

**Verdict: ours, open, and it is the same repair as the other two.** A
shadow scan advanced beside the candidate and adopted on failure. The
block layer's version is cheaper in one way -- `PAttr` can carry an
`iscan` without making `iscan` recursive -- and dearer in another: the
paragraph it retracts into has to be able to continue a scan someone
else started. `PPara` is mentioned 556 times, so that is a constructor,
not a field, and it pays the standing-quantifier list (`pad_state`,
`pstate_depth`, `lazy_ok`, `is_idle`, `in_fence`, `nested_container`,
`state_wf`, `finish`). Not the small independent step it was scoped as.

## Closed 2026-09-09 — a `]` that closes nothing keeps its opener

Found while probing the destination gap, not from the corpus: no case in
the 287 has the shape, and the generated corpus cannot reach it either,
since our renderer escapes a `]` in a label.

```
[u]b](c) d
```
| | |
| --- | --- |
| djot.js | `<a href="c">u]b</a> d` |
| ours, before | `[u]b](c) d` |

djot.js's `]` handler (`inline.ts:401-440`) closes the bracket for
exactly three following bytes -- `(`, `[`, `{` -- and returns null for
every other one, which leaves the `]` as an ordinary `str` match *and
the `[` opener on the stack*. So a later `]` can still close it, and
nothing between the two is cleared: `[*u]b*](c)` links a label of
`<strong>u]b</strong>`.

We closed at the `]` itself and put the brackets back as literal text
when the next byte disagreed, which resolved the label, abandoned any
delimiter scope opened inside it, and popped the frame -- all three
irreversible.

**The fix was to move the close one byte later.** `IClosed` now holds
the pending text and the untouched state (`IClosed (txt : string) (o :
ostate)`, down from three fields), `ilead`'s `]` arm is
`IClosed txt o` with no test at all, and `bclose` runs in the arm that
dispatches the next byte. Its `None` needs no unreachable case: no
bracket open means the `]` was text, which is the same fall-through.
Behaviour on every other input is unchanged, and `bclosed_lit` is now
reached only through the span, reference and destination fallbacks.

Two things came out of it rather than being paid for. `iresolve`'s
`IClosed` arm is a text state instead of a literal reconstruction, so
`iscan_wf_resolve` closes it by `exact H`; and
`attr_inside_a_decaying_bracket` moved to djot.js's reading
(`[a{.c}b] c` is `<span class="c">[a</span>b] c`) without being aimed
at -- the scope stays open, `oflatten` merges the opener's `[` into the
`Str` the spec attaches to. The note claiming a match would need
resolving twice was wrong, and is gone.

**Verdict: closed.** Measured over 200,966 documents in the alphabet
`[](){}*_a!\` (exhaustive at length 5, sampled at 6-11), run through
both parsers and djot.js: mismatches against djot.js go 826 -> 447. Of
the 391 documents whose output changed, 384 moved onto djot.js, five
moved off it and two changed without reaching it.

The seven are one thing, and it is not a mistake in the rule. Keeping
the opener alive makes a *later* `]` close it, so inputs that used to
stop at literal brackets now reach `IReference` and `IDest` -- and those
two read their region as raw source where djot.js keeps scanning it.
`_*[]][a_` is the shape: the trailing `_` closes the emphasis for
djot.js and is swallowed by our reference label. That is
`links_and_images:220`'s family (§*An unterminated link destination*)
plus its reference-label sibling, now reachable from more inputs rather
than newly wrong.

`make probe` runs the sweep's shape in miniature; the sweep itself used
`harness/main.exe --convert [--batch]`, added here so ours can be driven
on one document like the two oracle scripts can.

**Two adjacent gaps the sweep turned up, both predating this change and
both confirmed against the parent commit.** A backslash does not protect
a `]` in a reference label -- `[a][b\]c] d` is `<a>a</a> d` upstream and
`<a>a</a>c] d` here, because `INote` carries an `esc` flag and
`IReference` does not. And a `_` directly after a `{` cannot open:
`{a_x_` is `{a<em>x</em>` upstream and literal here, which has nothing
to do with brackets and accounts for 101 of the 447.

## Probed 2026-09-09 — `links_and_images:220` is not an ordinary shadow

The note under *An unterminated link destination* priced the repair as
"run the ordinary inline scan beside the candidate and keep it at end of
input". Probing djot.js refutes that shape three times over, and each
refutation is a constraint on whatever replaces it.

**The region is not a fresh scope, and not the ambient one either.**
`*x [u](a* b` is literal on both sides: a delimiter closer inside a
destination may not reach an opener from before the `[`. That is
`inline.ts:150` in so many words -- "When inside a link destination,
don't match openers from outside the link construct" -- and it is a
barrier the ambient scope stack does not have, since `oclose_go` walks
straight past a `FKBracket`. `[u](a *b [v](c) d* e` shows the barrier is
only at the bottom: matching inside the region is ordinary.

**The barrier is on `self.destination`, which a `]` does not clear.**
Only the closing `)` sets it false (`inline.ts:493`). So `*x [u](a ]b* c`
is still literal after the `]`, while `*x [u](a ](b) c* d` matches once
the destination has actually resolved.

**And a `]` inside the destination re-enters the bracket rather than
being text.** `[u](a ](b) c` is a link whose *label* is `u](a `, and
`[u](a ]{.c} b` is a span of the same. The opener is the original `[`,
so the region a failed destination gives back is not free-standing
content spliced after a literal `[u](` -- it is the label of a construct
that may still complete. `[u](a ]b ](c) d` is a link labelled
`u](a ]b `, which is that composed with the `]`-keeps-its-opener rule
above.

So the failure state is the bracket's own scope, still open, with the
label content and the `](` inside it as text; the success state is the
resolved `kids` and the accumulated `dst`. Both have to be live at once,
which is the two-state shape the note assumed, but the failure half is
a *frame* on the ordinary stack -- bracket-transparent to `bclose`,
opaque to `oclose_go` -- rather than an independent scan. Whether
`IDest` should carry an `iscan` at all is therefore open again: what it
needs is a frame kind, and the ordinary scanner running in it.

No implementation is proposed here. What is settled is that the three
gaps do not share one repair: `attributes:253` and `attributes:370` want
a scan with a different table, and this one wants a scope with a
different closing rule.

## Closed 2026-09-09 — an unterminated link destination

`links_and_images.test:220`. Upstream turns a destination's region into
source *at* the balanced `)` (`inline.ts:470`); with no `)` it keeps
whatever the ordinary scan made of it, so `[unclosed](hello *a` / `b*`
emphasises across the break and we rendered the region literally.

The probe entry above this one is what settled the shape: the region is
not a free-standing scan spliced after a literal `[u](`, because a
delimiter closer in it may not reach an opener from before the `[`
(`inline.ts:150`). It is the bracket's own opener, still open.

**So the `](` pushes the opener back.** `FKDest` is that frame: `[` or
`![` as its decay, a bracket to `fr_src`, and a barrier to `oclose_go`,
which now stops rather than abandoning it. `IDest` carries the ordinary
reading beside the destination one -- `sh : iscan`, the same scanner one
scope in, fed the same bytes -- and the byte that ends the state picks:
the balanced `)` builds the node from `kids` and `dst` and drops the
shadow, and the end of the paragraph keeps the shadow and drops the
rest. Neither is a replay.

`iscan` is recursive as a result, so `istep`, `ibreak`,
`ifinish_ostate`, `iout_app` and `iscan_wf` are fixpoints. The cost of
that was smaller than it looks: `ibreak` and `ifinish_ostate` split into
a `_flat` half over resolved states, which every existing case analysis
now runs on unchanged, and a two-line recursive half. `bdest_lit` and
its two lemmas are gone -- there is no literal fallback any more.

**One thing the probes did not predict.** A closer barred by the frame
must become *text*, not an opener: upstream adds a default match and
returns (`inline.ts:155-158`), where "no opener at all" falls through to
opening. `oclose_barred` is that distinction, and without it
`*[(](*\*[[` emphasised a backslash. It cost one arm in
`idelim_resolve` and one line in each of that function's three lemmas.

**Measured** over 260,806 documents in two alphabets (`[](){}*_a!\` and
`[](*_a` plus space and backtick, exhaustive at length 5, sampled to
12): mismatches against djot.js **1452 -> 943**, with 510 documents
moving onto the oracle, one off it and five changed without reaching it.
The corpus goes **284/287 -> 285/287**; shape, roundtrip, generated and
keyed are unchanged.

**Verdict: closed, with a named residue.** All six of those documents,
and the one that moved off, are the rule this step did not take: a `]`
inside a destination re-enters the bracket, so `[u](a ](b) c` is a link
labelled `u](a `. That wants `bclose_go` to offer the frame back *and* a
rule retiring `IDest` when its shadow consumes the frame, since
otherwise two candidates stay live. The barrier's exact extent is a
second, smaller residue: upstream applies it only when the top `[`
opener is the explicit link, so a plain `[` opened inside the
destination switches it off. Both are stated in
`.project/exact-html-gaps.md` under *The residue of the destination
gap*.

## 2026-09-09 -- djotjs-bug: the smart-quote default is process-global

Found while sweeping the attribute alphabet, where it accounted for 4069
of 4610 reported mismatches and none of them were real.

`betweenMatched(c, annotation, defaultmatch, opentest)` returns the
scanner for one delimiter row, and the scanner assigns to
`defaultmatch` (`inline.ts:118-136`):

```js
if (has_open_marker && defaultmatch.match(/^right/)) {
  defaultmatch = defaultmatch.replace(/^right/, "left");
} else if (has_close_marker && defaultmatch.match(/^left/)) {
  defaultmatch = defaultmatch.replace(/^left/, "right");
}
```

`defaultmatch` is the *outer* call's parameter. The eight rows are built
once at module load, so the assignment outlives the scan, the paragraph
and the document. Only the two quote rows are affected: the other six
are built with `"str"`, which neither regex matches. `cli.ts` aside,
these are the only mutable module-level bindings in the parser.

Within one document: `a "b {"} c "d` renders `a “b ”} c ”d`, the third
quote taking the default the second one left behind. djoths gives `“d`
and so do we. Across documents in one process, every document after a
`{"` or a `"}` inherits the flip.

**The harness now defines it away rather than adjudicating it.** Batch
mode existed to avoid node startup and promised nothing else; the leak
made it disagree with the same documents run one per process, so a
sweep's number depended on enumeration order. `djotjs.mjs` restores both
defaults before each document by parsing `{"` and `'}`, which are the
two spellings that flip a default back and change nothing when it is
already the row's own. Checked over 4680 documents in the alphabet
`{}#."='a`: batch output is now byte-identical to one process per
document, and `make test` and `make generated` do not move. Neither did
they before, so nothing published was wrong; the instrument was.

**The intra-document behaviour is left alone and is not settled here.**
Matching it means carrying a per-paragraph mutable default that no other
part of the scanner has, to reproduce an upstream aliasing slip that
djoths does not share. It is filed as `djotjs-bug` on the same footing
as the others: the syntax reference says the heuristics "can be
overridden by using curly braces to mark a quote as an opener `{"` or a
closer `"}`" (§Smart punctuation), which marks the quote the braces are
on and says nothing about the ones after it.

`.project/exact-html-gaps.md` counts two `ours` gaps and does not count
this one, since it is upstream's slip and not our divergence.

## Closed 2026-09-09 — an unclosed inline attribute keeps its ordinary reading

`attributes.test:370`. An attribute candidate used to retain only the
source consumed by `apparser`, so end of input could restore it only as
literal text. djot.js replays that region with attribute recognition off;
the observable result is the smart quote in `{a=" inline text`, and does
not inherently require replay.

This entry supersedes the preceding entry's statement that
`.project/exact-html-gaps.md` counts two `ours` gaps.

`IAttr` now carries an ordinary-inline `sh` beside the attribute machine.
The two readings consume each byte together. A completed spec selects the
attribute reading; immediate failure or paragraph end selects `sh`.
`istep_at` and `ibreak_at` carry a local attribute-recognition bit, false
only for that shadow. This is equivalent to scanning under
`with_inline_attrs false`, but keeps every other table capability implicit
and unchanged. `ifinish_ostate`, `iout_app`, and `iscan_wf` recurse through
the new field as they already did for `IDest`.

**Measured.** Exact HTML moves **285/287 -> 286/287**; the only corpus
remainder is `attributes.test:253`. The 6,167-document generated corpus
remains exact against djot.js. The full Rocq/Dune build succeeds.

**Verdict: closed.** No source byte is replayed, and the well-formedness
proof carries both live readings explicitly. The block-level recovery is
separate because it must return a scan in progress to the paragraph state.

### The reading is cut at slice boundaries

Keeping the ordinary reading current is not the same as scanning the
region as one string, which is what a first pass did. `reparseAttributes`
re-feeds the region in the slices the attribute parser was fed, and those
are cut at every byte of `reSpecial` (`inline.ts:67`), so each special
byte is the last byte of its own feed. A matcher whose loop is bounded by
that end cannot see past it: `{a--` is two hyphens and not an en dash,
`{...` three periods and not an ellipsis, `x{% <a> y` a literal
`<a>`, and `x{% \ y` a literal backslash. What crosses a boundary is
what lives in the parser rather than in the slice -- an open delimiter,
verbatim mode, a math prefix that peeks at the next byte -- so `{a="x"*b*`
still pairs its delimiters.

`islice_end` is that disposition, applied by `iattr_feed` to the reading
it stores. It settles `IText true`, `IBrace`, `IPeriod`, `IDash`,
`IClosed` and `IAuto`, and leaves everything else alone.

**Measured**, over two sweeps against djot.js, one document per process
verified on the first mismatches of each:

| sweep | at `5ccb0a7` | now |
| --- | --- | --- |
| `{`, `x{` + words over `.-$!{]*"a=% }'`, length <= 3 (5,908 docs) | 164 wrong | 60 |
| `x{% B y`, `x{a="B" y` for B over `<>[]()!\`*-.$a" {}\\_`, length <= 3 (14,478 docs) | 9,038 wrong | 507 |

No document that matched djot.js at `5ccb0a7` stops matching. Of the 507,
389 are the pre-existing `}`-inside-a-quoted-value family (wrong at
`5ccb0a7` too, and about `apparser`, not about slices), 112 are backtick
runs, which are cut in djot.js and not here -- a two-tick run inside a
region is two one-tick runs upstream and one unclosed run for us -- and
the rest are the `"`/`'` decay families this file already records.

## 2026-09-09 -- ours: a `key=` slice hides a marked opener

`{a=}=` is `<p>{a</p>` with a `<mark>}</mark>` upstream and literal text
here. The `=` the attribute machine took as the value separator becomes
a mark *opener* in djot.js's re-scan, pairing with the trailing `=` over
the `}` that failed the spec. Ours reads that same `=` as the closer of
a `=}` that decays, so nothing pairs.

Found by re-running the length-5 sweep over `{}#."='a` at `f159676`,
where it is the one mismatch that is not the decayed-quote attachment of
[[exact-html-gaps]].

**The shape, not the mechanism.** Probes bound it to the state rather
than the byte:

| input | agrees | |
| --- | --- | --- |
| `{a=}=` | no | the spec is live in `key=` when the `}` fails it |
| `x{a=}=`, `{a=}b=`, `{a=}=x` | no | leading and trailing text are irrelevant |
| `{#a=}=`, `{%=}=`, `{a=b}=` | yes | a different machine state at the `}` |
| `{a=}~}~`, `{a=}^}^`, `{a=}*}*` | yes | `~`, `^` and `*` do not reproduce it |
| `{a=}=}`, `{a==}`, `{a=x=`, `=x=` | yes | needs both the failure and a later `=` |

So it takes an attribute machine waiting for a value, a `}` that fails
it, and a marked-only row whose one-byte lookahead falls where the slice
was cut. `islice_end` settling the opener's pending side is the
candidate, since that is the disposition [[exact-html-gaps]] records for
the shadow, but it has not been pinned against `inline.ts` and no lemma
is named yet.

**Verdict: ours, undiagnosed.** One document in 37,448. Logged so the
re-measured count in [[exact-html-gaps]] has something to point at.

## Closed 2026-09-09 — a failed block attribute spec's lines

`attributes.test:253`. A `{` at the start of a line opens a block
attribute container; when the spec fails, djot.js converts it to a
paragraph and replays the lines it consumed through the inline parser
with `allowAttributes` false (`block.ts:592`, `inline.ts:651`). We kept
the same lines and read them with attributes on, so `{%` / `c` / `%}`
became a comment spec that closed across the paragraph, attached to
nothing and was dropped: `<p></p>` against upstream's three literal
lines.

The block path is the easy half of the inline one closed earlier the
same day. `block.ts:552` records one slice per line, so the region is a
whole number of leading lines and `islice_end`, the disposition that cuts
the inline shadow at every `reSpecial` byte, has no counterpart here.

**Closed.** `PParaOff k cur` is a paragraph whose first `k` lines are
read with the bit false, and `para_inlines_off` is that reading.
`para_recover` builds it at the two sites that were losing the bit: the
failure arm of `step`, and `finish` on a spec the input ended inside.

**Measured.** Exact HTML **286/287 -> 287/287**; the corpus has no
mismatch left. An 808-document sweep over two- and three-line
combinations of `{%`, `%}`, `c`, `  c`, `  %}`, `{#i`, `  .c}`, `{a=x`
and a blank goes from 92 mismatches to 46. The generated corpus stays
exact, roundtrip at depth 3 is clean, and the 37,448-document attribute
alphabet stays at 9 with no document changing.

**Verdict: closed.** What the sweep has left is below, and none of it is
this rule.

## Closed 2026-09-10 -- a blank line does not close a block attribute spec

```
{%

c
```

djot.js gives `<p>{%\nc</p>`, one paragraph joining the two lines with a
single soft break. We give two paragraphs, because `step`'s continuation
test is `Nat.ltb ind (off + indent_of l)` and a blank line fails it, so
the spec falls straight to the recovery and the recovered paragraph then
flushes on the same blank.

Two blanks do close it upstream (`{%` / blank / blank / `c` agrees), so
the rule is not "blanks are transparent".

**The mechanism** (`block.ts:566-598`). The continuation test is
`this.indent > container.extra.indent`, and a blank line is measured the
same way any line is, so an *unindented* blank fails it and drops into
the recovery arm on that very line. The arm emits `+para`, pops the
attribute container, replays the slices, and then sets
`this.pos = para.inlineParser.lastpos + 1` -- a position back inside the
lines it replayed. Everything after it in the line loop reads that
`pos`, so `isBlank = (self.pos === self.starteol)` is false: the blank is
never recognized as one, no new container is checked, and the paragraph
is handed an empty inline range. The next line continues it. A *second*
blank meets an ordinary open paragraph, whose `continue` refuses
whitespace, so it closes -- which is why the rule is not "blanks are
transparent".

The indent test is the whole of it, and a single space flips the answer:
`{%` / `""` / `c` is one paragraph, `{%` / `" "` / `c` is one paragraph
*containing a blank line*, because indent 1 > 0 makes the blank a
continuation whose slice is recorded. That second shape is the 2026-08
entry on a spec that *spans* a blank and then fails, and it stays
unmatched for the reason given there: `wf_block` excludes a paragraph
with a blank line in it and `roundtrip_blocks` would notice. The two
look alike, are separated by one space, and only one of them is closed.

24 of the 808 documents in the block sweep above. Closed 2026-09-10:
the `else` branch of `PAttr`'s continuation test now consumes a blank
without reprocessing it, leaving `PPend pend (para_recover 0 slices)`.
The one cost was `step_blank_lazy_false`, which quantified over all
states and is now false for an open spec; it took `blank_safe st = true`,
a hypothesis its single caller already had, and the added hypothesis
deleted two of its cases rather than adding any.

## 2026-09-09 -- djotjs-bug: a spec still open at the end loses its paragraph

```
{#i
  c
```

djot.js emits **nothing at all**. djoths and we emit `<p>{#i\nc</p>`,
and appending a blank line makes djot.js agree with us, so the paragraph
is lost on the `close()` path (`block.ts:600-616`) rather than withheld
on purpose: that path runs the same `reparseAttributes` the `continue`
path does and then calls `para.close()`, and the result does not reach
the output.

10 of the 808 documents in the block sweep. Logged, not matched.

## 2026-09-09 -- a container prefix inside the recovered paragraph

```
> {%
> c
> %}
```

| | |
| --- | --- |
| djot.js | `<p>{%\n&gt; c\n%}</p>` |
| djoths | `<p>{%</p>` then `<p>c\n%}</p>` |
| ours | `<p>{%\nc\n%}</p>` |

Note the `&gt; ` in djot.js's paragraph: the blockquote marker of the
second line is inside the text. Upstream replays absolute source
positions, and `this.pos = lastpos + 1` re-reads bytes the container
prefix had already eaten.

Three implementations, three answers, and the prose says nothing about
recovery from a failed block attribute spec at all. Reproducing djot.js
would mean keeping source offsets the parser does not have, to reproduce
a position slip rather than a rule. **Verdict: `SPEC-GAP`, ours stands**;
the top-level family is the one worth matching and is closed above.

## 2026-09-19 -- open: a spec after a word that djot.js splits into nodes

| Input | djot.js | ours |
| --- | --- | --- |
| `a b\*c{.x} d` | `a b<span class="x">*c</span> d` | `a <span class="x">b*c</span> d` |
| `a b--c{.x}` | `a b–<span class="x">c</span>` | `a <span class="x">b–c</span>` |
| `a b'c{.x}` | `a b’<span class="x">c</span>` | `a <span class="x">b’c</span>` |

djot.js attaches an inline spec to the last word of the last node before
it, and an escape or a smart-punctuation token starts a new `str` node, so
its "last word" stops at that boundary (`--sourcepos` shows `str "a b"`,
`str "*c"`). Our text merges across escapes and smart punctuation before
`oattach_list` runs `last_ws_split`, so the word runs back to the
whitespace. The apostrophe row makes this ordinary prose (`don't{.x}`).

Found while probing source locations, not measured over a sweep. Matching
would mean remembering where the last escape or smart-punctuation token
ended in the pending text, which is the same kind of spot the located
scanner has to keep for a word split anyway
(`260916.plan.source-locations.md` F8). Open conformance work, no verdict.

## 2026-09-21 -- ours: a table's span includes its caption

| Input | djot.js | ours |
| --- | --- | --- |
| `\| a \| b \|` / `\|---\|---\|` / `\| x \| y \|` / blank / `^ cap` | table `[0,29)`, caption `[33,36)` | table `[0,36)`, caption part `[31,36)` |

djot.js stops a table's `pos` at its last row and hangs the caption off
it as a separate positioned child; ours runs the table to the last byte
of the caption's text, and the caption's *part* span starts at the
authored `^` where its node span starts after it.  Both follow from
applying the plan's rule for what a node covers
(`260916.plan.source-locations.md` section 4.4) to the table's whole
construct.  What settles it is that the caption is a *child* of the
table in both ASTs, so djot.js's answer puts a child outside its
parent: the containment property step 3 of the plan states, and the one
a consumer walking the tree for the innermost node at a byte relies on.
Ours keeps it.  The caption's inline range is not affected: it is
djot.js's `[33,36)` exactly.  Pinned by `p_table_parts` and `c5_table_parts` in
`dev/check/Located.v`.

## 2026-09-26 -- ours: a decimal marker has at most 18 digits

| Input | djot.js | ours |
| --- | --- | --- |
| `1234567890123456789. ok` | `<ol start="1234567890123456800">` | `<p>1234567890123456789. ok</p>` |

djot.js reads the start with `parseInt` and prints the rounded float, so
from 16 digits on its `start` can differ from the number written
(`9999999999999999.` gives `start="10000000000000000"`).  Ours takes
no marker core longer than `Line.dec_digits_max` (18) digits, which keeps
every start below 10^18 and inside the OCaml `int` the extracted parser
represents numbers by (`Marker.dec_start_bound`).  Up to 15 digits the
two agree; from 16 to 18, ours prints the number written.  Pinned by
`decimal_too_long_is_text` in `OrderedList.v`.

## Closed 2026-09-28 -- a footnote's paragraph continues on a lazy line

| Input | djot.js | ours, before |
| --- | --- | --- |
| `[^n]: a` / `b` / blank / `[^n]` | note holds `a b` | note holds `a`; `<p>b</p>` in the main document |

Reported in jgm/djot discussion #414. The syntax reference lets a
footnote's paragraph lines omit the indentation, as in a block quote or
list item. `PFoot`'s continuation test took only blank lines and lines
indented past the opener, and closed on anything else without asking
`is_lazy`, which the quote and list branches do. It asks now.

Checked against djot.js for every line kind after an open paragraph in
a quote, a list item and a footnote: only a text line is lazy there,
and a line that opens a block ends the container, which is the rule
`is_lazy` already encodes. The one other difference that check shows is
a `^ b` line, the caption-without-a-table entry of 2026-08-22.

`step_lazy_restore` now states the rule for every container: a lazy
line parses as the same line with the containers' prefixes written
out. Pinned by `convert_footnote_lazy_line` and its two neighbours in
`Html.v`.

## 2026-09-28 -- SPEC-GAP: how a heading ends

Two cases found while pinning the syntax reference's prose
(`dev/check/Reference.v`). djot.js and ours agree on both; the
reference does not say what either does.

| Input | djot.js and ours | What the reference says |
| --- | --- | --- |
| `## a` / `# b` | two headings, `a` at level 2 and `b` at level 1 | "The heading ends when a blank line (or the end of the document or enclosing container) is encountered", and continuation lines "may also be preceded by the same number of `#` characters". Nothing about a different number. |
| `> # a` / `b` | one heading `a b` inside the quote | Lazy lines are allowed on "regular paragraph lines" of a block quote, list item or footnote. A heading is not a paragraph. |

The first contradicts the reference's sentence on how a heading ends,
unless a line of a different level counts as the start of a new block.
The second is `lazy_ok`'s `PHeading` case, which is deliberate: a lazy
line continues "the innermost open inline container (a paragraph or a
heading)". `lazy_stack_line` states only the paragraph case, as the
reference does.

**Verdict: `SPEC-GAP`, ours stands** (it matches djot.js on both).
Pinned by `heading_other_marker_count` and `heading_ends_with_container`
in `dev/check/Reference.v`.

## 2026-09-28 -- SPEC-GAP: an ambiguous marker with nothing after it

| Input | djot.js and ours |
| --- | --- |
| `v) a` | `<ol start="5" type="i">`, lower roman |

The reference says `v)` is both a lower-roman and a lower-alpha marker,
and that an ambiguity "will be resolved in such a way as to continue the
list, if possible". A one-item list has nothing to continue, and the
reference does not say which reading wins then. Both engines take roman.

**Verdict: `SPEC-GAP`, ours stands.** Pinned by `ordered_v_paren` in
`dev/check/Reference.v`.

## Closed 2026-09-29 -- djotjs-bug: a div's closing fence loosens a list, against the reference

| Input | djot.js and ours | The reference |
| --- | --- | --- |
| `- :::` / `  a` / `  :::` / `- c` | loose (`<p>c</p>`) | tight: "A list is classed as *tight* if it does not contain blank lines between items, or between blocks inside an item" |

No line of the input is blank. djot.js decides blankness after the
container closers have consumed the line (`block.ts:1051`), so a `:::`
that closes a div counts as a blank line; this was matched on purpose in
"Fixed: a div's closing line arms the enclosing list" (2026-08-09
section above), which compared against djot.js only.

Found while auditing the reference's tightness rule.

**Verdict: `djotjs-bug`, fixed 2026-09-29.** We follow the reference: the
arming is an artifact of where djot.js tests for a blank line.  Reported
upstream as jgm/djot.js#157.  The fix reverses "Fixed: a div's closing
line arms the enclosing list" (2026-08-22): `div_closer` is gone from
`step`, and with it `lines_gap`, `item_gap` and `item_ok`'s gap conjunct
in ListUniformity.v, since an item that ends on a nonblank line again
leaves no blank armed.  The two shapes that section's "Still ours"
residue kept out of the canonical view are back in
(`Roundtrip.div_ending_item_roundtrip`).  Pinned by
`list_div_closer_not_blank` in `dev/check/Reference.v`.

## Closed 2026-09-29 -- djotjs-bug: a blank before a nested list or an empty last item does not loosen

| Input | djot.js and ours | The reference |
| --- | --- | --- |
| `- a` / blank / `- - b` | tight | loose: the blank is between items, not at the start or end of a list |
| `- a` / blank / `-` | tight | loose, as above |
| `- a` / blank / `-` / `- b` | loose | loose |

Both are reported upstream as jgm/djot.js#45, where jgm calls them a bug
and notes that djot.lua gives the loose reading.

The first row reverses "a blank before an item that opens a list"
(2026-08-10), which matched djot.js on purpose by adding `starts_list`
to `list_next` (Step.v) and to `seps_loosen` and `list_loose_of`
(ListUniformity.v). The 2026-08-09 corpus entry had argued the loose
reading from the reference and the rationale; the fix a day later
overrode it.

The second row had a different cause: `list_next` kept the blank armed
when the marker had nothing after it, so it loosened only if another
item followed (third row).

**Verdict: `djotjs-bug`, fixed 2026-09-29.** `list_next` now spends an
armed blank into looseness at every sibling marker, whatever follows the
marker on its line; `starts_list` is gone from Step.v and
ListUniformity.v.  A blank before a nested list *inside* an item still
does not loosen (`list_content`), as the reference's `- two` / blank /
`  - sub` example requires.  Pinned by
`list_blank_before_nested_list_item` and
`list_blank_before_empty_last_item` in `dev/check/Reference.v`.

Generated documents against djot.js went from 0 mismatches to 531 (and
0 to 184 with lazy lines).  Every one differs from djot.js only in `<p>`
wrapping, and each is one of the three shapes: ours looser in 480 and
172, tighter (the div closer) in 51 and 12.  The accepted roundtrip pool
at depth 3 grew from 43857 to 57857, from the `Loose` spellings the old
rule made unreachable and the div-ending items.

## 2026-09-29 -- SPEC-GAP: which list a blank inside a nested block counts against

Found while stating the reference's tightness rule.  djot.js and ours
agree on all five; the reference does not decide them.

| # | Input | djot.js and ours |
| --- | --- | --- |
| a | `- - b` / blank / `- c` | outer tight |
| b | `- a` / blank / `  - b` / blank / `- c` | outer tight |
| c | `- - a` / blank / `  b` | outer tight |
| d | `- :::` / `  x` / blank / `  y` / `  :::` | tight |
| e | `- :::` / `  d` / blank / `- c` (div left open) | tight |

::: a
- - b

- c
:::

::: b
- a

  - b

- c
:::

::: c
- - a

  b
:::

:::: d
- :::
  x

  y
  :::
::::

:::: e
- :::
  d

- c
::::

In (a) to (c) the blank ends a nested list and also separates two items,
or two blocks of one item, of the outer list.  "Blank lines at the start
or end of a list do not count against tightness" does not say whether
the exemption also covers the outer list.  jgm's own djot.js tests say
it does: `lists.test` lines 242 and 308 (commit 0ec53d5f, 2022-12-24)
expect `- a` / blank / `  - b` / `  - c` / blank / `- d` and its
neighbour tight.  At the start of a nested list he ruled the other way
when the blank is between outer items (jgm/djot.js#45, entry above), so
the two edges are not symmetric.

In (d) and (e) the blank is part of the div's contents.  We read "blocks
inside an item" as the item's own blocks, as for a blank inside a code
block.

**Verdict: `SPEC-GAP`, ours stands** (it matches djot.js and jgm's tests
on all five).  Row (e) reversed 2026-09-30: see "Closed 2026-09-30 --
SPEC-GAP: whether a div left open at the end of an item holds the blank after
it".  The alternative for (a) to (c), where the blank loosens
the outer list, is on branch `hy/blank-after-nested-list`: it passes
every check of ours and fails the two djot.js tests.

## Closed 2026-09-29 -- djotjs-bug: a blank after a footnote in an item does not loosen

| Input | djot.js | Ours and the reference |
| --- | --- | --- |
| `- [^n]: a` / blank / `  b` | tight | loose: the blank is between two blocks of the item |
| `- [^n]: a` / blank / `- c` | tight | loose: the blank is between items |
| `- [^n]: a` / blank / `      b` / `- c` | tight | tight: the blank is inside the footnote |

A reference definition in the same place loosens in both engines
(`- [r]: u` / blank / `  b`).  The reference does not treat the two
differently; its exemption for "blank lines at the start or end of a
list" names lists only.

djot.js records a blank against a list only when the list is the
innermost open container or the one below it (`blankline` in
`src/parse.ts`).  A footnote in an item is a third level, list > item >
footnote, so the blank is dropped before the next line closes the
footnote.  A reference definition closes at the blank, so the list is
the second level again.  The same two-level lookup is behind
jgm/djot.js#157.  No test in djot.js covers a footnote in a list item.

Ours matched djot.js because `blank_absorbed` counted an open footnote
as absorbing, like a nested list.  Whether the blank is the footnote's
is known only at the next line: a line the footnote takes (indented
past its `[`) continues it, and anything else ends it.

**Verdict: `djotjs-bug`, fixed 2026-09-29.**  A footnote no longer
absorbs a blank in `blank_absorbed` (it reads through to what the
footnote has open, so a blank inside a nested list or code block in the
footnote is still theirs), and a content line the footnote takes clears
the armed flag without loosening (`foot_takes`, since renamed `keeps_line`, `list_content` in
Step.v; the mirrors `lines_loose` and `scan_list_content` in
ListUniformity.v).  Not reported upstream yet.  Pinned by
`list_blank_after_footnote_in_item`,
`list_blank_after_footnote_between_items` and
`list_blank_inside_footnote` in `dev/check/Reference.v`.  The generated
and file corpora do not change against djot.js (generated 531 and 184
mismatches, file 0), and the depth-3 roundtrip still accepts all 57857.

## Closed 2026-09-29 -- djotjs-bug: a blank before a table's caption loosens the list

| Input | djot.js | Ours and the reference |
| --- | --- | --- |
| `- \| a \|` / blank / `  ^ cap` / `- c` | loose | tight: the caption is part of the table |
| `- \| a \|` / blank / `  b` / `- c` | loose | loose: the table and the paragraph are two blocks |

The reference on captions: "The caption can come directly after the
table, or there can be an intervening blank line."  The blank is inside
the table, as a blank inside a footnote is inside the footnote.  djot.js
counts it because the caption is a separate container that opens after
the blank has been recorded.

Found by a throwaway probe while stating the reference's tightness rule
(`Tightness.v`): over about 268,000 hand-built item shapes, the caption
was the only case where the parser loosened and no blank separated two
blocks.

**Verdict: `djotjs-bug`, fixed 2026-09-29.**  `keeps_line` (Step.v),
which was `foot_takes`, now also answers for a table that a caption line
continues, so the caption clears the armed flag without loosening.  Not
reported upstream yet.  Pinned by `list_blank_before_caption` and
`list_blank_after_table` in `dev/check/Reference.v`.  The generated and
file corpora do not change against djot.js, and the roundtrip pools
keep their counts.


## Closed 2026-09-30 -- SPEC-GAP: whether a div left open at the end of an item holds the blank after it

| Input | djot.js, djoths | djot.lua | Ours |
| --- | --- | --- | --- |
| `- :::` / blank / `- b` | tight | loose | loose |
| `- [^1]: :::` / blank / `- b` | tight | loose | loose |
| `- :::` / `  - x` / blank / `- b` | tight | loose | loose |
| `` - ``` `` / blank / `- b` | tight | tight | tight |
| `- :::` / `  a` / blank / `  b` / `  :::` (row d above) | tight | loose | tight |

The reference says an unclosed div or code block ends "with the end of
the document or containing block", and does not say whether the item
ends before or after a trailing blank.  djot.js and djoths let the open
div hold the blank, as they do a blank inside it.  The blank adds
nothing to the div (the tree is the same without it), so the item is
read as ending at its last nonblank line, as an item with a closed div
does, and the blank lies between items.  A code block is different: the
blank becomes a line of its text, in all three engines and at the end of
a document too, so it is inside the item and the list stays tight.

Found while proving the converse of LS4 (`Tightness.v`): with the
footnote row, `separates_after` held and the list was tight, because
`closes_at`'s paragraph line ended the footnote and with it the div.

**Verdict: `SPEC-GAP`, ours changed; row (e) of the 2026-09-29 entry is
reversed.**  A blank inside a div that continues after it is still the
div's own (row d), where djot.lua differs.  `blank_absorbed` (Step.v)
no longer counts an open div, unless a block inside it holds the blank
(`blank_held`: code, an attribute spec, a key waiting for its fence);
`keeps_line` answers for an open div, so a line the item still has
clears the armed flag without loosening.  `separates_after` in
Tightness.v now says the blank leaves the item's blocks unchanged,
in place of `closes_at`.  Pinned by `list_blank_after_open_div` and
`list_blank_in_open_code` in `dev/check/Reference.v`.  The generated and
file corpora and the depth-3 roundtrip do not change.  Provisional, to be
revisited.

## 2026-09-30 -- SPEC-GAP: which whitespace may follow a quote's `>`

| Input | djot.js and ours |
| --- | --- |
| `>` then a tab, then `a` | a block quote holding `a` |

The reference says a quote line begins with `>` "followed either by a
space or by the end of the line".  djot.js's marker pattern is
`[>][ \t\r\n]`, so a tab or CR also counts, and `quote_prefix` accepts
any `is_ws` character, the same set.

**Verdict: `SPEC-GAP`, ours stands** (it matches djot.js).  Stated by
`classify_quote_marker` in `Line.v`, which names `is_ws`.

## 2026-09-30 -- SPEC-GAP: whitespace before a div's class

| Input | djot.js and ours |
| --- | --- |
| `:::foo` / `a` / `:::` | a div with class `foo` |

The reference says a div opens with "a line of three or more consecutive
colons, optionally followed by white space and a class name".  Read as
"optionally followed by (white space and a class name)", `:::foo` would
not open a div.  djot.js's `pattDivFenceEnd` allows no whitespace, and
so does `div_open`.

**Verdict: `SPEC-GAP`, ours stands** (it matches djot.js).  Stated by
`classify_div_fences` in `Line.v`, whose `gap` may be empty.

## Closed 2026-10-02 -- ours: whether a table has a caption is decided by its inlines

| Input | djot.js AST | ours until 2026-10-02 | HTML (both) |
| --- | --- | --- | --- |
| `\| a \|` / `^ {.x}` | `caption` with no children | no caption (`None`) | no `<caption>` |
| `\| a \|` / `^ x` | `caption` holding `x` | `Some [x]` | `<caption>x</caption>` |
| `\| a \|` alone | `caption` with no children | `None` | no `<caption>` |

The HTML is the same; the trees are not.  djot.js's AST gives every table
a caption node, empty when there is none, and its HTML renderer skips an
empty one (`src/html.ts:291`, "AST always has at least a dummy caption").
Whether a caption shows is decided at rendering.  Ours decides it in the
parser: `caption_of` (Step.v) runs the inline parser on the caption's
lines and returns `None` when the inlines come out empty.  That is the
choice the 2026-09-08 entry made, to keep `Some []` from being a second
spelling of `None`; djot.js has no second spelling because it has no
`None`.

The cost is the one exception to "block structure can be discerned
prior to inline parsing": `^ {.x}` has content, but djot's inline parser
leaves nothing of it, so whether the table has a caption depends on the
inline parse.  `block_shape_independent` erases captions for this reason,
and `inline_attrs_affect_caption_presence` (Invariants.v) exhibits the
dependence by comparing djot's inline syntax with one that has inline
attributes off.

Two ways to remove the exception, neither changing the HTML:

1. Decide by the lines: a `^` line with content is a caption even when
   its inlines are empty, and `^ ` alone is none.  `Some []` and `None`
   then both occur, and `wf_block` and `cblocks_ok` need a clause
   choosing one.
2. Follow djot.js: a table's caption is `inlines`, empty meaning none.
   One spelling, and the exception goes away with the option.  Touches
   the `Table` constructor everywhere: Step, Html, Roundtrip, Wf, and
   the `ocaml/` API, where the caption stops being optional.

**Verdict: ours, closed 2026-10-02 by option 2.**  `Table`'s caption is
`inlines` and `caption_of` returns the caption's inlines as parsed, so
the three inputs above give `[]`, `[x]` and `[]`, the shape of djot.js's
AST.  `inline_attrs_affect_caption_presence` is deleted and
`block_shape_independent` erases only inlines.  The caption's located
range (`PTable`) is now present whenever a `^` line was read, whatever
its inlines.  The `ocaml/` API changes with it: `Block.Table` carries
`Inline.t node list`, not an option.  The test suite, the generated
corpus against djot.js and the roundtrip pools keep their counts.

## 2026-10-03 -- ours: block attributes replace a div's class word

| Input | djot.js | ours |
| --- | --- | --- |
| `{.a}` / `::: b` / `y` / `:::` | `<div class="a b">` | `<div class="a">` |

Found while pinning the baseline for `.project/261001.plan.custom-tags.md`.
djot.js pushes the div's container with the pending block attributes
already on it (`pushContainer` calls `addBlockAttributes`), and the
fence's word then arrives as a `class` event, which appends
(`parse.ts:536`).  Ours builds the div with the word as its class
(`Step.div_block`) and then applies the pending set by assignment
(`Attr.apply_pending`, through `decorate_head`), so the pending `class`
overwrites the word.  The reference says classes given more than once
"will be combined", for inline attributes and for repeated block specs
alike.

**Verdict: ours, open.**  Not reported upstream, and not a djot.js
question.  The fix is in `apply_pending`: a pending `class` goes before a
class the block already has, as djot.js's order gives.  With custom tag
names on, `::: b` writes a name rather than a class, so there the case
does not arise.

## 2026-10-04 -- SPEC-GAP: which punctuation a heading identifier drops

Found while stating the reference's identifier rule over all texts
(`is_id_sep_punct`, `id_base_word_sep` in `Document.v`).  djot.js and
ours agree; the reference's wording says something else.

| Input | djot.js and ours | What the reference says |
| --- | --- | --- |
| `# a.b` | `a-b` | "removing punctuation (other than `_` and `-`)": read literally, `ab`. |
| `# c:d;e` | `c:d;e` | `:` and `;` are punctuation other than `_` and `-`, so `cde`. |

djot.js replaces each run of whitespace and of the bytes
``[]~!@#$%^&*(){}`,.<>\|=+/?`` by one space, trims, and joins with `-`
(`getUniqueIdentifier`, `parse.ts`).  So punctuation separates words
instead of vanishing, and the four ASCII punctuation bytes missing from
that list besides `_` and `-` are kept: `"`, `'`, `:`, `;`.  Bytes
outside ASCII are kept as well.  The reference's own example,
`My heading + auto-identifier`, comes out the same under both readings.

**Verdict: `SPEC-GAP`, ours stands** (it matches djot.js).  Identifiers
are link targets, so following the wording instead would break links
that work under djot.js.  Pinned by `heading_identifier_punctuation` in
`dev/check/Reference.v`.

The verdict was chosen by the agent and is pending the maintainer's
decision.  Following the wording instead is a change to `is_id_sep` and
`id_base` in `Document.v`, and the theorems that state the rule
(`is_id_sep_punct`, `id_base_word_sep`) would be restated with it.

## 2026-10-05 -- SPEC-GAP: which whitespace may follow a list marker

Found while stating the marker table over every spelling
(`classify_list_marker` in `Line.v`).

| Input | djot.js | Ours |
| --- | --- | --- |
| `-` then a tab, then `a` | a bullet item holding `a` | the same |
| `1.` then a tab, then `a` | an ordered item | the same |
| `- [x]` then a tab, then `a` | a checked task item | the same |
| `-` then a tab, then `[x] a` | a bullet item holding `[x] a` | a checked task item |

The reference says a list item is "a list marker followed by a space (or
a newline)", and a task item "begins with `[ ]`, `[X]`, or `[x]`
followed by a space".  Both engines take a tab or CR where it says
space, after a marker and after a checkbox, as they do after a quote's
`>` (2026-09-30).

**Verdict for the first three rows: `SPEC-GAP`, ours stands** (it
matches djot.js).

The fourth row is a difference.  djot.js matches a task marker with one
pattern that has a literal space between the bullet and the box, so a
tab there falls through to the plain bullet, whose own pattern takes the
tab.  Ours reads the bullet first, with any `is_ws` character after it,
and then looks for the box at the start of the item (`list_marker`).
The reference states the task rule about the item, "a bullet list item
that begins with" a box, and both engines accept the item in the fourth
row as a bullet list item, so by the wording it is a task item.

**Verdict for the fourth row: ours stands, pending the maintainer's
decision**; chosen by the agent.  Pinned by `task_tab_after_bullet` in
`dev/check/Reference.v`.  Following djot.js instead is a change to
`list_marker` (ask for a space before `task_check`) and to the
`SpellTask` clause of `marker_spelling`.

## 2026-10-05 -- a block attribute spec between a nested list and a blank

Found while trying to drop `run_safe` from the tightness theorems
(`Tightness.v`), which excludes an item whose lines leave a block
attribute spec open at a line boundary.  The item below holds a nested
list, a spec that attaches to nothing, and a paragraph.

| Item's lines | djot.js | Ours |
| --- | --- | --- |
| `- x` / `{.a}` / blank / `para` | loose | tight |
| `- x` / `{.a}` / blank / blank / `para` | loose | loose |
| `- x` / blank / `para` | tight | tight |

Ours changes its answer with the number of blanks.  The first blank
meets the spec still open (`blank_absorbed` of `PAttr` is true), so it
is not counted; it completes the spec, whose attributes are dropped, and
leaves the item idle.  A second blank then meets an idle state and is
counted.  djot.js counts the first blank already.

The rule as `Tightness.separates` states it calls both tight: the lines
before either blank parse to the nested list alone, and a blank directly
after a nested list ends is exempt.  So with the first two rows the
parser loosens at a blank the rule does not count, and
`item_loose_separates` is false without `run_safe`:
`["- x"; "{.a}"; ""; ""; "para"]` is the counterexample.

**Verdict: ours, decided 2026-10-06 (below).**  Two ways out:

- Follow djot.js.  The blank is not directly after the list, a spec
  line lies between, so it counts.  That is a change to `separates` (the
  exemption asks about the last line before the blank, not only the
  blocks) and to what a blank does at a finished spec.
- Keep the rule.  A spec that attaches to nothing is no block, so the
  blank is still directly after the list.  Then the second row is the
  bug: the state after a dropped spec must remember that a list just
  ended.

Either way `run_safe` cannot be dropped before this is settled.

**Decided 2026-10-06, by the maintainer: loose**, for a reason of its
own, not djot.js's.  An attribute line with a blank or the end of its
container after it attaches to nothing, and is a block of its own that
renders nothing, as a reference definition is.  The blank then lies
between that block and `para`, not directly after the nested list
(`list-tightness.md`, D1 and "Dangling block attributes").  djot.js
agrees on the output.  The parser decides tightness this way since
2026-10-06, but still drops the attribute from the AST, and
`Tightness.separates` reads the AST: on the input above it sees the
nested list end before the blank and calls it tight.  So
`item_loose_separates` is still false without `run_safe`, now with one
blank as well as two.  What remains is the attribute block in the AST,
and then the theorems without `run_safe`.

## 2026-10-05 -- SPEC-GAP: a heading is interrupted by any block opener

Follows the 2026-09-28 entry on how a heading ends, found while stating
it over every line (`heading_ends_at` in `Uniformity.v`).

| Input | djot.js and ours |
| --- | --- |
| `# a` / `- b` | a heading, then a list |
| `# a` / `> b` | a heading, then a quote |
| `# a` / `***` | a heading, then a thematic break |
| `# a` / a table row | a heading, then a table |

The reference says a heading ends at "a blank line (or the end of the
document or enclosing container)", and that a paragraph "can never be
interrupted by other block-level elements".  It does not say a heading
can be.  In both engines only a text line or a `#` line of the same
level continues a heading; every other line ends it and is read afresh.

**Verdict: `SPEC-GAP`, ours stands** (it matches djot.js).

## 2026-10-05 -- tightness cases collected in `list-tightness.md`

The tightness entries above are spread over two months and several were
reversed.  `list-tightness.md` lists every case with its current
outputs and says which verdicts are settled, which are provisional and
which are open.  Read it before any of the entries above.


## 2026-10-05 -- OURS: list tightness follows the proposal in `list-tightness.md`

A list item and a footnote end with their last nonblank line, so a blank
after an item lies between items and always loosens the list.  Inside an
item a blank loosens unless it is directly before or after a nested list
(an attribute on the nested list counts as part of it) or inside a
nested block.  A code block with no closing line drops its trailing
blank lines, everywhere.

| Input | djot.js | ours before | ours now |
| --- | --- | --- | --- |
| `- - b` / blank / `- c` | tight | tight | loose |
| `- a` / blank / `  - b` / blank / `- c` | tight | tight | loose |
| `- - a` / blank / `  b` | tight | tight | tight |
| ```` - ``` ```` / blank / `- b` | tight, code `"\n"` | tight, code `"\n"` | loose, code `""` |
| ```` ``` ```` / blank (end of document) | code `"\n"` | code `"\n"` | code `""` |
| `- - x` / `  {.a}` / blank / `  para` / `- b` | loose | tight | loose |
| `- a` / blank / `  {.x}` / `  - b` / `- c` | loose | loose | tight |

The fourth and fifth rows change the AST as well as the spacing.  The
last row is jgm/djot issue #200, where the djot author says tight.

Against djot.js: the test suite has 2 mismatches of 287, `lists.test`
242 and 308, both the second row's shape.  Generated documents: 1667 of
8687 differ, and 524 of 2074 with lazy lines; every one of them only in
`<p>` wrapping (before: 531 of 7094 and 184 of 1686, also all spacing).
The generated corpora grew with the round-trip fragment, which accepts
81845 documents at depth 3, up from 57857, since a loose rendering with
a nested list at an item's end now parses back as written.

**Verdict: `OURS`**, from the syntax reference as `list-tightness.md`
reads it.  C1 and D1 there are closed; B2 to B4 stand as before.

## 2026-10-07 -- SPEC-GAP: the attribute language

Found while writing the attribute grammar (`AttrSyntax.v`) and proving
the machine accepts exactly it (`AttrAgree.v`).  djot.js and ours agree
on every row; the reference is silent or says otherwise.

| Input | Both engines | What the reference says |
| --- | --- | --- |
| `a{.x class="y"}` | `class="y"` | Stacked specs "will be combined": |
| `a{.x}{class="y"}` | `class="x y"` | `avant{lang=fr}{.blue}` "is the same as" `avant{lang=fr .blue}`. |
| `a{k="x\<y"}` | value `x\<y` | "Backslash escapes may be used inside quoted values"; text escapes (O2) cover all ASCII punctuation. `<`, `>`, `@` are not escapable in a value. |
| `a{k="a  b"}` | value `a b` | Nothing.  Runs of space, CR and LF become one space; a tab is kept. |
| `a{#é}`, `a{#a;'"}` | identifiers | Nothing on identifier characters: any byte but whitespace and ASCII punctuation, where `: _ - ; ' "` do not count. |
| `a{.é}` | not a spec | Nothing on class characters: those of a bare value. |
| `a{# }`, `a{.}` | a spec with no attributes | Nothing. |
| `a{.a%c%}` | not a spec | Nothing on separation: an identifier, class or bare value is followed by whitespace or `}`; a quoted value or a closed comment by anything (`a{%c%.a}`, `a{k="v".c}`). |
| `a{k=v k=w}` | `k="w"` | The last value of a key wins, as stated for identifiers only. |

In the first two rows a `class` key inside one spec is an assignment
(`Attr.set`), while a later spec merges with `Attr.merge`, which
combines classes.

Inline only, outside the attribute language: a spec cannot begin with a
delimiter character, though `_` and `-` are key characters: `a{-k=v}` and
`a{_k=v}` read `{-` and `{_` as marked openers.

**Verdict: `SPEC-GAP`, ours stands** (it matches djot.js on every row).
The grammar states each choice where it is made.  Chosen by the agent and
pending the maintainer's decision.

## Closed 2026-10-08 -- ours, fixed: a backslash before `]` in a reference label

Found while probing escapes for the inline specification
(`261007.plan.inline-specification.md`, stage 1).

| Input | djot.js | ours before | ours now |
| --- | --- | --- | --- |
| `[a][b\]c]` | a link to label `b\]c` | a link to label `b\`, then `c]` | as djot.js |

djot.js matches the label's `]` with its general matcher, where `\]` is
an escape and closes nothing.  Our label state (`IReference`) ended at
any `]`, though the footnote label state already let a backslash protect
one (2026-08-15).  `IReference` now carries the same pending-backslash
flag as `INote`: the backslash and the byte after it go into the label
as written.  A canonical reference label (`ci_ok`) now has no backslash
(`ref_label_safe`), as a canonical footnote label already had none.
`make diff`, `make roundtrip`, `make check-stack` unchanged.  Pinned by
`reference_label_escaped_bracket` in `dev/InlineExamples.v`.

## 2026-10-08 -- open: a backslash before a line break inside a destination

Found with the entry above.

| Input | djot.js | Ours |
| --- | --- | --- |
| `[a](b\` / `c)` | `href="bc"` | `href="b\c"` |

L3 says the line breaks of a split URL are ignored and the lines
concatenated, which gives `b\c` read literally; djot.js reads the
backslash and the line break together as a hard-break escape and drops
both.  Ours stands for now; pending the maintainer's decision.  The
inline specification will state whichever is chosen.
