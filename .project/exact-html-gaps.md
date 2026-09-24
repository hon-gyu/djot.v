---
ai-disclosure: ai-generated
---
# The exact-HTML gaps, and what their status means

Evergreen, per [[README]]: it says what the gap is now. The list below
is regenerated with

```
dune exec harness/main.exe -- --verbose --report exact.txt
```

which prints input, expected and ours for every case we get wrong.

## What the corpus numbers are measuring

On the test suite, block structure with inline content dropped is
**287/287**, and exact HTML is **287/287** as well, as of 2026-09-09: the corpus has no mismatch left. The generated
corpus is exact and roundtrip is clean.

That is a smaller claim than it sounds, and the rest of this file is why.
The corpus is djot.js's regression suite, not a map of the grammar, and
four divergences are open that no corpus case contains. Quote the number
with the list, or do not quote it.

Five cases were closed on 2026-09-09, in this order: an unterminated link
destination (`links_and_images.test:220`), a marked opener with a `}`
after it taking the wrong side of its row's decay (`{"}`), a byte a decay
had rewritten hiding the source byte from the next delimiter's open rule
(`a''b'`, `a--'b'`), an unclosed inline attribute spec
(`attributes.test:370`), and the block-level recovery below
(`attributes.test:253`). Only the first and the last two moved the corpus
number; the others were found by sweeping, which is the point of the
clause in [[project-engineering-lessons]] about the corpus not being the
grammar.

Two more closed on 2026-09-10, both in the block-attribute recovery and
neither in the corpus: a blank line failing to close an open spec, and
the recovery dropping the attribute set an earlier spec left pending.
See [[260909.block-attr-reparse]].

## What is open

Four, none of them in the corpus:

| | where |
| --- | --- |
| a spec attaching to a decayed quote (`'{.a}`) | below |
| `{a=}=`, a `key=` slice hiding a marked opener | [[djotjs-divergences]] |
| a `]` inside a link destination re-entering the bracket | below |
| a container prefix inside a recovered paragraph | [[djotjs-divergences]] |

## Closed 2026-09-09 — a block-attribute candidate's lines, re-parsed

`attributes.test:253`

```
{%
SPDX-FileCopyrightText: 2025
%}

Hello.
```
| | |
| --- | --- |
| djot.js | `<p>{%\nSPDX-FileCopyrightText: 2025\n%}</p>` then `<p>Hello.</p>` |
| ours, before | `<p></p>` then `<p>Hello.</p>` |

**The mechanism, pinned** (`block.ts:533-596`). The container opens on a
`{` at the start of a line and keeps a live `AttributeParser`. Its
`continue` requires `this.indent > container.extra.indent`, so a
continuation line must be *more* indented than the brace -- which is our
rule too, `Nat.ltb aind (off + indent_of l)`. When the parser fails, or
when the indent runs out with the spec unfinished, djot.js converts the
container to a paragraph and calls
`para.inlineParser.reparseAttributes()` on the slices it accumulated:
the consumed source is scanned by the *inline* parser with attribute
recognition disabled, and the paragraph then continues normally, with
attributes enabled again, from `lastpos + 1`.

We accumulate the same slices and re-scan them with attributes **on**.
That is the whole difference. Four probes fix the boundary, and we match
djot.js on all of them: `{#i` / `  .c}` / `x` succeeds as one multi-line
spec on both sides (modulo the known attribute-ordering `render-only`
difference), `{%` / `  c` / `  %}` / `x` likewise, and the two
unindented recoveries `{#i` / `*a*` and `{a=x` / `hello` agree because
there the re-scan happens to reproduce the source. `:253` differs only
because its slices re-scan into a *comment* spec that closes, attaches
to nothing and is now dropped.

**Closed.** `PParaOff k cur` is a paragraph whose first `k` lines are
read with attribute recognition off, and `para_inlines_off` is that
reading. `para_recover` builds it at the two sites that were losing the
bit: the failure arm of `step`, and `finish` on a spec the input ended
inside. The count is not always `length slices` -- an indented line that
fails the spec is frozen too, and reaches the paragraph by being
reprocessed rather than by being recorded -- which is `para_recover`'s
`extra` argument.

This was priced here, before it was done, as a `pstate` change paying the
standing-quantifier list, and that was right. What the estimate missed
is that it is the *cheap* half of the inline gap closed the same day:
`block.ts:552` records one slice per line, so the region is whole lines
and `islice_end` has no counterpart. Six definitions needed a real arm,
five more were already right under a catch-all, and no proof needed an
argument about `k > 0`.

The obvious shortcut stays refuted, and is worth keeping written down:
escaping the slices' braces so an ordinary scan reads them literally is
not the same as scanning with attributes off, because `ibrace_step`
checks `dstyle_of` *before* `inline_attrs_enabled` -- so attributes-off
still opens `{-`, `{+` and the other marked delimiters, and `\{` would
not.

The corpus moved **286/287 -> 287/287**, an 808-document block sweep
went 92 mismatches to 46, and the generated corpus, roundtrip and the
37,448-document attribute alphabet did not move. The whole piece of work,
with its measurement and its hypotheses, is in
[[260909.block-attr-reparse]].

Logged 2026-09-08 under *Closed -- `attributes:89` and `attributes:95`*,
which is what exposed it: the case matched by accident while an
unattached spec kept its source.

### Still open — a blank line does not close a spec

The same sweep has 36 documents left, and they are one rule, not this
one:

```
{%

c
```
| | |
| --- | --- |
| djot.js | `<p>{%\nc</p>` |
| ours | `<p>{%</p>` then `<p>c</p>` |

A single blank line leaves the spec open upstream and two close it. Our
continuation test is `Nat.ltb ind (off + indent_of l)`, which a blank
line fails, so the spec falls to the recovery and the recovered paragraph
flushes on the same blank.

Not diagnosed, and **not the blank-line case this file already decided
against matching**. That one is a spec that *spans* a blank which djot.js
records as a slice, so the recovered paragraph contains a blank line,
which `wf_block` excludes because it does not round-trip. Here the
djot.js's paragraph holds no blank at all. The shapes look alike and the
verdict does not carry across; see [[djotjs-divergences]] under the
same date.

### Closed 2026-09-09 — an unclosed inline spec

`attributes.test:370`

```
{a=" inline text
```
| | |
| --- | --- |
| djot.js | `<p>{a=“ inline text</p>` |
| ours, before | `<p>{a=" inline text</p>` |

Note the curly quote. When a spec fails, djot.js replays the slices it
already fed the attribute machine through the *inline* scanner with
attributes switched off (`reparseAttributes`, `inline.ts:637`), so the
`"` turns smart on the second pass.

djot.js's implementation backtracks here, but its output does not require
backtracking. A one-pass parser can advance
the attribute candidate and an ordinary-inline shadow together as each
new byte arrives. A closing `}` selects the attribute branch; end of input
selects the shadow, which has already interpreted the quote and any
delimiters in their original context. No consumed byte is replayed.

**Closed.** `IAttr` now carries that ordinary scan as `sh`. `istep_at`
threads one local `attrs_enabled` bit: the candidate advances with the
ambient setting while its shadow advances with the bit false, and
`ifinish_ostate` selects the shadow if the candidate remains open. The
same bit is threaded through `ibreak_at`, so a multi-line candidate keeps
both readings current. No source byte is submitted to either reading
twice.

The shadow is not a scan of the region as one string: `reparseAttributes`
re-feeds the region in the slices the attribute machine was fed, cut at
every byte of `reSpecial`, so a matcher bounded by a slice end cannot see
past it. `islice_end`, applied where `iattr_feed` stores the shadow, is
that disposition -- which is why `{a--` is two hyphens and `x{% <a> y` a
literal `<a>`, while an open delimiter or verbatim mode, being parser
state rather than slice state, still crosses. The mechanism, the sweeps
that measured it and the families left over are in
[[djotjs-divergences]] under the same date.

The corpus moved **285/287 -> 286/287** and the 6,167-document generated
corpus stayed exact against djot.js. See [[no-backtracking]] for the
project-wide interpretation.

**Boundary.** The two agree on every spec that *closes*, whatever it
contains, and on every spec that *fails*, because there the re-scan
happens to reproduce the source. What was left after the shadow landed
was a spec that never closes and whose source holds a byte an inline
scan would have claimed, so the question was which states of the
attribute machine swallow such a byte rather than reject it. There are
three, not the two this note first claimed: a quoted value, a `{% %}`
comment, and an **id**, which takes any byte but whitespace and the
closing brace. `{#a"}x` was a span with that quote in its identifier on
both sides while `{#a"` differed.

`{.class` and `{key=bare` are agreed even unclosed, as the note said,
and for the reason it gave.

The family was 435 of the 439 mismatches this sweep reported before the
shadow landed, and is **0** here: `{#a"`, `{a="x` and `{% "x` all agree
now. Re-measured 2026-09-09 at `f159676`, exhaustive at length 5 over
`{}#."='a` (37,448 documents), the sweep leaves **9**, and none of them
is this family. Eight are the decayed-quote attachment below and one is
the marked-delimiter case in [[djotjs-divergences]] under *2026-09-09
-- ours: a `key=` slice hides a marked opener*.

The implementation trace is under *2026-08-22 -- ours: an unclosed
inline attribute spec*. Because that log is append-only, its old verdict
is superseded by *Reclassified 2026-09-06 -- `attributes:370` is open
too* at the end of the file.

## The residue of the destination gap

`links_and_images.test:220` is closed: an unterminated destination now
keeps the reading the ordinary scan gave it, because the `](` pushes the
bracket's opener back as an `FKDest` scope and scans the region inside
it. The scope decays to the `[` when the paragraph ends, so the label
and the `](` come back as the text they are.

What is not matched is one rule inside that scope, and it is worth
stating precisely because six documents in a 260k sweep still turn on
it:

**A `]` inside a destination re-enters the bracket.** Upstream's `]`
handler finds the same `[` opener it always does, so `[u](a ](b) c` is a
link whose *label* is `u](a `, and `[u](a ]{.c} b` is a span of it. The
re-entry also clears every opener between the `[` and the new `]`, which
is why `(_[](*](***[` is literal upstream and emphasised here. Our
`bclose_go` stops at an `FKDest` frame instead of offering it back.

Matching it needs two things the current shape does not have: `bclose_go`
treating the frame as a bracket, and a rule retiring the `IDest` state
when its shadow consumes the frame -- otherwise the outer candidate and
the re-entered one both stay live and a later `)` has two answers.

**And one upstream quirk the barrier does not reproduce.** The
`inline.ts:150` check applies only when the *top* `[` opener is the
explicit link, so a plain `[` opened inside the destination switches the
barrier off: `_[]([!a*[*_` closes the outer `_` upstream. `fr_barrier`
bars unconditionally.

## A spec that attaches to a decayed quote

`'{.a}` renders `<span class="a">rsquo</span>` here and a bare right
single quote upstream: djot.js drops the attributes. Eight documents in
the sweep above -- both quotes, and `#id` as well as `.class` -- which is
all of its residue but one.

Not diagnosed. `oattach` takes the run below the spec, and upstream
attaches to the preceding *match*, where an unmatched quote's default
match is apparently not a thing attributes may land on. Found
2026-09-09; the mechanism has not been pinned against `inline.ts`, so it
is listed here as an open question rather than a boundary.

## Diagnosis is not closure

`djotjs-divergences.md` is append-only, one entry per divergence, and
every entry ends in a verdict naming an authority:

| verdict | meaning |
| --- | --- |
| `render-only` | same parse, different serialization |
| `djoths-outdated` | djoths implements older syntax; follow djot.js |
| `djoths-bug` | djoths contradicts the prose spec |
| `djotjs-bug` | djot.js contradicts the prose where djoths follows it |
| `SPEC-GAP` | the prose is silent; the corpus is the only authority |
| `ours` | our output differs after the behaviour and boundary have been diagnosed |

Most of the log is the first four. Those are not our gaps at all: they
are djoths disagreeing with djot.js, recorded in a baseline run before
any Gallina existed so that later work would not chase ghosts. It is why
djoths shows 25 mismatches in the same run that gives us 4.

Only `ours` appears in our number. Diagnosis means that the input is
reproduced, djot.js's behaviour is pinned by running it, and the boundary
of the divergence is stated and checked. It does **not** mean that the
difference is closed or excused.

There can be two statuses after diagnosis:

1. **Intentional property boundary.** Matching would contradict a
   property the project has chosen to guarantee on the relevant input
   domain, and adding a side condition would evade that intended
   guarantee.
2. **Open conformance gap.** Matching is compatible with the chosen
   properties, but needs implementation work or narrower helper lemmas.
   The remaining block-level case in this note is currently in this
   class. `attributes:370` demonstrated the other outcome: djot.js's
   implementation replays source, but a product state computes the same
   output without replay.

Canonical unreachability is still important: it proves that an open gap
cannot invalidate canonical roundtrip. It is not evidence that the
parser already follows djot.js on that input.

## The caveat

`ours` is a verdict the project passes on itself, and 287/287 on exact
HTML is now what the corpus shows. That is not what is left. Five
divergences are open and none of them is in the corpus, so the honest
report is the number *and* the list at the top of this file.

`[u]b](c)` -- a `]` whose next byte makes no construct, which djot.js
leaves as text with the `[` opener still alive -- was a divergence on
plain input that no corpus case and no generated document contains, and
it was closed on 2026-09-09 without either number moving. So were the two
quote families named at the top. The five that remain are open on the
same terms: found by sweeping, invisible to both corpora, and each one
measured against an alphabet rather than a test file.

**And the number the sweeps report is only as good as djot.js.**
Until 2026-09-09 `djotjs.mjs --batch` disagreed with the same documents
run one per process, because djot.js's smart-quote defaults live in a
closure the scanner assigns to. A sweep's answer then depended on
enumeration order. That is fixed and checked; the point to carry is that
a differential number needs djot.js to be a function before it means
anything. See [[djotjs-divergences]], *the smart-quote default is
process-global*.

The fix resets the defaults *between* documents, which is all batch mode
ever promised. Within one document the leak is upstream's and is left
alone, so a sweep whose alphabet contains `{`, `}` and a quote still has
to subtract it: the 37,448-document sweep above reports 613 against the
shipped djot.js and 9 against a copy with the assignment made local, and
the 604 in between are that quirk rather than ours. Patching it is three
lines in `djot.js/lib/inline.js` -- give the scanner `let defaultmatch =
defaultmatch0;` of its own -- and any sweep that mixes braces with quotes
should be read against the patched copy.
