---
ai-disclosure: ai-generated
---
# The exact-HTML gaps, and what their status means

Evergreen, per [[README]]: it says what the gap is now. The list below
is regenerated with

```
dune exec harness/main.exe -- --verbose --report exact.txt
```

which prints input, expected and ours for every case either oracle
disagrees on. Ours are the ones with a `gallina:` line.

## What the two corpus numbers are measuring

`make shape` compares block structure with inline content dropped, and
is **287/287**. `make test` compares exact HTML and is **285/287**. Both
remaining cases are the same shape: djot.js re-reads the source a failed
attribute candidate consumed, with attribute recognition switched off,
and we re-read it with attributes on. Both are open conformance gaps.

Neither is reachable from a canonical document, which is why the
generated corpus and roundtrip are clean. That bounds their effect and
keeps them out of the roundtrip theorem. It does not make a difference
from the designated djot.js oracle correct or finished.

The third case, an unterminated link destination
(`links_and_images.test:220`), was closed on 2026-09-09; what is left of
it is below, under *The residue*.

## The two

### A block-attribute candidate's lines, re-parsed

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
| ours | `<p></p>` then `<p>Hello.</p>` |

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

**Open conformance gap, and not a cheap one.** The obvious shortcut is
refuted: escaping the slices' braces so an ordinary scan reads them
literally is not the same as scanning with attributes off, because
`ibrace_step` checks `dstyle_of` *before* `inline_attrs_enabled` -- so
attributes-off still opens `{-`, `{+` and the other marked delimiters,
and `\{` would not. `with_inline_attrs false` and the `DTable`
construction in `Profile.v` make "the same table with attributes off"
expressible in one definition, but the scan is not uniform: only the
*slices* are attributes-off, and the rest of the paragraph is not. The
faithful shape is a shadow scan advanced beside the candidate as lines
arrive, adopted on failure -- the same design as the two below, with the
difference that here it costs a `pstate` change (a paragraph state that
can continue a scan someone else started) rather than a self-recursive
`iscan`. `PPara` has 556 mentions, so a field on it is the wrong end;
a separate constructor pays the standing-quantifier list instead.

This one *is* reachable from a canonical document in principle, since it
is the parser's own paragraph that differs; it does not threaten
roundtrip, because both sides of the difference parse and render
consistently.

Logged 2026-09-08 under *Closed -- `attributes:89` and `attributes:95`*,
which is what exposed it: the case matched by accident while an
unattached spec kept its source. The mechanism above was pinned the same
day.

### An unclosed spec whose source an inline scan would have claimed

`attributes.test:370`

```
{a=" inline text
```
| | |
| --- | --- |
| djot.js | `<p>{a=“ inline text</p>` |
| ours | `<p>{a=" inline text</p>` |

Note the curly quote. When a spec fails, djot.js replays the slices it
already fed the attribute machine through the *inline* scanner with
attributes switched off (`reparseAttributes`, `inline.ts:637`), so the
`"` turns smart on the second pass.

**Open conformance gap.** djot.js's implementation backtracks here, but
its output does not require backtracking. A one-pass parser can advance
the attribute candidate and an ordinary-inline shadow together as each
new byte arrives. A closing `}` selects the attribute branch; end of input
selects the shadow, which has already interpreted the quote and any
delimiters in their original context. No consumed byte is replayed.

That product state is more involved than the current `IAttr` state, but
implementation and proof work are not semantic reasons to reject the
oracle result. `iscan_str_no_reread` describes the current outer scanner;
it does not prove this recovery behaviour impossible. See
[[no-backtracking]] for the project-wide interpretation.

**Boundary.** The two agree on every spec that *closes*, whatever it
contains. They differ only on a spec that never closes and whose source
holds a byte an inline scan would have claimed, and the attribute
machine admits an arbitrary byte in exactly two states -- a quoted value
and a `{% %}` comment. So `{#id`, `{.class` and `{key=bare` are agreed
even unclosed.

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

## Diagnosis is not closure

`oracle-disagreements.md` is append-only, one entry per divergence, and
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
   Both cases in this note are currently in this class. For
   `attributes:370`, the oracle's implementation replays source, but a
   product state can compute the same output without replay -- which is
   what the destination gap turned out to want, and got.

Canonical unreachability is still important: it proves that an open gap
cannot invalidate canonical roundtrip. It is not evidence that the
parser already follows djot.js on that input.

## The caveat

`ours` is a verdict the project passes on itself, so 285/287 must be
reported as two open compatibility gaps. They need not give up
`wf_block`, canonical roundtrip, or no-backtracking: their helper
theorems can be stated on the domain their consumers actually need.
Quote 287/287 on shape separately; it has no such qualification.

And three is what the *corpus* shows, which is not what is left.
`[u]b](c)` -- a `]` whose next byte makes no construct, which djot.js
leaves as text with the `[` opener still alive -- was a divergence on
plain input that no corpus case and no generated document contains. It
was found by probing the destination gap and closed on 2026-09-09
without either number moving.
