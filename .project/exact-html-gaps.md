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
is **287/287**. `make test` compares exact HTML and is **284/287**. The
three cases in the difference are one family: djot.js keeps a candidate
running beside the ordinary scan and we do not, so the source a failed
candidate consumed comes back differently. All three are open
conformance gaps.

Two of them are unreachable from a canonical document, which is why the
generated corpus and roundtrip are clean. That bounds their effect and
keeps them out of the roundtrip theorem. It does not make a difference
from the designated djot.js oracle correct or finished.

## The three

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

The block attribute machine fails on the three lines and both engines
retract to a paragraph of them. djot.js emits the consumed source as
literal text; we re-parse it, and the inline attribute machine reads
`{%`..`%}` as a comment spec that closes, attaches to nothing and is
dropped. Dropping is right -- `x{% c` / `%}y` is `xy` in djot.js too --
so the difference is only that djot.js never runs the inline scan over
those lines.

**Open conformance gap.** It is the block-level member of the family the
two below belong to, and takes the same repair: keep the candidate's
source beside an ordinary scan and choose the source when the candidate
dies. Two adjacent inputs stay in agreement and mark the boundary --
`{#i` / `*a*` and `{a=x` / `*b*}` both match, because there the re-parse
reproduces the source.

This one *is* reachable from a canonical document in principle, since it
is the parser's own paragraph that differs; it does not threaten
roundtrip, because both sides of the difference parse and render
consistently.

Logged 2026-09-08 under *Closed -- `attributes:89` and `attributes:95`*,
which is what exposed it: the case matched by accident while an
unattached spec kept its source.

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

### An unterminated link destination

`links_and_images.test:220`

```
[unclosed](hello *a
b*
```
| | |
| --- | --- |
| djot.js | `<p>[unclosed](hello <strong>a\nb</strong></p>` |
| ours | `<p>[unclosed](hello *a\nb*</p>` |

djot.js has no destination *mode*. It leaves every matcher running
inside `](` and turns the region literal only when the balanced `)`
arrives (`inline.ts:470`). With no `)`, it keeps what it matched.

**Open conformance gap.** Nothing forbids matching this: no theorem is at
stake and no source has to be re-read. A conforming one-pass state can
run the ordinary inline scan while also retaining the candidate
destination source. It keeps the source when `)` closes the destination
and keeps the inline interpretation at end of input. That is additional
state and proof work, but it is compatible with the no-backtracking
contract. The canonical renderer always closes a destination, so the
work changes malformed-input recovery rather than roundtrip behaviour.

**Boundary.** We agree whenever the destination closes, since a closed
destination's content is literal either way.

Argument under *2026-08-13 -- ours: constructs inside an unterminated
destination*.

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
   All three cases in this note are currently in this class. For
   `attributes:370`, the oracle's implementation replays source, but a
   product state can compute the same output without replay.

Canonical unreachability is still important: it proves that an open gap
cannot invalidate canonical roundtrip. It is not evidence that the
parser already follows djot.js on that input.

## The caveat

`ours` is a verdict the project passes on itself, so 284/287 must be
reported as three open compatibility gaps. They need not give up
`wf_block`, canonical roundtrip, or no-backtracking: their helper
theorems can be stated on the domain their consumers actually need.
Quote 287/287 on shape separately; it has no such qualification.
