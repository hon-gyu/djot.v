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
is **287/287**. `make test` compares exact HTML and is **283/287**. The
four cases in the difference are all inline and all in the same two
families. All four are open conformance gaps.

They are also all unreachable from a canonical document, which is why
the generated corpus and roundtrip are clean: none of these shapes can
occur in output the renderer produces. That bounds their effect and
keeps them out of the roundtrip theorem. It does not make a difference
from the designated djot.js oracle correct or finished.

## The four

### A spec with nothing it may attach to

`attributes.test:89`

```
{#id} at beginning
```
| | |
| --- | --- |
| djot.js | `<p> at beginning</p>` |
| ours | `<p>{#id} at beginning</p>` |

`attributes.test:95`

```
After {#id} space
{.class}
```
| | |
| --- | --- |
| djot.js | `<p>After  space\n</p>` |
| ours | `<p>After  space\n{.class}</p>` |

Both engines consume the first `{#id}` and drop it, since the text
before it ends in whitespace. They differ on `{.class}`, which sits
behind a soft break, and attachment declines a soft break.

djot.js's `-attributes` handler asks for the tip of the current
container and returns without doing anything when there is none
(`parse.ts:452`). The spec's source is already gone by then, consumed by
the attribute machine, so it vanishes.

**Open conformance gap.** The current implementation preserves a useful
unconditional productivity theorem: `parse_inline_line_nonempty` says a
nonblank line yields at least one inline. Following djot.js would falsify
that statement for `{#i}`. But the statement is a helper theorem, not a
djot semantic commitment. It can be narrowed to exclude input erased by
unattached attributes, while the block parser omits an empty paragraph
instead of constructing `Para []`. An empty heading already fits
`wf_block`.

The second case exposes a different proof boundary. Letting a spec at
the start of a line disappear against the preceding `SoftBreak` makes
resolution sensitive to whether the paragraph is scanned whole or
decomposed at that line. The current `oresolve_app` and
`para_inlines_cons2_closed` statements rule that out unconditionally.
They can instead acquire a side condition saying that no unresolved
attribute at the split may inspect the appended prefix. Canonical text
already discharges such a condition.

Neither repair requires source replay. The present behaviour kept the
theorems and their users simpler, but theorem convenience is not a
semantic reason to override the reference implementation. These two
cases remain work to do if exact djot.js recovery is the target.

Argument in `oracle-disagreements.md` under *2026-08-15 -- ours: a spec
with nothing before it*, amended 2026-08-22 when attachment moved after
the scan.

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
   All four cases in this note are currently in this class. For
   `attributes:370`, the oracle's implementation replays source, but a
   product state can compute the same output without replay.

Canonical unreachability is still important: it proves that an open gap
cannot invalidate canonical roundtrip. It is not evidence that the
parser already follows djot.js on that input.

## The caveat

`ours` is a verdict the project passes on itself, so 283/287 must be
reported as four open compatibility gaps. They need not give up
`wf_block`, canonical roundtrip, or no-backtracking: their helper
theorems can be stated on the domain their consumers actually need.
Quote 287/287 on shape separately; it has no such qualification.
