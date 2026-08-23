---
ai-disclosure: ai-generated
---
# The exact-HTML gaps, and what "adjudicated" means

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
four cases in the difference are all inline, all in the same two
families, and all deliberate.

They are also all unreachable from a canonical document, which is why
the generated corpus is 5090/5090 and the roundtrip is clean: none of
these shapes can occur in output the renderer produces. They are
fidelity gaps against djot.js's hand-written regression suite, not
defects in anything the theorems quantify over.

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

**Forced by a theorem.** The deciding input is not either corpus case
but `# {#i}`, where the spec is a heading's whole content and djot.js
renders `<h1></h1>`. `parse_inline_line_nonempty` says a nonblank line
yields at least one inline; `para_inlines_nonempty` and the `wf_block`
obligation on paragraphs rest on it. Dropping the spec would falsify it
for the string `{#i}`, which our own parser can reach.

Note what the argument is *not*. `wf_block` does not forbid an empty
heading -- its case is `Nat.leb 1 level && wf_inlines ils`, and
`parse_blocks "#"` really does give `Heading 1 []`. What an empty
heading would break is the *inline* theorem, and only because `{#i}` is
a nonblank line. `oracle-disagreements.md`'s entry says "a block with no
children is not in `wf_block`" alongside the real reason; that clause is
true of `Para` and `Section` and false of `Heading`, and a correction is
appended under the entry.

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

**Forced by the no-backtracking commitment.** That replay re-reads bytes
the scanner has already dispatched, which is the one instance of genuine
backtracking in either engine and exactly what `iscan_str_fuel`
certifies we do not do. Matching would mean giving up the property the
project exists to state.

**Boundary.** The two agree on every spec that *closes*, whatever it
contains. They differ only on a spec that never closes and whose source
holds a byte an inline scan would have claimed, and the attribute
machine admits an arbitrary byte in exactly two states -- a quoted value
and a `{% %}` comment. So `{#id`, `{.class` and `{key=bare` are agreed
even unclosed.

Argument under *2026-08-22 -- ours: an unclosed inline attribute spec*.

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

**A cost decision, and the only one of the four that is.** Nothing
forbids matching this: no theorem is at stake and the canonical view can
never produce such a document. Our destination accumulates literal text;
djot.js can afford not to because it holds the subject string and
re-slices it. To match we would have to run the ordinary scan *and*
accumulate the source beside it, discarding one at the close -- a third
retroactive disposition, which belongs with the construct that needs the
machinery anyway rather than with direct links.

**Boundary.** We agree whenever the destination closes, since a closed
destination's content is literal either way.

Argument under *2026-08-13 -- ours: constructs inside an unterminated
destination*.

## What "adjudicated" means

`oracle-disagreements.md` is append-only, one entry per divergence, and
every entry ends in a verdict naming an authority:

| verdict | meaning |
| --- | --- |
| `render-only` | same parse, different serialization |
| `djoths-outdated` | djoths implements older syntax; follow djot.js |
| `djoths-bug` | djoths contradicts the prose spec |
| `djotjs-bug` | djot.js contradicts the prose where djoths follows it |
| `SPEC-GAP` | the prose is silent; the corpus is the only authority |
| `ours` | we know what djot.js does and deliberately do not match |

Most of the log is the first four. Those are not our gaps at all: they
are djoths disagreeing with djot.js, recorded in a baseline run before
any Gallina existed so that later work would not chase ghosts. It is why
djoths shows 25 mismatches in the same run that gives us 4.

Only `ours` appears in our number, and adjudicating one means: the input
is reproduced, djot.js's behaviour is pinned by running it, a reason is
written down, and the boundary of the divergence is stated as a sentence
and checked against the oracle.

**It is not "excused".** The bar is one of two things, and each entry
has to say which:

1. **Matching would falsify a theorem** about output the parser can
   reach. The question is asked in that form -- *would matching break
   `parse (render d) = d` for a `d` the parser produces?* -- because
   `wf_block` is not a convention but the set of ASTs the roundtrip
   theorem quantifies over.
2. **The divergent inputs are unreachable from the canonical view**, so
   the gap is a corpus number rather than a bug. This one is only
   admissible with the boundary written out, since "unreachable" is a
   claim about `cb_ok` and `ci_ok` that has to be true.

Of the four above, two are (1), one is (1) against the no-backtracking
theorem rather than the roundtrip, and one is (2).

## The caveat

`ours` is a verdict the project passes on itself, so the discipline is
only as strong as the requirement that each entry name the lemma that
would break or state a boundary and check it. All four do.

But it does mean 283/287 is not directly comparable to another
implementation's score against the same corpus. Four of the gap are
choices, and three of them could be closed by giving up either
`wf_block` or the no-backtracking theorem. Quote the number with that
attached, or quote 287/287 on shape, which has no such asterisk.
