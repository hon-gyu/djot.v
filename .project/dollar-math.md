---
ai-disclosure: ai-generated
---
# Dollar math

Status: **implemented** (2026-09-27), v1. Rebased onto main on
2026-10-02. The setting, scanner states, proofs, extraction and the
Markdown-like profile's use of it are built. `dev/check/DollarMath.v`
pins every row of section 4 and the source ranges. Section 7 is the
estimate made before the code; section 7.1 records what the
implementation established or changed.

Prose first. Sections 0 to 6 define the syntax without naming a single
identifier in the development; everything that touches the code is
gathered in section 7.

Prior art is the math syntax github.com renders, pandoc's
`tex_math_dollars` and `tex_math_gfm`, and remark-math. The GFM spec
itself (github.github.com/gfm, 0.29) has no math: math on GitHub is a
github.com rendering feature layered on top of GFM. None of the three is
something to conform to; the discipline in [[extension-decisions]]
applies. The rules below are pandoc's, which are the only ones written
down, plus GitHub's ``$`…`$`` spelling.

## 0. The idea

A setting that lets `$…$` and `$$…$$` mean inline and display math, the
way Markdown users write them, and ``$`…`$`` mean inline math, the way
github.com accepts it.

```
The area is $\pi r^2$, and
$$\sum_{k=1}^n k = \frac{n(n+1)}{2}$$
```

The result is the same math node djot's ``$`x` `` and ``$$`x` `` produce.
Nothing downstream can tell which spelling was used.

The setting is independent of djot's own math syntax. A profile can have
either, both, or neither.

## 1. Baseline

Measured on 2026-09-27: github.com through its markdown API in `gfm`
mode, pandoc 3.2 with `-f markdown`, and remark-math (npm, current). `[x]`
is inline math with content `x`, `[[x]]` display math, anything else
text. djot today reads every input below as text, apart from its own
backticks.

| input | github.com | pandoc | remark-math |
| --- | --- | --- | --- |
| `$x+1$` | `[x+1]` | `[x+1]` | `[x+1]` |
| `x $$y$$ z` | `x [y] z` | `x [[y]] z` | `x [y] z` |
| `$ x $` | text | text | `[x]` |
| `$x $` | `[x ]` | text | `[x ]` |
| `It costs $5 and $10.` | text | text | `It costs [5 and ]10.` |
| `x$y$z` | text | `x[y]z` | `x[y]z` |
| `$a*b*c$` | `$a<em>b</em>c$` | `[a*b*c]` | `[a*b*c]` |
| `$\{x\}$` | `[{x}]` | `[\{x\}]` | `[\{x\}]` |
| `\$x$` | `[x]` | text | text |
| `$a$$b$` | `[a]$b$` | `[a][b]` | `[a$$b]` |
| `*a $b* c$` | `<em>a $b</em> c$` | `*a [b* c]` | `*a [b* c]` |
| ``$`x`$`` | `[x]` | ``[`x`]`` | ``[`x`]`` |

github.com finds math in the text left after Markdown has been parsed,
so emphasis and backslash escapes are applied inside what should have
been math content, and `\$` does not stop a `$` from opening math. Its
documentation asks for `<span>$</span>` to write a literal dollar beside
math. ``$`…`$`` was added on 2023-05-08 as the way around this.

pandoc reads math during the Markdown parse, under three rules on
whitespace and digits. remark-math reads `$` the way code spans read
backticks, with no such rules, so prices become math.

## 2. The setting

One inline setting, off in djot's profile. When it is off, every `$`
reads as it does today.

In the rules, whitespace is a space, a tab or a line end. A run is the
unescaped `$` bytes starting where the scanner currently is.

## 3. Rules

`$…$`

1. A run of exactly one `$` opens inline math if the byte after it is
   not whitespace and not a backtick.
2. The next unescaped `$` decides. It closes the math if the byte before
   it is not whitespace and the byte after it is not a digit, and it
   consumes that one `$` only. Otherwise the opener is text, and this
   `$` is read again from rule 1.
3. Inside the math, a backslash and the byte after it are kept as
   written, and that byte cannot close.
4. The content is the source between the delimiters, soft line breaks
   included.

`$$…$$`

5. A run of exactly two `$` opens display math, closed by the next `$$`.
   The whitespace and digit conditions of rules 1 and 2 do not apply.
   The content must be nonempty and keeps its surrounding whitespace. If
   no closer arrives, both dollars are text.
6. A run of three or more `$` is text.

``$`…`$``

7. A `$` directly before a backtick run, then a code span, then a `$`
   directly after the closing backtick run, is inline math whose content
   is the code span's content. Without the trailing `$`, the leading `$`
   is text and the span is ordinary code. There is no `$$` form.
8. When djot's math syntax is also on, a `$` or `$$` directly before a
   backtick is djot's prefix, as today. Rule 7 then only adds that one
   `$` directly after the inline form's closing run is consumed.

Scope and priority

9. A closer must arrive before the end of the paragraph, heading, table
   cell or caption. Otherwise the opener is text and the source after it
   reads as if the `$` had been escaped.
10. Once math closes, it wins over emphasis, links and spans that
    overlap it.
11. A `$` inside something read verbatim (a code span, an autolink, an
    attribute block, a link destination) is not an opener. Math content
    is verbatim in turn.
12. `\$` outside math is a literal `$`, never an opener or a closer.

## 4. Examples

With the setting on and djot's math syntax off.

| input | result |
| --- | --- |
| `$x+1$` | `[x+1]` |
| `x $$y$$ z` | `x [[y]] z` |
| `$ x $`, `$x $` | text |
| `It costs $5 and $10.` | text |
| `To split $100 in half, we calculate $100/2$` | `To split $100 in half, we calculate [100/2]` |
| `x$y$z` | `x[y]z` |
| `$a$1b$` | `$a[1b]` |
| `$a\$b$` | `[a\$b]` |
| `$a*b*c$` | `[a*b*c]` |
| `$\{x\}$` | `[\{x\}]` |
| `\$x$` | text |
| `$a$$b$` | `[a][b]` |
| `$$a$$b$$` | `[[a]]b$$` |
| `$$x$` | text |
| `$$$x$$$` | text |
| `*a $b* c$` | `*a [b* c]` |
| `[a $b](u) c$` | `[a [b](u) c]` |
| `` `a $b` c$ `` | code `a $b`, then ` c$` |
| `` $a `b$ `` | ``[a `b]`` |
| `$a *b* c` | `$a `, strong `b`, ` c` |
| ``$`x`$`` | `[x]` |
| ``$``a`b``$`` | ``[a`b]`` |
| ``$`x` y`` | `$`, code `x`, ` y` |
| `$$`, `x^2`, `$$` on three lines | a paragraph holding `[[⏎x^2⏎]]` |

## 5. Differences from prior art

From pandoc `-f markdown`:

- `$$x$` is text; pandoc reads `$[x]` (rule 5).
- `$$$x$$$` is text; pandoc reads `[[$x]]$` (rule 6).
- ``$`x`$`` is math; pandoc has it only in its `gfm` reader (rule 7).
- ``$`x` y$`` is `$`, code `x`, ` y$`; pandoc's `gfm` reader reads
  ``[`x` y]`` (rule 1 excludes a `$` before a backtick).

From github.com, every row of section 1 where the two columns differ:
`$x $`, `x$y$z`, `$a*b*c$`, `$\{x\}$`, `\$x$`, `$a$$b$`, `*a $b* c$`.
Also ```` ```math ```` stays a code block tagged `math` (section 6).

## 6. Out of scope for v1

- ```` ```math ```` as display math. It is a block rule with the same
  shape as raw blocks: one arm where a fence becomes a block, and one
  condition keeping a code block tagged `math` out of the canonical
  fragment. Left out so v1 touches the inline layer only.
- remark-math's `$$` fenced block, which may contain blank lines.
- `\(…\)` and `\[…\]`, which would take `\(` away as an escape.

Rendering back to djot is unchanged. The output is djot, so math is
written in djot's syntax (``$`x` ``, ``$$`x` ``) and every `$` in text is
already escaped. A document read with this setting and rendered comes
out with its `$…$` spelled ``$`…` ``.

## 7. In the development

Read off the tree at `b077866`; an estimate, to be checked against the
built construct.

- `dconfig` gains a boolean beside `dc_math`, with a `with_` function
  and its isolation lemma, and a line in `dev/check/Capabilities.v`.
- The scanner already holds a pending `$` or `$$` in `IDollar` until the
  next byte arrives. Today its non-backtick branch makes the dollars
  text. The new branch opens a math candidate that carries an ordinary
  reading of the same bytes, the construction `IAttr` uses for attribute
  blocks. The candidate is chosen at its closer; the ordinary reading is
  chosen at a failed closer or at the end of the paragraph.
- Rule 2 bounds the live readings. Inline content holds no unescaped
  `$`, so an inline candidate's ordinary reading never opens another
  candidate. Display content holds no `$$`, so a display candidate's
  ordinary reading can open at most one inline candidate. At most two
  candidates are live at once.
- Rule 7 with djot's math syntax off needs a state after a code span
  that began with `$`, holding the `$` until the byte after the closing
  run decides between math and text-then-code. With djot's math syntax
  on it is one extra byte of lookahead after the existing math close.
- The canonical view has no math constructor and `$` is always escaped
  in text, so the roundtrip is unaffected. The work is in the proofs
  that case on scanner states: well-formedness, the no-reread theorem,
  locations, and the inversion lemmas. The proof sites that handle
  `IAttr` are the size estimate.

### 7.1 What the implementation established

- The setting is `dc_dollar_math` in `InlineTable.v`, with
  `with_dollar_math` and `dollar_math_enabled` (`InlineView.v`).
  `dev/check/Capabilities.v` pins it off in djot, independent of
  `dc_math`, and restored by `with_dollar_math true`.
- The candidate is two scanner states, `IDollarMath` (inside the content)
  and `IDollarMathClose` (a `$` read, the next byte decides). Each carries
  the ordinary reading of the same bytes as a nested state, the way
  `IAttr` does. The two-candidate bound in section 7 was not needed and
  is not proved.
- Across lines: a candidate of either kind survives a soft break, which
  stays in its content (`$a` then `b$` is `[a⏎b]`), and a `$$` that ends
  a line opens a display candidate at the break. A `$` that ends a line
  closes inline math there when the byte before it is not whitespace.
- Rule 5 in practice: a `$$` followed by a third `$` does not close, so
  `$$x$$$` is text and `$$x$$$y$$` is `[[x$$$y]]`. `$$$$` is text, since
  the content would be empty.
- Rule 7 is a new backtick-span kind, `VMaybeDollarMath`, not a state
  after the span. The leading `$` is flushed as pending text and taken
  back (`opop_str`) when a `$` follows the closing run. Rule 8 is one
  arm on djot's inline math span: with the setting on, a `$` after the
  closing run is consumed.
- Proofs: well-formedness (`Wf.v`), the inversion lemmas behind the
  roundtrip (`InlineInvert.v`), locations (`InlineLocated.v`), and the
  emphasis flanking and nonempty-content theorems (`InlineSpans.v`) all
  hold with the setting on. `InlinePrecedence.v` covers text without
  `$`, so it only needed its line-end resolution to leave a pending `$`
  alone, since a break may now open display math from it.
- Main's renderer leaves some punctuation bare, but not `$`, so the
  rendering claim in section 6 still holds.

## 8. Undecided

- The setting's name. -> `dc_dollar_math`
- Whether the Markdown-like profile turns it on. -> yes
