---
ai-disclosure: ai-generated
---
# Callouts

Status: **specified, not implemented** (2026-09-23). Nothing below is
pinned yet. Section 8 is the estimate and section 9 is what is still
undecided; both are written to be checked against the tree once the
construct is built, as [[wikilinks]] section 8.1 was.

Prose first. Sections 0 to 7 define the syntax without naming a single
identifier in the development; everything that touches the code is
gathered in section 8.

Prior art is Obsidian's callouts, and GitHub's alerts, which are the
same syntax with a fixed set of five kinds and no title. Both are
prior art, not something to conform to: no djot implementation has the construct, so
the discipline in [[extension-decisions]] applies rather than
[[project-engineering-lessons#Ask djot.js]].

## 0. The idea

A callout is a block quote whose opening line names a kind, and
optionally a fold state and a title.

```
> [!note] Backlinks
> A backlink is a link seen from its target.
```

This is a callout of kind `note`, titled `Backlinks`, whose body is one
paragraph.

**This file defines syntax only.** The parser records what was written:
the kind as a string, the fold marker, the title and the body. What a
kind means (an icon, a colour, a default title), whether `NOTE` and
`note` are the same kind, and what folding does are for the consumer to
define. The HTML renderer (section 5) is one consumer. No rule below is
justified by what a kind means.

Djot already has a way to write a styled box, `::: note`, and nothing
here replaces it. The reason for the construct is compatibility with
documents written for Obsidian, which is the same reason wikilinks
exist.

## 1. Baseline: what djot does with these documents today

Not decisions. Pinned from djot.js v0.3.2 on 2026-09-23. Our own parser
has not been checked row by row yet; pinning these as `Example`s is the
first step of section 8.

| input                                  | djot today                                               |
| -------------------------------------- | -------------------------------------------------------- |
| `> [!note] Title` / `> body`           | a quote holding one paragraph, `[!note] Title` `body`    |
| `> [!note]` / `> body`                 | the same with no title text                              |
| `> [!NOTE]`                            | a quote holding the paragraph `[!NOTE]`                  |
| `> [!note]- T` / `> b`                 | a quote holding one paragraph                            |
| `> [!note]x`                           | a quote holding the paragraph `[!note]x`                 |
| `> [!no te] T`                         | a quote holding the paragraph `[!no te] T`               |
| `> [!note] T` / `lazy`                 | `lazy` joins the quote's paragraph                       |
| `> [!note] T` / blank / `> b`          | two quotes                                               |
| `> > [!note] T`                        | a quote in a quote, holding the paragraph                |
| `> [!note](x)`                         | a quote holding a **link** with text `!note`             |
| `> [!note]{.a}`                        | a quote holding a **span** with class `a`                |
| `> [!note][r]` with `[r]: u` elsewhere | a quote holding a **reference link** with text `!note`   |
| `> [!note]: u`                         | an empty quote and a **reference definition** `!note`    |
| `>[!note] T`                           | not a quote: djot needs whitespace after `>`             |

The first eight rows are the construct's territory: every one is a
paragraph whose text starts with `[!`, and nothing in djot reads the
`[!` as anything but text.

The four bold rows are the ones that constrain the design. Each is a
document where the characters after `[!kind]` already make djot
markup, so a callout that claimed them would change the meaning of a
construct djot has, not just of plain text. Section 3.3 keeps all four.

The last row is inherited unchanged. Obsidian accepts `>[!note]`; we do
not, because it is not a quote.

## 2. Enabling

One block setting, off by default, beside the existing block settings.

Callouts are **non-conservative**: with the setting on, a document
containing a quote whose opening line starts with `[!kind]` means
something it did not mean before. The divergent set is narrow: it is
exactly the first eight rows of section 1 and their variations, which is
narrower than [[wikilinks]] section 2 could claim, since a callout has
to be the first thing on the first line of a quote.

**The canonical renderer needs no change to make this safe.** A
canonical `Str` already escapes `[`, `!` and `]`, so a quote whose first
paragraph is the text `[!note] T` renders as `> \[\!note\] T` (checked
2026-09-23) and comes back as a paragraph with either setting. The other
constructs whose spelling begins with `[` are covered by section 3.2 and
3.3: a link, span or reference link whose text begins with an image
spells `[![`, a wikilink `[[`, a footnote reference `[^`, and none of
those is `[!` followed by a kind character. Section 6 states this as a
claim to check, not as a fact.

## 3. The syntax

### 3.1 Where a callout opens

On **the line that opens a quote**, and only there. The line's content
after the quote prefix is tested before it is parsed as anything else.

- A quote that is already open does not test its later lines. `> a`
  then `> [!note] T` is one quote holding the paragraph `a` `[!note] T`,
  as it is today.
- Every quote opener is tested, wherever it is. `> > [!note] T` is a
  callout inside a quote, `- > [!note] T` a callout inside a list item,
  and a key or a block attribute in front of a callout applies to it,
  all because the test is part of opening a quote and every one of those
  opens a quote through the same step.
- The test is on the raw line, before inline parsing. It cannot run on
  the parsed paragraph, because by then `[!note](x)` is already a link.

### 3.2 The header

The opening line's content, after the quote prefix, is a header when it
is:

1. `[!`;
2. a **kind**: one or more letters, digits, `-` or `_`;
3. `]`;
4. optionally a **fold marker**, `+` or `-`;
5. then either the end of the line, or a space or tab followed by the
   **title**.

The kind is recorded exactly as written. `NOTE` and `note` are different
kinds to the parser; a consumer that wants them equal folds case, as it
would for a wikilink target.

The kind's alphabet is narrower than Obsidian's, which accepts nearly
anything up to the `]`. The narrow set is what keeps the renderer's own
spellings out of the recognizer (section 2): a link whose text begins
with an image renders `[![`, and `[` is not a kind character. Widening
the alphabet would turn that into a condition the canonical view has to
carry.

### 3.3 Where a `[!` is not a header

Anything that fails 3.2 is not a header, and the line is parsed as it
is today. The cases that matter:

| content after `> ` | why not                        | what it is                 |
| ------------------ | ------------------------------ | -------------------------- |
| `[!note](x)`       | `(` after the `]`              | a link                     |
| `[!note]{.a}`      | `{` after the `]`              | a span                     |
| `[!note][r]`       | `[` after the `]`              | a reference link           |
| `[!note]: u`       | `:` after the `]`              | a reference definition     |
| `[!note]x`         | a letter after the `]`         | a paragraph                |
| `[!note]-x`        | a letter after the fold marker | a paragraph                |
| `[!no te] T`       | a space in the kind            | a paragraph                |
| `[!] T`            | empty kind                     | a paragraph                |
| `[![a](b)](c)`     | `[` where the kind starts      | a link around an image     |

The first four are why rule 5 asks for whitespace or the end of the
line. It is one rule, and it is exactly what keeps every construct djot
spells as `[text]` followed by a character: all of them put punctuation
directly after the `]`.

### 3.4 The title

The rest of the line after the whitespace, with leading and trailing
whitespace dropped, parsed as inline content on one line. It is inline
content and not a string because it is displayed text: a title can
carry emphasis, a link, or a wikilink, and a rename that rewrites
wikilinks has to find the ones in titles.

No title and an empty title are the same: `> [!note]` and `> [!note] `
both have an empty title. What an empty title displays as is the
consumer's choice.

The title is one line. The next line is body, never title, so the title
never has a continuation line.

### 3.5 The body

Every following line of the quote, parsed as blocks exactly as the
contents of an ordinary quote are. The body starts on the line after the
header, with no blank line needed.

**A line without `>` directly after the header closes the callout.**
In djot that line would join the quote's paragraph as a lazy
continuation, but after a header there is no open paragraph for it to
join: the header opened none. Lazy continuation into the *body* works
as it does in any quote:

```
> [!note] T
> para
lazy
```

is a callout whose body is one paragraph, `para` `lazy`.

A blank line closes the callout as it closes a quote. `> [!note] T`
followed by a blank line is a callout with an empty body.

## 4. What it produces

A block node of its own, holding the kind as a string, the fold marker
(none, `+` or `-`), the title as inlines, and the body as blocks.

It is distinct from a block quote for the reason a wikilink is distinct
from a link: the canonical renderer writes back the spelling the source
used, so if a callout parsed to a quote with an attribute, the renderer
could not tell which quotes to write with a header.

A new node rather than an optional header on the quote node. Most
traversals would carry a header on the quote unchanged, but every
traversal that visits inlines would have to remember to look inside the
title, and one that forgot would compile and quietly miss a footnote
reference or a wikilink. A new node makes every traversal choose.

## 5. How it renders

Obsidian's classes, and a `<details>` element when there is a fold
marker. Without one:

```html
<div class="callout" data-callout="note">
<div class="callout-title">Backlinks</div>
<div class="callout-content">
<p>A backlink is a link seen from its target.</p>
</div>
</div>
```

With `+` the outer element is `<details class="callout"
data-callout="note" open>` and the title element is `<summary
class="callout-title">`; with `-` the same without `open`.

`data-callout` is the kind as written. An empty title renders no title
element in the plain form and an empty `<summary>` in the folded one;
the renderer does not invent a title from the kind, since that is
meaning, and section 0 leaves meaning to the consumer. The node's
attributes go on the outer element, merged with `class="callout"` the
way a div's are.

## 6. Canonical spelling

`> [!kind]` then the fold marker, then a space and the title when the
title is nonempty; then the body, each line under `> `, exactly as a
quote's body is written. There is one spelling, so the choice is forced.

The conditions on a canonical callout:

- the kind is nonempty and within 3.2's alphabet;
- the title is what a one-line heading's content may be: no line break,
  no leading or trailing whitespace;
- the body satisfies what a canonical quote's contents satisfy.

**No condition on anything else.** The claim of section 2 is that no
canonical quote renders to a first line that 3.2 reads as a header, and
the claim is what lets the roundtrip theorem take no new hypothesis. It
rests on the escape set, and [[project-engineering-lessons#Probe a
theorem's shape before proposing it]] says to check it before relying on
it: the extracted roundtrip over a pool of quotes whose first child
starts with every inline that renders a leading `[`, with the setting
on.

## 7. Worked examples

```
> [!warning]- Do not rename
> Renaming breaks the backlinks below.
>
> - [[a]]
> - [[b]]
```

a callout of kind `warning`, fold `-`, title `Do not rename`, whose body
is a paragraph and a list.

```
> [!tip]
> Plain body.
```

kind `tip`, no fold marker, empty title, one paragraph.

```
> [!note] Outer
> > [!note] Inner
> > text
```

a callout whose body is one callout. The inner header is on the line
that opens the inner quote, which is what 3.1 asks.

```
> quoted
> [!note] T
```

one quote holding one paragraph: the second line does not open the
quote, so it is not tested.

## 8. What this costs the development

The one section that names things in the code. Written before the work,
so every number here is a prediction to be checked afterwards.

**A block setting.** One `bconfig` field, off in `djot_bconfig`, as
`bkeyed` is, with the same field-local plumbing (`bkeyed` has 26
mentions across `theories/`).

**A header recognizer in `Line.v`.** A function from the content after
the quote prefix to an optional header, plus the lemma that it answers
`None` on every string beginning with anything but `[!`.

**No new parser state.** `PQuote` gains a header field. The only
transition that reads it is the quote opener: where `open_quote` today
descends into the rest of the line, with a header it opens with the
idle state and stores the title line with its column, as `PHeading`
stores its lines. Every other `PQuote` transition carries the field
unchanged, and `finish` emits the new node when it is set. There are 27
`PQuote` mentions in `Step.v`, 4 in `Uniformity.v` and 2 in `Wf.v`, and
the prediction is that none but the opener and `finish` does more than
carry the field.

**The standing state theorems.** `step_fuel_shift`, `step_fuel_pad`,
`step_blank_finish`, `finish_wf` and `finish_supported` quantify over
all states. The header records no column of its own; the title's column
is whatever `PHeading`'s stored lines record, which those theorems
already accept. So the prediction is that
each takes a new case no harder than the quote's, and no hypothesis.
This is the claim to probe first, with the two-line `Compute` from
[[project-engineering-lessons#Probe the definitions a theorem already
constrains, too]].

**A block constructor**, `Callout` in `Ast.v`, with arms in every block
traversal. `Keyed` is the model, being the most recent block node that
carries inlines and blocks together. `Document.v` mentions `BlockQuote`
24 times and `Wf.v` 26; each traversal that visits inlines also takes a
title case, the way `Heading` does. `Site.v`'s destination traversal and
rewrite take one arm each, which is what makes a wikilink in a title
renamable.

**A canonical constructor**, `CCallout` beside `CQuote` in `Render.v`,
with arms in `cb_lines`, `cb_ast`, `cb_ok` and `cblock_ind2`, and in
`Address.v`, `Site.v`, `Generate.v` and `Roundtrip.v` where `CQuote`
appears (2, 2, 3 and 8 mentions).

**One HTML arm**, section 5.

**Predicted obligations, stated so their failure names something.**

- `roundtrip_blocks` gains no hypothesis, for section 6's reason.
  `cb_ok` gains a clause for the new constructor and no existing clause
  changes.
- `quote_uniformity` and the lemmas under it in `Uniformity.v`
  (`parse_lines_quote` and its continuation forms) **become false** with
  the setting on: a quote whose first stripped line is a header does not
  parse as `BlockQuote` of its stripped contents. They gain one
  hypothesis, that the setting is off or the first line is not a header,
  and a companion theorem states the callout's own uniformity: the body
  lines, stripped, parse exactly as they would at top level.
- No state-quantified theorem gains a hypothesis (above).

**The located parse.** The node's span runs from the quote prefix of the
header to the last body line, the extent `PQuote` already records. The
title's inlines are located at their own columns because the title is a
stored line. The erasure refinement takes one case.

**djot.js stops covering this**, as it does for keys and wikilinks.
The baseline rows of section 1 are what djot.js still checks: with the
setting off, every one must be unchanged. What remains is a generator
pool and a harness roundtrip mode, as wikilinks have, and a
`dev/check/Callout.v` pinning sections 3 and 7.

## 9. Open questions

### 9.1 A blank quote line between header and body

`> [!note] T`, `>`, `> body` is a callout whose body starts with a blank
line, which a quote's contents allow. Whether the canonical spelling
should ever write it is decided by whether an empty-first-line body is
canonical at all, which is the quote's own answer; recorded here so it
is checked rather than assumed.

### 9.2 Kinds outside the alphabet

Obsidian users write kinds like `[!my type]` rarely, and the narrow
alphabet turns those into paragraphs. If a real document needs one, the
cost is known (section 3.2): a condition on link text in the canonical
view, the way wikilinks pay one.
