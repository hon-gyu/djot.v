---
ai-disclosure: ai-generated
---
# Callouts

The extension is implemented, and its rules are stated in
`theories/spec/callouts.dj`. That file is the reference from now on. This
note is the work log behind it: the reasons, the alternatives, and what the
implementation cost. It is not updated when the rules change.

Status: **implemented** (2026-09-27). The recognizer, parser setting,
distinct node, located title, HTML and source renderers, canonical view,
roundtrip proof, generated checks, extraction, and public facade are built.
Section 8 records the original predictions and section 8.1 records what
the implementation established or changed.

The first consumer is a notes application that is replacing its
cmarkit fork with this parser and already relies on callouts; section 8
lists what it reads.

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

Not decisions. Pinned from djot.js v0.3.2 on 2026-09-23, and checked
against our extracted parser with the djot profile on 2026-09-26: every
row agrees. `dev/check/Callout.v` now pins every row as a default-profile
`Example`.

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
It is an extension in the sense of the public API: off in both named
profiles, and named as one (section 8).

Callouts are **non-conservative**: with the setting on, a document
containing a quote whose opening line starts with `[!kind]` means
something it did not mean before. The divergent set is narrow: it is
exactly the first eight rows of section 1 and their variations, which is
narrower than [[wikilinks]] section 2 could claim, since a callout has
to be the first thing on the first line of a quote.

**The canonical view excludes the collision rather than proving it
absent.** A canonical `Str` already escapes `[`, `!` and `]`, so a quote
whose first paragraph is the text `[!note] T` renders as
`> \[\!note\] T` (checked 2026-09-23) and comes back as a paragraph
with either setting. The other constructs whose spelling begins with `[`
are covered by section 3.2 and 3.3: a link, span or reference link
whose text begins with an image spells `[![`, a wikilink `[[`, a
footnote reference `[^`, and none of those is `[!` followed by a kind
character. That argument is checked by a finite probe, not proved, so a
canonical quote also requires that its first rendered line is not a
header (section 6).

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
2. a **kind**: one or more ASCII letters, digits, `-` or `_`;
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
data-callout="note" open="">` and the title element is `<summary
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

- the kind is nonempty and within 3.2's alphabet (`callout_kind_ok`);
- the title is what a one-line heading's content may be: no line break,
  no leading or trailing whitespace (`callout_title_ok`);
- the body satisfies what a canonical quote's contents satisfy.

**No condition on anything else for a callout.** An ordinary canonical
quote additionally checks that its first rendered line is not a callout
header when this setting is on. The finite escape probe found no such
collision, but it did not prove the universal escape claim. The explicit
check keeps `roundtrip_blocks` valid without adding a theorem hypothesis.

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

**Names.** Extensions are spelled `Ext_*` in the public types since
2026-09-26, so the node is `Ext_callout`, not `Callout`. The setting is
`bcallouts`, set by `with_callouts` in `Step.v`, and the facade switch
is `Profile.with_ext_callouts`, beside `with_ext_keyed`.

**A block setting.** One `bconfig` field, off in `djot_bconfig` and
`markdown_like_bconfig`, as `bkeyed` is, with the same field-local
plumbing (`bkeyed` has 26 mentions across `theories/`, 17 of them in
`Step.v`'s `with_*` definitions).

**A header recognizer in `Line.v`.** `callout_header` takes the content
after the quote prefix and returns an optional kind, fold marker
(`Ast.callout_fold`, `FoldExpanded` for `+` and `FoldCollapsed` for `-`)
and raw title suffix. It retains trailing whitespace for located parsing; the
title value is trimmed at close. `callout_header_other_prefix` proves it
answers `None` on every string beginning with anything but `[!`.
`callout_header_line` is the canonical spelling, shared by the canonical
view and the source renderer, and `callout_header_line_inv` proves the
recognizer reads it back. `Step.quote_header` applies the recognizer
only when the setting is on.

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

**A block constructor**, `Ext_callout` in `Ast.v`, with arms in every block
traversal. `Keyed` is the model, being the most recent block node that
carries inlines and blocks together. `Document.v` mentions `BlockQuote`
24 times and `Wf.v` 26; each traversal that visits inlines also takes a
title case, the way `Heading` does. In `Document.v` that is each of the
passes (identifiers, references, footnotes) and `Undo.pass`: a heading
inside a callout body gets an identifier, and a footnote definition
inside one moves to the side table, as inside a quote. `Site.v`'s
destination traversal and rewrite take one arm each, which is what
makes a wikilink in a title renamable.

**A canonical constructor**, `CCallout` beside `CQuote` in `Render.v`,
with arms in `cb_lines`, `cb_ast`, `cb_ok` and `cblock_ind2`, and in
`Address.v`, `Site.v`, `dev/Generate.v` and `Roundtrip.v` where `CQuote`
appears (2, 2, 3 and 8 mentions). `Render.render_block_lines` also takes
an arm, since the facade's source renderer will be built on it.

**One HTML arm**, section 5.

**Predicted obligations, stated so their failure names something.**

- `roundtrip_blocks` gains no hypothesis. `cb_ok` gains a callout clause;
  the quote clause also gains the first-line header check described in
  section 6. The original prediction that its clause would be unchanged
  was not discharged by a universal escape proof.
- `quote_uniformity`, `quote_uniformity_pad` and the lemmas under them
  in `Uniformity.v` (`parse_lines_quote_pad` and its continuation forms)
  **become false** with
  the setting on: a quote whose first stripped line is a header does not
  parse as `BlockQuote` of its stripped contents. They gain one
  hypothesis, that the setting is off or the first line is not a header,
  and a companion theorem states the callout's own uniformity: the body
  lines, stripped, parse exactly as they would at top level.
- No state-quantified theorem gains a hypothesis (above).

**The located parse.** The node's span runs from the quote prefix of the
header to the last body line, the extent `PQuote` already records. The
title's inlines are located at their own columns because the title is a
stored source suffix. The recognizer must keep trailing whitespace in
that suffix until inline parsing: stripping it in `Line.v` loses the
end-anchored column used by `parse_inline_line_located`. Strip it for
the title's value when the quote closes. The erasure refinement takes
one case.

**djot.js stops covering this**, as it does for keys and wikilinks.
The baseline rows of section 1 are what djot.js still checks: with the
setting off, every one must be unchanged. What remains is a generator
pool in `dev/Generate.v` and a `test/roundtrip.exe --callouts` mode with
its `make` recipe, as keys and wikilinks have, and a
`dev/check/Callout.v` pinning sections 3 and 7.

**The facade** (`ocaml/src/djot.ml`, `djot.mli`). `Block.t` re-exports
the kernel type, so the new constructor appears there with a doc
comment naming its fields. `Mapper` and `Folder` match every constructor
by name and will not compile until the arm is placed; the title is
inlines and the body blocks, as `Ext_keyed`'s label and block are.
`Profile.with_ext_callouts`, a case in `ocaml/test/api.ml`, and the
extension list in `ocaml/README.md`. The root README's list of settings
gains a line saying what the setting breaks, which by the prediction
above is container uniformity for block quotes.

**What the first consumer reads.** The kind, the fold marker, the title as inlines
and the body as blocks: nothing the node does not already hold. Two
differences from the fork it is leaving, both on the consumer's side:

- the fork lowercased the kind; this parser keeps it as written
  (section 3.2), so the consumer folds case when it reads it;
- the fork kept the header inside the quote and offered a function to
  strip it; here the body is already separate.

The consumer's own notes use only kinds inside section 3.2's alphabet
(`NOTE`, `FAQ`, `todo`, `example` and the like, surveyed 2026-09-26).

### 8.1 Order of work

Each step ends with the tree building and the existing checks passing.

1. **Probe.** The two-line `Compute` from [[project-engineering-lessons#Probe
   the definitions a theorem already constrains, too]] on the
   state-quantified theorems, and the escape claim of section 6 with a
   throwaway pool. If either fails, stop and revise this file before
   writing the parser.
2. **Pin the baseline.** `dev/check/Callout.v` with section 1's rows as
   `Example`s under the default setting.
3. **Recognizer.** The header function in `Line.v` and its `None` lemma,
   with 3.2's and 3.3's rows as `Example`s.
4. **Node and setting.** `Ext_callout` in `Ast.v`, `bcallouts` and
   `with_callouts` in `Step.v`, and every traversal arm: `Wf.v`,
   `Document.v`, `Html.v` (section 5), `Site.v`, `Address.v`. With the
   setting off the parser never builds the node, so nothing observable
   changes yet.
5. **Parser.** `PQuote`'s header field, the opener and `finish`, then
   the standing state theorems, then section 7's examples pinned whole.
6. **Uniformity.** The hypothesis on the quote theorems and the
   callout's own uniformity theorem.
7. **Canonical form and roundtrip.** `CCallout`, its generator pool, the
   roundtrip mode and recipe.
8. **Extraction and facade.** Regenerate `ocaml/kernel` (`make ocaml-pkg-regen`),
   then the facade, its test and both READMEs. `make ocaml-pkg-check-current` must
   pass.

After step 8, go back over section 8 and record which predictions held,
as [[wikilinks]] section 8.1 does.

Checkpoint (2026-09-27): all eight stages are implemented. The existing
default-profile examples and enabled examples in `dev/check/Callout.v`
compile; the latter cover nested and lazy bodies, invalid suffixes,
blank closure, inline titles, list and keyed nesting, block attributes,
folded HTML with an `open` attribute, and an empty title. The
state transition and uniformity theorems compile, and
`callout_uniformity` and `roundtrip_blocks` have no additional
assumptions. `dune build`, `make ocaml-pkg-check-current`, the standalone `ocaml`
build and tests, and the extracted callout roundtrip pool at depths
1–3 pass (321, 3720, and 43882 accepted documents, no mismatches).
The djot.js corpus is absent from this checkout, so `make diff` and
`make check-spans` cannot run here. The quote escape claim remains a
finite probe plus the explicit `cb_ok` check, rather than a universal
lemma derived from the inline renderer.

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

### 9.3 A location for the header

The facade reports a node's delimiting syntax (`Doc.syntax_locs`): fence
lines and attribute specs. The header line is the callout's delimiter in
the same sense, and an editor would want it (hovering the kind, folding
from the header). Recording it is one more syntax role at the quote
opener. Nothing needs it yet; decide when a consumer asks.
