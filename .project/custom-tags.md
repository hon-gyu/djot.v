---
ai-disclosure: autonomous
---
# Custom tag names

Status: **implemented** (2026-10-03), from
[[261001.plan.custom-tags]]. The six decisions the plan lists were made
by an agent and have not been reviewed by a human; section 9 lists what
a review should look at first. `dev/check/Tag.v` pins every row of
sections 1, 3 and 7, the HTML of section 5 and the source ranges, and
the roundtrip test has a tags pool: the ordinary documents plus named
spans and divs in each container, rendered to djot and read back with
the setting on.

Prose first. Sections 0 to 7 define the syntax without naming a single
identifier in the development; everything that touches the code is
gathered in section 8.

Source: <https://github.com/jgm/djot/issues/240> (open, no consensus).
No djot implementation has the construct, so the discipline in
[[extension-decisions]] applies rather than
[[project-engineering-lessons#Ask djot.js]].

## 0. The idea

A div and a span each have a **name**, separate from their classes.

```
::: details
text
:::

Press :kbd[Ctrl+C] to copy.
```

The first is a div named `details`; the second contains a span named
`kbd`. With the setting off, djot reads `details` as the div's class and
`:kbd` as text before a bracket.

This file defines syntax only. The parser records the name as written,
and what a name means is the consumer's. The HTML renderer (section 5)
is one consumer.

## 1. Baseline: what djot does with these documents today

Not decisions. Pinned from djot.js v0.3.2 and from our own parser on
2026-10-03; the two agree on every row.

| input | djot today |
| --- | --- |
| `:kbd[Ctrl+C]` | literal text |
| `:kbd[a]{.x}` | text `:kbd`, then a span with class `x` |
| `:kbd[a](u)` | text `:kbd`, then a link |
| `a:kbd[b]{.x}` | text `a:kbd`, then a span |
| `:kbd:[a]{.x}` | the symbol `kbd`, then a span |
| `:[a]{.x}` | text `:`, then a span |
| `:kbd[a` | literal text |
| ``:kbd`x` `` | text `:kbd`, then a verbatim |
| `[a]{:kbd}`, `[a]{kbd}` | literal text |
| `::: details` / `x` / `:::` | a div with class `details` |
| `::: a b` / `x` / `:::` | a paragraph |

One related row disagrees, and it is not about names: `{.a}` before
`::: b` gives djot.js the classes `a b` and gives us only `a`. It is
logged in [[djotjs-divergences]] (2026-10-03) and left open there. With
the setting on, `b` is a name and the case does not arise.

## 2. Enabling

One setting that moves both spellings, off in djot and in the
Markdown-like profile.

It is **non-conservative** in both halves:

- Every `::: word` line changes meaning, from a class to a name. This is
  visible in HTML: `<div class="details">` becomes `<details>`.
- Every document containing a colon, then one or more symbol characters,
  then `[` changes meaning. Prose such as `note:see[this](url)` is in
  that set. djot.js's test suite contains no such text, and four
  `::: word` lines, all in its div tests.

Canonical text already escapes `:`, so text ending in `:kbd` before a
bracket renders as `\:kbd` and comes back as text with either setting.

## 3. The syntax

### 3.1 A div's name

The word after a div's opening fence is its name. Which lines open a
div does not change: the word is still drawn from letters, digits, `_`
and `-`, and a second word still makes the line a paragraph. A fence
with no word opens an unnamed div.

`::: div` is the div named `div`. It is not a second spelling of `:::`.

### 3.2 A span's name

`:name[` opens a named span. The name is one or more symbol characters
(the characters a symbol `:name:` may contain), and the decision is made
at the `[`: until then the colon and the name are read exactly as a
symbol is, and a second colon still makes a symbol.

`:[` has no name and is a colon before an ordinary bracket.

### 3.3 Where a named span closes

At the first `]` that arrives while it is the innermost open bracket.
The span closes there; nothing after the `]` is waited for. So a
following `(url)` or `[label]` is text, and a following `{...}` attaches
attributes to the span as it would to any inline.

An ordinary bracket inside a named span keeps djot's rule: its `]`
closes it only if a `(`, `[` or `{` follows, and otherwise the bracket
stays open and takes the next `]`. So `:kbd[x [a] y]` has no named
span (see 3.4).

A delimiter inside a named span that is still open at the `]` becomes
text, and a delimiter closer inside one may close an opener outside it,
abandoning the span, exactly as for an ordinary bracket.

### 3.4 Where `:name[` is not a named span

- An escaped colon: `\:kbd[a]` is text, then an ordinary bracket.
- A span that never closes: `:kbd[a` is its own text, as an unclosed
  bracket is.
- A span whose `]` an inner ordinary bracket takes: `:kbd[x [a] y]` is
  text throughout.
- A bracket right inside a named span is never a footnote or a wikilink
  opener's second bracket: `:kbd[^x]` is a span holding `^x`.

### 3.5 Attributes

Attribute specs are unchanged. `[a]{:kbd}` and `[a]{kbd}` remain text.
A name and a class are separate fields, so `{.a}` before `::: b` gives a
div named `b` with class `a`.

## 4. What it produces

A span or a div with its name. The unnamed span and div are the ones
djot builds. The name is recorded as written: there is no length bound,
no case folding, and the block and inline alphabets are not unified.

## 5. How it renders

The name is the element name when it is ASCII letters, digits and
hyphens starting with a letter, and is not, in any letter case, a void
element (`br`, `img`, `input`, ...), a raw-text or escapable raw-text
element (`script`, `style`, `textarea`, `title`), or a legacy element
that switches the tokenizer (`xmp`, `iframe`, `noembed`, `noframes`,
`plaintext`, `noscript`). Otherwise the element is `div` or `span` and
the name goes in a `data-tag` attribute.

```
:kbd[Ctrl]          <kbd>Ctrl</kbd>
::: details         <details>
:script[x]          <span data-tag="script">x</span>
:a_b[x]             <span data-tag="a_b">x</span>
```

The reason is that the renderer escapes for ordinary content. Inside
`<script>` that escaping is not what the browser undoes, so the output
would not denote the tree, and a void element cannot hold children.
`data-tag` rather than a class, because writing the name as a class
would merge name and class again.

## 6. Canonical spelling

A named span is `:name[` then its children then `]`; its children may be
empty, as a link's text may. A named div is `::: name`, then its blocks,
then `:::`. Both need the setting, and a name made of the characters its
opener reads: symbol characters for a span, class characters for a div.

## 7. Worked examples

With the setting on:

| input | result |
| --- | --- |
| `:kbd[Ctrl+C]` | a span named `kbd` holding `Ctrl+C` |
| `:kbd[a]{.x}` | that span, with class `x` |
| `:kbd[a](u)` | a span named `kbd`, then the text `(u)` |
| `note:see[this](url)` | `note`, a span named `see`, then `(url)` |
| `:kbd:[a]{.x}` | the symbol `kbd`, then an unnamed span |
| `:kbd[]` | an empty span named `kbd` |
| `:a[:b[c]]` | a span named `a` holding one named `b` |
| `[:kbd[a]](u)` | a link whose text is a named span |
| `:kbd[_a]_` | a span holding `_a`, then `_` |
| `_:kbd[a_]` | emphasis over `:kbd[a`, then `]` |
| `::: details` / `x` / `:::` | a div named `details` |
| `{.a}` / `::: b` / `y` / `:::` | a div named `b` with class `a` |

## 8. In the development

- The tree: `Div` and `Span` carry the name as a string, empty meaning
  unnamed. Every proof gained a binder and no theorem gained a case.
- Blocks: `bdiv_names`, read in one place, `Step.div_block`. The
  canonical div `CDiv` carries the name, `div_name_ok` admits a nonempty
  one only with the setting on, and `div_uniformity` is stated for any
  word the opener reads back. `Invariants.v` has the setting's
  preservation lemmas, `with_div_names_opens_nothing` and
  `with_div_names_only_at_words`.
- Inlines: `dc_tags`. The symbol state turns a `[` after a nonempty
  alias into a frame `FKTag name`; `ilead` closes it at a `]` through
  `tag_close`. `bunpush` never matches the frame, which is why no
  condition on a named span's first child is needed. The canonical view
  gains `CITag`, and `iscan_cis_scope` its case.
- The scanner invariants (`Wf.v`, `InlineSpans.v`, `InlineLocated.v`,
  `InlineBuffer.v`, the suffix laws in `InlineInvert.v`) cover the new
  frame. The symbol state's span invariant now records that the state
  held at the colon, which the frame needs as its start.
- `InlinePrecedence.v` is unchanged in statement: `:` is outside its
  alphabet, so `para_inlines_matching` holds at every setting without
  modelling named brackets.
- `Profile.with_tags` moves both settings; `Html.named_elem` is
  section 5.

Against the plan: step 3 (the field) was mechanical as predicted; step 4
was small; step 5 needed no new scanner state, one frame kind and one
strengthened invariant. The plan's expected extension of the precedence
model turned out unnecessary for the reason above.

Checks: test suite 287/287, generated documents 531 and 184 mismatches
against djot.js as before, roundtrip at depth 3 57857, located bounds
58150, and the tags pool 364, 4437 and 57909 at depths 1 to 3, all
roundtripping. `Print Assumptions` on the roundtrip, uniformity,
incrementality, single-pass and precedence theorems shows nothing.

## 9. Open questions

### 9.1 The unreviewed decisions

The plan's D1 to D6 are implemented as written. The ones with the most
user-visible consequence:

- D3, `]` closes at once. `:kbd[a](u)` loses the link reading. The
  alternative (wait one byte, as `]` does) would give `Link` a name or
  drop it.
- D5, `::: div` is named `div`. The proposal in the issue folds it into
  the unnamed div.
- D2, the leading colon. Prose like `note:see[this](url)` changes
  meaning. The issue's alternatives `!tag[...]` and `[x]{:tag}` avoid
  this but collide with images or with attribute syntax.

### 9.2 HTML beyond escaping

Section 5 guards only escaping and void elements. Elements the HTML
parser closes or moves implicitly (`p` inside `p`, `tr` outside a
table, `a` inside `a`) still render as written, and a browser may build
a different tree from them. A name that is also an attribute the user
wrote, `{data-tag=x}` on a fallback element, gives two `data-tag`
attributes.

### 9.3 A named div inside a div

The canonical spelling fixes the fence at three colons, so a div
directly inside a div is outside the canonical view, named or not. The
tags pool shows the exclusion is reached.
