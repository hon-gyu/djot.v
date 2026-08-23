---
ai-disclosure: ai-generated
date: 2026-08-23
author: anthropic/claude-opus-5
---
# Coming from Markdown

What a CommonMark or GitHub-Markdown user can type here unchanged, what
reads differently, and the reason in each case.

The standard this markup is measured against is not "no surprise for a
Markdown user". It is **no surprise without a good reason**. Every entry
below carries its reason, and an entry whose reason is only "djot does it
that way" is flagged as open rather than settled.

Behaviour is pinned by compiling `Example`s, named in each row. Prose
drifts; those do not.

## The profile this describes

Five things are configurable today, and this document describes the
Markdown-facing choice for each. djot's own answer is in the last column.

| setting | Markdown-facing | djot |
| --- | --- | --- |
| strong / emphasis spelling | `**strong**`, `_emph_` (`markdown_config`) | `*strong*`, `_emph_` (`djot_config`) |
| djot-only delimiter containers | disabled (`markdown_like_config`) | highlight, insert, delete, super/subscript and smart quotes enabled |
| sublist without a blank line | allowed (`markdown_bconfig`) | not allowed (`djot_bconfig`) |
| `===` / `--` underlines a heading | allowed (`markdown_bconfig`) | not allowed |
| pipe tables and captions | disabled (`markdown_bconfig`) | enabled |

The first two compose in `markdown_like_config`: it starts from the doubled
strong spelling and applies the proved multi-row disable operation. The last
three live in one record with one field each. `markdown_bconfig`
composes their field-local knobs, and `check/Markdown.v` pins the combined
profile as well as the individual settings in `check/Sublist.v` and
`check/Setext.v`.

The profile is not yet a CommonMark implementation: djot-only block and
non-delimiter inline constructs remain enabled. See
[What could become opt-in](#what-could-become-opt-in).

## Works exactly as you expect

- `# Heading` through `###### Heading`
- `> blockquote`
- fenced code with ``` or `~~~`, with a language tag
- `` `code` `` inline
- `- item`, `* item`, `+ item`, `1. item`, `1) item`
- `[text](url)`, `[text][ref]` with `[ref]: url`, `![alt](url)`
- `***` and `---` on their own line as a thematic break
- task lists, `- [x]` and `- [ ]`
- footnotes, `[^1]` with `[^1]: text`
- `**strong**` and `_emphasis_` (in the Markdown-facing profile)
- `\` before punctuation escapes it
- setext underlines, `===` and `---` (in the Markdown-facing profile)
- nested lists without a blank line before them (same profile)

## Reads differently, with a reason

### `*a*` is literal text, not italic

`*italic*` comes out as the four characters `*italic*`.
(`md_single_star_is_text`)

**Why.** A delimiter character belongs to one row of the table at one
fixed width. If `**` is strong, then `*` is not a delimiter at all.
Supporting both would require deciding what `***a***` and `**a*` mean by
counting characters, which is the run-length arithmetic that produces
CommonMark's emphasis corner cases. The payoff for refusing it is that
`2*3*4` is literal text (`md_arithmetic_is_text`) and `a*b*c` is literal
text (`md_intraword_star_is_text`), with no rule about what surrounds the
asterisks.

**Status: open.** This is the largest single surprise, and the failure is
silent-ish: the text stays visible but the emphasis is lost. djot's own
profile is not better here, only differently wrong, since `*italic*` is
**bold** there. Neither profile gives italic. A warning at parse time is
probably the right answer and does not exist yet.

### Emphasis works inside words

`he_ll_o` emphasizes `ll`. CommonMark deliberately does not.
(`md_intraword_emph`)

**Why.** `can_open` and `can_close` are one whitespace test each. Adding
CommonMark's flanking rules costs a second condition on both sides of
every bare delimiter, and the ambiguity those rules exist to prevent is
already prevented by one character having one width. The escape hatch is
the ordinary brace form: `he{_ll_}o` emphasizes `ll` explicitly, and
`he\_ll\_o` is literal.

### A blockquote does not interrupt a paragraph

```
a
> b
```

is one paragraph containing the literal text `> b`, not a paragraph
followed by a quote. (`parse_quote_no_interrupt`)

**Why.** Which block a line belongs to is decided by the line before it
and the open containers, never by re-reading. That is what
`prefix_determinism` and `no_future_line_dependence` state. Letting a
quote marker reach back into an open paragraph is the class of rule that
those theorems exclude. Put a blank line before the quote.

Note the asymmetry: a **list** marker can interrupt a paragraph in the
Markdown-facing profile, because that rule was stated over the open
paragraph alone, with no reference to the enclosing container, which is
what kept `list_uniformity` true. The same treatment for quotes has not
been done.

### `>` needs a space

`>not a quote` is a paragraph. (`ParserExamples.v:103`)

**Why.** Same rule as `#hi` not being a heading, which CommonMark also
enforces. Consistency, at a small cost.

### Consecutive headings of the same level merge

```
# a
# b
```

is **one** heading whose text is `a`, a soft break, `b`.
(`parse_heading_lazy`) So is

```
# a
b
```

A heading continues until something ends it: a blank line, a different
level, or a block construct. (`parse_heading_level_change`,
`parse_heading_interrupted`)

**Status: open, and the most likely real-world trap after `*a*`.** Two
adjacent one-line headings is a shape people actually write. The reason
is uniform continuation, which is a genuine simplification, but the cost
here looks higher than the benefit and it deserves a second look.

### `--` and `...` become typography

`---` inside a paragraph becomes an em dash, `--` an en dash, `...` an
ellipsis, and `"` and `'` become curly quotes. (`parse_no_interrupt`,
`ellipsis_and_remainder`)

**Why.** Inherited from djot, on by default. Escaping works: `\-\-\-`
stays literal, and so does a fenced code block or `` `verbatim` ``, which
are never touched.

Curly quotes are rows in the delimiter table and are switched off in
`markdown_like_config`. Dashes and ellipses remain scanner dispatch, but the
same profile now sets `dc_smart_typography` to false, so all three spellings
above stay literal there. Djot's configuration keeps them enabled.

### A hard line break is a trailing backslash

End the line with `\`, not with two trailing spaces. (`escaped_eol_is_hard_break`)

**Why.** Trailing whitespace is invisible in an editor and is stripped by
most tooling. This is a straightforward improvement and the reason is
good.

### A list changes style, so it changes list

```
- a
+ b
```

is two lists, not one. (`parse_list_style_change`) CommonMark does the
same thing, so this is listed only because it looks like a bug when you
hit it.

## Not available, and why

### No indented code blocks

Four leading spaces is not code. Use a fence.

**Why.** Indentation already means container nesting, and overloading it
is the source of a large fraction of CommonMark's list ambiguities. Cost
to the user is near zero since fences are universally supported.

### No raw HTML

`<div>` is literal text.

**Why.** Two reasons, and the second is the stronger one. It removes an
entire ambiguity class from the parser, and it is what makes an
output-safety theorem about the renderer possible at all: if no HTML can
enter through the source, then every `<` in the output came from the
renderer. Raw output is still reachable deliberately, through a fenced
block tagged `=html`.

## Extra syntax you do not have in Markdown

Additive, so not a surprise, except that a document using these
characters literally may read differently.

| syntax | what |
| --- | --- |
| `{#id .class key=val}` | attributes, on a block or an inline span |
| `:::` | a div, a named block container |
| `[text]{.class}` | a span |
| `{=highlight=}`, `{+insert+}`, `{-delete-}` | marked spans |
| `^super^`, `~sub~` | super and subscript |
| `$math$`, `$$display$$` | math |
| `` `code`{=html} `` | raw inline for one format |
| `: term` | definition lists |
| `` ` `` fence with `=format` | a raw block |

The characters to watch are `{`, `}`, `[`, `]`, `$`, `^`, `~`, `:` and
`.`, all of which are reserved and all of which escape with `\`.

## What could become opt-in

Asked because a Markdown user should not have to learn what they are not
using. Where things stand:

**Already switched off in `markdown_like_config`, and the proofs go through
there.** Highlight, insert, delete, superscript, subscript, single and double
curly quotes are rows in the delimiter table. `disable_rows` turns them off
compositionally. This removes them from the canonical view too, so the
roundtrip theorem specializes to the reduced table rather than being
restated for it.

**Already switched off in `markdown_bconfig`.** Djot pipe rows and their
caption continuation are a single table capability. With it off, row-shaped
source is paragraph text and canonical tables are outside the accepted
roundtrip fragment. GFM-style tables are therefore not currently part of the
Markdown-like profile either; adding a separate caption-free GFM table mode
would be a new extension.

**Would need a new setting.** Attributes, divs, spans, math, footnotes, definition
lists, raw blocks and raw inline (all hardwired in the block layer).

**The shape the work takes** is known, since it was done once for the
delimiter rows and twice in the block layer: a predicate in the settings
record, one extra case in each of the five theorems that quantify over
all parser states, and one clause in the canonical view's acceptance
predicate saying the switched-off construct is not produced. The last
part is what keeps the roundtrip theorem true at every setting, and it is
also why "off" means something rather than being announced.

**One constraint on how this is spelled.** Compatibility with djot is
non-negotiable, so djot's instance has to keep everything on. "Opt-in"
therefore means a named profile in which these are off, not a change of
default. Profiles, not flags.

## The four known conformance gaps

Against djot.js on its own 287-case corpus: block structure agrees
287/287, exact HTML agrees 283/287. All four differences are deliberate
and argued in `.project/oracle-disagreements.md`. Three involve an
attribute block that never closes or has nothing before it in its scope,
one an unterminated link destination. None is reachable from a document
this renderer can produce.
