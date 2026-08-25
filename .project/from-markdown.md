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

Twelve things are configurable today, and this document describes the
Markdown-facing choice for each. djot's own answer is in the last column.

| setting | Markdown-facing | djot |
| --- | --- | --- |
| strong / emphasis spelling | `**strong**`, `_emph_` (`markdown_config`) | `*strong*`, `_emph_` (`djot_config`) |
| djot-only delimiter containers | disabled (`markdown_like_config`) | highlight, insert, delete, super/subscript and smart quotes enabled |
| sublist without a blank line | allowed (`markdown_bconfig`) | not allowed (`djot_bconfig`) |
| `===` / `--` underlines a heading | allowed (`markdown_bconfig`) | not allowed |
| pipe tables and captions | disabled (`markdown_bconfig`) | enabled |
| ATX heading continuation | one source line (`markdown_bconfig`) | same-level markers and lazy text continue |
| fenced divs | disabled (`markdown_bconfig`) | enabled |
| task-list checkboxes | literal bullet text (`markdown_bconfig`) | task-list items |
| fenced `=format` blocks | ordinary code blocks (`markdown_bconfig`) | raw output blocks |
| inline `` `code`{=format} `` | code plus literal format text (`markdown_like_config`) | raw inline output |
| ``$`x` `` and ``$$`x` `` | literal dollars plus code (`markdown_like_config`) | inline and display math |
| `: term` | a bullet item (`markdown_bconfig`) | a definition list |

The first two, raw inline and math compose in `markdown_like_config`: it
starts from the doubled strong spelling and applies field-local capability
updates. The eight block settings live in one record with one field each,
and `markdown_bconfig` composes their field-local knobs. `check/Markdown.v`
pins the combined profile, and `check/Sublist.v` and `check/Setext.v` pin the
individual settings.

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

**Status: settled for this profile.** This is Markdown-like syntax, not a
CommonMark-compatible emphasis grammar. Once that boundary is stated,
`*italic*` remaining literal is not a surprise: this profile deliberately
uses `_italic_` and reserves `**strong**` as the only asterisk delimiter.
Djot's own profile makes a different explicit choice, where `*italic*` is
strong. No diagnostic or CommonMark-style delimiter-run machinery is
intended.

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

### Consecutive headings of the same level merge in djot

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

**Markdown-profile status: fixed.** `markdown_bconfig` closes an ATX heading
after its first source line, so the first example is two headings and the
second is a heading followed by a paragraph
(`md_adjacent_headings_stay_separate`,
`md_text_after_heading_is_a_paragraph`). Djot retains lazy continuation.
Canonical multiline headings are excluded only at the single-line setting,
which keeps the generic roundtrip theorem valid for both profiles.

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
renderer. Djot still offers raw output deliberately through a fenced block
tagged `=html`; the Markdown-facing profile reads that fence as a code block
whose language is `=html`.

## Extra syntax you do not have in Markdown

Additive, so not a surprise, except that a document using these
characters literally may read differently.

| syntax | what |
| --- | --- |
| `{#id .class key=val}` | attributes, on a block or an inline span |
| `:::` | a div, a named block container |
| `- [x] item` | a task-list item (ordinary bullet text in the Markdown-facing profile) |
| `[text]{.class}` | a span |
| `{=highlight=}`, `{+insert+}`, `{-delete-}` | marked spans |
| `^super^`, `~sub~` | super and subscript |
| ``$`x` ``, ``$$`x` `` | math (literal dollars plus code here) |
| `` `code`{=html} `` | raw inline in Djot (code plus literal `{=html}` here) |
| `: term` | a definition list (an ordinary bullet item here) |
| `` ` `` fence with `=format` | a raw block in Djot (a code block here) |

The characters to watch are `{`, `}`, `[`, `]`, `$`, `^`, `~`, `:` and
`.`, all of which are reserved and all of which escape with `\`.

## What could become opt-in

Asked because a Markdown user should not have to learn what they are not
using. Where things stand:

**Already switched off in `markdown_like_config`, and the proofs go through
there.** Highlight, insert, delete, superscript, subscript, single and double
curly quotes are rows in the delimiter table. `disable_rows` turns them off
compositionally. Raw inline is a separate scanner capability; when disabled,
the verbatim remains code and its complete `{=format}` suffix is text. These
constructs are removed from the canonical view too, so the roundtrip theorem
specializes to the reduced table rather than being restated for it.

Math is the third scanner capability and the one that cost nothing on the
canonical side, because the canonical view never had a math constructor. With
it off the dollar prefix is not dropped and not announced: it becomes literal
text before the code span it was about to mark, so ``$`x` `` reads as `$`
followed by `` `x` `` (`markdown_like_math_is_code_and_text`).

**Already switched off in `markdown_bconfig`.** Djot pipe rows and their
caption continuation are a single table capability. Fenced divs, task-list
checkboxes, raw blocks and definition lists are independent capabilities.
The definition list is the one gated at the close rather than at the open,
because it has no opener of its own: `: t` is an ordinary list item at every
setting, and what the capability decides is whether the item's content is
split into a term and a definition
(`markdown_like_definition_list_is_a_bullet_list`). When task semantics
are off, the complete checkbox token remains ordinary bullet-item text,
including `[x]` versus `[X]` and its following separator. Each disabled
canonical construct is outside the accepted roundtrip fragment. A disabled
raw fence retains its complete `=format` info string as an ordinary code
block. GFM-style tables are therefore not currently part of the Markdown-like
profile either; adding a separate caption-free GFM table mode would be a new
extension.

**Would need a new setting.** Attributes, spans and footnotes.

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
