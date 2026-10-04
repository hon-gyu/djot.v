---
ai-disclosure: ai-generated
date: 2026-10-04
author: anthropic/claude-opus-5-5
status: open; to revisit
---
# Decision: when two labels are the same

## The question

Reference labels and footnote labels are compared after normalization:
leading and trailing whitespace is dropped and each run of space, tab,
CR or LF becomes one space. So `[^a  b]` and `[^a b]` are one footnote.
Case is kept, so `[^a]` and `[^A]` are two.

The rule is `normalize_label` in `theories/Ast.v`. It was taken from
djot.js's behaviour. The syntax reference does not state it.

Should we follow djot.js here at all?

## What the syntax reference says

- "No case normalization is done on reference labels, a reference defined
  as `[link]` cannot be used as `[Link]`, as it can in Markdown."
- Its examples use labels with one inner space (`[foo bar]`,
  `[product page]`).
- Nothing on leading, trailing or repeated whitespace, and nothing on a
  label that is broken across two lines.
- For footnotes it says only that a footnote reference is `^` plus "the
  reference label", so whatever holds for reference labels holds there.

So the reference fixes case and leaves whitespace open.

## Where the rule is used

- At parse time, on the label stored in the tree: `Reference` targets of
  links and images, and `FootnoteReference` (`InlineScan.v`,
  `InlineInvert.v`, `Precedence.v`). A reference written `[^a` / `b]`
  across two lines is stored as `a b`.
- In the document pass, on the keys of the two tables: reference
  definitions, footnote definitions, and the reference each heading gets
  from its text (`Document.v`).
- At lookup (`lookup_reference`, `lookup_note` in `Ast.v`; footnote
  numbering in `Html.v`).
- In the canonical renderer's side conditions: a label is canonical only
  if it is already normalized (`InlineView.v`).

A definition node keeps its label as written. Only the table key and the
label inside a reference are normalized.

## Options

1. Keep the rule. A label broken across lines in running text matches a
   definition written on one line, which is the case the rule exists
   for. Cost: a rule with no source in the reference.
2. Compare labels byte for byte. This is the plain reading of a silent
   reference. A label broken across lines then never matches a one-line
   definition, and the label stored in a reference would hold a newline.
3. Normalize only line breaks (a break and the whitespace around it
   become one space) and compare the rest byte for byte. This keeps the
   one case option 1 is for and drops the rest.

## What a change would touch

- The inline parser's stored labels, so the trees of documents with
  unnormalized labels change.
- The roundtrip side conditions in `InlineView.v`, which get weaker
  under option 2 (every label is its own normal form).
- The heading references: a heading's text is normalized the same way to
  form its label, and that is a separate choice from the one above.
- `Doc.footnotes` and `Doc.reference` docs in `ocaml/src/djot.mli`.

## Status

Not decided. The current behaviour is option 1. Raised on 2026-10-04
while reviewing the `Doc.footnotes` docstring.
