---
ai-disclosure: ai-generated
---
# Wikilinks

Status: **implemented** (2026-09-22). Sections 0, 3, 4, 5, 6 and 9.2
were revised that day so that the construct carries syntax only, 9.4 was
added, and section 8 was restated against the tree before any code was
written and checked against it afterwards (8.1). `dev/check/Wikilink.v`
pins every row of sections 3 and 7 and the source ranges; `make wiki`
runs the extracted roundtrip over the wikilink pool.
Section 8 is the estimate, and section 9 is what is still undecided;
both are written to be checked against reality once the construct is
built, in the way [[keyed-blocks]] section 9 was.

Prose first. Sections 0 to 7 define the syntax without naming a single
identifier in the development; everything that touches the code is
gathered in section 8.

Prior art is Obsidian, and it is a reference rather than an oracle: no
djot implementation has this construct, so the discipline in
[[extension-decisions]] applies rather than
[[project-engineering-lessons#Ask the oracle]].

## 0. The idea

A wikilink is a target string in double brackets, with an optional alias
after a `|`, and optionally preceded by a `!`.

```
see [[Backlinks]] for the reverse direction
see [[Backlinks|the other direction]]
![[Backlinks]]
```

The first is a wikilink with target `Backlinks` and no alias, the second
has the alias `the other direction`, and the third is the first with its
embed bit set.

**This file defines syntax only.** The parser records what was written:
the target, the alias, and whether a `!` preceded the brackets. What a
target denotes (a note, a heading inside one, a URL), how it resolves,
and what an embed does are for the consumer to define. `Site.v`'s link
convention ([[260903.rename-canonicity]]) is one consumer and the HTML
renderer (section 5) is another. No rule below is justified by what a
target means.

The reason to have the construct is syntactic too: one string is both
the destination and the display text, so a tool that rewrites the
destination has one occurrence to change and no displayed copy to keep
in agreement with it.

## 1. Baseline: what djot does with these documents today

Not decisions. Pinned from djot.js v0.3.2 and from our own parser on
2026-09-05; the two agree on every row.

| input           | djot today                              |
| --------------- | --------------------------------------- |
| `[[a]]`         | literal text `[[a]]`                    |
| `[[a\|b]]`      | literal text                            |
| `[[]]`          | literal text                            |
| `[[a`           | literal text                            |
| `![[a]]`        | literal text                            |
| `x [[a]] y`     | literal text throughout                 |
| `[[a [[b]] c]]` | literal text                            |
| `[[*a*]]`       | `[[`, a strong span over `a`, then `]]` |
| ``[[a`b`]]``    | `[[a`, a verbatim, then `]]`            |

Every row but the last two is a single `Str`, which is the strongest
form of "the slot is free": a document containing `[[` almost always
means nothing to djot beyond its own characters.

The last two are the exception and they are the reason the setting is a
mode rather than a default. With wikilinks off, the region between the
brackets is ordinary inline content and its markup is live. With them
on, the region is source, and `[[*a*]]` has a target that contains
asterisks.

## 2. Enabling

One inline setting, off by default, beside the existing inline knobs for
math, raw spans, inline attributes and footnotes.

Wikilinks are **non-conservative**: with the setting on, a document
containing `[[...]]` means something it did not mean before. But the
divergent set is exactly the documents containing `[[`, which is a much
narrower claim than [[keyed-blocks]] section 2 could make: a key changes
the meaning of any paragraph containing a colon, which is most prose.

**The canonical renderer needs no change to make this safe.** A canonical
`Str` already escapes `[`, so a text run holding the characters `[[a]]`
renders as `\[\[a\]\]` and comes back as text with either setting. It
escapes `!` as well, so a text run ending in `!` before a wikilink cannot
reparse as an embed. The obligation that cost keys a whole subsection is
already discharged, and it was discharged before this construct was
thought of.

## 3. The syntax

### 3.1 Where a wikilink opens

At a `[` that arrives **immediately inside a bracket that has just
opened**: nothing has been emitted into the bracket's scope and no text
is pending. So `[[` opens one, and the `[` of `x[[a]]` opens one too,
since the second `[` still sits at the start of the first one's scope.

This is the footnote rule with a different second character. `[^` is
recognised the same way and for the same reason, and the recognition
happens at the second character rather than at the close, because what
follows is **source** and this scanner keeps no source beside classified
nodes.

Two consequences worth stating, both inherited:

- **It needs no lookahead.** The decision is made at the second `[` and
  never revised. What follows is accumulated as bytes.
- **A `[` that is not in that position is unaffected.** `[a[b]]` opens
  no wikilink, because the second `[` arrives with `a` pending.

### 3.2 Where it closes

At the first unescaped `]]`.

A single `]` is content: `[[a]b]]` has target `a]b`. A backslash protects
the next character from its role and is **not decoded**: `[[a\]]]` has
target `a\]`, the backslash and the bracket both content and the pair
after them the closer. This is a footnote label's disposition, and djot's
for its labels. The node records what was written, and a consumer that
wants escapes decoded decodes them. Section 6 keeps `]` and `\` out of
canonical targets altogether, so this spelling has to be defined but
never has to be pleasant.

**It does not cross a line break.** A candidate still open at the end of
a line decays to literal text, as an unclosed autolink does. The reason
is to bound what a stray opener can capture. The closer is the first
`]]` and nothing is revised, so a candidate that crossed breaks would
turn every line between a stray `[[` and an unrelated `]]` into one
target string. On one line, the most a stray `[[` can capture is the
rest of its line. Obsidian draws the same line.

**A candidate that never closes is literal text**, put back with both
brackets, and the scan resumes after them.

### 3.3 The target and the alias

The region is split at its **first unescaped `|`**. Before it is the
target, after it the alias; with no `|` the whole region is the target
and there is no alias.

Both halves are **raw source**, not inline content. `[[a|*b*]]` displays
the four characters `*b*`. This is the footnote label's disposition and
it is what keeps the node a leaf, which is most of why section 8's
estimate is small. 9.1 is the question of whether it should stay that
way.

**Nothing is trimmed.** `[[ a ]]` has target ` a `, spaces included.
Trimming would be friendlier and it is what Obsidian does, but it is a
normalization, and a normalization the renderer cannot undo: the source
`[[ a ]]` and the source `[[a]]` would produce the same node and only
one of them could be spelled back. So the parse keeps what is written
and section 6 excludes the untidy spellings from the canonical fragment
instead, which is where a condition of that kind belongs.

**An empty target is not a wikilink.** `[[]]` and `[[|b]]` decay to
literal text. `[[]]` is ordinary text in prose about code (an empty
nested list), so leaving it alone shrinks section 2's divergent set by a
shape that real documents contain. It also matches Obsidian. Admitting
it would be consistent too, so this is a choice and not a consequence.

### 3.4 Where a `[[` is not a wikilink

| #   | input         | reading             | why                                 |
| --- | ------------- | ------------------- | ----------------------------------- |
| 1   | `\[[a]]`      | literal text        | the first bracket is escaped        |
| 2   | `[a[b]]`      | as today            | the second `[` is not at the start  |
| 3   | `[[]]`        | literal text        | the target is empty                 |
| 4   | `[[a`         | literal text        | never closed                        |
| 5   | `[[a` / `b]]` | literal text        | a candidate does not cross a break  |
| 6   | `` `[[a]]` `` | verbatim            | fences and verbatim are not scanned |
| 7   | `![[a]]`      | an embed wikilink   | the `!` is recorded, see 9.2        |
| 8   | `\| [[a\|b]] \|` | cells `[[a` and `b]]`, literal text | the row is split into cells first, see 9.4 |
| 9   | `[[1]](u)`    | a wikilink, then the text `(u)` | the second `[` opens at the start of the first |
| 10  | `[[a](b)`     | literal text        | the wikilink never closes, and the link inside it was source |

Row 7 is the one that is a decision rather than a consequence. The `!`
marks an embed the way it marks an image: `![a](b)` is an image where
`[a](b)` is a link, and `![[a]]` is a wikilink with its embed bit set.
What an embed does is up to the consumer (section 0). An earlier draft
decayed the `!` to text, which would force any consumer that does give
embeds a meaning to rescan the source to learn whether it was there.

This needs no new rule. The first `[` of `![[` opens an image scope, so
3.1 applies unchanged and the bit is the kind of the scope the second `[`
arrives in.

Rows 9 and 10 are what the setting costs ordinary links. `[[1]](u)`, a
Markdown spelling of a link whose text is `[1]`, becomes a wikilink with
target `1` followed by text. And a `[` at the start of any link's text
is the second `[` of 3.1, so whatever it begins is read as a wikilink
region: `[[a](b)` is a wikilink candidate that never closes, and it
decays to text with the link it contained. Both are consequences of
deciding at the opener with no lookahead, and both are confined to
documents containing `[[`, which is section 2's claim.

## 4. What it produces

A node of its own, holding the target and an optional alias as strings,
and the embed bit.

The AST keeps it distinct from an ordinary link because the canonical
renderer writes back the spelling the source used: `[[a]]` and `[a](a)`
are different documents, and if the parse mapped both to one node only
one of them could be spelled back. The construct would then be
input-only, as underlined headings are. How it renders to HTML is a
separate question, and there it is sugar (section 5).

The alias is a field rather than a wrapper: `[[a]]` and `[[a|a]]` are
different documents, they render the same, and the renderer has to
choose between them, so the distinction has to be in the node.

## 5. How it renders

As the ordinary link it desugars to. A wikilink with target `t` renders
exactly as `Link [Str d] (Direct t)`, where `d` is the alias if there is
one and `t` otherwise. An embed renders as the `Image` of the same. The
node's attributes pass through as they do for a link.

```html
<a href="a">a</a>
<a href="a">the other direction</a>
<img alt="a" src="a">
```

The `href` is the raw target. Resolution belongs to the consumer and
happens before rendering, by rewriting the target, which is the path an
ordinary link's destination already takes.

There is no `wikilink` class. An earlier draft added one so that the two
constructs would not render identically, borrowing [[keyed-blocks]]
9.3's reason, but no theorem asks HTML output to tell them apart:
`Html.v` states nothing about injectivity. A class is a presentation
choice, and node attributes already let a consumer make it without a
renderer setting. A consumer that wants the class adds it to every
wikilink node before rendering, and a writer can spell `[[a]]{.wikilink}`
where inline attributes are on. Rendering by desugaring also keeps the
HTML arm to one line that calls the link or image arm, so it adds no
output shape the renderer does not already produce.

## 6. Canonical spelling

`[[target]]`, or `[[target|alias]]` when there is an alias, with a `!`
in front for an embed. There is only one spelling, so the choice is
forced.

The conditions on a canonical wikilink, which are conditions on the
strings rather than on the tree:

- the target is nonempty;
- neither half contains `]`, `|`, a newline, or a backslash.

Both are what make the source reparse to the node it came from, and they
are all of it. An untrimmed target is not excluded: `[[ a ]]` parses back
to itself, so tidiness is a check for a consumer that generates targets
(a rename, say) to run, not a condition of the canonical view.

One condition is on the tree rather than on the strings, and it applies
to the ordinary constructs, not to this one. With the setting on, **the
text of a link or reference may not begin with a child whose source
begins with `[`**: a wikilink, a footnote reference, or a link or
reference that is not an image. Rows 9 and 10 of 3.4 are why: the
renderer would write `[[[a]]](u)` or `[[^a]](u)`, and the scan reads the
second `[` as a wikilink opener. There is no other spelling of those
children, so the canonical fragment excludes them, as it excludes a table
cell whose row would not split back (9.4).

## 7. Worked examples

```
see [[Backlinks]] for more
```

one paragraph: the text `see `, a wikilink to `Backlinks` with no alias,
and the text ` for more`.

```
see [[Backlinks|the other direction]]
```

the same with the alias `the other direction`.

```
[[a]] and [[b|c]]
```

two wikilinks in one paragraph, which is the case that makes the point
that this is an inline construct and not a line one.

```
[[a [[b]] c]]
```

a wikilink to `a [[b`, then the text ` c]]`. The inner `[[` is content,
because the closer is the first `]]` and nothing looks inside the region.
This is the shape where the syntax reads worst, and it is the price of
deciding at the opener with no lookahead.

## 8. What this costs the development

The one section that names things in the code. Written before the work,
so every number here is a prediction to be checked afterwards.

**An inline constructor** carrying two strings and a bit. `UrlLink` is the nearest
existing leaf and is mentioned 12 times across `Ast.v`, `Document.v`,
`Html.v` and `Inline.v`. `Wf.v` does not mention it, which is the
interesting half: a leaf carrying strings has nothing for
well-formedness to say about it.

**A scanner state and one dispatch arm.** The state is `INote`'s with a
second string and a pending-`]` bit; the arm is the guard at the bottom
of `ilead` that recognises `[^`, with `[` in place of `^`, reading the
embed bit off the image flag the enclosing scope already carries. It also needs
an arm in the end-of-line disposition and one in the break disposition,
both of which are the decay to literal text that an unclosed autolink
already performs.

**Two scan lemmas.** `iscan_note_label` and `iscan_note_text` are the
template: about 35 and 25 lines, the first an induction over the label
and the second a `change`-heavy unfolding of the dispatch. The pending-`]`
bit makes the first slightly worse than its model.

**An inline setting.** One `dconfig` field, one field-local `with_`
function, one preservation theorem that is one line, exactly as every
other inline knob is.

**A canonical constructor**, if the roundtrip is wanted. `CINote` is the
model: 34 mentions, 28 of them in `Inline.v`, plus arms in the size,
source, well-formedness, AST and separation functions, plus one case in
the central scan lemma that runs about 12 lines on the existing template.

**Free, and this is the part worth predicting explicitly.** The
convention layer needs two arms and gains no theorem. A wikilink's target
is a destination, so the destination traversal and the destination
rewrite in `Site.v` take one arm each, and every rename theorem stated
over them applies unchanged. `l_ok`, `l_spell` and `l_parse` do not move:
a wikilink target is exactly the string those already speak about.

**One HTML arm**, the desugaring of section 5, which calls the existing
link and image arms.

**Also free.** The canonical renderer's escaping, for section 2's reason.
The exclusion of an aliased wikilink from a table cell (9.4): `ctrow_ok`
already asks `row_reparses` of every canonical row, and a row whose cell
renders as `[[a|b]]` does not scan back to the same cells.
Nothing in the block layer, since this is an inline construct that
occupies no line position. No parser state, no container, and therefore
none of the state-quantified block theorems.

**The located scan.** Source locations landed after the first draft of
this section, and every scanner state now owes two more cases: one in
the erasure refinement (`erase_iscan`, `erase_istep_at`) and one in the
line-composition family (`iout_app`, `istep_at_out_app`). The located
node spans from the `[[`, or the `!` of an embed, to the closing `]]`,
the extent `INote` already records for `[^`.

**Predicted obligations, stated so their failure names something.** No
existing theorem statement gains a hypothesis. One existing predicate
gains a clause: `ci_ok` of a link or reference, for section 6's
bracket-start condition, which moves the `ci_ok` equation for links and
the scan-lemma cases that unfold it. The single-line inline knob
preservation lemma is the only theorem the setting itself owes.

**The oracle stops covering this**, as it does for keys: no djot
implementation has the construct, so every wikilink document is a
divergence by construction. What remains is the extracted roundtrip sweep
and the generated corpus against our own parser.

### 8.1 Afterwards

Checked against the tree on 2026-09-22, prediction by prediction.

- **Constructor, setting, HTML arm, `Site.v`.** As predicted. `Site.v`
  took one arm each in `ci_dests` and `ci_map_dest`, one in the
  induction principle, and one proof case in `ci_map_dest_id`; no
  statement moved. `render_wikilink` in `Html.v` states section 5.
- **Scanner.** One state and one guard, as predicted, with the guard in
  the `[` branch of `ilead` rather than at its bottom, since the `[`
  branch runs first. The located scan cost its predicted erasure and
  composition cases, and `Wf.v` one arm in `iscan_wf` and four proof
  cases the section did not list: the invariant is quantified over all
  scanner states, which is the `pstate` checklist's lesson one layer
  down.
- **"No existing theorem statement gains a hypothesis."** False, and
  for the reason section 6's condition exists. `iscan_bracket_open`
  said a `[` in text mode always pushes a bracket, which the setting
  makes false; it now takes `wiki_opens ... = false` unless it is an
  image's. That hypothesis travels to `iscan_note_text` and to the
  central scan lemma `iscan_cis_scope`, whose bracket instances
  (`iscan_cis_bracket`, `iscan_cis_ref`) discharge it from
  `bracket_kids_ok`. No headline theorem moved: `roundtrip_blocks` and
  the erasure refinements are stated as before.
- **"One existing predicate gains a clause."** Held: `bracket_kids_ok`
  in `ci_ok` of a link and a reference.
- **"Two scan lemmas."** Three: the region scan, the split of a
  canonical region, and the whole wikilink, the last about 50 lines.
- **Not predicted at all.** A generator pool and a harness mode, the way
  keys have one, since the plain pool is read at djot's table and so
  never meets the construct.

## 9. Open questions

### 9.1 Should the alias be inline content?

Raw source for now, decided on cost rather than on principle, which is
the kind of decision [[extension-decisions]] says to label as open rather
than to dress up.

Raw keeps the node a leaf, and being a leaf is what makes section 8's
estimate hold: a leaf needs no child scope to reconstruct, no recursion
in the canonical view, and no scope discipline in the scanner.

The case for inline content is that an alias is *display text*, and every
other display text in the language is inline content. `[[a|the **other**
direction]]` is a thing a writer will eventually type. If it is wanted
later, the node gains a child list and the canonical constructor becomes
link-shaped rather than note-shaped, which is a real step up in cost and
touches the scanner rather than only the types: the region would stop
being source and start being a scope.

The thing to decide it on is not taste but whether any *theorem* wants
one or the other. As of writing, none does.

### 9.2 Embeds

**Answered: the parser records the `!`, and the meaning is the
consumer's.** `![[a]]` is a wikilink with its embed bit set (3.4 row 7),
and HTML renders it as an image (section 5). A consumer that
transcludes, as Obsidian does, replaces embed nodes with another
document's blocks before rendering. That makes one document's output
depend on another's, which is a site-level operation and stays outside
this construct.

### 9.3 Target substructure

Obsidian's `[[note#heading]]` and `[[note#^block]]` name a place inside a
note rather than the note. Nothing here forbids them: the target is a
string, and `#h` is part of it. Whether that string is *split* is up to
the consumer, and `Site.v`'s convention already has the field for saying
which targets it can name.

This is the right seam and it is worth checking it stays that way: if the
splitting ever has to happen in the parser, the target stops being one
string and section 8's "free" claim about the convention layer stops
being true.

### 9.4 Aliases in table cells

**Decided: no alias inside a table cell.** A row is split into cells
before any inline scanning, and the splitter knows only verbatim and
backslash escapes, so `| [[a|b]] |` is two cells, `[[a` and `b]]`, each
of which decays to literal text (3.4 row 8). A wikilink without an alias
works in a cell as anywhere else.

Keeping `[[a|b]]` whole would mean the row splitter repeating 3.1's
decision, which depends on the bracket scope it opens in, from a layer
below the inline settings. The two scanners would then have to agree
on the decision, and that coupling is not worth one case.

Obsidian's convention is to write `[[a\|b]]` in a table and read the
`\|` as the separator. Here the row splitter leaves a bar after a
backslash in its cell, and 3.2 keeps the backslash, so that spelling
reaches the node as target `a\|b` with no alias. A consumer following
Obsidian can split it there. Making the parser do the split would give
a backslash different meanings in and out of a cell, and the inline
scanner does not know which it is in; it would need a cell flag threaded
into the scan. Open if a consumer asks for it, at that cost.
