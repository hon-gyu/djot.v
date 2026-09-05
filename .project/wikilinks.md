---
ai-disclosure: ai-generated
---
# Wikilinks

Status: **spec drafted, waiting for polish**. Nothing in this file
exists in the tree yet, and the prose has not had a second pass.
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

A note names another note by its name, not by its path.

```
see [[Backlinks]] for the reverse direction
```

That is one link, to the note called `Backlinks`, displayed as
`Backlinks`. With an alias it displays something else:

```
see [[Backlinks|the other direction]]
```

The construct exists because the ordinary spelling makes a writer say
the name twice, once as text and once as a destination, and the two
drift apart under renaming. A wikilink says it once, which is what makes
a rename mechanical: there is one occurrence to rewrite and nothing to
keep in agreement with it.

**The target is a name, not a URL.** What that name resolves to is not
this file's business -- [[260903.rename-canonicity]] and `Site.v` own
that, through a link convention that already exists and already models a
flat vault. A wikilink is the syntax half of something whose semantics
are in the tree.

## 1. Baseline: what djot does with these documents today

Not decisions. Pinned from djot.js v0.3.2 and from our own parser on
2026-09-05; the two agree on every row.

| input           | djot today                                |
| --------------- | ----------------------------------------- |
| `[[a]]`         | literal text `[[a]]`                      |
| `[[a\|b]]`      | literal text                              |
| `[[]]`          | literal text                              |
| `[[a`           | literal text                              |
| `![[a]]`        | literal text                              |
| `x [[a]] y`     | literal text throughout                   |
| `[[a [[b]] c]]` | literal text                              |
| `[[*a*]]`       | `[[`, a strong span over `a`, then `]]`   |
| ``[[a`b`]]``    | `[[a`, a verbatim, then `]]`              |

Every row but the last two is a single `Str`, which is the strongest
form of "the slot is free": a document containing `[[` almost always
means nothing to djot beyond its own characters.

The last two are the exception and they are the reason the setting is a
mode rather than a default. With wikilinks off, the region between the
brackets is ordinary inline content and its markup is live. With them
on, the region is source, and `[[*a*]]` names a note whose name contains
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
renders as `\[\[a\]\]` and comes back as text with either setting. The
obligation that cost keys a whole subsection is already discharged, and
it was discharged before this construct was thought of.

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

A single `]` is content: `[[a]b]]` names `a]b`. A backslash protects the
next character, so `[[a\]]]` names `a]`, the escaped bracket being
content and the pair after it the closer. Section 6 keeps `]` out of
canonical targets altogether, so this spelling has to be defined but
never has to be pleasant.

**It does not cross a line break.** A candidate still open at the end of
a line decays to literal text, exactly as an unclosed autolink does. The
reason is not symmetry with autolinks but the convention layer: a target
is a path, and no link convention can name a path containing a newline,
so a wikilink spanning a break could never resolve to anything. A
footnote label, which does cross, is normalized whitespace rather than a
name.

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

**Nothing is trimmed.** `[[ a ]]` names the note ` a `, spaces included.
Trimming would be friendlier and it is what Obsidian does, but it is a
normalization, and a normalization the renderer cannot undo: the source
`[[ a ]]` and the source `[[a]]` would produce the same node and only
one of them could be spelled back. So the parse keeps what is written
and section 6 excludes the untidy spellings from the canonical fragment
instead, which is where a condition of that kind belongs.

**An empty target is not a wikilink.** `[[]]` and `[[|b]]` decay to
literal text. There is nothing to name, and admitting them would put a
node in the tree that no convention can resolve.

### 3.4 Where a `[[` is not a wikilink

| #   | input       | reading             | why                                |
| --- | ----------- | ------------------- | ---------------------------------- |
| 1   | `\[[a]]`    | literal text        | the first bracket is escaped       |
| 2   | `[a[b]]`    | as today            | the second `[` is not at the start |
| 3   | `[[]]`      | literal text        | the target is empty                |
| 4   | `[[a`       | literal text        | never closed                       |
| 5   | `[[a` / `b]]` | literal text      | a candidate does not cross a break |
| 6   | `` `[[a]]` `` | verbatim          | fences and verbatim are not scanned |
| 7   | `![[a]]`    | `!` then a wikilink | see 9.2                            |

Row 7 is the one that is a decision rather than a consequence. In
Obsidian `![[a]]` embeds the note's contents; here the `!` is an image
marker that finds no image and decays to text, and the wikilink is
recognised normally. Embedding is a transclusion, which is a document
operation and not an inline one.

## 4. What it produces

A node of its own, holding the target and an optional alias, both as
strings.

It is not sugar for an ordinary link. Sugar would mean the two spellings
were indistinguishable once parsed, so the canonical renderer would spell
every wikilink as `[a](a)` and the construct would be input-only. That is
a real option -- underlined headings are input-only for exactly this
reason -- and it is rejected here because the point of a wikilink is to
survive a rename, and surviving a rename means being written back.

The alias is a field rather than a wrapper: `[[a]]` and `[[a|a]]` are
different documents, they render the same, and the renderer has to
choose between them, so the distinction has to be in the node.

## 5. How it renders

An anchor whose destination is the target and whose content is the alias
if there is one and the target otherwise, carrying a class.

```html
<a class="wikilink" href="a">a</a>
<a class="wikilink" href="a">the other direction</a>
```

The `href` is the raw target rather than a resolved URL. Resolution is
the convention's job and it happens before rendering, by rewriting
destinations, which is the same path an ordinary link's destination
takes. The class is what keeps a wikilink and an ordinary link from
rendering identically, for [[keyed-blocks]] 9.3's reason.

## 6. Canonical spelling

`[[target]]`, or `[[target|alias]]` when there is an alias. There is
only one spelling, so the choice is forced.

The conditions on a canonical wikilink, which are conditions on the
strings rather than on the tree:

- the target is nonempty;
- neither half contains `]`, `|`, a newline, or a backslash;
- the target has no leading or trailing whitespace.

The first three are what make the source reparse to the node it came
from. The fourth is 3.3's deferred tidiness: an untrimmed target parses
fine and renders fine, and it is excluded from the tested fragment
because nothing should be generating one.

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

**An inline constructor** carrying two strings. `UrlLink` is the nearest
existing leaf and is mentioned 12 times across `Ast.v`, `Document.v`,
`Html.v` and `Inline.v`. `Wf.v` does not mention it, which is the
interesting half: a leaf carrying strings has nothing for
well-formedness to say about it.

**A scanner state and one dispatch arm.** The state is `INote`'s with a
second string and a pending-`]` bit; the arm is the guard at the bottom
of `ilead` that recognises `[^`, with `[` in place of `^`. It also needs
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

**Also free.** The canonical renderer's escaping, for section 2's reason.
Nothing in the block layer, since this is an inline construct that
occupies no line position. No parser state, no container, and therefore
none of the state-quantified block theorems.

**Predicted obligations, stated so their failure names something.** No
existing theorem statement gains a hypothesis. No existing predicate
splits in two. The single-line inline knob preservation lemma is the only
theorem the setting itself owes.

**The oracle stops covering this**, as it does for keys: no djot
implementation has the construct, so every wikilink document is a
divergence by construction. What remains is the extracted roundtrip sweep
and the generated corpus against our own parser.

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

`![[a]]` is a `!` followed by a wikilink here, and in Obsidian it embeds
the target's contents. Embedding is transclusion: it makes a document's
meaning depend on another document, which is a site-level operation and
would need the site to be an argument to rendering. That is a larger
change than this construct and it is deliberately not started here.

### 9.3 Target substructure

Obsidian's `[[note#heading]]` and `[[note#^block]]` name a place inside a
note rather than the note. Nothing here forbids them: the target is a
string, and `#h` is part of it. Whether that string is *split* is the
convention's business, and the convention already has the field for
saying which targets it can name.

This is the right seam and it is worth checking it stays that way: if the
splitting ever has to happen in the parser, the target stops being one
string and section 8's "free" claim about the convention layer stops
being true.
