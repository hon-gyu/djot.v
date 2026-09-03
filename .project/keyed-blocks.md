---
ai-disclosure: ai-generated
---
# Keyed blocks

Status: **specification under discussion**. Nothing is implemented, and
this file stands on its own: it is the definition of the construct, not
a staging area, and it stays here once the construct exists.

Prose first. Sections 0 to 7 define the syntax without naming a single
identifier in the development; everything that touches the code is
gathered in section 8, and section 9 is what is still undecided.

Prior art is oyster's `struct`, in `oyster/specification/oyster/`. It is
a reference, not an oracle, and nothing below depends on having read it.

## 0. The idea

A colon is a binary connective. It takes an **inline** on the left and a
**block** on the right, and builds a node saying "this block is what
this label names".

```
label : block
```

The reading a writer should be able to hold in their head, and the thing
every rule below exists to protect:

> When I see a colon, I am one level deeper in the abstraction stack.
> When the block after it finishes, I am back where I was.

Everything the colon does is tree shape. It moves no text, it consumes
no prefix, it shifts no column. Two documents that differ only in
whether keys are enabled hold the same inline content in the same order.

## 1. Baseline: what djot does with these documents today

Not decisions. Pinned from djot.js v0.3.2 on 2026-09-03, and the reading
each rule below displaces. Every row is a *bad* reading for a writer who
meant a key, which is the argument for the construct.

| input                                           | djot today                                                       |
| ----------------------------------------------- | ---------------------------------------------------------------- |
| `foo:` / `- bar`                                | one paragraph, `"foo:"` softbreak `"- bar"`                      |
| `foo:` / ` ``` ` / `bar` / ` ``` `              | one paragraph; a fence cannot interrupt a paragraph either       |
| `- foo:` / ` ``` ` / `bar` / ` ``` ` / `- baz`  | list, then code block, then a **second** list                    |
| `- tt` / `  - foo:` / ...                       | `- foo:` is lazy text of `tt`; a sublist needs a preceding blank |
| `- foo` / blank / `  ``` ` / `  bar` / `  ``` ` | works, but the blank forces the list **loose**                   |

The last row is the honest statement of the motivation. It is not that
djot cannot put a code block in a list item; it is that the only way to
do it costs a blank line, which costs tightness, and that the unindented
spelling is not available at all.

## 2. Enabling

One block setting, off by default. With it off, every spelling below is
ordinary paragraph text and the parse is bit-identical to djot's.

Keys are **non-conservative**: turning them on changes the meaning of
documents that are already valid djot. Every row of the table above is
such a document. That is what the configurable syntax family is for, but
it means keys are a mode, not a default.

## 3. Where a colon is a connective

Two positions, and only two.

### 3.1 Line-final

A text line whose content, after trailing whitespace is removed, ends
with an unescaped `:`, arriving when nothing is open at that level.

```
foo:
```

The label is everything before the colon. The block is the next one.

### 3.2 Inline

The first unescaped `:` on such a line, when it is followed by a space
or by the end of the line.

```
foo: bar
```

The label is `foo`. The block is the paragraph starting at `bar`.

The line-final case is the same rule with an empty remainder: the block
has to come from the following lines instead. That is why nothing below
distinguishes the two forms. They differ only in whether the block
starts on the key line.

Chains follow, and are not a separate rule. A key's block is parsed like
any other block, and a paragraph beginning `label: ` is a key, so
`foo: bar: baz` is `foo` naming `bar` naming the paragraph `baz`.
Forbidding that would take an exception saying a key's block may not
itself be keyed, which is a worse rule than the one it removes. The scan
is left to right and each split is final, so nothing is reconsidered.
<!-- CR: hmm, is it true that forbidding it would cause such issue? I am heasitant on whether to allow multiple keys in one line. 
It kinds of hurt readability and it's less intuitive. I think at least we should have a knob to disable multiple keys in one line?
Is it really bad to add the restriction that a line can only have one key?
 -->

Colons in ordinary prose are therefore keyed:

```
Note: this matters.
```

is a key named `Note`. That is the cost of the inline form and it is
accepted; a writer who means punctuation escapes it.

```
Note\: this matters.
```

### 3.3 Where it is not a connective

<!-- CR: the first row sounds a bit weird because there's actually a connective in the end. it's just not the middle one. -->

| spelling              | reading                           | why                                  |
| --------------------- | --------------------------------- | ------------------------------------ |
| `foo\: bar:`          | label `foo: bar`, keyed           | an escaped colon is literal          |
| `foo\: bar`           | plain paragraph                   | no unescaped colon                   |
| `:::`                 | div opener, or text with divs off | ends in a colon but is read earlier  |
| `:` alone             | plain paragraph                   | the label would be empty             |
| `: term`              | definition-list marker            | the colon is initial, not final      |
| `http://x` in prose   | plain paragraph                   | the colon is not followed by a space |
| `# foo:`              | plain heading                     | a key opens from a text line only    |
| a line inside a fence | verbatim                          | fences are not classified            |

The heading row is a decision rather than a consequence. Headings
already build document structure through sections, and a line that was
both a heading and a key would carry two nesting effects at once.

## 4. Scope: exactly one block

A key claims **one** block, and its scope ends when that block ends.

This is what makes the stack reading true. A scope that ran to the next
blank line would end where the writer happened to leave a blank, which
is not a level in any stack; a writer who has finished the block expects
to be back at the level they came from, whether or not they typed a
blank line.

A block ends the way that block always ends. Nothing new is introduced,
and the consequences differ by block:

| the key's block               | ends at                                               |
| ----------------------------- | ----------------------------------------------------- |
| fenced code, raw block        | its closing fence                                     |
| fenced div                    | its closing fence                                     |
| thematic break                | the same line                                         |
| heading, without continuation | the same line                                         |
| table                         | the first line that is neither a row nor a caption    |
| paragraph                     | a blank line, or a line that cuts the paragraph       |
| list                          | a blank, or a line that is neither content nor marker |
| blockquote                    | the first line without the prefix                     |

The split in this table is what section 5 turns on. The first four rows
end on a line the block itself consumes and nobody else needs to see.
The last four end on a line that belongs to whatever is outside.

## 5. Claiming a block out of column

A list decides what is inside an item by column: a line indented past
the marker is content, a line at or before it is not. A key says the
opposite, that this block belongs here whatever column it sits at. So
while a key's block is open, the enclosing containers stop asking about
column and the line goes straight down to the key.

`````
- foo:
```
bar
```
- baz
`````

```
BulletList (tight)
├── item
│   └── Keyed "foo"
│       └── CodeBlock "bar"
└── item
    └── Para "baz"
```

Line 2 sits at column 0 and so does the list's marker, so ordinarily the
list ends there, which is why djot produces two lists for this input.
Here the open key holds the list open and takes the fence. Line 4 closes
the fence, which ends the key's block, which ends the override. Line 5
is a marker at column 0 with nothing open below, so the list sees it and
it is that same list's second item.

### 5.1 The override is about column only

It does not remove a blockquote's `>` prefix and does not neutralise a
div's closing fence.

A key is a claim about where a block *sits*, and column is the only
containment that is about where a block sits. A quote prefix and a div
fence are marks on the line, present or absent; letting a key drop them
silently would make a quoted region's extent depend on a colon several
lines above it. So inside a blockquote the key's block still carries the
prefix:

`````
> foo:
> ```
> bar
> ```
`````

### 5.2 Only self-closing blocks may be claimed out of column

This is the crucial restriction, and this example is why:

```
- foo:
- bar
```

It is **two list items**. `foo:` is not a key; the colon is literal
text, exactly as if the writer had typed `- foo:` and then a second
bullet, which is what they did.

Two readings compete for line 2. Either the open key takes it, in which
case `- bar` starts a fresh list nested inside `foo`; or the enclosing
list takes it as its own second item, in which case `foo` never gets a
block and the colon retracts. The second wins, and the reason is that
the first has no way back. A list ends at a blank line or at a line that
is neither its content nor a marker, so every following bullet at that
column would join the inner list and the outer one could never resume.
A claim you cannot return from is not a level in a stack, it is a
takeover, and it breaks the one reading this construct exists to
provide.

Generalised, using the table in section 4: **a key may claim a block out
of column only when that block ends on a line it consumes.** Fenced
code, raw blocks, fenced divs, thematic breaks and single-line headings
qualify. Paragraphs, lists, tables and blockquotes do not, because they
end by being interrupted, and the interrupting line is precisely the one
the enclosing container needed to see.

The restriction applies **only** to claiming out of column. Where no
override is in play, because the block sits where it would sit anyway,
a key may claim any block at all. Both of these are fine:

```
foo:
- bar
- baz
```

`````
- foo:
  ```
  bar
  ```
`````

The first is at top level, where no list is being held open. The second
indents the fence into the item the ordinary way. Only the unindented
form inside a container needs the override, and only there is the block
restricted.

## 6. Retraction

A key that never gets a block is not a key. The colon is literal text
and the line is the paragraph it would have been.

```
foo:

bar
```

```
Para "foo:"
Para "bar"
```

The same at end of input: a document that is only `foo:` is one
paragraph. The same inside a list: `- foo:` then a blank then `- bar` is
a loose two-item list whose first item is `Para "foo:"`, and the blank
makes it loose exactly as it does today.

Nothing is undone by this. A key produces no node until it closes, so
retraction discards a state rather than revising a result. Block
attributes and table captions already work this way: both wait, and both
turn back into ordinary text if what they were waiting for never comes.

## 7. Worked examples

Trees are in keyed mode. The baselines are in section 1.

### 7.1 Top level, line-final

```
foo:
- bar
- baz
```

```
Keyed "foo"
└── BulletList (tight)
    ├── item → Para "bar"
    └── item → Para "baz"
```

The list is the key's one block and ends at end of input. No override is
involved: because the key line does not open a paragraph, the marker on
line 2 arrives with nothing open and starts a list normally. That alone
is what fixes the first two rows of section 1, and it is worth
separating from section 5, because it is by far the cheaper half.

### 7.2 Top level, inline

```
foo: bar
```

```
Keyed "foo"
└── Para "bar"
```

With a further line `baz`, the block is `Para "bar\nbaz"`, because the
block is a paragraph and a paragraph continues.

### 7.3 A key inside a list item, indented

`````
- foo:
  ```
  bar
  ```
`````

```
BulletList (tight)
└── item
    └── Keyed "foo"
        └── CodeBlock "bar"
```

Line 2 is indented past the marker, so the item takes it the ordinary
way and no override is needed. This is the direct answer to the last row
of section 1: a **tight** list item with a code block child, which djot
cannot spell at all.

### 7.4 Returning to the enclosing list

The example in section 5. What it asserts is that `foo` and `baz` are
siblings.

### 7.5 Returning to a nested list

`````
- tt
  - foo:
```
bar
```
  - baz
`````

```
BulletList (tight)
└── item
    ├── Para "tt"
    └── BulletList (tight)
        ├── item → Keyed "foo" → CodeBlock "bar"
        └── item → Para "baz"
```

**This needs a second setting as well as keys.** In djot a sublist must
be preceded by a blank line, so line 2 is lazy text of `tt` and there is
no inner list for `foo` to be an item of. The setting that changes it is
the one that lets a list marker interrupt a paragraph, which exists in
the tree already and is on the wanted list in `beyond-djot.md`. Keys do
not supply it and cannot stand in for it.

Given that setting, line 3 passes through two lists that the open key is
holding open, and reaches the fence. Line 5, at column 2 with the key
finished, is content to the outer list (its marker is at column 0) and a
marker to the inner one (whose marker is at column 2), so `baz` is
`foo`'s sibling. That is the stack discipline two levels deep.

### 7.6 Nesting keys

```
foo:
bar:
baz
```

```
Keyed "foo"
└── Keyed "bar"
    └── Para "baz"
```

Line 2 arrives with `foo`'s key open and nothing else, so it opens a key
of its own. `baz` is a paragraph, which ends at end of input; that ends
`bar`'s block, which is `foo`'s block, so both close together. The
one-line form `foo: bar: baz` gives the same tree.

## 8. What this costs the development

The one section that names things in the code.

**A new block constructor**, `Keyed`, holding one inline label and its
children. Around thirteen sites match on the block type across `Wf.v`,
`Html.v`, `Document.v`, `Render.v` and `Ast.v`'s induction principle.

**A new parser state**, sitting in the container stack beside `PDiv`,
which it closely resembles: it eats no prefix and shifts no column, so
it records no column either, and `step_fuel_shift` and `step_fuel_pad`
cost nothing. There are 25 explicit `destruct` sites over the state type
and 27 mentions of `PDiv`; most of the new arms are the `PDiv` arm
copied. `finish`, `lazy_ok`, `feed_lazy`, `pstate_depth`,
`blank_absorbed`, `blank_safe` and `pad_safe` each take one.

**Free**: `prefix_determinism`, `no_future_line_dependence` and
`prefix_state_suffices`. All three are facts about `parse_lines` being a
fold and are proved without mentioning `step`, so a new state cannot
reach them. The knob's preservation lemma is one line, like every other
block knob's.

**Breaks**: `wrap_neutral`, and through it `hard_wrap_one_para`. With
keys on, a text line and the nonblank lines after it are no longer one
paragraph. The keyed setting therefore joins `with_marker_interrupts`
and `with_underline` as one that preserves the property only under a
side condition, which for a bool is that it is off.

**Canonical spelling**, for the roundtrip fragment: the two-line form
rather than the inline one, the block at the key's own column with no
blank between, and labels whose rendering would end in a colon excluded
from the fragment rather than escaped, the way a fence its own content
would close is excluded. The canonical constructor is then a wrapper of
exactly the shape `CId` has, one source line in front of an existing
block, and it inherits that constructor's arms in `ends_clist`,
`is_clist` and the pair predicates.

**Unscoped**, and the reason section 5 is separated from the rest: an
item holding a block claimed out of column renders some of its lines
unindented. Today `litem_lines` indents an item's lines uniformly and
`list_uniformity` reads an item's content as its lines with that indent
removed. A block at column 0 inside an item at column 2 has no indent to
remove, so the item is no longer related to its top-level reading by
`pad_state`, and `step_fuel_pad` is the lemma that relation runs
through. Nothing here says how much of `ListUniformity.v` that touches.
This is the only part of the proposal whose cost is unknown, and it is
worth landing sections 3, 4, 6 and 7.1 to 7.3 without it.

## 9. Open questions

### 9.1 The inline form splits inside opaque inline constructs

The rule in 3.2 is lexical: it scans the raw line for the first colon
followed by a space, before any inline parsing. So it fires inside
constructs whose contents should be opaque.

```
`a: b` is how you write it
```

The first colon-space is inside the verbatim span. The label would be
`` `a ``, carrying an unclosed backtick, and the block would start at
`` b` is how you write it ``.

```
[see: here](x) is the reference
```

Same, with the label `[see` carrying an unclosed bracket.

The escape hatch of 3.2 does not cover the first case: verbatim spans
are literal, so `` `a\: b` `` contains a backslash rather than escaping
anything. A writer who wants that line has no spelling for it.

Three candidate rules:

1. **The label may not contain a backtick or an opening bracket.**
   Line-local, cheap, checkable without inline parsing. Rejects
   `` `code`: a description ``, which is a label a writer would
   plausibly want.
2. **The label must be complete inline content.** Precise, and admits
   `` `code`: a description ``. Requires running the inline scanner on
   the candidate label, which makes deciding a block's shape depend on
   the inline layer, a dependence that does not exist today.
3. **Accept it and log it.** The failing shapes are unusual at the start
   of a line, and the writer can reorder.

Undecided. Note that the line-final form of 3.1 has a milder version of
the same problem: `` a `b:` `` ends in a colon inside a verbatim span.

### 9.2 The cost of claiming out of column

The last entry in section 8. Until it is measured, the price of section
5 is unknown, and section 5 is the half that delivers the unindented
spelling. Sections 3, 4, 6 and the first three worked examples do not
depend on it, so the question is whether to land them first and measure
section 5 separately. The recommendation here is yes.

### 9.3 How a keyed node renders

There is no djot.js image and no HTML precedent. A description list with
one term and one definition reuses vocabulary that says roughly the
right thing. A section with a heading says something about document
structure that is probably too strong. A div with the label as an
attribute says the least and is the easiest to change later.

Deliberately the last question, because nothing above depends on the
answer.
