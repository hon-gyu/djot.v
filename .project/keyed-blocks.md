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

A colon is a binary connective. It takes **inline content** on the left
and a **block** on the right, and builds a node saying "this block is
what this label names". The left operand is content, not one element: a
label may be a word, a styled run, a link, or a mix.

<!-- CR: hmm, I don't understand how "inline content" differ from "inline"? could you explain?
Also, I don't want to say "A names B". It's just a loose connective and the semantics should be decided by the reader and the writer.
 -->

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

The colon has to be a real one, by the same test 3.2 uses: everything
before it must be settled. So `` a `b:` `` is not a key,
because its final colon is inside a verbatim span.

<!-- CR: the final result that this is not a key looks intuitive but I wonder how we can implement this? 
what will happen at the byte of the colon? how can we know if the backtick will be closed or not? -->

### 3.2 Inline

A `:` on such a line, followed by a space or by the end of the line,
splits it into a label and a value.

```
foo: bar
```

The label is `foo`. The block is the paragraph starting at `bar`.

The line-final case is the same rule with an empty value: the block has
to come from the following lines instead. That is why nothing below
distinguishes the two forms. They differ only in whether the block
starts on the key line.

**Which colon.** The first one that is not escaped, is followed by a
space or the end of the line, and is a point where the label is
**settled**.

Settled means: nothing later in the line can change how the text before
the colon reads. That is the property a split has to preserve, because
the split throws the rest of the line away as far as the label is
concerned, and a label that reads differently once cut is a label the
writer did not write.

It is not a claim that the text before the colon is *valid*. Every
string is valid inline content in djot, which has no inline errors:
`x{title="a` on a line of its own is fine, and reads as the literal text
`x{title=` followed by a curly quote and `a`. That is exactly why it is
not settled. Inside `x{title="a: b"}y: z` the same characters read as
the word `x` carrying a title. Splitting at the first colon would
silently give the label the first reading, so that colon is not a
candidate and the scan goes on to the next one.

Operationally the test is one bit of the inline scanner's own state:
**nothing is open**. No verbatim run, no attribute brace, no bracket, no
delimiter that a later character could still close. The scanner already
carries exactly that, so the whole test is a query at each candidate
position, and reading the line once answers it at all of them. This is a
scan, not a search with backtracking: the split point is found in one
pass and never revised.
<!-- CR: this is good. but writing-wise we should move this to an earlier point so that it's clearer.
I believe this paragraph also answers my previous CR question, right? If so, no need to answer that one.-->

| #   | line                              | splits at       | label              |
| --- | --------------------------------- | --------------- | ------------------ |
| 1   | `foo: bar`                        | the first colon | `foo`              |
| 2   | `` `a: b` is how you write it ``  | nowhere         | not a key          |
| 3   | `` `code`: a description ``       | after the span  | `` `code` ``       |
| 4   | `[see: here](x) is the reference` | nowhere         | not a key          |
| 5   | `[see](x): the reference`         | after the link  | `[see](x)`         |
| 6   | `foo{#my-foo}: bar`               | after the brace | `foo{#my-foo}`     |
| 7   | `x{title="a: b"}y: z`             | after `y`       | `x{title="a: b"}y` |
| 8   | `"foo: bar" and more`             | nowhere         | not a key          |
| 9   | `"foo": bar`                      | after the quote | `"foo"`            |
| 10  | `_a: b_`                          | nowhere         | not a key          |

Rows 2, 4, 8 and 10 have exactly one candidate colon and it is inside an
open construct, so those lines are not keys. Row 10 is the one worth
staring at: `_a: b_` is emphasis over `a: b`, and the label `_a` would
be the literal characters `_a`, so the colon is not a connective. Rows
8 and 9 are the same construct opened and closed, since a quotation mark
pairs in djot like any other delimiter.

**A label is inline content, not one element.** Row 7's label is two
nodes, the word `x` carrying a title and the word `y`. Nothing requires
it to be a single inline, and requiring that would buy nothing: adjacent
words are one text node anyway, so the restriction would only reject
labels that mix a styled run with plain text.
<!-- CR: hmm, I am confused about this rule. What is the AST like for `x{title="a: b"}y` today?
are you suggesting that x`y`: z can be a key? -->

**Attributes carry through**, which is row 6. A label is inline content
like any other, so it may hold emphasis, a link, a verbatim span, or an
attribute brace, and the attribute attaches inside the label exactly as
it would in a paragraph. In `foo{#my-foo}: bar` the id lands on the word
`foo`, because that is the inline element the brace follows. It does
**not** name the keyed node. To name the node, put the attribute on its
own line above, which already works and is already what an address is:

```
{#my-foo}
foo: bar
```

**One key per line.** A line is split at most once. What follows the
colon opens a paragraph and is not read again as a key line, so
`foo: bar: baz` is `foo` naming a paragraph whose text is `bar: baz`,
not a chain. That paragraph continues onto later lines like any other;
what it does not do is split a second time. `foo: bar:` is likewise
`foo` naming a paragraph reading `bar:`, trailing colon and all.

Nesting is by line:

```
foo:
bar: baz
```

is `foo` naming `bar` naming `baz`, because line 2 is a fresh line and
gets its own split.

One colon per line, one level per line. The alternative, re-reading the
value as if it were a fresh line, is not harder to define, but it makes
a single prose sentence nest twice: `Note: see this: it matters` would
be two accidental levels rather than one. Splitting once bounds the
damage of the case below at one level.

The price is that the one-line form is not quite sugar for the two-line
one. For almost every value the two spell the same tree:

<!-- CR: writing-wise, I don't really think this is a "price" at all. -->

```
foo: bar
```

```
foo:
bar
```

Both give `foo` naming `Para "bar"`. But when the value would itself be
a key line, they part:

```
foo: bar: baz
```

```
foo:
bar: baz
```

The first is `foo` naming `Para "bar: baz"`, one level. The second is
`foo` naming `bar` naming `Para "baz"`, two levels, because line 2 of
the second is a line and gets a line's split. That single exception is
the entire cost of the rule, which is why there is no setting for it: a
setting would exist to move one sentence.

**Colons in ordinary prose are keyed.**

```
Note: this matters.
```

is a key named `Note`. That is the cost of the inline form and it is
accepted; a writer who means punctuation escapes it.

```
Note\: this matters.
```

### 3.3 Where a colon is not a connective

| #   | colon                               | reading                | why                               |
| --- | ----------------------------------- | ---------------------- | --------------------------------- |
| 1   | `foo\: bar`                         | literal text           | escaped                           |
| 2   | `` `a: b` ``                        | literal text           | inside an unclosed construct      |
| 3   | `http://x`                          | literal text           | not followed by a space           |
| 4   | the second colon in `foo: bar: baz` | literal text           | the line is split once            |
| 5   | the second colon of `foo: bar:`     | literal text           | same, and it is the value's text  |
| 6   | `:::`                               | div opener             | the line is read as a div first   |
| 7   | `:` alone                           | plain paragraph        | the label would be empty          |
| 8   | the leading one of `: term`         | definition-list marker | initial, not final                |
| 9   | the one in `{#i}: bar`              | plain paragraph        | the label would be empty          |
| 10  | the one in `# foo:`                 | plain heading          | a key opens from a text line only |
| 11  | any colon inside a fence            | verbatim               | fences are not classified         |

`foo\: bar:` is therefore keyed, with label `foo: bar`: the escaped
colon is text and the final one is the connective.

Row 9 is an instance of row 7 rather than a rule of its own, and it is
the one case where that takes an argument. `{#i}` at the head of a line
is an inline attribute with no inline in front of it to decorate, so
djot drops it: `{#i}: bar` is one paragraph holding the single text node
`: bar`, with no attribute anywhere, and the identifier is gone. The
label a split would produce is therefore not the string `{#i}` but the
empty sequence, which row 7 already refuses. The parse is the same with
keys on and with keys off.

This is worth knowing rather than worth fixing. A writer who meant to
name the node wants the block-attribute line of 3.2, on its own line
above; a writer who meant the literal braces escapes the first one.

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

### 5.2 A block whose end nobody announces cannot be claimed out of column

The override lasts exactly as long as the block, so the block has to say
when it is over. A fence says so: its closing line is its own, and the
list underneath knows it is back in charge on the next line. A list does
not say so. A list ends when something else takes the line, and taking
the line is precisely what the override was preventing.

So there is nothing for the override to last until, and the ordinary
rules apply:

```
- foo:
- bar
```

This is **two list items**. `foo:` is not a key, the colon is literal
text, and this is the same document a writer gets from typing a bullet
and then another bullet, which is what they did.

It could not have been otherwise. Suppose the key took line 2. Then
`- bar` starts a fresh list inside `foo`, and every following bullet at
that column joins *that* list, because a list ends at a blank line or at
a line it does not recognise, and there is no such line. The outer list
never resumes. That is not one level deeper, it is a takeover, and it is
the one reading this construct exists to rule out.

Read off the table in section 4, the blocks whose end is on a line of
their own are fenced code, raw blocks, fenced divs, thematic breaks and
single-line headings. Those are the ones a key can pull out of column.
Paragraphs, lists, tables and blockquotes end by being interrupted, and
the interrupting line is the one the container outside needed to see.

None of this is a limit on what a key may name. It is a limit on where
that block may sit, and it applies only when a key is holding a
container open. Both of these are fine, and neither involves an
override:

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

The first is at top level, where no list is being held open, so the key
names a list with nothing overridden. The second indents the fence into
the item the ordinary way. A key names any block at all; only the
unindented spelling inside a container asks anything of the block.

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
`bar`'s block, which is `foo`'s block, so both close together.

This is the only spelling of that tree. `foo: bar: baz` on one line is
`foo` naming the paragraph `bar: baz`, by the one-key-per-line rule in
3.2: a level costs a line.

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

**The split test reaches into the inline layer.** Deciding where a line
splits needs to know whether the scanner has anything open, which
`classify` cannot see:
`Line.v` sits below `Inline.v`. It does not have to. The test belongs in
`open_kind`'s text arm, in `Step.v`, which already imports `Inline`, so
the layering costs nothing and no existing definition moves. Two things
it does cost. The test has to be stable under a leading run of spaces,
or `step_fuel_pad` fails; normalising the line first is enough. And
every concrete `Example` that parses a text line now scans it twice, a
constant factor rather than a branching one, but worth a `coqc -time`
reading before and after.

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

### 9.1 Does "nothing is open" really mean "settled"?

Section 3.2 gives the split rule twice: once as what it must achieve,
that no later character changes how the label reads, and once as how it
is tested, that the scanner has nothing open at that point. Those are
two different statements and the spec assumes they coincide.

They do on every row of that section's table, and they had better,
because the test is what runs and the property is what a writer relies
on. The direction that could fail is a construct whose reading depends
on what follows while the scanner considers nothing open. Smart quotes
looked like a candidate, since a lone `"` is a curly quote and a paired
one is a quotation, but djot pairs them like any other delimiter and the
opener is on the stack, so the test already refuses the split.

So this is an obligation rather than a question: state it, and either
prove it or find the construct that breaks it. It is the one place where
the block layer's decision rests on an inline-layer invariant, which is
also what makes it worth stating rather than assuming.

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
