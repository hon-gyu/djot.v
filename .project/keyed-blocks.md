---
ai-disclosure: ai-generated
---
# Keyed blocks

The constructor this file calls `Keyed` was renamed `Ext_keyed` on
2026-09-26, to mark it as an extension in the public API.

Status: **implemented**. 9.1 is closed: the split test was wrong for a
delimiter run against the colon, and `iscan_settled` is the repair.
Section 5 is in for every block it admits: fenced code and raw blocks,
fenced divs, and thematic breaks. `claimable` handles their opening
lines; `announces_end` keeps a fence or div claimed until its closer.
9.2 records the blank-safety refinement the div required. 9.3 settles
the HTML shape as a one-term description list carrying the `keyed`
class. `Inline.key_split` is the
split rule of 3.1 and the one-inline rule of 3.2, with every row of
section 3's three tables pinned as an `Example` beside it; `Ast.Keyed`
is the node, with arms in `Wf.v`, `Html.v` and `Document.v`; and the
parser produces one, through `Step.bkeyed`, `Step.open_text` and the
`PKey` state. Sections 3, 4, 5, 6 and every worked example of section 7 are
pinned as whole documents in `dev/check/Keyed.v`; 7.5 is
stated against `keyed_sublist_bconfig`, since it needs the sublist
setting as well as keys. `out_of_column_needs_the_setting` in that
file is what the parser does with keys off, and
`out_of_column_is_claimed` is the same document with them on. `Render.CKey` gives keys a canonical
two-line spelling and the existing `roundtrip_blocks` theorem covers
them. `test/roundtrip.exe --keyed` runs the extracted roundtrip over a separate keyed
pool; no external parser covers that pool.
This file stands on its own: it is the
definition of the construct, not a staging area, and it stays here once
the construct exists.

Prose first. Sections 0 to 7 define the syntax without naming a single
identifier in the development; everything that touches the code is
gathered in section 8, and section 9 is what is still undecided.

Prior art is oyster's `struct`, in `oyster/specification/oyster/`. It is
prior art, not something to conform to, and nothing below depends on having read it.

## 0. The idea

A colon is a binary connective. It takes **one inline** on the left and
a **block** on the right, and pairs them.

One inline, not a sequence of them: a run of text, or an emphasis, or a
link, or a verbatim span. A run of text is one element however long it
is, so most labels are just words. The restriction is deliberate and it
is the construct's main defence: a label that has to be one element
cannot run away with a sentence, so a colon deep inside a marked-up
paragraph can never quietly become a key, and a writer is pushed toward
names short enough to be names. 3.2 says where the boundary falls and
3.6 says what it declines.

```
label : block
```

The reading a writer should be able to hold in their head, and the thing
every rule below exists to protect:

> When I see a colon, I am one level deeper in the abstraction stack.
> When the block after it finishes, I am back where I was.

**A key changes the tree, not the text.** No line is reindented, no
container prefix is consumed, no column shifts. The only bytes a key
removes from the content are the connective colon and the whitespace
after it, and the inlines on either side read exactly as they would have
read with keys off. What moves is where those inlines sit in the tree.

That last clause is a claim, not a convention, and 9.1 is the obligation
to make it good: it is true because a split is only taken at a position
where nothing later in the line can change how the label reads.

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

One rule, asked once per line.

### 3.1 The split

A line is split at its first colon that is

- **unescaped**;
- **not preceded by whitespace**, so the colon sits against the label;
- **followed by a space or by the end of the line**, where a tab is not
  a space; and
- reached while the inline scanner has **nothing open and nothing
  undecided**: no verbatim run, no attribute brace, no bracket, no
  delimiter that a later character could still close, and no delimiter
  run still being spelled, whose role the byte after it would settle.
  The last clause is 9.1; `iscan_settled` is the test.

```
foo: bar
```

The label is `foo`, the value is `bar`, and the block is the paragraph
the value starts.

The value may be empty:

```
foo:
```

This is the same rule with nothing after the colon, so the block comes
from the following lines instead. The two spellings are one construct.
They differ only in where the block comes from, which is 3.3.

The colon has to be a real one by the test above rather than by
appearance, so `` a `b:` `` is not a key: its only colon is inside a
verbatim span.

**It needs no lookahead**, which is the part worth checking. Take
`` a `b:` ``. At the byte of the colon the scanner is inside a verbatim
run, and the question "will that run be closed?" never has to be
answered, because both answers give the same verdict. If a closing run
comes, the colon was inside the span. If none comes, djot runs the
verbatim to the end of the line, so the colon is inside the span anyway.
Either way it is not a connective, and the decision is available at the
colon itself.

That is the shape of the whole rule. Where the scanner is unsure at the
colon, the line is not a key, and the writer gets the paragraph they
would have got before keys existed. Declining is always safe; splitting
is what has to be justified.

The scanner already carries the open-construct bit, so the test is a
query at each candidate position, and one pass over the line answers it
at all of them. It is a scan, not a search with backtracking: the split
point is found in one pass and never revised.

**What "nothing open" buys.** Splitting at a colon throws the rest of
the line away as far as the label is concerned, so it may only happen
where throwing it away costs nothing: nothing later in the line may
change how the text before the colon reads. "Nothing open" delivers
that, and it is not a claim that the text before the colon is *valid* on
its own. Every string is valid inline content in djot, which has no
inline errors. `x{title="a` on a line of its own is fine, and reads as
the literal `x{title=`, a curly quote, and `a`. That is exactly why it
is not a split point: inside `x{title="a: b"}y: z` the same characters
read as the word `x` carrying a title, so splitting at the first colon
would silently give the label the other reading. The scan goes on to the
next colon instead.

The implication runs one way only. `_a: b` has an unmatched `_`, which
djot leaves as literal text, so splitting there would in fact have
changed nothing; the scanner declines anyway, because at the colon it
cannot yet know the `_` is unmatched. That conservatism is the price of
no lookahead and it is worth it. That the implication holds in the
direction that matters is 9.1, and it is the formal content of the
promise section 0 makes.

| #   | line                              | splits at       |
| --- | --------------------------------- | --------------- |
| 1   | `foo: bar`                        | the first colon |
| 2   | `` `a: b` is how you write it ``  | nowhere         |
| 3   | `` `code`: a description ``       | after the span  |
| 4   | `[see: here](x) is the reference` | nowhere         |
| 5   | `[see](x): the reference`         | after the link  |
| 6   | `foo{#my-foo}: bar`               | after the brace |
| 7   | `x{title="a: b"}y: z`             | after `y`       |
| 8   | `"foo: bar" and more`             | nowhere         |
| 9   | `"foo": bar`                      | after the quote |
| 10  | `_a: b_`                          | nowhere         |
| 11  | `foo : bar`                       | nowhere         |
| 12  | `a*: b*`                          | nowhere         |

Rows 2, 4, 8 and 10 have exactly one candidate colon and it arrives with
something open, so those lines have no split point at all. Row 12 is
9.1: the `*` is a delimiter run still being spelled, so at the colon it
is undecided rather than open, and settling it needs the byte the colon
occupies. Alone it would be the literal `a*`; in place it opens the
strong span that swallows the colon. Row 10 is the
one worth staring at: `_a: b_` is emphasis over `a: b`, and the label
`_a` would be the literal characters `_a`. Rows 8 and 9 are the same
construct open and closed, since a quotation mark pairs in djot like any
other delimiter. Row 11 is the adjacency rule, which exists so that the
spacing prose uses for a punctuating colon keeps it punctuation.

### 3.2 What the label may be: one inline

A split point is necessary and not sufficient. The text before the
colon has to be a single inline element.

The counts are not obvious from the source, because resolution merges
adjacent text and decayed punctuation merges with its neighbours:

| label source            | nodes | what they are                     | key? |
| ----------------------- | ----- | --------------------------------- | ---- |
| `foo`                   | 1     | a text run                        | yes  |
| `foo bar baz`           | 1     | still one text run                | yes  |
| `it's`                  | 1     | the apostrophe curls and merges   | yes  |
| `a -- b`                | 1     | the dash likewise                 | yes  |
| `foo\: bar`             | 1     | the escape leaves one run         | yes  |
| `` `code` ``            | 1     | a verbatim span                   | yes  |
| `[see](x)`              | 1     | a link                            | yes  |
| `"foo"`                 | 1     | a quotation                       | yes  |
| `*bold*`                | 1     | a strong span                     | yes  |
| `x{title="a"}`          | 1     | a text run carrying an attribute  | yes  |
| ``x`y` ``               | 2     | a text run and a verbatim span    | no   |
| `x{title="a: b"}y`      | 2     | two runs, only one with the title | no   |
| ``the `--flag` option`` | 3     | text, verbatim, text              | no   |

So a label is one thing: a phrase, however long and however much
punctuation it holds, or one marked-up element. What it may not be is a
phrase with markup embedded in it. An attribute brace is not a second
thing, since attributes ride on the element in front of them, which is
why `x{title="a"}` is a key and `x{title="a: b"}y` is not: the second
has a second run, and two runs carrying different attributes cannot
merge.

**Why one, and not any number.** The restriction is the point. A label
that has to be one element cannot run away with a sentence, so a colon
sitting deep inside a marked-up paragraph can never quietly become a
key. And a writer structuring knowledge with this syntax is pushed
toward names short enough to be names, which is the property that keeps
a keyed document tractable as data: every label is one element, not an
arbitrary run of prose. The lines it declines are the price, and 3.6
names them, because the boundary is not visible in the output.

The test costs no lookahead either. Nothing is open at the split point,
so everything before it is already resolved and already merged, and the
count is available right there. It is also monotone: once the label is
two elements no later colon can bring it back to one, because collapsing
two settled elements into one would take a construct opening before both
of them, and that would have made the earlier point unsettled. A line
whose label has gone to two elements is not a key, and the scan can stop
rather than looking further along.

**Attributes carry through.** A label is an inline like any other, so it
may be an emphasis, a link, a verbatim span, or a text run carrying an
attribute brace, and the attribute attaches inside the label exactly as
it would in a paragraph. In `foo{#my-foo}: bar` the id lands on the word
`foo`, because that is the element the brace follows. Note that it does not
identify the keyed node. To name the node, put the attribute on its
own line above:

```
{#my-foo}
foo: bar
```

### 3.3 What follows the colon

**The value is inline content, never block syntax.** What follows the
colon on the key line opens a paragraph, and is not classified as a line
of its own. So `foo: - bar` is `foo` over the paragraph `- bar`, not
over a list, and `foo: # h` is `foo` over the paragraph `# h`.

A list marker does the opposite with the rest of its line, and djot.js
confirms it: `- # foo` is a heading inside the item, `- > q` a
blockquote inside it. A key departs from that precedent deliberately.
The text on the key line is the key's *value*, and a writer who wants a
block writes it on the lines below, where it is read as a block like any
other.

**One key per line.** A line is split at most once. What follows the
colon opens a paragraph and is not read again as a key line, so
`foo: bar: baz` pairs `foo` with a paragraph whose text is `bar: baz`,
not a chain. That paragraph continues onto later lines like any other;
what it does not do is split a second time. `foo: bar:` is likewise
`foo` paired with a paragraph reading `bar:`, trailing colon and all.

Nesting is by line:

```
foo:
bar: baz
```

is `foo` over `bar` over `baz`, because line 2 is a fresh line and
gets its own split.

One colon per line, one level per line. The alternative, re-reading the
value as if it were a fresh line, is not harder to define, but it makes
a single prose sentence nest twice: `Note: see this: it matters` would
be two accidental levels rather than one. Splitting once bounds the
damage of the case below at one level.

**So the one-line form is not sugar for the two-line one.** The two
agree whenever the value is ordinary text, and part whenever it is
anything a line can mean:

| value      | on the key line   | on the line below       |
| ---------- | ----------------- | ----------------------- |
| `bar`      | `Para "bar"`      | `Para "bar"`            |
| `bar: baz` | `Para "bar: baz"` | `bar` over `Para "baz"` |
| `- bar`    | `Para "- bar"`    | a list                  |
| `# h`      | `Para "# h"`      | a heading               |
| ` ``` `    | `` Para "```" ``  | an open code fence      |
| `> q`      | `Para "> q"`      | a blockquote            |

Every row is the same fact: the one-line form is for values, the
two-line form is for blocks.

**Colons in ordinary prose are keyed.**

```
Note: this matters.
```

is a key named `Note`. That is the cost of the inline form and it is
accepted; a writer who means punctuation escapes it.

```
Note\: this matters.
```

### 3.4 Where a colon is not a connective

| #   | colon                               | reading                | why                               |
| --- | ----------------------------------- | ---------------------- | --------------------------------- |
| 1   | `foo\: bar`                         | literal text           | escaped                           |
| 2   | `` `a: b` ``                        | literal text           | inside an unclosed construct      |
| 3   | `http://x`                          | literal text           | not followed by a space           |
| 4   | `foo:<tab>bar`                      | literal text           | a tab is not a space              |
| 5   | `foo : bar`                         | literal text           | whitespace in front of it         |
| 6   | the second colon in `foo: bar: baz` | literal text           | the line is split once            |
| 7   | the second colon of `foo: bar:`     | literal text           | same, and it is the value's text  |
| 8   | `:::`                               | div opener             | the line is read as a div first   |
| 9   | `:` alone                           | plain paragraph        | the label would be empty          |
| 10  | the leading one of `: term`         | definition-list marker | initial, not final                |
| 11  | the one in `[see]: bar`             | reference definition   | the line is a definition first    |
| 12  | the one in `[^n]: text`             | footnote definition    | likewise                          |
| 13  | the one in `# foo:`                 | plain heading          | a key opens from a text line only |
| 14  | any colon inside a fence            | verbatim               | fences are not classified         |

`foo\: bar:` is therefore keyed, with label `foo: bar`: the escaped
colon is text and the final one is the connective.

Rows 11 and 12 are the harshest, because they are the two where the
writer gets no paragraph to look at. A line beginning with a bracketed
phrase and a colon is already a reference definition, and one beginning
with a caret label is already a footnote definition; both produce *no
output at all*, so a mistyped key of that shape disappears. The
consequence to know is that a bare bracketed phrase cannot be a label.
`[see](x): bar` is a key, because that is a link; `[see]: bar` is not.

Row 10 holds only while definition lists are on, since a leading `: `
is their marker. With them off the line is text and the colon is
declined by row 9 instead, the label being empty either way.

A line beginning with a brace is not a case here, although djot.js makes
it one. There an inline attribute with nothing in front of it to
decorate is dropped, so `{#i}: bar` is a paragraph holding `: bar` alone
and there is no label element for a split to take. We keep such a spec
as literal text, on purpose and for a reason that predates keys
(`djotjs-divergences.md`, 2026-08-15: dropping it would falsify
`parse_inline_line_nonempty`). So `{#i}: bar` is a key whose label is
the four literal characters `{#i}`, and `{#i}foo: bar` a key labelled
`{#i}foo` rather than `foo`.

This is worth knowing rather than worth fixing. A writer who meant to
identify the node wants the attribute on its own line above, as in 3.2;
a writer who meant the literal braces has them already.

The heading row is a decision rather than a consequence. Headings
already build document structure through sections, and a line that was
both a heading and a key would carry two nesting effects at once.

### 3.5 When the split happens

Once, when the line is classified, and never again.

A line is tested for a split exactly when it would otherwise open a
paragraph: it is text, nothing else has claimed it, and nothing is open
at that level. That is one moment in the line fold, and it is the same
moment at which a fence, a quote, a list marker or a table row would
have been recognised instead.

Three things follow, and they are most of what a writer needs to know.

**Continuation lines are never tested.** A paragraph is already open
when its second line arrives, so a colon there is text:

```
foo
bar: baz
```

is one paragraph. This is the reason a key can be read off the line that
starts a block rather than off the block as a whole, and it is why a key
directly under a paragraph needs a blank line in front of it.

**The test runs on what is left of the line.** Container prefixes come
off first, so inside a blockquote the split is looked for in `foo: bar`,
not in `> foo: bar`. Leading indentation is stripped the same way, which
is also what keeps a line's reading independent of how deep it sits.

**What the split produces is an index, not a tree.** The parser records
two pieces of source, the label's and the value's, and nothing more. The
label's inlines are built later, when the keyed node is constructed,
exactly as a paragraph's inlines are built when the paragraph closes. So
the scan at classification is used to find a byte offset and to answer
two yes/no questions; it builds nothing that is kept.

That is what makes retraction exact. When a key gets no block the state
still holds the line as it was written, so it becomes the paragraph it
would have been, colon and all, with no reconstruction and nothing to
get wrong. The decision at classification is never revised; the only
thing that can happen to it is being dropped whole.

The cost is that the line's bytes are scanned twice, once to find the
split and once when the label and value become nodes. It is a constant
factor, not a branching one.

### 3.6 Where a line does not read as it looks

The unintuitive cases, collected. Each one follows from a rule above and
from no special case, and each parses differently from what its shape
suggests. There are two kinds: a line that looks like a key and is
declined, and a line that is split somewhere other than where the eye
lands. Nothing in the output says which rule applied, which is the
reason to have the list at all.

| line                                  | what it is                 | why                                    |
| ------------------------------------- | -------------------------- | -------------------------------------- |
| `foo:bar`                             | a paragraph                | no space after the colon               |
| `foo:<tab>bar`                        | a paragraph                | a tab is not a space                   |
| `foo : bar`                           | a paragraph                | a space before the colon               |
| ``the `--flag` option: what it does`` | a paragraph                | the label is three elements            |
| `x{title="a: b"}y: z`                 | a paragraph                | the label is two runs                  |
| `[see]: bar`                          | nothing at all             | a reference definition                 |
| `{#i}foo: bar`                        | a key labelled `{#i}foo`   | a leading brace is literal text here   |
| `see http://x: it works`              | a key named `see http://x` | the second colon splits                |
| a key line under a paragraph          | more of the paragraph      | a key cannot interrupt one             |
| `> foo:` then an unprefixed block     | `Para "foo:"` in the quote | the quote ended first (5.1, 6.1)       |

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
The last four end on a line that belongs to whatever is outside. The
heading row is the one that depends on a setting, and 5.2 explains why
that keeps it out of the first group in practice.

**A line may end the key's block and go on to produce another.** A step
that closes a paragraph can emit a thematic break in the same breath:

```
foo:
bar
***
```

The key's block is `Para "bar"`; the break is not inside the key, it is
the next block at the enclosing level. The rule is that a key takes the
*first* block that comes out and nothing after it, which is forced by
the node holding a single block rather than a list of them.

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

The reason is 5.2's, one level up. The override is tolerable only
because it is *bounded*: the block it holds open announces its own end,
and the override ends with it. A quote has no such end. What ends a
quote is the absence of the prefix, so a key that dropped prefixes would
delete the very thing that says where the quote stops, and the override
would have nothing to last until. The same goes for a div's closing
fence.

Column is different in exactly that respect, and not because it is
somehow less binding: a claim about where a block *sits* leaves the
block's own ending intact. So inside a blockquote the key's block still
carries the prefix:

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
their own are fenced code, raw blocks, fenced divs and thematic breaks.
Those are the ones a key can pull out of column. Paragraphs, lists,
tables and blockquotes end by being interrupted, and the interrupting
line is the one the container outside needed to see.

Headings are not on that list, although section 4 says a heading ends on
its own line. That row is conditional: in djot a plain text line
continues a heading (`# h` then `more` is one heading, checked against
djot.js), so a heading announces its end only in a profile with
heading continuation switched off. Rather than make the override depend
on a second setting, headings are excluded outright; a key over a
heading has to indent it like any other block.

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
takes a list with nothing overridden. The second indents the fence into
the item the ordinary way. A key takes any block at all; only the
unindented spelling inside a container asks anything of the block.

## 6. Retraction

**To retract is to become the paragraph the key line would have been
with keys off.** The key's state is discarded, the colon goes back to
being literal text, and the *key line alone* becomes a paragraph, at the
place and in the container the key line sat in. Nothing that arrived
after it is part of that paragraph.

```
foo:

bar
```

```
Para "foo:"
Para "bar"
```

Nothing is undone by this. A key produces no node until it closes, so
retraction discards a state rather than revising a result. Block
attributes and table captions already work this way: both wait, and both
turn back into ordinary text if what they were waiting for never comes.
And because the state kept the line as written (3.5), the paragraph is
the original bytes rather than something reassembled.

### 6.1 When it happens

A key retracts when it is ended while it has **nothing open under it**.
That is the whole test, and it is deliberately a question about the
key's own state rather than about what the document goes on to do.

| input                            | outcome                                    |
| -------------------------------- | ------------------------------------------ |
| `foo:` / blank / `bar`           | retract, then `Para "bar"`                 |
| `foo:` alone at end of input     | retract                                    |
| `- foo:` / `- bar`               | retract, two items (5.2)                   |
| `> foo:` / a line with no `>`    | quote ends, retract inside it              |
| `:::` / `foo:` / `:::`           | div closes, retract inside it              |
| `foo:` / `- a` / blank / `- b`   | **no** retraction, the blank is the list's |
| `foo:` / fence / blank inside it | **no** retraction, the blank is content    |

The last two rows are why the test cannot be "a blank retracts". A blank
line reaches the key only when nothing under the key has claimed it
first, and every container that survives a blank claims it.

The list case behaves as it does today: `- foo:` then a blank then
`- bar` is a loose two-item list whose first item is `Para "foo:"`, and
the blank is what makes it loose.

### 6.2 The corner: started, but producing nothing

A block attribute line starts something without producing a block:

```
foo:
{#i}

bar
```

At the blank, the key has an attribute spec open, so it does not
retract, and it goes on to take `Para "bar"` from below the blank. That
contradicts the first row of the table above, and it is accepted rather
than repaired: the alternative is a notion of "started but may still
vanish" that nothing else in the parser has, for a two-line shape nobody
writes on purpose. Revisit it if it ever shows up in real documents.

The same corner at end of input has to go the other way, and does:

```
foo:
{#i}
```

A lone attribute line contributes no block at all (checked against
djot.js: `{#i}` on its own renders nothing). So the key ends with no
block and retracts, giving `Para "foo:"` and nothing else. The `{#i}`
line vanishes exactly as it does today. Retraction reproduces the key
line, never the lines that followed it.

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
`foo` paired with the paragraph `bar: baz`, by the one-key-per-line rule in
3.3: a level costs a line.

## 8. What this costs the development

The one section that names things in the code.

**A new block constructor**, `Keyed`, holding one inline label and one
`node block`, not a list of them. Section 4 is the reason: the scope is
exactly one block, so `wf_block` needs no singleton side condition and
the "first block only" rule of section 4 is forced rather than checked.
`BlockQuote`, the nearest existing container, is mentioned 85 times
across eight files; the ones that will want a real arm rather than a
copied one are `Ast.v`'s induction principle, `Wf.v`, `Html.v`,
`Render.v`, `Uniformity.v` and `Document.v`, the last being the file the
site and rename model has to traverse through.

**A new parser state**. It sits in the container stack and, like `PDiv`,
eats no prefix and shifts no column, so it records no column either and
`step_fuel_shift` and `step_fuel_pad` cost nothing on its own account.
But its *continuation rule* is `PPend`'s, not `PDiv`'s: a div closes
when a line says so, a key closes when the state under it emits a block,
and `pend_result` is the only existing shape for that. Read the new arm
off `PPend` and the state's column-freedom off `PDiv`.

There are 25 explicit `destruct` sites over the state type and 27
mentions of `PDiv`. Twelve functions recurse over the state and each
needs an arm: `finish`, `lazy_ok`, `feed_lazy`, `pstate_depth`,
`blank_absorbed`, `blank_safe`, `pad_safe`, `is_idle`, `in_fence`,
`div_closer`, `pad_state` and `fence_cols_ok`. Two of those have
behaviour attached and are not mechanical:

- `in_fence` must see through a key, or a `:::` line inside a code block
  inside a key would close an enclosing div.
- `div_closer` must see through a key, or `- foo:` / `:::` / `bar` /
  `:::` / `- baz` gets its tightness wrong: the div's closing line is
  what arms the enclosing list.

`is_idle` is what 6.1's retraction test asks, which is why the rule is
stated as "nothing open under it" rather than as a claim about the
document.

**The split test reaches into the inline layer, and that is affordable.**
It needs the scanner's opener state and the resolved node count, neither
of which `classify` can see, since `Line.v` sits below `Inline.v`. It
does not have to. The test belongs in `open_kind`'s text arm in
`Step.v`, which already imports `Inline` and, more to the point, already
sits inside `Section WithTable`: the delimiter table is a section
variable there, so the argument stays implicit and no call site moves.

That placement is what 3.3's value rule buys. `open_kind` gets neither
the offset nor a way to re-enter the line parser, so a key whose value
were classified could not live there: it would join the six kinds
`direct_open` excludes and would need a column, a descent and a fuel
step, like `open_list`. A value that is always a paragraph opens with
`([], PKey lbl (PPara [value]))` and needs none of it.

Two smaller costs remain. The test has to be stable under a leading run
of spaces or `step_fuel_pad` fails, and normalising the line first is
enough -- `open_kind`'s arm takes the *already normalised* line
(`open_text (drop_leading_ws l)`) so that the rewrite every pad proof
already performs is the whole of the argument. And every concrete
`Example` that parses a text line scans it twice, a constant factor
rather than a branching one: a clean build went from 99s to 105s.

**What the placement costs that this section did not say.** Putting the
test in `open_kind` gives `open_line` a `dtable` parameter, because
`key_label_ok` resolves inlines. Nine statements in `Invariants.v`
spell `@open_line K` explicitly and every one of them became
`@open_line T K`; the change is a `sed` and no proof moved, but the
*spelling* of a theorem is not something a "which proofs use the
structure" census counts.

**And the first-line condition cannot be deferred.** `keyless` was
meant to arrive with the renderer, but `parse_lines_text` is where a
text line opens a paragraph and it needs the hypothesis on the spot.
Its users are `parse_lines_para_seed`, `parse_lines_para_run` and
`parse_lines_para_run_blank`, and those terminate in exactly two
places: `wrap_neutral` (which gains `bkeyed = false` as its third
conjunct, as this section predicted) and `para_ok`. So the parser half
and `para_ok`'s new conjunct are one step, not two.

**The label test depends on the merge pass.** Whether a label is one
inline or two is a fact about the *resolved* inline list, so it turns on
resolution merging adjacent text and on decayed punctuation merging with
its neighbours. `it's` and `foo\: bar` are keys because of that pass and
would not be without it. This is a coupling to record rather than a
problem: the pass is what makes "one text run is one thing" true, and it
is why the rule can be stated on node counts at all. It does mean the
rule is about our normalised inline list and not about djot.js's, which
does not merge these and would count `it's` as three.

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
rather than the inline one, and the block at the key's own column with
no blank between. The canonical constructor is then a wrapper of exactly
the shape `CId` has, one source line in front of an existing block, and
it inherits that constructor's arms in `ends_clist`, `is_clist` and the
pair predicates.

**And a rendering obligation that is wider than the label.** With keys
on, any first line carrying a split point comes back as a key, so it is
not only labels that are at risk:

- A label containing a splitting colon breaks in place. `Keyed "Note:
  this" b` renders `Note: this:`, which splits at the *first* colon and
  returns `Keyed "Note"` over `Para "this:"`. Trailing colons are the
  obvious case but not the only one.
- Every canonical paragraph is at risk too, not just those under a key.
  `Para "Note: this matters"` renders as itself and reparses as a key.
  `para_ok` asks `is_text` of a paragraph's first line so that reparsing
  opens a paragraph there; with keys on, `is_text` stops being enough
  and a first-line condition has to join it, next to the existing
  `negb (bcuts l)` conjunct.

The decision is to **escape rather than exclude**. `\:` reads as a plain
colon, so escaping preserves the content exactly, where excluding would
throw a large share of ordinary paragraphs out of the tested fragment
for no gain. Only the first line of a block needs it, since 3.5 says
continuation lines are never tested.

**Implemented:** `Inline.needs_escape` claims the colon, so the shared
inline spelling escapes it on every line, with either block setting.
This keeps the renderer independent of the block configuration and
protects future canonical labels as well as paragraphs. The extra
escapes on continuation lines and with keys off decode to the same
text. `dev/check/Keyed.v` pins acceptance and roundtrip for literal-colon
paragraphs at top level, inside quotes and lists, and under an explicit
id; it also pins an escaped label followed by the real connective.
`CKey` carries one `cinline` and one child block. Its label check asks
that the rendered line classify as text, split at the appended colon,
and retain the label's trailing whitespace when parsed. Empty labels,
trailing whitespace, and spellings that take precedence as another
block (for example a footnote reference followed by a colon) are outside
the canonical fragment.

**One more obligation than `CId`.** A blank while the key waits for a
child retracts it. `key_content_ok` checks the child's prefix until its
first emission, or until the prefix ends in a state that can carry the
key through any suffix. It admits pending attributes around a live
child, so both `CKey label (CId id child)` and `CId id (CKey label child)`
round-trip. The proof reuses the pending-attribute preservation lemma;
no existing theorem statement gains a hypothesis. Destination traversal
visits both the label and the child, and explicit-id collection visits
the child. List and table endings remain visible through the wrapper.

**djot.js stops covering this.** djot.js has no keyed construct, so
every keyed document is a divergence by construction and the
differential harness cannot adjudicate one. What is left is the
extracted roundtrip sweep and the generated corpus against our own
parser. That is a real reduction in what the project's usual safety net
covers, and worth knowing before the construct grows.

**Minor.** `def_split` takes an item's leading paragraph as a definition
list term, so an item whose first block is a `Keyed` has no term.

**Section 5, and what it actually cost.** The worry here was that an
item holding a block claimed out of column renders some lines
unindented, which would take the item out of `pad_state`'s reach and
through `step_fuel_pad`. That never came due: both spellings denote the
same tree, so `cb_lines` keeps indenting and `ListUniformity.v`'s
rendering side is untouched. What it cost instead was a weakened descent
test in `step`, one conjunct on ten close-side statements, one
hypothesis through four lemmas in the item chain, and two inductions
about the state a blank leaves behind. 9.2 has the table and the one
state that had to be excluded to make the second induction true.

## 9. Questions resolved during implementation

### 9.1 Is "nothing open" enough, on every construct?

No, as first implemented. Found by counterexample and fixed.

The rule states a test, "nothing open at the colon", and separately what
the test is for, "no later character changes how the label reads". The
test has to imply the property. It does not have to be implied by it,
and deliberately is not: `_a: b` is declined although splitting it would
have been harmless.

Stated: for every line with `key_split l = Some (lbl, v)`, reading `lbl`
alone gives the same element that reading `l` gives at that position.
`key_label_ok` forces the label to one element, so this is one
comparison.

It was false for a delimiter run against the colon. `a*: b*` split with
label `a*`, which alone is one text run; in place the line reads as `a`
followed by a strong span over `: b`, so the `*` opened and took the
colon. The keys-off and keys-on readings disagreed about the text, not
only the tree. Every delimiter did it: `*`, `_`, `^`, `~` and `"`.

The cause was `iscan_closed`, which calls `iresolve` first. `iresolve`
is the end-of-line disposition and settles a pending delimiter run as
literal text. A byte following the run makes it an opener instead,
because the opening test in `idelim_done` consults that byte and
`iresolve` passes `None`. So `iscan_closed` answers "would everything be
closed if the line ended here", which is what `ibreak_closed` wants, and
the split needs "is anything waiting on what comes next".

The fix is `iscan_settled c st`: resolve with `c` known to follow, then
ask the same question. `iscan_closed` keeps its meaning and its eleven
users, since the body moved to `iclosed_at` and both predicates call it.
Only `IDelim` answers differently, and only about opening, so a run that
closes is unaffected and row 9 of 3.1's table still splits. Nothing else
in 3.1 or 3.2 moved and no sweep changed.

Only canonical labels escape the delimiter, so no canonical document
reached the gap and the roundtrip fragment never saw it. It was
reachable only from hand-written source, where neither the corpus nor
the generated pool looks, because djot.js has no keyed construct to
compare against.

The two candidates this section predicted are both clean. Smart quotes
pair like every other delimiter and the opener is on the stack, so the
test refused them already. An attribute brace that decorates nothing is
dropped and its neighbours merge, so `a {#i}b: c` resolves to the single
run `a b`; 3.2's monotonicity argument is stated for merging and has to
cover deletion as well. Restated: both operations act on the resolved
list at or after the point in question, so neither can change an element
already settled and counted.

### 9.2 The cost of claiming out of column

Paid, for fences, thematic breaks and fenced divs.

The estimate that mattered was not the one this section first made. Two
things it got wrong, both found by building the change:

**The canonical spelling never had to move.** Section 8 priced the
override off the rendering -- an item holding a claimed block renders
some lines unindented, which takes it out of `pad_state`'s reach. That
is owed only if the unindented spelling becomes canonical, and it need
not: both spellings denote the same tree, so `cb_lines` keeps indenting
and `list_uniformity` is untouched. Section 5 adds a spelling, not a
document.

**The test cannot read the state alone.** Written as "is a key holding
a block that announces its own end" the override is inert, because the
fence line arrives while the key is still *waiting* and its block is not
open; the block can only be open once the line has been taken, which is
what the test decides. `key_claims` reads the arriving line as well: a
key below is waiting and the line opens a block whose end is announced,
or a key below is already holding one. `is_idle` is the waiting test,
which is the key's own retraction condition (6.1) -- the same condition
that says the key may still claim says a blank retracts it, and that is
what makes the override end with a blank.

What it cost, in the end:

| where | what |
| --- | --- |
| `Step.v` | the test, three pad lemmas, `key_claims_not_claimable` |
| `Step.v`, `Wf.v` | 20 `destruct` sites, mechanical once the test is named |
| `Step.v` | 10 close-side statements gain the test as their hypothesis; the one descend-side statement keeps its column hypothesis and derives the weaker test |
| `ListUniformity.v` | one hypothesis through four lemmas, and two new inductions |

The two inductions are the discharge. `step_blank_key_claims` says no
key admitted by `blank_safe` is left able to claim after a blank, which
is what `parse_list_close` and the item chain need.
`step_blank_inner_settled` is what its `PKey` case needs: a block which
produced nothing on a blank kept its container and, unless it already
held an announced-end block, did not acquire one. `parse_list_close`'s
*statement* did not change: the override is ruled out inside the proof.
Where the arriving line is a sibling marker the discharge is simpler
still -- a marker opens no announced-end block, so
`key_claims_not_claimable` settles it.

**One state had to be excluded to make that true.** `blank_safe`'s
`PPend` arm now also asks that what is under the pending attribute is
not idle. A settled attribute with nothing under it yet is closed in
`blank_safe`'s own sense -- a blank drops it -- but the drop leaves an
idle state, and a key above would still be waiting after a blank that 6
says retracts it. No run produces the shape: the line that settles an
attribute is also the line that starts the block it decorates. The
sweeps are unchanged, which is the evidence that no document was lost.

**The thematic break is the direct case.** `claimable KThematic` hands
the line to a waiting key, and the block it emits closes the key in that
same step. There is no live state and therefore no blank-line
obligation.

**The fenced div is in, and the old falsifier chose the boundary.** A
plain `PDiv` remains `blank_safe`: a blank advances its contents while
the div stays open, and the ordinary finish equation still holds. A
`PKey` holding that div is different, because it still owns every line
through the closing `:::`. Its `blank_safe` arm now additionally rejects
an `announces_end` child. `step_blank_inner_settled` carries the matching
precondition, so the list-close proof excludes only the transient keyed
state rather than excluding divs generally.

`div_out_of_column_is_claimed` pins the whole transition: text after a
blank remains inside the keyed div, its closing fence arms the outer
list's loose flag, and the following marker resumes that same list.
`key_over_div_is_not_blank_safe` pins the proof boundary directly.

### 9.3 How a keyed node renders

**Answered: a one-term description list carrying a
class.** `Keyed [Str "foo"] (Para "bar")` renders

```html
<dl class="keyed">
<dt>foo</dt>
<dd>
<p>bar</p>
</dd>
</dl>
```

There is no djot.js image and no HTML precedent, so this is a choice
rather than a finding. The description-list vocabulary says roughly the
right thing and keeps the label as inline content, which the third
candidate could not: a label is an inline, and an attribute value is a
string, so a div naming the key in an attribute would lose a label's
markup. A section with a heading says something about document structure
that is probably too strong. The class is what keeps a keyed node and a
one-term definition list from rendering identically.

`render_keyed_description_list` in `Html.v` pins the choice. It is an
output contract rather than a djot.js finding: changing it later would be
a deliberate presentation change, not a parser correction.
