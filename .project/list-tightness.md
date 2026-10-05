---
ai-disclosure: ai-generated
author: anthropic/claude-opus-5-5
---
# List tightness: the cases and where each stands

Every tightness case decided or found so far, in one place.  The entries
in `djotjs-divergences.md` are the history, in the order things were
found; several of them say "closed" or "fixed" for a choice that was made
by an agent and is still open to revision.  This file says which is
which.

The djot.js and our outputs below were run again on 2026-10-05, djot.js
at `d7c3904`.  What djot.lua and djoths give, and what was
said upstream, is taken from the log and was not checked again.  "Tight"
and "loose" are about the outermost list.

## The rule

The syntax reference:

> A list is classed as *tight* if it does not contain blank lines between
> items, or between blocks inside an item.  Blank lines at the start or
> end of a list do not count against tightness.

Our reading, as `Tightness.v` states it (`separates`,
`separates_after`): a list is loose exactly when a blank lies between
two of its items, or between two of one item's own blocks, with three
exceptions.

1. A blank directly before a nested list inside an item.
2. A blank directly after a nested list ends.
3. A blank inside a nested block (a div, a code block, a footnote, a
   table before its caption, a nested list's own items), which counts
   only for that block.

Exceptions 1 and 2 are the reference's "start or end of a list" applied
to a nested list.

## Proposal: a definition for the syntax reference

Proposed 2026-10-05.  It uses only terms the reference already has: a
list item "consists of" lines, a block left open "ends with ... the
containing block", and a list "contains" blank lines.  What the reference
leaves out is whether blank lines after an item's last line are part of
the item; the change to the List item section says they are not.

It decides the first two shapes of C1 (below) loose, C2 loose, D1 loose,
the open code block in group A loose, and an attribute line before a
nested list (jgm/djot issue #200) tight.

### Why the reference needs changing

The current text:

> A list is classed as *tight* if it does not contain blank lines
> between items, or between blocks inside an item.  Blank lines at the
> start or end of a list do not count against tightness.

It leaves three questions open, and on each the implementations, or
djot.js and the djot author, give different answers.  The djot.js
results below were checked on 2026-10-05 at `d7c3904`; the others are
from `djotjs-divergences.md`.

**1. Where does a list item end?**  The reference says an item consists
of a marker "followed by one or more lines, indented relative to the
list marker".  A blank line has no indentation, so it does not say
whether blank lines after the item's last line are part of the item.
It matters when the item leaves a block open, since that block "ends
with ... the containing block":

```
- :::

- b
```

If the blank is part of the first item, it is inside the open div and
the list is tight.  If not, it lies between two items and the list is
loose.  djot.js and djoths say tight; djot.lua says loose.  With a code
block in place of the div, the same question decides the AST as well:
djot.js keeps the blank as a line of code (`text="\n"`) and calls the
list tight.

**2. Which list does "start or end of a list" protect?**  A list starts
with a marker line, so it cannot contain a blank before its first item;
"start" only has a meaning for a nested list, and the reference's
example is one (a blank before `  - sub` inside an item).  The text does
not say how far the exemption reaches.  The djot author's ruling on

```
- a

- - b
```

is that it is loose: the blank is between two outer items, not at the
start of the inner list (djot.js says tight, which the author called a
bug).  The mirror image at the end of a nested list

```
- a

  - b

- c
```

is tight in djot.js, and its tests expect that (`lists.test` 242 and
308).  The reference gives no way to tell whether "end of a list" means
something different from "start".

**3. Is a block attribute part of the block?**  The reference says what
an attribute attaches to, not whether its line counts as part of that
block.  So it cannot say whether the blank here is "at the start" of the
nested list:

```
- a

  {.x}
  - b
- c
```

djot.js says loose; the djot author says it should be tight
(jgm/djot issue #200).

The proposal answers each: an item ends with its last nonblank line
(1); the exemption covers a blank inside an item next to a nested list,
and never a blank between items (2); an attribute attached to a block
counts as part of it (3).

### The change

The change to `doc/syntax.md` in the djot repository:

````diff
--- a/doc/syntax.md
+++ b/doc/syntax.md
@@ -441,6 +441,10 @@ example:
 
      > containing a block quote
 
+A list item ends with its last nonblank line; blank lines after it are
+not part of the item. A block left open inside the item, such as a code
+block or a div with no closing fence, ends there too.
+
 Indentation may be “lazily” omitted on paragraph lines following the
 first line of a paragraph:
 
@@ -543,8 +547,11 @@ its first item. The numbers of subsequent items are irrelevant.
     8) six
 
 A list is classed as *tight* if it does not contain blank lines between
-items, or between blocks inside an item. Blank lines at the start or end
-of a list do not count against tightness.
+items, or between blocks inside an item. A blank line inside an item
+does not count if it comes directly before or directly after a list
+nested in that item; block attributes attached to the nested list count
+as part of it. Nor does a blank line inside a block nested in an item,
+such as a div, a code block or a nested list.
 
     - one
     - two
@@ -560,6 +567,87 @@ less space between items.
 
     - two
 
+A blank line between two paragraphs of an item also makes the list
+loose:
+
+    - one
+
+      more
+    - two
+
+A blank line directly after a nested list does not, when the item
+continues after it:
+
+    - one
+    - two
+
+      - sub
+      - sub
+
+      more
+
+Attributes attached to the nested list are part of it, so the blank
+line here is still directly before the nested list, and the list is
+tight:
+
+    - one
+
+      {.note}
+      - sub
+    - two
+
+This list is loose. No line of the first item follows the blank line,
+so the item does not contain it, and it lies between two items:
+
+    - one
+
+      - sub
+
+    - two
+
+So is this one, for the same reason. The blank line comes before the
+second item, not inside it:
+
+    - one
+
+    - - sub
+
+This list is tight. The blank line is inside the code block, which
+continues up to its closing fence:
+
+    - ```
+      a
+
+      b
+      ```
+    - two
+
+This list is loose. No line of the first item follows the blank line,
+so the item ends with the line `code`, and the code block, which has no
+closing fence, ends with it. The blank line lies between two items, and
+the code block contains only `code`:
+
+    - ```
+      code
+
+    - two
+
+This list is tight. A caption is part of the table it follows, so the
+blank line is inside the table:
+
+    - | a |
+
+      ^ caption
+    - two
+
+This list is tight. The last item ends with its line `- two`, and the
+list with it, so the list does not contain the blank line:
+
+    - one
+    - two
+
+    A paragraph.
+
 
 ### Code block
 
@@ -741,6 +829,10 @@ by the contents of the note, indented to any column beyond the column in
 which the reference starts. The contents of the note are parsed as
 block-level content.
 
+A footnote ends with its last nonblank line; blank lines after it are
+not part of the footnote. A block left open inside the footnote, such as
+a code block or a div with no closing fence, ends there too.
+
     Here's the reference.[^foo]
 
     [^foo]: This is a note
````

Notes, not for the reference:

- "Blank lines at the start or end of a list do not count against
  tightness" is gone.  For the outer list it follows from where an item
  ends; for a nested list it is the sentence on blank lines directly
  before or after one.
- Only list items and footnotes change where they end.  At the end of
  the document, or in a block quote (whose `>` marks a line as the
  quote's), a blank line after an unclosed code block is still code.
- D1 has no example in the reference, because an attribute that
  attaches to nothing is a corner case that would confuse readers more
  than it helps.  The input:

  ```
  - - x
    {.a}

    para
  - b
  ```

  The blank is inside the first item, since `para` is a line of that
  item and comes after it.  `{.a}` is followed by a blank instead of a
  block, so it is attached to nothing and is not part of the nested
  list.  The line before the blank is therefore not the nested list's
  last line, the exception does not apply, and the blank lies between
  two blocks of the item: loose.
- The attribute example is jgm/djot issue #200, where djot.js and our parser
  both give loose today.

## Status at a glance

| Group | Cases | Status |
| --- | --- | --- |
| A | the basic ones | agreed with djot.js, not in question |
| B | 4 shapes where we differ from djot.js on purpose | decided by an agent from the reference; B1 confirmed upstream, B2 to B4 not |
| C | 2 shapes the reference does not decide | provisional |
| D | 2 shapes where our parser was inconsistent | D1 open, needs a decision; D2 fixed |

## A. Agreed, not in question

Both parsers give the same answer and the reference is clear.

A blank between items: loose.

```
- a

- b
```

A blank between two blocks of an item: loose.  The same with a quote, a
reference definition or a table as the first block.

```
- a

  b
```

A blank before a nested list inside an item: tight (exception 1; it is
the reference's own `- two` / blank / `  - sub` example).

```
- a

  - b
```

A blank inside a div that continues after it: tight (exception 3).

```
- :::
  x

  y
  :::
```

A blank inside an open code block: tight.  The blank is a line of the
code.

````
- ```

- b
````

A blank inside a footnote, when the next line is indented into the
footnote: tight.

```
- [^n]: a

      b
- c
```

A blank inside a definition list nested in an item: tight.

```
- : t

    d
- x
```

## B. We differ from djot.js on purpose

Each was decided by reading the reference.  The log marks all four
"closed", but only B1 has the djot author's agreement.

### B1. A blank before an item that starts with a nested list, or before an empty last item

```
- a

- - b
```

```
- a

-
```

- djot.js: tight, both.
- Ours: loose, both.
- Why: the blank is between two items.  It is not at the start of the
  inner list, which begins after the `- ` on the next line.
- Standing: the djot author called this a bug upstream, and djot.lua
  gives the loose reading.  The firmest of the four.
- Pinned: `list_blank_before_nested_list_item`,
  `list_blank_before_empty_last_item`.

### B2. A div's closing fence

```
- :::
  a
  :::
- c
```

- djot.js: loose.
- Ours: tight.
- Why: no line of the input is blank.  djot.js tests for a blank after
  the closing fence has been consumed, so the fence counts as one.
- Standing: reported upstream; no answer recorded here.  We first
  matched djot.js (2026-08-22) and reversed it (2026-09-29).
- Pinned: `list_div_closer_not_blank`.

### B3. A blank after a footnote in an item

```
- [^n]: a

  b
```

```
- [^n]: a

- c
```

- djot.js: tight, both.
- Ours: loose, both.
- Why: the blank is between two blocks of the item (first), or between
  items (second).  A reference definition in the same place loosens in
  both parsers, and the reference does not treat the two differently.
  djot.js drops the blank because the footnote is a third container
  level and it looks only two levels up.
- Standing: an agent's verdict.  Not reported upstream.
- Pinned: `list_blank_after_footnote_in_item`,
  `list_blank_after_footnote_between_items`.

### B4. A blank before a table's caption

```
- | a |

  ^ cap
- c
```

- djot.js: loose.
- Ours: tight.
- Why: the reference says a caption may follow the table "directly ...
  or there can be an intervening blank line", so the blank is inside
  the table.
- Standing: an agent's verdict.  Not reported upstream.
- Pinned: `list_blank_before_caption`, with `list_blank_after_table`
  for the loose neighbour (a paragraph in place of the caption).

## C. The reference does not decide; our answer is provisional

### C1. A blank directly after a nested list ends

```
- - b

- c
```

```
- a

  - b

- c
```

```
- - a

  b
```

- djot.js: tight, all three.
- Ours: tight, all three.
- The question: the blank ends the nested list, and it also lies
  between two items (first two) or two blocks (third) of the outer
  list.  The reference exempts blanks "at the start or end of a list"
  and does not say whether that also clears the outer list.
- For tight: djot.js's own tests expect it (`lists.test` 242 and 308).
- For loose: it would make the two ends symmetric.  At the start of a
  nested list the djot author ruled that a blank between outer items
  does loosen (B1).  The loose reading is implemented on branch
  `hy/blank-after-nested-list`; it passes every check of ours and fails
  those two djot.js tests.
- Pinned: `Generate.nested_list_end_blank_tight`.

Every case in D1 rests on this exemption, so C1 is worth deciding first.

### C2. A blank after an item that leaves a div open

```
- :::

- b
```

```
- :::
  d

- c
```

```
- [^1]: :::

- b
```

- djot.js and djoths: tight.
- djot.lua: loose.
- Ours: loose (changed 2026-09-30; before that, tight).
- The question: an unclosed div ends "with the end of the document or
  containing block".  Does the item end before the trailing blank or
  after it?
- For loose: the blank adds nothing to the div (the tree is the same
  without it), so the item ends at its last nonblank line, as an item
  with a closed div does, and the blank is between items.
- For tight: the div is still open when the blank arrives, and a blank
  inside a div that continues is the div's own (group A).
- The log entry says "provisional, to be revisited".
- Pinned: `list_blank_after_open_div`, `list_blank_in_open_code`.

## D. Open: our parser is inconsistent

### D1. A block attribute line between a nested list and a blank

Found 2026-10-05.  The attribute line attaches to nothing, so it leaves
no block.

One blank, then a paragraph:

```
- - x
  {.a}

  para
- b
```

- djot.js: loose.  Ours: tight.

Two blanks, then a paragraph:

```
- - x
  {.a}


  para
- b
```

- djot.js: loose.  Ours: loose.

The same pair with the next item in place of the paragraph:

```
- - x
  {.a}

- b
```

- djot.js: loose.  Ours: tight.

```
- - x
  {.a}


- b
```

- djot.js: loose.  Ours: loose.

A spec over two lines behaves as the one-line spec does:

```
- - x
  {.a
   .b}

  para
- b
```

- djot.js: loose.  Ours: tight.

For comparison, without the attribute line both are tight with one blank
or two (C1), and with the attribute line after the blank both are tight:

```
- - x

  {.a}
  para
- b
```

What is wrong on our side: the answer changes with the number of blanks.
The first blank arrives while the spec is still open and is swallowed.
It finishes the spec, the attributes are dropped, and the item is idle.
A second blank then meets an idle item and is counted.

What the rule in `Tightness.v` says: tight for all five, since the lines
before the blank parse to the nested list alone and exception 2 applies.
So on the two-blank inputs the parser loosens where the rule counts no
blank.  This is why `item_loose_separates` needs `run_safe` (no
attribute spec open at a line boundary): without it,
`["- x"; "{.a}"; ""; ""; "para"]` is a counterexample.

The choice:

- **Loose for all five, as djot.js.**  The nested list ended at the
  `{.a}` line, so the blank is not at the list's end; it lies between
  two blocks of the item.  The parser counts a blank that meets a
  finished spec.  The rule's exception 2 has to ask about the line
  before the blank, because the parse cannot see a dropped spec.
- **Tight for all five, as the rule now reads.**  A spec that attaches
  to nothing is no block, so the blank is still directly after the
  list.  The parser remembers, after dropping a spec, that a list just
  ended.  The rule is unchanged, and we differ from djot.js on all
  five.

If C1 is changed to loose, exception 2 goes away and this case goes with
it: all five are loose and only the parser's swallowed first blank needs
fixing.

### D2. A keyed block holding an unclosed div, inside a footnote (fixed 2026-10-05)

Extension only (keyed blocks on); djot.js has nothing to compare.

```
- [^1]: k:
    :::
    a

  x
```

Before the fix:

- Parse: a footnote, then the paragraph `x`, with the blank between
  them.
- The rule: loose.  The parser: tight.

The cause was not in the tightness scan.  A key whose block is a div or
a code block keeps every line until the closing fence, whatever its
column; a list item hands such a line down (`list_takes`).  A footnote
did not: it ended at `x`, which is not indented into it, and the div
ended with it.  So the list was told the key held the blank, and the
footnote then let the line go.

Now a footnote hands a line a key claims to its contents, as an item
does (`foot_takes` in `Step.v`).  `x` is a line of the div, the blank is
inside the div, and the item is one footnote: tight, by the parser and
by the rule.  The same input without the key is unchanged (C2): the
footnote ends at `x` and the item is loose.

Cost: the footnote theorems that say which line ends a note
(`footnote_content_uniformity_tail` and the four built on it) now ask
that the note does not take the line (`foot_takes ... = false`) where
they asked that it is not indented past the opener.  With keyed blocks
off the two are the same.  Pinned by
`out_of_column_is_claimed_in_a_footnote` in `dev/check/Keyed.v`.

This does not depend on C2.

## Decisions wanted, in the order they depend on each other

1. C1: does a blank directly after a nested list loosen the outer list?
2. C2: does an item end before or after a trailing blank when it leaves
   a div open?
3. D1, given 1: loose or tight when an attribute line sits between the
   list and the blank.
4. B2 to B4: keep each against djot.js, or wait for upstream.

## Where it lives

- Parser: `blank_absorbed`, `blank_held`, `keeps_line`, `list_content`
  and `list_next` in `Step.v`.
- The scan the renderer and the uniformity theorems use: `lines_loose`,
  `item_loose`, `seps_loosen`, `list_spacing_of` in `ListUniformity.v`.
- The rule and its proofs: `Tightness.v`; plan and proof notes in
  `260929.plan.list-tightness.md`.
- Pinned examples: `dev/check/Reference.v`, the prose part's "List"
  section.
