(* ai-disclosure: autonomous *)

(* Concrete `parse_blocks` / `parse_lines` regressions for the block
   parser: one closed document per construct, each decided by
   `reflexivity`.  Nothing requires this file, so a proof about `step`
   never has these in scope.

   Concrete evaluation here is `reflexivity`, never bare `cbn`: see the
   build-time note in `.project/project-engineering-lessons.md`. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Line Ast Attributes Parser Reparse.
Import ListNotations.

Local Open Scope string_scope.

(*
Sanity checks
=============
*)

Example located_lines_keep_their_piece_index :
  pend_state (snd (cut loc_step ["a"; "b"] fresh))
  = PPara [(1, "b"); (0, "a")].
Proof. reflexivity. Qed.

Example parse_two_paras :
  parse_blocks "hi
there

bye" =
  [ mk (Para [mk (Str "hi"); mk SoftBreak; mk (Str "there")])
  ; mk (Para [mk (Str "bye")]) ].
Proof. reflexivity. Qed.

Example parse_thematic :
  parse_blocks "one

  * * * *

two" =
  [ mk (Para [mk (Str "one")])
  ; mk ThematicBreak
  ; mk (Para [mk (Str "two")]) ].
Proof. reflexivity. Qed.

(* Paragraphs are never interrupted: thematic-break- or fence-shaped
   lines inside a paragraph are text.  Text the inline layer then reads,
   which is why the three hyphens arrive as an em dash rather than as
   themselves -- djot.js agrees, and the block-level point is unchanged:
   the line did not close the paragraph. *)
Example parse_no_interrupt :
  parse_blocks "one
---" =
  [ mk (Para [mk (Str "one"); mk SoftBreak; mk (Str emdash)]) ].
Proof. reflexivity. Qed.

Example parse_code_block :
  parse_blocks "``` ruby
x = 5
```" =
  [ mk (CodeBlock "ruby" ("x = 5" ++ nl)) ].
Proof. reflexivity. Qed.

Example parse_raw_block :
  parse_blocks "``` =html
<hr>
```" =
  [ mk (RawBlock "html" ("<hr>" ++ nl)) ].
Proof. reflexivity. Qed.

(* Unclosed fences extend to end of input; content is never classified. *)
Example parse_unclosed_fence :
  parse_blocks "~~~
* * *
para" =
  [ mk (CodeBlock "" ("* * *" ++ nl ++ "para" ++ nl)) ].
Proof. reflexivity. Qed.

Example parse_blank_only : parse_blocks "  " = [].
Proof. reflexivity. Qed.

(*
Block quotes
------------

Each example is a case from djot.js/test/block_quote.test or a probe
against djot.js; the comment gives the behaviour being pinned. *)

Example parse_quote_basic :
  parse_blocks "> Basic
> quote." =
  [ mk (BlockQuote [mk (Para [mk (Str "Basic"); mk SoftBreak; mk (Str "quote.")])]) ].
Proof. reflexivity. Qed.

(* A bare ">" is a quote with no content, which is why wf_block lets
   BlockQuote be empty. *)
Example parse_quote_empty :
  parse_blocks ">" = [mk (BlockQuote [])].
Proof. reflexivity. Qed.

(* ">" without following whitespace is not a prefix at all. *)
Example parse_quote_needs_ws :
  parse_blocks ">not a quote" =
  [ mk (Para [mk (Str ">not a quote")]) ].
Proof. reflexivity. Qed.

(* A blank prefixed line ends the inner paragraph without ending the
   quote; a truly blank line ends the quote. *)
Example parse_quote_two_paras :
  parse_blocks "> a
>
> b" =
  [ mk (BlockQuote [ mk (Para [mk (Str "a")]); mk (Para [mk (Str "b")]) ]) ].
Proof. reflexivity. Qed.

Example parse_quote_split :
  parse_blocks "> a

> b" =
  [ mk (BlockQuote [mk (Para [mk (Str "a")])])
  ; mk (BlockQuote [mk (Para [mk (Str "b")])]) ].
Proof. reflexivity. Qed.

(* Nesting comes from re-entering the classifier on the stripped line. *)
Example parse_quote_nested :
  parse_blocks "> > > deep" =
  [ mk (BlockQuote [mk (BlockQuote [mk (BlockQuote
      [mk (Para [mk (Str "deep")])])])]) ].
Proof. reflexivity. Qed.

(* Lazy continuation: a prefix-less text line still joins the innermost
   open paragraph, at any depth. *)
Example parse_quote_lazy :
  parse_blocks "> > deep
lazy" =
  [ mk (BlockQuote [mk (BlockQuote
      [mk (Para [mk (Str "deep"); mk SoftBreak; mk (Str "lazy")])])]) ].
Proof. reflexivity. Qed.

(* ...but only into a paragraph.  Verbatim content is not lazily
   continued, so the quote closes and a new paragraph starts. *)
Example parse_quote_no_lazy_fence :
  parse_blocks "> ```
> x
y" =
  [ mk (BlockQuote [mk (CodeBlock "" ("x" ++ nl))])
  ; mk (Para [mk (Str "y")]) ].
Proof. reflexivity. Qed.

(* Nor is a line that starts a block of its own: the quote closes. *)
Example parse_quote_closed_by_thematic :
  parse_blocks "> a
* * * *" =
  [ mk (BlockQuote [mk (Para [mk (Str "a")])]); mk ThematicBreak ].
Proof. reflexivity. Qed.

(*
Headings
--------

Pinned against djot.js probes, as above.  Section wrapping and
auto-identifiers are deliberately absent: they are a whole-document
pass, not part of the line fold. *)

Example parse_heading_basic :
  parse_blocks "## hi" = [mk (Heading 2 [mk (Str "hi")])].
Proof. reflexivity. Qed.

(* The whitespace after the hashes is required. *)
Example parse_heading_needs_ws :
  parse_blocks "#hi" = [mk (Para [mk (Str "#hi")])].
Proof. reflexivity. Qed.

Example parse_heading_empty :
  parse_blocks "#" = [mk (Heading 1 [])].
Proof. reflexivity. Qed.

(* Same level continues the heading; the text joins with a SoftBreak. *)
Example parse_heading_multiline :
  parse_blocks "# a
# b" =
  [mk (Heading 1 [mk (Str "a"); mk SoftBreak; mk (Str "b")])].
Proof. reflexivity. Qed.

(* ...and so does a bare text line, lazily. *)
Example parse_heading_lazy :
  parse_blocks "# a
b" =
  [mk (Heading 1 [mk (Str "a"); mk SoftBreak; mk (Str "b")])].
Proof. reflexivity. Qed.

(* A different level starts a new heading rather than continuing. *)
Example parse_heading_level_change :
  parse_blocks "# a
## b" =
  [mk (Heading 1 [mk (Str "a")]); mk (Heading 2 [mk (Str "b")])].
Proof. reflexivity. Qed.

(* Unlike a paragraph, a heading *is* interrupted by a block start. *)
Example parse_heading_interrupted :
  parse_blocks "# a
* * * *" =
  [mk (Heading 1 [mk (Str "a")]); mk ThematicBreak].
Proof. reflexivity. Qed.

Example parse_heading_interrupted_quote :
  parse_blocks "# a
> q" =
  [ mk (Heading 1 [mk (Str "a")])
  ; mk (BlockQuote [mk (Para [mk (Str "q")])]) ].
Proof. reflexivity. Qed.

(* Heading content is inline: it is never reclassified, so a quote
   marker inside one is just text. *)
Example parse_heading_content_not_reclassified :
  parse_blocks "# > q" = [mk (Heading 1 [mk (Str "> q")])].
Proof. reflexivity. Qed.

(* Containers compose for free: the quote strips, then the classifier
   sees a heading. *)
(*
Bullet lists
------------
*)

Example parse_list_tight :
  parse_blocks "- a
- b" = [mk (BulletList "-" Tight
              [ mk [mk (Para [mk (Str "a")])]; mk [mk (Para [mk (Str "b")])] ])].
Proof. reflexivity. Qed.

(* A blank line between items, with content after it, loosens the list. *)
Example parse_list_loose :
  parse_blocks "- a

- b" = [mk (BulletList "-" Loose
              [ mk [mk (Para [mk (Str "a")])]; mk [mk (Para [mk (Str "b")])] ])].
Proof. reflexivity. Qed.

(* A trailing blank does not: the next event closes the list. *)
Example parse_list_trailing_blank :
  parse_blocks "- a
" = [mk (BulletList "-" Tight [mk [mk (Para [mk (Str "a")])]])].
Proof. reflexivity. Qed.

(* Thematic breaks win over bullet markers: `classify` tests them
   first. *)
Example parse_list_not_thematic :
  parse_blocks "* * *" = [mk ThematicBreak].
Proof. reflexivity. Qed.

(* A marker never interrupts an open paragraph, so this is one item whose
   paragraph runs on, not a nested list. *)
Example parse_list_no_interrupt :
  parse_blocks "- a
  - b"
  = [mk (BulletList "-" Tight
           [mk [mk (Para [mk (Str "a"); mk SoftBreak; mk (Str "- b")])]])].
Proof. reflexivity. Qed.

(* A different bullet character is a different list. *)
Example parse_list_style_change :
  parse_blocks "- a
* b"
  = [ mk (BulletList "-" Tight [mk [mk (Para [mk (Str "a")])]])
    ; mk (BulletList "*" Tight [mk [mk (Para [mk (Str "b")])]]) ].
Proof. reflexivity. Qed.

(* Lazy continuation reaches into the item's paragraph. *)
Example parse_list_lazy :
  parse_blocks "- a
b"
  = [mk (BulletList "-" Tight
           [mk [mk (Para [mk (Str "a"); mk SoftBreak; mk (Str "b")])]])].
Proof. reflexivity. Qed.

(* A bare marker opens an item with no content. *)
Example parse_list_empty_item :
  parse_blocks "-
- b"
  = [mk (BulletList "-" Tight [ mk []; mk [mk (Para [mk (Str "b")])] ])].
Proof. reflexivity. Qed.

Example parse_heading_in_quote :
  parse_blocks "> # a" =
  [mk (BlockQuote [mk (Heading 1 [mk (Str "a")])])].
Proof. reflexivity. Qed.

(* Paragraphs are never interrupted, quotes included. *)
Example parse_quote_no_interrupt :
  parse_blocks "a
> b" =
  [ mk (Para [mk (Str "a"); mk SoftBreak; mk (Str "> b")]) ].
Proof. reflexivity. Qed.

(*
Block attributes
----------------

Every case below was checked against `djot.js` before it was written
down; the ones the corpus does not cover are marked. *)

(* The ordinary case: a spec on a line of its own decorates the block
   that follows it. *)
Example parse_attr_para :
  parse_blocks "{#id .class}
A paragraph"
  = [Node NoPos [("id", "id"); ("class", "class")]
       (Para [mk (Str "A paragraph")])].
Proof. reflexivity. Qed.

(* A blank line drops them. *)
Example parse_attr_blank_resets :
  parse_blocks "{#id}

A paragraph"
  = [mk (Para [mk (Str "A paragraph")])].
Proof. reflexivity. Qed.

(* Consecutive specs merge: later values win, classes accumulate, and
   each key keeps the position it first took. *)
Example parse_attr_consecutive :
  parse_blocks "{#id}
{key=val}
{.foo .bar}
{key=val2}
{.baz}
{#id2}
Okay"
  = [Node NoPos [("id", "id2"); ("key", "val2"); ("class", "foo bar baz")]
       (Para [mk (Str "Okay")])].
Proof. reflexivity. Qed.

(* Duplicate explicit ids are source data, not a parser error.  The
   editing layer may reject this document as ambiguous, but parsing must
   retain both occurrences. *)
Example parse_attr_duplicate_ids_preserved :
  parse_blocks "{#x}
a

{#x}
b"
  = [ Node NoPos [("id", "x")] (Para [mk (Str "a")])
    ; Node NoPos [("id", "x")] (Para [mk (Str "b")]) ].
Proof. reflexivity. Qed.

(* An empty id token contributes no attribute; this is distinct from an
   invalid spec, which falls back to paragraph text below. *)
Example parse_attr_empty_id_absent :
  parse_blocks "{# }
a" = [mk (Para [mk (Str "a")])].
Proof. reflexivity. Qed.

(* The attributes land on the container, not on its first child, and
   nesting is by the container the spec sits in. *)
Example parse_attr_nested_quote :
  parse_blocks "> {.foo}
> > {.bar}
> > nested"
  = [mk (BlockQuote
           [Node NoPos [("class", "foo")]
              (BlockQuote
                 [Node NoPos [("class", "bar")]
                    (Para [mk (Str "nested")])])])].
Proof. reflexivity. Qed.

Example parse_attr_id_nested_quote :
  parse_blocks "> {#x}
> a"
  = [mk (BlockQuote
          [Node NoPos [("id", "x")] (Para [mk (Str "a")])])].
Proof. reflexivity. Qed.

(* An indented line continues a spec across a line break. *)
Example parse_attr_continuation :
  parse_blocks "{#id .class
  style=""color:red""}
A paragraph"
  = [Node NoPos [("id", "id"); ("class", "class"); ("style", "color:red")]
       (Para [mk (Str "A paragraph")])].
Proof. reflexivity. Qed.

(* Without the indent there is no continuation, and the whole thing is a
   paragraph of the lines it ate -- including the line that refused to
   continue it. *)
Example parse_attr_unindented_is_para :
  parse_blocks "{a=x
hello"
  = [mk (Para [mk (Str "{a=x"); mk SoftBreak; mk (Str "hello")])].
Proof. reflexivity. Qed.

(* ...and paragraphs are not interruptible, so a heading marker on the
   next line is text too. *)
Example parse_attr_failed_para_not_interrupted :
  parse_blocks "{a=x
# non-heading"
  = [mk (Para [mk (Str "{a=x"); mk SoftBreak; mk (Str "# non-heading")])].
Proof. reflexivity. Qed.

(* A spec that does not parse never opens at all: `<` is outside the
   identifier class, so the line is ordinary text. *)
Example parse_attr_invalid_is_text :
  parse_blocks "{#a<b}
foo"
  = [mk (Para [mk (Str "{#a<b}"); mk SoftBreak; mk (Str "foo")])].
Proof. reflexivity. Qed.

(* A comment-only spec contributes no attributes but is still consumed. *)
Example parse_attr_comment :
  parse_blocks "{%
  a comment
  %}
Hello."
  = [mk (Para [mk (Str "Hello.")])].
Proof. reflexivity. Qed.

(* Not in the corpus: a blank line indented past the opener continues an
   open spec rather than closing it, since a blank line's indentation is
   its whole length.  djot.js agrees: `{#i` / two spaces / two spaces and
   `}` yields `<p id="i">Hi</p>`. *)
Example parse_attr_blank_continues_spec :
  parse_blocks "{#i
  
  }
Hi"
  = [Node NoPos [("id", "i")] (Para [mk (Str "Hi")])].
Proof. reflexivity. Qed.

(* Not in the corpus, and our one deliberate divergence.  djot.js records
   the blank continuation line as a slice, so a spec that spans a blank
   line and *then* fails reproduces the blank inside its paragraph:
   `<p>{#i\n\n<}\nHi</p>`.  We drop it, because a paragraph carrying a
   blank line does not round-trip -- parsing that rendering back splits
   the paragraph in two -- and `Wf.wf_block` rules it out for exactly
   that reason.  See the note in `step_fuel`'s PAttr branch. *)
Example parse_attr_failed_after_blank_drops_it :
  parse_blocks "{#i
  
  <}
Hi"
  = [mk (Para [ mk (Str "{#i"); mk SoftBreak
              ; mk (Str "<}"); mk SoftBreak; mk (Str "Hi")])].
Proof. reflexivity. Qed.

(*
Reference definitions
=====================

Every case here was decided against djot.js first; the boundaries are
tighter than the prose spec suggests.
*)

Example parse_ref_simple :
  parse_blocks "[foo]: /url"
  = [mk (RefDef "foo" "/url")].
Proof. reflexivity. Qed.

(* Continuation lines are indented past the bracket and carry one
   whitespace-free run each; the runs concatenate with no separator. *)
Example parse_ref_continued :
  parse_blocks "[foo]: /url
  /more"
  = [mk (RefDef "foo" "/url/more")].
Proof. reflexivity. Qed.

(* A second definition at the same column is not a continuation of the
   first: the test is "indented past", not "indented". *)
Example parse_ref_sibling :
  parse_blocks "[a]:
[b]: v"
  = [mk (RefDef "a" ""); mk (RefDef "b" "v")].
Proof. reflexivity. Qed.

(* Two tokens after the colon is not a definition at all, and neither is
   a trailing space: the pattern demands end of line right after the
   destination. *)
Example parse_ref_two_tokens_is_text :
  parse_blocks "[a]: u v"
  = [mk (Para [mk (Str "[a]: u v")])].
Proof. reflexivity. Qed.

(* Nor is a destination with no space before it. *)
Example parse_ref_no_space_is_text :
  parse_blocks "[a]:u"
  = [mk (Para [mk (Str "[a]:u")])].
Proof. reflexivity. Qed.

(* A definition never interrupts a paragraph -- paragraphs are
   uninterruptible here as everywhere. *)
Example parse_ref_after_text_is_text :
  parse_blocks "text
[a]: u"
  = [mk (Para [mk (Str "text"); mk SoftBreak; mk (Str "[a]: u")])].
Proof. reflexivity. Qed.

(* The footnote container claims `[^...]:` first, so such a line is not a
   reference definition. *)
Example parse_ref_footnote_label_excluded :
  parse_blocks "[^a]: note"
  = [mk (FootnoteDef "a" [mk (Para [mk (Str "note")])])].
Proof. reflexivity. Qed.

Example parse_footnote_indented_body :
  parse_blocks "[^a]:
  note"
  = [mk (FootnoteDef "a" [mk (Para [mk (Str "note")])])].
Proof. reflexivity. Qed.

Example parse_footnote_empty_then_block :
  parse_blocks "[^a]:

next"
  = [mk (FootnoteDef "a" []); mk (Para [mk (Str "next")])].
Proof. reflexivity. Qed.

Example parse_footnote_list_body :
  parse_blocks "[^a]: - item"
  = [mk (FootnoteDef "a"
       [mk (BulletList "-" Tight [mk [mk (Para [mk (Str "item")])]])])].
Proof. reflexivity. Qed.

(* The opener shifts the list's indentation.  djot.js agrees: in the
   footnote these are two list items, while at top level the second line
   continues the first item's paragraph.  This refutes whole-body
   footnote uniformity without a condition on column-bearing states. *)
Example footnote_list_shift_counterexample :
  parse_blocks "[^a]: - x
  - y"
  <> [mk (FootnoteDef "a" (parse_blocks "- x
  - y"))].
Proof. discriminate. Qed.

Example parse_footnote_inside_quote :
  parse_blocks "> [^a]: note"
  = [mk (BlockQuote
       [mk (FootnoteDef "a" [mk (Para [mk (Str "note")])])])].
Proof. reflexivity. Qed.

Example parse_footnote_no_space_is_inline :
  parse_blocks "[^a]:note"
  = [mk (Para [mk (FootnoteReference "a"); mk (Str ":note")])].
Proof. reflexivity. Qed.

(* A label may contain `[`: only `]` ends it. *)
Example parse_ref_label_open_bracket :
  parse_blocks "[a[b]: u"
  = [mk (RefDef "a[b" "u")].
Proof. reflexivity. Qed.

(* Block attributes decorate the definition as they would any block, so
   they reach the reference the document pass reads off it. *)
Example parse_ref_attributes :
  parse_blocks "{#x}
[a]: u"
  = [Node NoPos [("id", "x")] (RefDef "a" "u")].
Proof. reflexivity. Qed.

(* Tightness and what absorbs a blank line inside a list item, pinned
   against djot.js.  `blank_absorbed` is the list of containers that
   survive a blank, so the examples are that predicate read back off the
   parser. *)

(* A div survives the blank and takes it, so the list stays tight. *)
Example parse_blank_absorbed_by_div :
  parse_blocks "- :::
  a

  t
  :::"
  = [mk (BulletList "-" Tight
           [mk [mk (Div "" [mk (Para [mk (Str "a")]); mk (Para [mk (Str "t")])])]])].
Proof. reflexivity. Qed.

(* A block quote does not: the prefix-less blank closes it, so the blank
   reaches the list and loosens it. *)
Example parse_blank_not_absorbed_by_quote :
  parse_blocks "- > a

  t"
  = [mk (BulletList "-" Loose
           [mk [mk (BlockQuote [mk (Para [mk (Str "a")])]); mk (Para [mk (Str "t")])]])].
Proof. reflexivity. Qed.

(*
Tables
======

The head/align fold, read back off the parser.  Each of these was
measured against djot.js first; `Line.v` pins the row scanner, these pin
what a run of rows becomes.
*)

(* A separator promotes the row before it and sets the alignment of the
   rows after it. *)
Example parse_table_header :
  parse_blocks "| a | b |
|---|--:|
| c | d |"
  = [mk (Table (mk [])
           [ mk [ mk (Cell HeadCell AlignDefault [mk (Str "a")])
             ; mk (Cell HeadCell AlignRight [mk (Str "b")]) ]
           ; mk [ mk (Cell BodyCell AlignDefault [mk (Str "c")])
             ; mk (Cell BodyCell AlignRight [mk (Str "d")]) ] ])].
Proof. reflexivity. Qed.

(* With no row before it, a separator only sets alignment. *)
Example parse_table_separator_first :
  parse_blocks "|--:|
| b |"
  = [mk (Table (mk []) [mk [mk (Cell BodyCell AlignRight [mk (Str "b")])]])].
Proof. reflexivity. Qed.

(* Two separators in a row both claim the same preceding row, so the
   second one's alignment wins. *)
Example parse_table_two_separators :
  parse_blocks "| a |
|---|
|:-:|
| b |"
  = [mk (Table (mk [])
           [ mk [mk (Cell HeadCell AlignCenter [mk (Str "a")])]
           ; mk [mk (Cell BodyCell AlignCenter [mk (Str "b")])] ])].
Proof. reflexivity. Qed.

(* Alignment runs out positionally rather than repeating. *)
Example parse_table_ragged :
  parse_blocks "| a |
|--:|
| b | c |"
  = [mk (Table (mk [])
           [ mk [mk (Cell HeadCell AlignRight [mk (Str "a")])]
           ; mk [ mk (Cell BodyCell AlignRight [mk (Str "b")])
             ; mk (Cell BodyCell AlignDefault [mk (Str "c")]) ] ])].
Proof. reflexivity. Qed.

(* Separators alone are a table with no rows at all. *)
Example parse_table_no_rows :
  parse_blocks "|---|" = [mk (Table (mk []) [])].
Proof. reflexivity. Qed.

(* A cell is inline-parsed on its own, so a delimiter never crosses a
   bar (`tables.test:13`). *)
Example parse_table_cells_are_separate :
  parse_blocks "|*c| d* |"
  = [mk (Table (mk [])
           [mk [ mk (Cell BodyCell AlignDefault [mk (Str "*c")])
            ; mk (Cell BodyCell AlignDefault [mk (Str "d*")]) ]])].
Proof. reflexivity. Qed.

(* A line that fails the row scan is not a row: the table closes and the
   line opens a paragraph (`tables.test:31` is this shape). *)
Example parse_table_closed_by_bad_row :
  parse_blocks "| a |
| b
| c |"
  = [ mk (Table (mk []) [mk [mk (Cell BodyCell AlignDefault [mk (Str "a")])]])
    ; mk (Para [mk (Str "| b"); mk SoftBreak; mk (Str "| c |")]) ].
Proof. reflexivity. Qed.

(* A table does not interrupt a paragraph, as nothing in djot does. *)
Example parse_table_after_para :
  parse_blocks "p
| a |"
  = [mk (Para [mk (Str "p"); mk SoftBreak; mk (Str "| a |")])].
Proof. reflexivity. Qed.

(* A blank ends the rows but not the table: a caption may still follow,
   across any number of blanks. *)
Example parse_table_caption_after_blanks :
  parse_blocks "| a |


^ cap"
  = [mk (Table (mk [mk (Str "cap")])
           [mk [mk (Cell BodyCell AlignDefault [mk (Str "a")])]])].
Proof. reflexivity. Qed.

(* But a blank does end the rows: a row after one starts a second
   table. *)
Example parse_table_blank_splits :
  parse_blocks "| a |

| b |"
  = [ mk (Table (mk []) [mk [mk (Cell BodyCell AlignDefault [mk (Str "a")])]])
    ; mk (Table (mk []) [mk [mk (Cell BodyCell AlignDefault [mk (Str "b")])]]) ].
Proof. reflexivity. Qed.

(* A caption owns every nonblank line after it, row lines included, and
   a blank ends it. *)
Example parse_table_caption_swallows :
  parse_blocks "| a |
^ cap
| b |"
  = [mk (Table (mk [mk (Str "cap"); mk SoftBreak; mk (Str "| b |")])
           [mk [mk (Cell BodyCell AlignDefault [mk (Str "a")])]])].
Proof. reflexivity. Qed.

(* `^ ` with nothing after it is the empty caption, which is no
   caption. *)
Example parse_table_caption_empty :
  parse_blocks "| a |
^ "
  = [mk (Table (mk []) [mk [mk (Cell BodyCell AlignDefault [mk (Str "a")])]])].
Proof. reflexivity. Qed.

(* A caption with no table before it is a paragraph.  djot.js swallows
   the following lines into a caption and then drops the lot, rendering
   nothing at all; this is the logged divergence, and it is structural
   here -- there is no caption container except inside a table. *)
Example parse_caption_without_table :
  parse_blocks "^ cap
| a |"
  = [mk (Para [mk (Str "^ cap"); mk SoftBreak; mk (Str "| a |")])].
Proof. reflexivity. Qed.

(* Once a block intervenes the caption no longer reaches the table. *)
Example parse_table_caption_too_late :
  parse_blocks "| a |

p

^ cap"
  = [ mk (Table (mk []) [mk [mk (Cell BodyCell AlignDefault [mk (Str "a")])]])
    ; mk (Para [mk (Str "p")])
    ; mk (Para [mk (Str "^ cap")]) ].
Proof. reflexivity. Qed.

(*
Definition lists
================

A definition list is an ordinary list whose marker style is `:`, so what
is pinned here is the one thing that differs: the term split
`Ast.def_item` runs when an item closes.
*)

(* The item's first block, when it is a paragraph, becomes the term and
   leaves the definition. *)
Example parse_deflist :
  parse_blocks ": apple

  red fruit"
  = [mk (DefinitionList Loose
           [mk (mk [mk (Str "apple")], mk [mk (Para [mk (Str "red fruit")])])])].
Proof. reflexivity. Qed.

(* Without the blank the two lines are one paragraph, so the whole item
   is the term. *)
Example parse_deflist_one_para :
  parse_blocks ": apple
  red fruit"
  = [mk (DefinitionList Tight
           [mk (mk [mk (Str "apple"); mk SoftBreak; mk (Str "red fruit")], mk [])])].
Proof. reflexivity. Qed.

(* The term is the first paragraph wherever it starts, so a marker line
   with nothing on it still takes the paragraph below as its term. *)
Example parse_deflist_term_below :
  parse_blocks ":

  d"
  = [mk (DefinitionList Loose [mk (mk [mk (Str "d")], mk [])])].
Proof. reflexivity. Qed.

(* An item whose first block is not a paragraph has no term. *)
Example parse_deflist_no_term :
  parse_blocks ": # h"
  = [mk (DefinitionList Tight [mk (mk [], mk [mk (Heading 1 [mk (Str "h")])])])].
Proof. reflexivity. Qed.

(* A colon list and a bullet list do not merge: the style sets do not
   intersect, so the first list closes. *)
Example parse_deflist_not_bullet :
  parse_blocks ": a
- b"
  = [ mk (DefinitionList Tight [mk (mk [mk (Str "a")], mk [])])
    ; mk (BulletList "-" Tight [mk [mk (Para [mk (Str "b")])]]) ].
Proof. reflexivity. Qed.

(* And it does not interrupt a paragraph, as nothing in djot does. *)
Example parse_deflist_after_para :
  parse_blocks "p
: a"
  = [mk (Para [mk (Str "p"); mk SoftBreak; mk (Str ": a")])].
Proof. reflexivity. Qed.

(*
Task lists
==========

A task list is a bullet list whose marker carries a checkbox, so what is
pinned here is where the checkbox goes: on the *item*, not on the list.
*)

Example parse_tasklist :
  parse_blocks "- [ ] a
- [x] b"
  = [mk (TaskList Tight
           [ mk (Incomplete, [mk (Para [mk (Str "a")])])
           ; mk (Complete, [mk (Para [mk (Str "b")])]) ])].
Proof. reflexivity. Qed.

(* A marker at end of line is an item with no blocks at all. *)
Example parse_tasklist_empty :
  parse_blocks "- [ ]" = [mk (TaskList Tight [mk (Incomplete, [])])].
Proof. reflexivity. Qed.

(* The content after the marker is ordinary block content. *)
Example parse_tasklist_heading :
  parse_blocks "- [ ] # h"
  = [mk (TaskList Tight [mk (Incomplete, [mk (Heading 1 [mk (Str "h")])])])].
Proof. reflexivity. Qed.

(* `-X` and `-` do not intersect, so a bullet sibling starts a new list. *)
Example parse_tasklist_not_bullet :
  parse_blocks "- [ ] a
- b"
  = [ mk (TaskList Tight [mk (Incomplete, [mk (Para [mk (Str "a")])])])
    ; mk (BulletList "-" Tight [mk [mk (Para [mk (Str "b")])]]) ].
Proof. reflexivity. Qed.

(* Two spaces before the bracket, or none after it, and the marker is an
   ordinary bullet whose content happens to start with a bracket. *)
Example parse_tasklist_wide :
  parse_blocks "-  [ ] a"
  = [mk (BulletList "-" Tight [mk [mk (Para [mk (Str "[ ] a")])]])].
Proof. reflexivity. Qed.

(* And only a bullet takes one. *)
Example parse_tasklist_colon :
  parse_blocks ": [ ] a"
  = [mk (DefinitionList Tight [mk (mk [mk (Str "[ ] a")], mk [])])].
Proof. reflexivity. Qed.
