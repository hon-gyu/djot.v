(* ai-disclosure: ai-generated *)

(*
The syntax reference's examples, pinned
=======================================

Every code example in the djot syntax reference, as it reads at jgm/djot
`doc/syntax.md` commit d77f8a0 (2026-07-01), with the HTML djot.js gives
for it (djot.js at d7c3904).  One `Example` per code block, named after
its section; the sections below follow the reference's.  An example the
reference shows as several snippets in one block is one document here.
A second part pins the outcomes the prose states without a code block.

These are the reference's own illustrations of its rules, so a parser
change that breaks one contradicts the reference where it is most
explicit.  They are single documents: what each rule says over all
inputs is the business of the theorems, and
`.project/syntax-reference-coverage.md` says which rule has one.

Some examples differ from djot.js: `table_caption_alone`,
`task_tab_after_bullet`, and the tightness cases in the prose part's
"List" section, see there.
*)

From Stdlib Require Import String.
From DjotV Require Import Html.
Open Scope string_scope.

(*
Inline syntax
=============
*)

(*
Precedence
----------
*)

Example precedence_first_closed_emph :
  convert "_This is *regular_ not strong* emphasis
"
  = "<p><em>This is *regular</em> not strong* emphasis</p>
".
Proof. vm_compute. reflexivity. Qed.

Example precedence_first_closed_strong :
  convert "*This is _strong* not regular_ emphasis
"
  = "<p><strong>This is _strong</strong> not regular_ emphasis</p>
".
Proof. vm_compute. reflexivity. Qed.

Example precedence_link_closes_first :
  convert "[Link *](url)*
"
  = "<p><a href=""url"">Link *</a>*</p>
".
Proof. vm_compute. reflexivity. Qed.

Example precedence_strong_closes_first :
  convert "*Emphasis [*](url)
"
  = "<p><strong>Emphasis [</strong>](url)</p>
".
Proof. vm_compute. reflexivity. Qed.

Example precedence_nesting :
  convert "_This is *strong within* regular emphasis_
"
  = "<p><em>This is <strong>strong within</strong> regular emphasis</em></p>
".
Proof. vm_compute. reflexivity. Qed.

Example precedence_braces :
  convert "{_Emphasized_}
_}not emphasized{_
"
  = "<p><em>Emphasized</em>
_}not emphasized{_</p>
".
Proof. vm_compute. reflexivity. Qed.

Example precedence_closest_opener :
  convert "*not strong *strong*
"
  = "<p>*not strong <strong>strong</strong></p>
".
Proof. vm_compute. reflexivity. Qed.

Example precedence_verbatim :
  convert "`No _emphasis_ inside verbatim`
"
  = "<p><code>No _emphasis_ inside verbatim</code></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Link
----
*)

Example link_inline :
  convert "[My link text](http://example.com)
"
  = "<p><a href=""http://example.com"">My link text</a></p>
".
Proof. vm_compute. reflexivity. Qed.

Example link_url_split :
  convert "[My link text](http://example.com?product_number=234234234234
234234234234)
"
  = "<p><a href=""http://example.com?product_number=234234234234234234234234"">My link text</a></p>
".
Proof. vm_compute. reflexivity. Qed.

Example link_reference :
  convert "[My link text][foo bar]

[foo bar]: http://example.com
"
  = "<p><a href=""http://example.com"">My link text</a></p>
".
Proof. vm_compute. reflexivity. Qed.

Example link_reference_local :
  convert "[foo][bar]
"
  = "<p><a>foo</a></p>
".
Proof. vm_compute. reflexivity. Qed.

Example link_empty_label :
  convert "[My link text][]

[My link text]: /url
"
  = "<p><a href=""/url"">My link text</a></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Image
-----
*)

Example image :
  convert "![picture of a cat](cat.jpg)

![picture of a cat][cat]

![cat][]

[cat]: feline.jpg
"
  = "<p><img alt=""picture of a cat"" src=""cat.jpg""></p>
<p><img alt=""picture of a cat"" src=""feline.jpg""></p>
<p><img alt=""cat"" src=""feline.jpg""></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Autolink
--------
*)

Example autolink :
  convert "<https://pandoc.org/lua-filters>
<me@example.com>
"
  = "<p><a href=""https://pandoc.org/lua-filters"">https://pandoc.org/lua-filters</a>
<a href=""mailto:me@example.com"">me@example.com</a></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Verbatim
--------
*)

Example verbatim_backticks :
  convert "``Verbatim with a backtick` character``
`Verbatim with three backticks ``` character`
"
  = "<p><code>Verbatim with a backtick` character</code>
<code>Verbatim with three backticks ``` character</code></p>
".
Proof. vm_compute. reflexivity. Qed.

Example verbatim_space_stripped :
  convert "`` `foo` ``
"
  = "<p><code>`foo`</code></p>
".
Proof. vm_compute. reflexivity. Qed.

Example verbatim_unclosed :
  convert "`foo bar
"
  = "<p><code>foo bar</code></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Emphasis/strong
---------------
*)

Example emphasis :
  convert "_emphasized text_

*strong emphasis*
"
  = "<p><em>emphasized text</em></p>
<p><strong>strong emphasis</strong></p>
".
Proof. vm_compute. reflexivity. Qed.

Example emphasis_not_opened :
  convert "_ Not emphasized (spaces). _

___ (not an emphasized `_` character)
"
  = "<p>_ Not emphasized (spaces). _</p>
<p>___ (not an emphasized <code>_</code> character)</p>
".
Proof. vm_compute. reflexivity. Qed.

Example emphasis_nested :
  convert "__emphasis inside_ emphasis_
"
  = "<p><em><em>emphasis inside</em> emphasis</em></p>
".
Proof. vm_compute. reflexivity. Qed.

Example emphasis_braces :
  convert "{_ this is emphasized, despite the spaces! _}
"
  = "<p><em> this is emphasized, despite the spaces! </em></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Highlighted
-----------
*)

Example highlighted :
  convert "This is {=highlighted text=}.
"
  = "<p>This is <mark>highlighted text</mark>.</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Super/subscript
---------------
*)

Example super_subscript :
  convert "H~2~O and djot^TM^
"
  = "<p>H<sub>2</sub>O and djot<sup>TM</sup></p>
".
Proof. vm_compute. reflexivity. Qed.

Example super_subscript_braces :
  convert "H{~one two buckle my shoe~}O
"
  = "<p>H<sub>one two buckle my shoe</sub>O</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Insert/delete
-------------
*)

Example insert_delete :
  convert "My boss is {-mean-}{+nice+}.
"
  = "<p>My boss is <del>mean</del><ins>nice</ins>.</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Smart punctuation
-----------------
*)

Example smart_quotes :
  convert """Hello,"" said the spider.
""'Shelob' is my name.""
"
  = "<p>“Hello,” said the spider.
“‘Shelob’ is my name.”</p>
".
Proof. vm_compute. reflexivity. Qed.

Example smart_quotes_braces :
  convert "'}Tis Socrates' season to be jolly!
"
  = "<p>’Tis Socrates’ season to be jolly!</p>
".
Proof. vm_compute. reflexivity. Qed.

Example smart_quotes_escaped :
  convert "5\'11\""
"
  = "<p>5'11""</p>
".
Proof. vm_compute. reflexivity. Qed.

Example smart_dashes_ellipsis :
  convert "57--33 oxen---and no sheep...
"
  = "<p>57–33 oxen—and no sheep…</p>
".
Proof. vm_compute. reflexivity. Qed.

Example smart_dash_runs :
  convert "a----b c------d
"
  = "<p>a––b c——d</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Math
----
*)

Example math :
  convert "Einstein derived $`e=mc^2`.
Pythagoras proved
$$` x^n + y^n = z^n `
"
  = "<p>Einstein derived <span class=""math inline"">\(e=mc^2\)</span>.
Pythagoras proved
<span class=""math display"">\[ x^n + y^n = z^n \]</span></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Footnote reference
------------------
*)

Example footnote_reference :
  convert "Here is the reference.[^foo]

[^foo]: And here is the note.
"
  = "<p>Here is the reference.<a id=""fnref1"" href=""#fn1"" role=""doc-noteref""><sup>1</sup></a></p>
<section role=""doc-endnotes"">
<hr>
<ol>
<li id=""fn1"">
<p>And here is the note.<a href=""#fnref1"" role=""doc-backlink"">↩︎</a></p>
</li>
</ol>
</section>
".
Proof. vm_compute. reflexivity. Qed.

(*
Line break
----------
*)

Example line_break :
  convert "This is a soft
break and this is a hard\
break.
"
  = "<p>This is a soft
break and this is a hard<br>
break.</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Comment
-------
*)

Example comment_in_attribute :
  convert "{#ident % later we'll add a class %}
"
  = "".
Proof. vm_compute. reflexivity. Qed.

Example comment_alone :
  convert "Foo bar {% This is a comment, spanning
multiple lines %} baz.
"
  = "<p>Foo bar  baz.</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Symbols
-------
*)

Example symbols :
  convert "My reaction is :+1: :smiley:.
"
  = "<p>My reaction is :+1: :smiley:.</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Raw inline
----------
*)

Example raw_inline :
  convert "This is `<?php echo 'Hello world!' ?>`{=html}.
"
  = "<p>This is <?php echo 'Hello world!' ?>.</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Span
----
*)

Example span :
  convert "It can be helpful to [read the manual]{.big .red}.
"
  = "<p>It can be helpful to <span class=""big red"">read the manual</span>.</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Inline attributes
-----------------
*)

Example inline_attributes :
  convert "An attribute on _emphasized text_{#foo
.bar .baz key=""my value""}
"
  = "<p>An attribute on <em id=""foo"" class=""bar baz"" key=""my value"">emphasized text</em></p>
".
Proof. vm_compute. reflexivity. Qed.

Example inline_attributes_stacked :
  convert "avant{lang=fr}{.blue}
"
  = "<p><span lang=""fr"" class=""blue"">avant</span></p>
".
Proof. vm_compute. reflexivity. Qed.

Example inline_attributes_merged :
  convert "avant{lang=fr .blue}
"
  = "<p><span lang=""fr"" class=""blue"">avant</span></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Block syntax
============
*)

(*
Heading
-------
*)

Example heading :
  convert "## A level _two_ heading!
"
  = "<section id=""A-level-two-heading"">
<h2>A level <em>two</em> heading!</h2>
</section>
".
Proof. vm_compute. reflexivity. Qed.

Example heading_marked_continuation :
  convert "# A heading that
# takes up
# three lines

A paragraph, finally
"
  = "<section id=""A-heading-that-takes-up-three-lines"">
<h1>A heading that
takes up
three lines</h1>
<p>A paragraph, finally</p>
</section>
".
Proof. vm_compute. reflexivity. Qed.

Example heading_lazy_continuation :
  convert "# A heading that
takes up
three lines

A paragraph, finally.
"
  = "<section id=""A-heading-that-takes-up-three-lines"">
<h1>A heading that
takes up
three lines</h1>
<p>A paragraph, finally.</p>
</section>
".
Proof. vm_compute. reflexivity. Qed.

(*
Block quote
-----------
*)

Example block_quote :
  convert "> This is a block quote.
>
> 1. with a
> 2. list in it.
"
  = "<blockquote>
<p>This is a block quote.</p>
<ol>
<li>
with a
</li>
<li>
list in it.
</li>
</ol>
</blockquote>
".
Proof. vm_compute. reflexivity. Qed.

Example block_quote_lazy :
  convert "> This is a block
quote.
"
  = "<blockquote>
<p>This is a block
quote.</p>
</blockquote>
".
Proof. vm_compute. reflexivity. Qed.

(*
List item
---------
*)

Example list_item :
  convert "1.  This is a
 list item.

 > containing a block quote
"
  = "<ol>
<li>
<p>This is a
list item.</p>
<blockquote>
<p>containing a block quote</p>
</blockquote>
</li>
</ol>
".
Proof. vm_compute. reflexivity. Qed.

Example list_item_lazy :
  convert "1.  This is a
list item.

  Second paragraph under the
list item.
"
  = "<ol>
<li>
<p>This is a
list item.</p>
<p>Second paragraph under the
list item.</p>
</li>
</ol>
".
Proof. vm_compute. reflexivity. Qed.

Example list_item_no_sublist :
  convert "- a
  - b
"
  = "<ul>
<li>
a
- b
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_item_sublist_after_blank :
  convert "- a

  - b
"
  = "<ul>
<li>
a
<ul>
<li>
b
</li>
</ul>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

(*
List item / Definition list item
--------------------------------
*)

Example definition_list_item :
  convert ": orange

  A citrus fruit.
"
  = "<dl>
<dt>orange</dt>
<dd>
<p>A citrus fruit.</p>
</dd>
</dl>
".
Proof. vm_compute. reflexivity. Qed.

(*
List
----
*)

Example list_style_change :
  convert "i) one
i. one (style change)
+ bullet
* bullet (style change)
"
  = "<ol type=""i"">
<li>
one
</li>
</ol>
<ol type=""i"">
<li>
one (style change)
</li>
</ol>
<ul>
<li>
bullet
</li>
</ul>
<ul>
<li>
bullet (style change)
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_ambiguous_marker :
  convert "i. item
j. next item
"
  = "<ol start=""9"" type=""a"">
<li>
item
</li>
<li>
next item
</li>
</ol>
".
Proof. vm_compute. reflexivity. Qed.

Example list_start_number :
  convert "5) five
8) six
"
  = "<ol start=""5"">
<li>
five
</li>
<li>
six
</li>
</ol>
".
Proof. vm_compute. reflexivity. Qed.

Example list_tight :
  convert "- one
- two

  - sub
  - sub
"
  = "<ul>
<li>
one
</li>
<li>
two
<ul>
<li>
sub
</li>
<li>
sub
</li>
</ul>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_loose :
  convert "- one

- two
"
  = "<ul>
<li>
<p>one</p>
</li>
<li>
<p>two</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

(*
Code block
----------
*)

Example code_block_longer_fence :
  convert "````
This is how you do a code block:

``` ruby
x = 5 * 6
```
````
"
  = "<pre><code>This is how you do a code block:

``` ruby
x = 5 * 6
```
</code></pre>
".
Proof. vm_compute. reflexivity. Qed.

Example code_block_closed_by_parent :
  convert "> ```
> code in a
> block quote

Paragraph.
"
  = "<blockquote>
<pre><code>code in a
block quote
</code></pre>
</blockquote>
<p>Paragraph.</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Thematic break
--------------
*)

Example thematic_break_indented :
  convert "Then they went to sleep.

      * * * *

When they woke up, ...
"
  = "<p>Then they went to sleep.</p>
<hr>
<p>When they woke up, …</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Raw block
---------
*)

Example raw_block :
  convert "``` =html
<video width=""320"" height=""240"" controls>
  <source src=""movie.mp4"" type=""video/mp4"">
  <source src=""movie.ogg"" type=""video/ogg"">
  Your browser does not support the video tag.
</video>
```
"
  = "<video width=""320"" height=""240"" controls>
  <source src=""movie.mp4"" type=""video/mp4"">
  <source src=""movie.ogg"" type=""video/ogg"">
  Your browser does not support the video tag.
</video>
".
Proof. vm_compute. reflexivity. Qed.

(*
Div
---
*)

Example div :
  convert "::: warning
Here is a paragraph.

And here is another.
:::
"
  = "<div class=""warning"">
<p>Here is a paragraph.</p>
<p>And here is another.</p>
</div>
".
Proof. vm_compute. reflexivity. Qed.

(*
Pipe table
----------
*)

Example table_row :
  convert "| 1 | 2 |
"
  = "<table>
<tr>
<td>1</td>
<td>2</td>
</tr>
</table>
".
Proof. vm_compute. reflexivity. Qed.

Example table_header :
  convert "| fruit  | price |
|--------|------:|
| apple  |     4 |
| banana |    10 |
"
  = "<table>
<tr>
<th>fruit</th>
<th style=""text-align: right;"">price</th>
</tr>
<tr>
<td>apple</td>
<td style=""text-align: right;"">4</td>
</tr>
<tr>
<td>banana</td>
<td style=""text-align: right;"">10</td>
</tr>
</table>
".
Proof. vm_compute. reflexivity. Qed.

Example table_alignment_changes :
  convert "| a  |  b |
|----|:--:|
| 1  | 2  |
|:---|---:|
| 3  | 4  |
"
  = "<table>
<tr>
<th>a</th>
<th style=""text-align: center;"">b</th>
</tr>
<tr>
<th style=""text-align: left;"">1</th>
<th style=""text-align: right;"">2</th>
</tr>
<tr>
<td style=""text-align: left;"">3</td>
<td style=""text-align: right;"">4</td>
</tr>
</table>
".
Proof. vm_compute. reflexivity. Qed.

Example table_no_header :
  convert "|:--|---:|
| x | 2  |
"
  = "<table>
<tr>
<td style=""text-align: left;"">x</td>
<td style=""text-align: right;"">2</td>
</tr>
</table>
".
Proof. vm_compute. reflexivity. Qed.

Example table_escaped_pipes :
  convert "| just two \| `|` | cells in this table |
"
  = "<table>
<tr>
<td>just two | <code>|</code></td>
<td>cells in this table</td>
</tr>
</table>
".
Proof. vm_compute. reflexivity. Qed.

(* The reference shows the caption on its own; djot.js drops a caption
   with no table before it and prints nothing, we keep it as a paragraph.
   Adjudicated in `.project/djotjs-divergences.md`, "a caption with no
   table" (2026-08-22).  The two examples after it are the rule the
   snippet illustrates, a caption under a table, where the two agree. *)
Example table_caption_alone :
  convert "^ This is the caption.  It can contain _inline formatting_
  and can extend over multiple lines, provided they are
  indented relative to the `^`.
"
  = "<p>^ This is the caption.  It can contain <em>inline formatting</em>
and can extend over multiple lines, provided they are
indented relative to the <code>^</code>.</p>
".
Proof. vm_compute. reflexivity. Qed.

Example table_caption_after_table :
  convert "| a |
^ caption
"
  = "<table>
<caption>caption</caption>
<tr>
<td>a</td>
</tr>
</table>
".
Proof. vm_compute. reflexivity. Qed.

Example table_caption_after_blank :
  convert "| a |

^ caption
"
  = "<table>
<caption>caption</caption>
<tr>
<td>a</td>
</tr>
</table>
".
Proof. vm_compute. reflexivity. Qed.

(*
Reference link definition
-------------------------
*)

Example reference_definition :
  convert "[google]: https://google.com

[product page]: http://example.com?item=983459873087120394870128370
  0981234098123048172304
"
  = "".
Proof. vm_compute. reflexivity. Qed.

Example reference_attributes :
  convert "{title=foo}
[ref]: /url

[ref][]
"
  = "<p><a href=""/url"" title=""foo"">ref</a></p>
".
Proof. vm_compute. reflexivity. Qed.

Example reference_attributes_link_overrides :
  convert "{title=foo}
[ref]: /url

[ref][]{title=bar}
"
  = "<p><a href=""/url"" title=""bar"">ref</a></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Footnote
--------
*)

Example footnote :
  convert "Here's the reference.[^foo]

[^foo]: This is a note
  with two paragraphs.

  Second paragraph.

  > a block quote in the note.
"
  = "<p>Here’s the reference.<a id=""fnref1"" href=""#fn1"" role=""doc-noteref""><sup>1</sup></a></p>
<section role=""doc-endnotes"">
<hr>
<ol>
<li id=""fn1"">
<p>This is a note
with two paragraphs.</p>
<p>Second paragraph.</p>
<blockquote>
<p>a block quote in the note.</p>
</blockquote>
<p><a href=""#fnref1"" role=""doc-backlink"">↩︎</a></p>
</li>
</ol>
</section>
".
Proof. vm_compute. reflexivity. Qed.

Example footnote_lazy :
  convert "Here's the reference.[^foo]

[^foo]: This is a note
with two paragraphs.

  Second paragraph must
be indented, at least in the first line.
"
  = "<p>Here’s the reference.<a id=""fnref1"" href=""#fn1"" role=""doc-noteref""><sup>1</sup></a></p>
<section role=""doc-endnotes"">
<hr>
<ol>
<li id=""fn1"">
<p>This is a note
with two paragraphs.</p>
<p>Second paragraph must
be indented, at least in the first line.<a href=""#fnref1"" role=""doc-backlink"">↩︎</a></p>
</li>
</ol>
</section>
".
Proof. vm_compute. reflexivity. Qed.

(*
Block attributes
----------------
*)

Example block_attributes :
  convert "{#water}
{.important .large}
Don't forget to turn off the water!

{source=""Iliad""}
> Sing, muse, of the wrath of Achilles
"
  = "<p id=""water"" class=""important large"">Don’t forget to turn off the water!</p>
<blockquote source=""Iliad"">
<p>Sing, muse, of the wrath of Achilles</p>
</blockquote>
".
Proof. vm_compute. reflexivity. Qed.

(*
Links to headings
-----------------
*)

Example heading_identifier :
  convert "## My heading + auto-identifier
"
  = "<section id=""My-heading-auto-identifier"">
<h2>My heading + auto-identifier</h2>
</section>
".
Proof. vm_compute. reflexivity. Qed.

Example heading_implicit_reference :
  convert "See the [Epilogue][].

    * * * *

# Epilogue
"
  = "<p>See the <a href=""#Epilogue"">Epilogue</a>.</p>
<hr>
<section id=""Epilogue"">
<h1>Epilogue</h1>
</section>
".
Proof. vm_compute. reflexivity. Qed.

(*
Cases the prose states
======================

Outcomes the reference states in its prose, a quoted snippet or a
sentence, rather than in a code block.  Same form as above: our HTML,
which is djot.js's for every case here except the three in "List".
*)

(*
Inline syntax: prose
====================
*)

(*
Precedence
----------
*)

Example marked_closer_needs_marked_opener :
  convert "{_hi_
"
  = "<p>{_hi_</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Ordinary text
-------------
*)

Example escape_punctuation :
  convert "\* \% \~
"
  = "<p>* % ~</p>
".
Proof. vm_compute. reflexivity. Qed.

Example escape_other_is_literal :
  convert "\a \1
"
  = "<p>\a \1</p>
".
Proof. vm_compute. reflexivity. Qed.

Example escape_newline_hard_break :
  convert "a  \
b
"
  = "<p>a<br>
b</p>
".
Proof. vm_compute. reflexivity. Qed.

Example escape_newline_after_spaces :
  convert "a\  
b
"
  = "<p>a<br>
b</p>
".
Proof. vm_compute. reflexivity. Qed.

Example escape_space_nbsp :
  convert "a\ b
"
  = "<p>a&nbsp;b</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Link
----
*)

Example link_no_space_before_destination :
  convert "[a] (b)
"
  = "<p>[a] (b)</p>
".
Proof. vm_compute. reflexivity. Qed.

Example link_no_space_before_label :
  convert "[a] [b]

[b]: /u
"
  = "<p>[a] [b]</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Autolink
--------
*)

Example autolink_no_newline :
  convert "<http://a
b>
"
  = "<p>&lt;http://a
b&gt;</p>
".
Proof. vm_compute. reflexivity. Qed.

Example autolink_literal :
  convert "<http://a\_b>
"
  = "<p><a href=""http://a\_b"">http://a\_b</a></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Verbatim
--------
*)

Example verbatim_no_escapes :
  convert "`a\`b`
"
  = "<p><code>a\</code>b<code></code></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Emphasis/strong
---------------
*)

Example emphasis_opener_before_space :
  convert "_ a_
"
  = "<p>_ a_</p>
".
Proof. vm_compute. reflexivity. Qed.

Example emphasis_closer_after_space :
  convert "_a _
"
  = "<p>_a _</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Highlighted
-----------
*)

Example highlight_needs_braces :
  convert "=a=
"
  = "<p>=a=</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Insert/delete
-------------
*)

Example insert_needs_braces :
  convert "+a+ -b-
"
  = "<p>+a+ -b-</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Math
----
*)

Example math_display :
  convert "$$`x`
"
  = "<p><span class=""math display"">\[x\]</span></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Line break
----------
*)

Example hard_break_backslash :
  convert "a\
b
"
  = "<p>a<br>
b</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Symbols
-------
*)

Example symbol :
  convert ":a:
"
  = "<p>:a:</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Span
----
*)

Example span_needs_attributes :
  convert "[a]
"
  = "<p>[a]</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Inline attributes
-----------------
*)

Example inline_attrs_last_id :
  convert "a{#x #y}
"
  = "<p><span id=""y"">a</span></p>
".
Proof. vm_compute. reflexivity. Qed.

Example inline_attrs_classes_combine :
  convert "a{.x .y}{.z}
"
  = "<p><span class=""x y z"">a</span></p>
".
Proof. vm_compute. reflexivity. Qed.

Example inline_attrs_bare_value :
  convert "a{k=v_:-1}
"
  = "<p><span k=""v_:-1"">a</span></p>
".
Proof. vm_compute. reflexivity. Qed.

Example inline_attrs_quoted_escape :
  convert "a{k=""x\""y""}
"
  = "<p><span k=""x&quot;y"">a</span></p>
".
Proof. vm_compute. reflexivity. Qed.

Example inline_attrs_need_adjacency :
  convert "a {.x}
"
  = "<p>a </p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Block syntax: prose
===================
*)

(*
Paragraph
---------
*)

Example paragraph_ends_at_container :
  convert "> a

b
"
  = "<blockquote>
<p>a</p>
</blockquote>
<p>b</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Heading
-------
*)

Example heading_needs_space :
  convert "#a
"
  = "<p>#a</p>
".
Proof. vm_compute. reflexivity. Qed.

(* The reference says a heading ends at a blank line and that its
   continuation lines may repeat the same number of `#`; it does not say
   what a different number does.  djot.js starts a new heading.  Logged
   as a `SPEC-GAP` in `.project/djotjs-divergences.md`. *)
Example heading_other_marker_count :
  convert "## a
# b
"
  = "<section id=""a"">
<h2>a</h2>
</section>
<section id=""b"">
<h1>b</h1>
</section>
".
Proof. vm_compute. reflexivity. Qed.

(* The reference allows lazy lines in paragraphs only; djot.js also
   continues a heading on a line without the quote's `>`.  Logged as a
   `SPEC-GAP` in `.project/djotjs-divergences.md`. *)
Example heading_ends_with_container :
  convert "> # a
b
"
  = "<blockquote>
<h1 id=""a-b"">a
b</h1>
</blockquote>
".
Proof. vm_compute. reflexivity. Qed.

(*
Block quote
-----------
*)

Example quote_needs_space :
  convert ">a
"
  = "<p>&gt;a</p>
".
Proof. vm_compute. reflexivity. Qed.

Example quote_bare_marker :
  convert ">
> a
"
  = "<blockquote>
<p>a</p>
</blockquote>
".
Proof. vm_compute. reflexivity. Qed.

Example quote_no_lazy_first_line :
  convert "> a

b
"
  = "<blockquote>
<p>a</p>
</blockquote>
<p>b</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
List item
---------
*)

Example list_marker_then_newline :
  convert "-
  a
"
  = "<ul>
<li>
a
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example ordered_roman_wide :
  convert "(xix) a
"
  = "<ol start=""19"" type=""i"">
<li>
a
</li>
</ol>
".
Proof. vm_compute. reflexivity. Qed.

Example ordered_v_paren :
  convert "v) a
"
  = "<ol start=""5"" type=""i"">
<li>
a
</li>
</ol>
".
Proof. vm_compute. reflexivity. Qed.

(*
List item / Task list item
--------------------------
*)

Example task_items :
  convert "- [ ] a
- [x] b
- [X] c
"
  = "<ul class=""task-list"">
<li>
<input disabled="""" type=""checkbox""/>
a
</li>
<li>
<input disabled="""" type=""checkbox"" checked=""""/>
b
</li>
<li>
<input disabled="""" type=""checkbox"" checked=""""/>
c
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

(* A tab after the bullet, as after any marker.  djot.js asks for a space
   there and reads a plain bullet; `.project/djotjs-divergences.md`,
   2026-10-05. *)
Example task_tab_after_bullet :
  convert "-	[x] a
"
  = "<ul class=""task-list"">
<li>
<input disabled="""" type=""checkbox"" checked=""""/>
a
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

(*
List item / Definition list item
--------------------------------
*)

Example definition_term_lines :
  convert ": a
  b

  c
"
  = "<dl>
<dt>a
b</dt>
<dd>
<p>c</p>
</dd>
</dl>
".
Proof. vm_compute. reflexivity. Qed.

(*
List
----

"A list is classed as *tight* if it does not contain blank lines between
items, or between blocks inside an item."  djot.js gets the first five
wrong: it calls the first two tight (jgm/djot.js#45), the third loose
(jgm/djot.js#157), and the fourth and fifth tight, because it counts a
blank only against a list among the two innermost open containers and a
footnote in an item is a third.  In the sixth the blank is the
footnote's own, since the footnote continues past it.  The same holds
of a table and its caption ("there can be an intervening blank line"),
which djot.js calls loose; a paragraph after the table is a second
block, and loosens.  A div left open ends with its item, at the line
before the blank, so the blank lies between items; djot.js keeps it
inside the div and calls the list tight.  A code block left open takes
the blank as a line of code, and stays tight in both.
*)

Example list_blank_before_nested_list_item :
  convert "- a

- - b
"
  = "<ul>
<li>
<p>a</p>
</li>
<li>
<ul>
<li>
b
</li>
</ul>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_before_empty_last_item :
  convert "- a

-
"
  = "<ul>
<li>
<p>a</p>
</li>
<li>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_div_closer_not_blank :
  convert "- :::
  a
  :::
- c
"
  = "<ul>
<li>
<div>
a
</div>
</li>
<li>
c
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_after_footnote_in_item :
  convert "- [^n]: a

  b
"
  = "<ul>
<li>
<p>b</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_after_footnote_between_items :
  convert "- [^n]: a

- c
"
  = "<ul>
<li>
</li>
<li>
<p>c</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_inside_footnote :
  convert "- [^n]: a

      b
- c
"
  = "<ul>
<li>
</li>
<li>
c
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_before_caption :
  convert "- | a |

  ^ cap
- c
"
  = "<ul>
<li>
<table>
<caption>cap</caption>
<tr>
<td>a</td>
</tr>
</table>
</li>
<li>
c
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_after_table :
  convert "- | a |

  b
- c
"
  = "<ul>
<li>
<table>
<tr>
<td>a</td>
</tr>
</table>
<p>b</p>
</li>
<li>
<p>c</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_after_open_div :
  convert "- :::

- b
"
  = "<ul>
<li>
<div>
</div>
</li>
<li>
<p>b</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_after_open_code :
  convert "- ```

- b
"
  = "<ul>
<li>
<pre><code></code></pre>
</li>
<li>
<p>b</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_after_nested_list_between_items :
  convert "- - b

- c
"
  = "<ul>
<li>
<ul>
<li>
b
</li>
</ul>
</li>
<li>
<p>c</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_after_nested_list_before_item :
  convert "- a

  - b

- c
"
  = "<ul>
<li>
<p>a</p>
<ul>
<li>
b
</li>
</ul>
</li>
<li>
<p>c</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_after_nested_list_in_item :
  convert "- - a

  b
"
  = "<ul>
<li>
<ul>
<li>
a
</li>
</ul>
b
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_before_attribute_on_nested_list :
  convert "- a

  {.x}
  - b
- c
"
  = "<ul>
<li>
a
<ul class=""x"">
<li>
b
</li>
</ul>
</li>
<li>
c
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_after_dropped_attribute :
  convert "- - x
  {.a}

  para
- b
"
  = "<ul>
<li>
<ul>
<li>
x
</li>
</ul>
<p>para</p>
</li>
<li>
<p>b</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_before_dangling_attribute_at_end :
  convert "- a

  {.x}
"
  = "<ul>
<li>
<p>a</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_before_dangling_attribute_then_nested_list :
  convert "- a

  {.x}

  - b
"
  = "<ul>
<li>
<p>a</p>
<ul>
<li>
b
</li>
</ul>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_before_dangling_attribute_in_nested_list :
  convert "- - a

    {.x}
- b
"
  = "<ul>
<li>
<ul>
<li>
<p>a</p>
</li>
</ul>
</li>
<li>
b
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_before_stacked_dangling_attributes :
  convert "- a

  {.x}
  {.y}
"
  = "<ul>
<li>
<p>a</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_before_unfinished_spec :
  convert "- a

  {.x
"
  = "<ul>
<li>
<p>a</p>
<p>{.x</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_before_failed_spec :
  convert "- a

  {.x
  oops
"
  = "<ul>
<li>
<p>a</p>
<p>{.x
oops</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

Example list_blank_before_dangling_attribute_over_two_lines :
  convert "- a

  {.x
   .y}
"
  = "<ul>
<li>
<p>a</p>
</li>
</ul>
".
Proof. vm_compute. reflexivity. Qed.

(*
Code block
----------
*)

Example code_block_info_only :
  convert "```ruby x
a
```
"
  = "<p><code>ruby x
a
</code></p>
".
Proof. vm_compute. reflexivity. Qed.

Example code_block_info_spaces :
  convert "```  ruby  
a
```
"
  = "<pre><code class=""language-ruby"">a
</code></pre>
".
Proof. vm_compute. reflexivity. Qed.

Example code_block_longer_closer :
  convert "```
a
`````
b
"
  = "<pre><code>a
</code></pre>
<p>b</p>
".
Proof. vm_compute. reflexivity. Qed.

Example code_block_unclosed :
  convert "```
a
"
  = "<pre><code>a
</code></pre>
".
Proof. vm_compute. reflexivity. Qed.

Example code_block_unclosed_trailing_blank :
  convert "```
a

"
  = "<pre><code>a
</code></pre>
".
Proof. vm_compute. reflexivity. Qed.

(*
Thematic break
--------------
*)

Example thematic_dashes :
  convert "- - -
"
  = "<hr>
".
Proof. vm_compute. reflexivity. Qed.

Example thematic_mixed_ws :
  convert "*	* *
"
  = "<hr>
".
Proof. vm_compute. reflexivity. Qed.

(*
Div
---
*)

Example div_class_only :
  convert "::: a b
c
:::
"
  = "<p>::: a b
c
:::</p>
".
Proof. vm_compute. reflexivity. Qed.

Example div_longer_closer :
  convert ":::
a
::::
b
"
  = "<div>
<p>a</p>
</div>
<p>b</p>
".
Proof. vm_compute. reflexivity. Qed.

Example div_unclosed :
  convert "> :::
> a

b
"
  = "<blockquote>
<div>
<p>a</p>
</div>
</blockquote>
<p>b</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Pipe table
----------
*)

Example table_separator_first :
  convert "|--|
|a|
"
  = "<table>
<tr>
<td>a</td>
</tr>
</table>
".
Proof. vm_compute. reflexivity. Qed.

Example table_row_needs_closing_pipe :
  convert "| a | b
"
  = "<p>| a | b</p>
".
Proof. vm_compute. reflexivity. Qed.

Example table_header_resets :
  convert "| a |
|---|
| b |
|:-|
| c |
"
  = "<table>
<tr>
<th>a</th>
</tr>
<tr>
<th style=""text-align: left;"">b</th>
</tr>
<tr>
<td style=""text-align: left;"">c</td>
</tr>
</table>
".
Proof. vm_compute. reflexivity. Qed.

(*
Reference link definition
-------------------------
*)

Example reference_case_sensitive :
  convert "[Link][]

[link]: /u
"
  = "<p><a>Link</a></p>
".
Proof. vm_compute. reflexivity. Qed.

Example reference_url_lines :
  convert "[a]: /u
  v

[a][]
"
  = "<p><a href=""/uv"">a</a></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Footnote
--------
*)

Example footnote_indent_past_reference :
  convert " [^a]: x

  y
"
  = "".
Proof. vm_compute. reflexivity. Qed.

Example footnote_indent_not_past :
  convert " [^a]: x

 y

[^a]
"
  = "<p>y</p>
<p><a id=""fnref1"" href=""#fn1"" role=""doc-noteref""><sup>1</sup></a></p>
<section role=""doc-endnotes"">
<hr>
<ol>
<li id=""fn1"">
<p>x<a href=""#fnref1"" role=""doc-backlink"">↩︎</a></p>
</li>
</ol>
</section>
".
Proof. vm_compute. reflexivity. Qed.

(*
Block attributes
----------------
*)

Example block_attributes_multiline :
  convert "{#a
 .b}
c
"
  = "<p id=""a"" class=""b"">c</p>
".
Proof. vm_compute. reflexivity. Qed.

Example block_attributes_multiline_unindented :
  convert "{#a
.b}
c
"
  = "<p>{#a
.b}
c</p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Links to headings
-----------------
*)

Example heading_identifier_footnote :
  convert "# Introduction[^1]

[^1]: n
"
  = "<section id=""Introduction"">
<h1>Introduction<a id=""fnref1"" href=""#fn1"" role=""doc-noteref""><sup>1</sup></a></h1>
</section>
<section role=""doc-endnotes"">
<hr>
<ol>
<li id=""fn1"">
<p>n<a href=""#fnref1"" role=""doc-backlink"">↩︎</a></p>
</li>
</ol>
</section>
".
Proof. vm_compute. reflexivity. Qed.

Example heading_identifier_symbol :
  convert "# a :sym: b
"
  = "<section id=""a-b"">
<h1>a :sym: b</h1>
</section>
".
Proof. vm_compute. reflexivity. Qed.

Example heading_identifier_unique :
  convert "# a

# a
"
  = "<section id=""a"">
<h1>a</h1>
</section>
<section id=""a-1"">
<h1>a</h1>
</section>
".
Proof. vm_compute. reflexivity. Qed.

(* "removing punctuation (other than `_` and `-`)" as djot.js reads it:
   a punctuation byte separates words as a space does, and `:` and `;`
   stay (`is_id_sep_punct`, Document.v). *)
Example heading_identifier_punctuation :
  convert "# a.b  c:d;e_f-g!
"
  = "<section id=""a-b-c:d;e_f-g"">
<h1>a.b  c:d;e_f-g!</h1>
</section>
".
Proof. vm_compute. reflexivity. Qed.
