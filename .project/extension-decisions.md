---
ai-disclosure: ai-generated
---
# Extension decisions

Standing log of semantic decisions for behaviour **djot does not have**.
Undated, per `.project/README.md`: it reflects the current state, and an
entry that stops being true is edited, not appended to.

## Why this is not `djotjs-divergences.md`

That log adjudicates cases where two implementations that both exist
disagree, or where one contradicts the prose. Its verdicts name an
authority (`djoths-outdated`, `djotjs-bug`, `SPEC-GAP`) and it is
append-only, because it records history.

Here there is no authority by construction: these are choices about
syntax djot does not implement, so
[[project-engineering-lessons#Ask djot.js]] has nothing to ask. Its
replacement is the discipline below. The two logs also have opposite
lifecycles: a djot.js divergence is a fact about the past, an extension
decision is a *live constraint* on the config family that every later
table entry has to keep satisfying.

## Discipline

1. **Every entry pins djot's current behaviour first.** The extension is
   only meaningful against a baseline, and by
   [[260811.inline-parser]] §0.1 the baseline is usually *not* "this
   is a syntax error" but some other valid reading that the extension
   displaces.
2. **Every decision is pinned by an `Example`, not by this prose.** Prose
   drifts; a compiling `Example` does not. This file is an index into
   those examples plus the argument for each. An entry with no example
   reference is either open or a bug.
3. **A decision is only settled once it has a reason that is not taste.**
   Acceptable reasons: it falls out of a theorem we want (the usual
   case), it preserves a stated invariant, or it is forced by
   conflict-freeness. "It looks nicer" is not one; leave it open instead.
4. **Non-conservative decisions are labelled as such.** If enabling a
   flag changes the meaning of a document that is already valid djot,
   that is a compatibility fact users need, and it is the thing the
   config family exists to keep honest.

## Baseline: doubled delimiters in djot today

Pinned from djot.js v0.3.2, 2026-08-11. These are *not* decisions; they
are what the extension has to be stated against.

| input | djot today |
| ----- | ---------- |
| `__a__` | `<em><em>a</em></em>` |
| `___a___` | three nested `<em>` |
| `____a____` | four nested `<em>` |
| `__a_` | `_<em>a</em>` |
| `_a__` | `<em>a</em>_` |
| `__` | literal `__` |
| `____` | literal `____` |
| `x__a__` | `x<em><em>a</em></em>` |
| `__a__b__` | `<em><em>a</em></em>b__` |
| `*a*` | `<strong>a</strong>` |
| `**a**` | `<strong><strong>a</strong></strong>` |
| `2*3*4` | `2<strong>3</strong>4` |

These are now pinned as `Example`s in `theories/Inline.v` (`emph_run_*`),
per discipline 2. Pinning them found that **we did not implement them**:
`oclose_go` treated a matching-but-empty scope as a scope to abandon,
dissolving its opener into text and searching deeper, so `___a___` came
out `<em>_</em>a<em>_</em>` and `____` came out `<em>_</em>_`. djot.js
looks at the top of the opener stack and nowhere else (inline.ts:145),
and an empty top means *no close* -- the opener stays and the closer
becomes an opener. Fixed before any of the table work, since step 7
generalizes exactly this function.

The rule these come from: each `_` is an **independent delimiter that
stacks**, not a run whose length is measured. `can_open` needs a nonspace
to the right, `can_close` a nonspace to the left (`inline.ts:110-112`),
and empty emphasis is excluded (`inline.ts:141`), which is the whole of
why `__` and `____` are literal.

That "no run arithmetic anywhere" property is precisely what djot's
rationale bought by banning doubled delimiters, and it is what the
extension spends. Worth being explicit that this is the trade, because
it is the reason CommonMark's emphasis rules are what they are.

## Open: `E1`, doubled strong emphasis

**Ask.** [[beyond-djot]]: allow a doubled delimiter for strong where the
strong character differs from the emphasis character, configurably, with
djot as the instance that disables it.

**The tables this ships.** The point is not "a knob"; it is named
configurations, all inhabitants of one family. `markdown_like_config` is
djot's table with the strong row changed, and nothing else: every djot-only
container stays on, and switching one off is a separate knob.

| | emphasis | strong | a lone `*` |
| --- | --- | --- | --- |
| `djot_config` | `_` | `*` | strong |
| `markdown_like_config` | `_` | `**` | literal text |

The second is Markdown's *spelling* with djot's *semantics*: no run-length
arithmetic, no flanking rules, no "three means both". A character belongs
to one row at one width, so there is nothing to disambiguate -- which is
djot's property, and keeping it is the whole reason the extension is a
table rather than a set of rules. The visible payoff is that `2*3*4` is
literal text rather than emphasis around the `3`.

Everything else stays djot's, deliberately. In particular there is **no
word rule**: `he_ll_o` emphasizes `ll` in both tables, because djot's
`can_open` / `can_close` are one whitespace test each and its `opentest`
slot is `alwaysTrue` for these rows (`inline.ts:284-315`). A reader who
wants the other reading writes `he{_ll_}o`, which is djot's own
mechanism, unchanged. Adding a CommonMark-style word rule was
considered and dropped: it buys a familiarity that costs a second
condition on both sides of every bare delimiter, and the ambiguity it
exists to prevent is already prevented by one character having one
width.

**Status: settled and pinned.** The table is now a record (`dconfig` in
`theories/Inline.v`) carrying, per row, the character it is written
with, how wide it is and how it may be written; `djot_config` and
`markdown_like_config` are its two inhabitants. `dstyle_of` looks a character
up in the table instead of repeating it, so the character assignment
lives in one place.

A row now carries a **width** as well as a character, and its delimiter
is that many copies of it (`dtoken`). The scanner spells tokens: a run of
the character is cut into tokens of the row's width and any remainder is
text, which is why a width suffices and a general string is not needed --
the character belongs to one row, so there is nothing to disambiguate.
`IDelim` counts the characters that have arrived after the first, so no
state ever holds an empty token.

The pieces, in the order they bite:

1. **Scanning a token: done.** `iscan_chars_delim` walks the counter up
   through the row's characters, `iscan_dtoken` scans a whole token from
   text and leaves it complete with its role undecided, and
   `iscan_marked_close_step` closes a marked span on token-then-`}`.
   These replace `istep_marked_close`, which was a single `istep` and so
   silently assumed one character; the three call sites now go through
   them. The only hypothesis is that a row has a token at all
   (`dwidth k <> 0`).

2. **The canonical renderer: done.** `ci_src` and `inline_text` both
   spell a delimiter as `marked_open` / `marked_close`, so what the
   renderer writes is what the scanner reads at any width. The expected
   cost -- restating the three decompositions that had been written in
   the one-character form -- came in smaller than the estimate: with
   `marked_close_app` (a close with an empty tail absorbs what follows)
   each is two lines, and every proof that merely *carried* the spelling
   was untouched, since `cbn` never had to see through it. `dwidth_nonzero`
   replaces two unfoldings of djot's table with one fact checked in one
   place.

3. **The marked open: done.** Found by building at a two-character
   table, where `iscan_marked_open` stopped being provable:
   `ibrace_step` matched `dstyle_of c` on the byte after `{` and pushed
   the scope there and then, so at width two the push came a character
   early and the rest of the token was scanned as text. `IDelim` now
   carries a `marked` flag and the braced open enters it like the bare
   one, through `idelim_marked`, which pushes the moment the row's width
   is reached -- so a marked state is never a *complete* token, and the
   branch that reads `canclose` is the one it never reaches. A partial
   token decays through `idelim_run`, which puts the `{` back.

   The cost was a field, not a constructor: nothing gained a case, and
   the exhaustive matches took one more `_`. The four proofs that did
   move (`istep_out_app`, `iscan_wf_step`, `iscan_wf_resolve`,
   `iscan_productive_step`) all moved for the same reason, and it is one
   worth recording -- **at width one the partial-token branch is
   statically dead**, since `S seen <? 1` reduces to `false` whatever
   `seen` is, so `cbn` used to discharge it silently. Widening the table
   is what makes those branches reachable, and each wanted the same three
   facts: `idelim_marked_out_app`, `idelim_marked_wf`,
   `idelim_marked_productive`.

4. **The table's obligations, as a checkable condition: done.**
   Threading turned out to have a half that had to come first, and it is
   the half with the content. Many facts the scanner uses were being
   proved *by computing on djot's table* -- `dwidth k <> 0`, "a row's
   character is punctuation", "a row's character is not a backtick",
   "a row's character finds that row again" -- and each would have become
   an unprovable goal the moment the table was a variable.

   `dconfig_ok` now checks four conditions rather than one: rows are
   unambiguous (as before), and every row is *written* (nonzero width),
   *escapable* (its character is punctuation) and *free* (its character
   is not one of the seven the scanner claims for itself, which is now
   `dreserved`). `config_ok` is the single `vm_compute` on the table in
   force, and every other fact is derived from it. So pointing `config`
   at another table re-checks all of it at once, and threading becomes
   the mechanical edit it was supposed to be: `config_ok` turns into the
   hypothesis each statement carries.

   Two things fell out that are worth having on their own. `needs_escape`
   is now literally `dreserved || is_delim` -- the two kinds of claimed
   character -- and its punctuation obligation splits along that seam
   instead of brute-forcing 256 bytes through the table. And **`ci_ok`
   now requires a delimiter's row to be switched on**: `ci_src` spells a
   switched-off row exactly like a switched-on one, so without the
   condition the canonical view would render `{+a+}` for a table that
   reads it as text. That is what makes `DOff` mean something -- turning
   a row off removes it from the canonical view too, which is "which
   containers exist is a setting" done properly rather than announced.

   Conditions 2 to 4 are asked of every row, not only the enabled ones.
   That was the cheap spelling: asked only of enabled rows, "has a token"
   would have needed "this row exists" as a hypothesis on a dozen
   scanning lemmas and then on the productivity and well-formedness
   chains behind them. Asked of all rows, the tax is that a table must
   spell even a row it does not use with something admissible.

5. **Threading, the inline layer: done.** The table is now a parameter.
   `dtable` is a class carrying a `dconfig` *and* its `dconfig_ok` proof,
   so an instance is admissible or it does not exist, and `Inline.v`'s
   whole general half is a section over one. `djot_table` is an exported
   instance and `markdown_like_table` is a plain definition, named where it is
   wanted -- two instances of one class in scope is how the wrong table
   gets inferred.

   A class rather than a section variable, and that is the whole reason
   the step was affordable: the argument stays implicit, so not one call
   site downstream changed. `Wf.v` alone mentions inline-layer symbols
   245 times, and an explicit parameter would have been 245 edits there
   before counting the rest.

   `dev/check/Markdown.v` is the payoff. It used to need a recipe -- point
   `config` at the second table, truncate the djot examples, rebuild --
   and now it names `markdown_like_table` in its notations and compiles
   against the ordinary build, beside djot's own examples.

   One fact fell out of the discharge that is worth keeping: `ci_inlines`
   takes **no** table argument, while `ci_line`, `ci_ok`, `escape_str`
   and `parse_inline_line` all do. The AST a canonical inline denotes is
   the same whatever spells it; only the source and the acceptance
   predicate depend on the table. That is the roundtrip read backwards,
   and Rocq's section discharge noticed it without being asked.

6. **Threading, the layers above: done.** Eight files -- `Step.v`,
   `Uniformity.v`, `ListUniformity.v`, `OrderedList.v`, `Document.v`,
   `Render.v`, `Wf.v`, `Roundtrip.v` -- are now sections over a `dtable`,
   because `para_inlines` is what a paragraph is made of and so
   `parse_lines` itself depends on the table. The headline statements
   quantify over it:

   ```coq
   roundtrip_blocks : forall (T : dtable) (cbs : list cblock), ...
   roundtrip_doc, list_uniformity, wf_parse, wf_parse_doc,
   prefix_determinism, no_future_line_dependence, quote_uniformity : likewise
   ```

   `dev/check/Markdown.v` closes the loop by *applying* them:
   `md_roundtrip_blocks` is `@roundtrip_blocks markdown_like_table`, the same
   proof term at the other instance. Not a rebuild -- the rebuild audit
   could only ever say "the script still works"; this says the theorem
   holds of the family and names two inhabitants.

   Each file's concrete examples sit after its `End`, where inference
   finds djot's instance, so they read exactly as before. Two files
   needed a second section for the material *after* their example block
   (`Uniformity.v`'s determinism theorems, `Roundtrip.v`'s document-level
   roundtrip); missing that is silent, since the statement still
   typechecks -- it just quietly means djot. Checking is one `Check
   @thm`, and it is worth doing for anything that matters.

   Left specialized on purpose: `OrderedList.v`'s trailing corollaries
   (roman and alpha numbering at concrete marker shapes, interleaved with
   their examples) and `Generate.v` (a corpus generator for djot's own
   test harness). Neither is about delimiters.

   `Html.v` needed nothing: `render_html` renders an AST and never
   consults the table, so the discharge gave it no parameter.

**Where the second-table build stops.** Every general statement in
`Inline.v` and every file downstream of it -- `Wf.v`, `Roundtrip.v`,
`Parser.v`, the renderer -- compiles under `markdown_like_config`, and also
under a table that additionally switches a row off. Measured by pointing
`config` at it, truncating `Inline.v`'s pinned examples and building the
rest: what fails is exactly those examples, which spell djot's `*a*` as
strong and are supposed to be about djot. So the roundtrip theorems are
already theorems about a two-character strong delimiter; what threading
buys is saying so in the statements rather than by rebuilding.

**Settled so far:**

- *The extension is non-conservative.* Every string the second table
  reads differently is already a valid djot document: `*a*` is strong in
  djot and literal under `markdown_like_config`, `**a**` is nested strong
  there and one strong span here. So the theorem cannot be "we extend
  djot"; it is "djot's table and the Markdown-like table are both
  inhabitants of a family satisfying the same invariants".
- *The sufficient condition has a name, and is now stated and proved.*
  "Strong character differs from emphasis character" is one instance of
  the whole table being unambiguous: no two rows that are switched on
  claim the same character. That is `dconfig_ok`, a decidable check on a
  table, and `dstyle_at_dchar` is what it buys -- a row's own character
  finds that row again, which is the only fact about the table the
  scanner needs. `djot_config_ok` and `markdown_like_config_ok` check it;
  `clashing_config_not_ok` shows it has teeth, and
  `clashing_config_ok_when_off` shows switching a row off frees its
  character.

  The condition is also local now. `update_drow` replaces one `dentry`, and
  `drow_update_compatible` checks exactly what is not inherited from the
  input table: the new row is intrinsically valid and its trigger differs
  from every unchanged enabled row. `update_drow_preserves_admissible` proves that
  check sufficient. `markdown_like_config` is the update of djot's strong row to
  `markdown_strong_entry`; executable controls reject a clash with `_`, a
  scanner-reserved backslash, and width zero.

- *A row can be switched off.* `dsyntax` is three-valued -- off, braces
  required, braces optional -- where the old `dbare` was a boolean.
  Djot's rows are all on: braces required for `{= =}` and `{+ +}`,
  optional for the rest. Off is what makes "which containers exist" a
  setting rather than a fixed list.

- *Switches compose.* `disable_rows` lifts the single-row preservation
  theorem over an explicit list. No shipped profile disables a row;
  `dev/check/Capabilities.v` disables all seven djot-only containers and
  pins their literal reading and rejection from the canonical fragment.

**The open sub-questions, now measured.** `dev/check/Markdown.v` pins
`markdown_like_config`'s behaviour -- thirty examples, with the two-step
recipe in its header (point `config` at it, truncate `Inline.v`'s
djot-specific examples, compile). No existing implementation can adjudicate any of this:
djot.js has no doubled row, so the evidence is what our own table does,
which is why it is pinned rather than described.

- `***a***` gives `<strong>*a</strong>*`. A run *is* cut into tokens from
  the left, and the remainder's fate is **not symmetric**: the leading
  extra `*` lands inside the span, because it is read after the opener
  has been taken; the trailing one lands outside, because the closer is
  taken first.
- `****a****` nests, one level per *token* rather than per character --
  the same answer a one-character row gives to `____a____`, restated at
  the right granularity.
- `**` and `****` are literal, and so is `{**a*}`. This is the half that
  was open, and it needed no restatement at all: `oclose_go` asks whether
  the *top scope is empty*, not how far the opener ended from `pos`, so
  djot.js's `opener.endpos !== pos - 1` -- which measures a one-character
  gap and would have had to become `opener.endpos + length(delim) - 1` --
  has no counterpart here. The exclusion generalizes for free because it
  was never stated in positions.

**The compatibility fact**, which is what discipline 4 asks for: what
changes under `markdown_like_config` is every document that used `*` for
strong. `*a*` is literal text there, and `**a**` is one strong span where
djot reads nested strong. Emphasis is untouched, since `_` is emphasis in
both tables. The change is loud rather than silent -- a document whose
meaning moves usually goes *literal*, which is visible in the output.

The braced form works at width two (`{**a**}` is strong; `{*a*}` and
`{**a*}` are literal, with the `{` back in front), and the canonical view
round-trips there: `{**a**}` and `{_a{**b**}_}` parse back to what
rendered them, which is the behavioural half of what the proofs say.

**Decided by construction, where it used to be open:** whether `*`
remains available as strong at width one when `**` is strong. It does
not, and this is no longer a preference. A character belongs to one row
(`dconfig_ok`, with `dstyle_at_dchar` the fact the scanner uses) and a
row's width is a field rather than something negotiated per run, so "one
delimiter at one length" is what the table *can* express, not what we
chose to allow. `md_single_star_is_text` is the behaviour. That is also
what keeps the run arithmetic out, which the baseline section names as
the extension's cost -- and it is what makes `2*3*4` literal without any
rule about what surrounds the asterisks.

## Settled: `E2`, a list marker that interrupts a paragraph

**Ask.** [[beyond-djot]]: in djot a sublist must always be preceded by a
blank line; make that optional under a flag, with the question "how does
the list-uniformity hold under this new rule?" attached.

**The baseline, first.** Not "a list needs a blank line". A *sibling*
marker already interrupts with no blank, because the list container's
continuation rule sees the line before the paragraph does. What djot
refuses is a marker arriving while a paragraph is open, wherever that
paragraph is:

| input | djot today |
| ----- | ---------- |
| `- a` / `- b` | two items |
| `- a` / `  - b` | one item whose text is `a` / `- b` |
| `- a` / blank / `  - b` | one item containing a nested list |
| `p` / `1. one` | one paragraph |

**The decision, and it is not taste.** The rule is stated over the open
paragraph and *without reference to the enclosing container*. Restricting
it to sublists -- which is what the ask says literally -- falsifies
`list_uniformity`, whose conclusion is that an item's lines parse as they
would at top level: a marker cannot mean one thing inside an item and
another outside. Stated container-blind, the theorem is untouched and now
reads `forall (T : dtable) (K : bconfig) ...`. That is the answer to the
question [[beyond-djot]] attached to the ask.

The price is that the extension is **not conservative**, and the ask as
posed cannot be made conservative: `p` / `1. one` is valid djot today
with a different meaning.

**The two knobs this ships.**

| | a bullet | `1.` | any other numeral |
| --- | --- | --- | --- |
| `djot_bconfig` | never interrupts | never | never |
| `sublist_bconfig` | interrupts | interrupts | never |

The third column is the whole of the restriction, and it is settled by
the corpus rather than by preference. Of 291 corpus cases, five contain a
paragraph whose interior line is a marker. Four are the sublist shape the
ask is about. The fifth is `lists.test:33`:

```
The civil war ended in
1865. And this should not start a list.
```

which is djot's own regression test for the accidental list, with its
intent written into the input. Admitting `1` and no other numeral keeps
it prose, and the test is line-local -- the marker's own numeral, no
context and no state -- so nothing about single-pass scanning moves.

**The compatibility fact** (discipline 4): under `sublist_bconfig` every
document containing a paragraph line that begins with a bullet or `1.`
changes meaning, and the change is silent rather than loud -- prose
becomes a list rather than becoming literal text. Four corpus cases move,
all of them intentionally. Prose ending in any other number, in a roman
numeral or in an initial is untouched.

At the configuration boundary, `block_prefix_ok` also checks that a marker
setting admitting the bodyless `-` bullet is not combined with an underline
setting admitting the same lone dash. `bmarker_update_compatible` is the local
obligation when this setting is installed.

**What it costs the canonical view: nothing.** `para_ok` gains one clause
(an interior line is not a marker the knob acts on) and it is discharged
by escaping that predates the knob: `cline` writes `- b` as `\- b`, which
classifies as text at every setting. Filtering the generated pool by
`cb_ok` gives the same 245 and 2910 at all three knobs, which is what the
marker-shaped leaf in `Generate.leaves` exists to say.

**Status: settled, pinned, and proved as a configuration property**, in
`dev/check/Sublist.v` per discipline 2 --
`djot_swallows_the_marker`, `sublist_nests_without_a_blank`,
`sublist_interrupts_at_top_level`, `any_marker_invents_a_list`,
`sublist_leaves_the_year_alone`, and `sublist_roundtrip_blocks`, which is
`roundtrip_blocks` applied to the other knob rather than reproved. The
argument and the measurements are in
[[260823.phase4-block-knob]].

The Phase 5 refinement is `Invariants.accidental_list_immune`.  Its extracted
local condition, `marker_interrupt_precondition`, says exactly that a policy
can interrupt only where `prose_safe_markers` does.
`with_marker_interrupts_accidental_list_immune_iff` proves the condition both
necessary and sufficient, rather than presenting it as a conservative recipe.
Thus `prose_safe_markers` is the maximally permissive immune policy;
`sublist_bconfig` is the promised setting strictly more permissive than djot,
and the unrestricted setting is rejected by the `1865.` witness.

**Open inside it.** Whether `i.` should be admitted. It is excluded with
every other numeral today, which keeps `written by` / `i. m. author`
prose; the case for admitting it is that a roman opener is ambiguous
anyway and the list would be one item long. Nothing forces it either way,
so by discipline 3 it stays open.

## Settled: `E3`, setext headings

**Ask.** [[beyond-djot]]: bring back setext-style (underlined) headings.

**The baseline, first.** djot has no underline rule at all, so both lines
are prose -- and `---` is not even inert, since smart punctuation reads
it as an em dash:

| input | djot today |
| ----- | ---------- |
| `a` / `===` | one paragraph, `a` then `===` |
| `a` / `---` | one paragraph, `a` then an em dash |
| `a` / `-` | one paragraph (a lone `-` is a bullet marker, and markers do not interrupt) |
| blank / `---` | a thematic break |

**Where it landed, against the prediction.** [[260823.phase4-block-knob]]
§8 guessed this would be "a different shape -- it needs the *previous*
line, which the paragraph accumulator has but the classifier does not".
Half right. It does need the previous lines, and that is exactly why it
belongs in the same place the sublist setting does: the open-paragraph
branch of `step` *is* the accumulator, so the heading's text is already
in hand and the underline test is line-local. What it does not need is a
new `line_kind`. The kinds an underline can wear are taken -- `===` is
`KText`, `---` is `KThematic`, `-` is a bullet -- so `underline_of` is a
query beside `classify` rather than a case inside it, which also keeps
`line_kind` from widening (the cost recorded in
[[project-engineering-lessons#A hang or a sudden slowdown is the
definition's shape]]).

**The setting.**

```coq
Definition setext_underline (c : ascii) (n : nat) : option nat :=
  if Ascii.eqb c "=" then Some 0                                  (* level 1 *)
  else if Ascii.eqb c "-" then (if Nat.leb 2 n then Some 1 else None)
  else None.
```

`Some k` means level `S k`, so a setting cannot ask for a level-0
heading and `wf_block`'s `1 <= lvl` holds without a class law -- the same
trick that keeps `bmarker_interrupts` from needing one.

**Why `-` needs two.** Not a style choice. `classify "-"` is `KList`, so
a lone `-` already answers to the sublist setting; admitting it here
would put one line under two settings and make the answer depend on the
order `step` tests them in. At two or more there is no other reading.
`a` / `--` is a level-2 heading, `a` / `-` stays prose
(`a_single_dash_is_not_an_underline`).

This is machine-checked by `block_prefix_ok`; `bunderline_update_compatible`
is the local obligation for installing an underline setting, and an
executable counterexample rejects a setting that admits the lone dash over
`sublist_bconfig`.

**Only an open paragraph underlines**, which is the whole of why a
thematic break survives: with nothing above it, `---` is classified as it
always was. And because the rule is stated over the paragraph rather
than over the document, it works inside a quote or a list item without
saying so -- the same property that keeps `list_uniformity` true at every
setting.

**The compatibility fact** (discipline 4): `a` / `---` and `a` / `===`
are valid djot today and change meaning. **Zero of the 291 corpus cases
contain the shape** -- no case has a nonblank line followed by a line of
`=` or of two-or-more `-` -- so nothing in the corpus moves, but that is
a fact about the corpus, not a conservativity claim.
[[project-engineering-lessons#The corpus is djot.js's regression suite]]
is the reason to say it that way round.

**What it cost the canonical view: nothing**, again, and for the same
reason: `cline` escapes both `=` and `-`, so a canonical paragraph never
contains a line that could be an underline. Filtering the generated pool
by `cb_ok` gives the same 245 and 2910 at djot's settings, at
`sublist_bconfig` and at `setext_bconfig`.

**The one refactor it forced, and it is an improvement.** `para_ok`'s
side condition and `step_para_cont`'s hypothesis were both about list
markers; they are now about `bcuts`, the single question "does a setting
take this line out of an open paragraph". A third setting that ends a
paragraph extends `bcuts` and touches nothing else.

**Status: settled and pinned** in `dev/check/Setext.v`, closing with
`setext_roundtrip_blocks` -- `roundtrip_blocks` applied to the setting
rather than reproved.

**Open inside it.** Whether a setext heading should be allowed to carry
an attribute block, and whether the underline should be renderable at
all: the canonical renderer writes every heading `# ` style, so a setext
heading round-trips as an ATX one. That is a choice (the AST does not
record which spelling it came from) and it is the one that keeps the
renderer knob-independent, but it means the extension is input-only.

## Deferred asks

From [[beyond-djot]], not inline and not this file's business yet: link
references. They get entries here only if they turn out
to need a decision no existing implementation can settle.

## Settled: `E4`, tables as a profile capability

**Ask.** A profile should be able to leave djot tables out. Core CommonMark
defines no table construct; GFM adds pipe tables but no caption syntax. The
ask came from an earlier Markdown-like profile that removed tables; that
profile now keeps them (see the profiles entry below), so `btables` is a
capability every shipped profile leaves on.

**Boundary.** `Line.classify` continues to recognize a syntactic row as
`KRow`; classification is shared evidence, not a feature decision. A new
block setting answers one question at `Step.open_kind`: does `KRow` open a
`PTable`, or does its complete source line open an ordinary paragraph?
Continuation of an explicit `PTable` state is unchanged. This keeps the gate
at one entry point and preserves the meaning of state-based theorems.

**Canonical consequence.** `Render.cb_ok (CTable rows)` must include the same
setting. When tables are off, canonical tables are outside the roundtrip
domain; ordinary paragraphs containing pipe-row source remain inside it and
are escaped only as existing paragraph rules require.

**Predicted obligations.** The idle-row equation gains the setting premise;
the three table fold equations do not. The all-state `step` proofs split the
new boolean only in their `KRow` case. The canonical table cases in
`Roundtrip.v` receive the enabled fact from `cb_ok`. No AST, classifier, table
assembly, caption, or renderer data type changes.

**Status: settled and pinned.** The prediction held. `btables` is the third
field of `bconfig`; `with_tables` preserves block incrementality and the
lone-dash compatibility invariant. Djot and the individual sublist/setext
profiles keep it enabled, and so does `markdown_like_bconfig`.
`dev/check/Capabilities.v` pins a two-row table spelling as one paragraph with
tables off and checks that `CTable` is then outside the canonical fragment.
Typography stays independent of tables: `with_smart_typography false` makes
`---` literal without touching tables.

## Settled: single-line ATX headings in the Markdown profile

Djot lets a same-level heading marker or a plain text line continue an open
heading. This makes `# a` / `# b` one heading, a silent surprise for Markdown
authors. `bheading_continues` now states that choice explicitly: djot keeps it
enabled and `markdown_like_bconfig` disables it.

The disabled transition closes the heading and opens the current line exactly
as the idle state would, without a second source read or another fuel step.
`heading_ok` admits multiple canonical source lines only when continuation is
enabled; at the Markdown setting it requires exactly one. The roundtrip proof
therefore splits locally between the old accumulation lemma and an empty
rendered suffix, while block incrementality and prefix compatibility remain
parametric. `dev/check/Markdown.v` pins adjacent headings, lazy text, and both
sides of the canonical-view boundary.

## Settled: profiles are open compositions, and divs are optional

`Profile.profile` pairs a `dtable` with a `bconfig`; it is not an enum.
`djot_profile` and `markdown_like_profile` are reviewed starting points, while
`with_inline_profile` and `with_block_profile` retain arbitrary combinations
of the fine-grained knobs.

The Markdown-like profile extends djot: it adds `**` strong, setext
underlines and sublists without a blank line, and makes ATX headings one
line, and it switches nothing off. A capability is disabled only where a
Markdown spelling needs it, and heading continuation is the one such case.
Removing a djot construct is a knob a caller applies to either profile
(`dev/check/Capabilities.v`), not part of a profile's definition. Every
guarantee the development proves (roundtrip, well-formedness, block
incrementality, single-pass inline scanning, wrap neutrality) holds at
every setting of these knobs, so a profile's choice among them is a
default, not a restriction.

Fenced divs were the first djot-only block construct given a switch.
`bdivs` acts only at `KDiv` opening, and `cb_ok` excludes `CDiv` at the same
setting.

Task lists deliberately do not receive a nominal boolean in this step. Their
classifier erases `[x]` versus `[X]`, source that is required when task syntax
falls back to literal bullet content, and their per-item statuses remain the
one deferred canonical-roundtrip case. GFM tables similarly wait for a
distinct recognizer before `btables` becomes a dialect mode.

## Pinned, not yet reviewed: custom tag names

**Ask.** <https://github.com/jgm/djot/issues/240>: a div and a span each gain a name, `::: details`
and `:kbd[...]`. Specified in [[custom-tags]]; the reasoning for each
decision is [[261001.plan.custom-tags]]'s, which an agent wrote and no
human has reviewed yet. The entries below are pinned by examples in
`dev/check/Tag.v` and stay "not yet reviewed" until that review.

**Baseline.** `baseline_inline_alone`, `baseline_inline_then_bracket`,
`baseline_inline_not_a_name`, `baseline_div_word_is_a_class`,
`baseline_two_words_is_not_an_opener`, all checked against djot.js.

**Non-conservative.** Both halves: every `::: word` and every
`:symbol-chars[` not right after a letter, digit or colon changes
meaning. The setting is off in both named
profiles (`names_off_in_named_profiles`).

| | decision | pinned by |
| --- | --- | --- |
| D1 | the name is a string field on `Div` and `Span`, empty meaning unnamed | `div_named_div_is_not_unnamed`, `tagged_nesting` |
| D2 | the inline spelling is `:name[...]`, decided at the `[` from the symbol state; not right after a letter, digit or colon (amended in review, 2026-10-03) | `tagged_inline_rows`, `tagged_not_a_name`, `tagged_not_after_a_word` |
| D3 | `]` closes a named bracket at once | `tagged_close_is_immediate` |
| D4 | names are recorded as written; an empty inline name is not a name | `tagged_not_a_name`, `div_word_is_a_name` |
| D5 | `::: div` is named `div` | `div_named_div_is_not_unnamed` |
| D6 | HTML uses the name only for elements with ordinary content, else `data-tag` | `html_names`, `html_fallbacks`, `Html.named_elem_cases` |

**Consequences pinned alongside.** A name sits beside a pending class
(`div_name_beside_a_class`); unclosed or captured named brackets decay
(`tagged_decay`); a named bracket interacts with delimiters as a bracket
does (`tagged_with_delimiters`) and is never taken back for a note
(`tagged_not_a_note`). The roundtrip holds at the profile
(`tag_roundtrip_blocks`).
