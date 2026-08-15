---
ai-disclosure: ai-generated
---
# Extension decisions

Standing log of semantic decisions for behaviour **djot does not have**.
Undated, per `.project/README.md`: it reflects the current state, and an
entry that stops being true is edited, not appended to.

## Why this is not `oracle-disagreements.md`

That log adjudicates cases where two implementations that both exist
disagree, or where one contradicts the prose. Its verdicts name an
authority (`djoths-outdated`, `djotjs-bug`, `SPEC-GAP`) and it is
append-only, because it records history.

Here there is no authority by construction: these are choices about
syntax djot does not implement, so
[[project-engineering-lessons#Ask the oracle]] has nothing to ask. Its
replacement is the discipline below. The two logs also have opposite
lifecycles: an oracle disagreement is a fact about the past, an extension
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

**The two tables this ships.** The point is not "a knob"; it is two
named configurations, both inhabitants of one family.

| | emphasis | strong | a lone `*` |
| --- | --- | --- | --- |
| `djot_config` | `_` | `*` | strong |
| `markdown_config` | `_` | `**` | literal text |

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

**Status: in progress.** The table is now a record (`dconfig` in
`theories/Inline.v`) carrying, per row, the character it is written
with, how wide it is and how it may be written; `djot_config` and
`markdown_config` are its two inhabitants. `dstyle_of` looks a character
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
   instance and `markdown_table` is a plain definition, named where it is
   wanted -- two instances of one class in scope is how the wrong table
   gets inferred.

   A class rather than a section variable, and that is the whole reason
   the step was affordable: the argument stays implicit, so not one call
   site downstream changed. `Wf.v` alone mentions inline-layer symbols
   245 times, and an explicit parameter would have been 245 edits there
   before counting the rest.

   `check/Markdown.v` is the payoff. It used to need a recipe -- point
   `config` at the second table, truncate the djot examples, rebuild --
   and now it names `markdown_table` in four notations and compiles
   against the ordinary build, beside djot's own examples.

   One fact fell out of the discharge that is worth keeping: `ci_inlines`
   takes **no** table argument, while `ci_line`, `ci_ok`, `escape_str`
   and `parse_inline_line` all do. The AST a canonical inline denotes is
   the same whatever spells it; only the source and the acceptance
   predicate depend on the table. That is the roundtrip read backwards,
   and Rocq's section discharge noticed it without being asked.

6. **Threading, the layers above.** `Wf.v`, `Roundtrip.v`, `Render.v`,
   `Parser.v` and `Document.v` still resolve the instance to djot's at
   elaboration, so `roundtrip_blocks` is currently a theorem about djot
   rather than about the family. Making it the latter is one `Context`
   line per file plus whatever examples have to move out of the section.
   The rebuild audit says the proofs do not care which table it is; what
   remains is saying so in the statements.

**Where the second-table build stops.** Every general statement in
`Inline.v` and every file downstream of it -- `Wf.v`, `Roundtrip.v`,
`Parser.v`, the renderer -- compiles under `markdown_config`, and also
under a table that additionally switches a row off. Measured by pointing
`config` at it, truncating `Inline.v`'s pinned examples and building the
rest: what fails is exactly those examples, which spell djot's `*a*` as
strong and are supposed to be about djot. So the roundtrip theorems are
already theorems about a two-character strong delimiter; what threading
buys is saying so in the statements rather than by rebuilding.

**Settled so far:**

- *The extension is non-conservative.* Every string the second table
  reads differently is already a valid djot document: `*a*` is strong in
  djot and literal under `markdown_config`, `**a**` is nested strong
  there and one strong span here. So the theorem cannot be "we extend
  djot"; it is "djot's table and the Markdown-like table are both
  inhabitants of a family satisfying the same invariants".
- *The sufficient condition has a name, and is now stated and proved.*
  "Strong character differs from emphasis character" is one instance of
  the whole table being unambiguous: no two rows that are switched on
  claim the same character. That is `dconfig_ok`, a decidable check on a
  table, and `dstyle_at_dchar` is what it buys -- a row's own character
  finds that row again, which is the only fact about the table the
  scanner needs. `djot_config_ok` and `markdown_config_ok` check it;
  `clashing_config_not_ok` shows it has teeth, and
  `clashing_config_ok_when_off` shows switching a row off frees its
  character.

- *A row can be switched off.* `dsyntax` is three-valued -- off, braces
  required, braces optional -- where the old `dbare` was a boolean.
  Djot's rows are all on: braces required for `{= =}` and `{+ +}`,
  optional for the rest. Off is what makes "which containers exist" a
  setting rather than a fixed list.

**The open sub-questions, now measured.** `check/Markdown.v` pins
`markdown_config`'s behaviour -- thirty examples, with the two-step
recipe in its header (point `config` at it, truncate `Inline.v`'s
djot-specific examples, compile). No oracle can adjudicate any of this:
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
changes under `markdown_config` is every document that used `*` for
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

## Deferred asks

From [[beyond-djot]], not inline and not this file's business yet:
setext headings, optional blank line before a sublist (with its
list-uniformity question), link references. They get entries here only if
they turn out to need a decision no oracle can settle.
