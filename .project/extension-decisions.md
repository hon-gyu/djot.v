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
| `**a**` | `<strong><strong>a</strong></strong>` |

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

**Ask.** [[beyond-djot]]: allow `__` for strong where the strong
character differs from the emphasis character, configurably, with djot
as the instance that disables it.

**Status: in progress.** The table is now a record (`dconfig` in
`theories/Inline.v`) carrying, per row, the character it is written with
and how it may be written; `djot_config` is one inhabitant and
`swapped_config` -- emphasis and strong exchanging characters -- is a
second. `dstyle_of` looks a character up in the table instead of
repeating it, so the character assignment lives in one place.

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

3. **The marked open: done.** Found by building at `emph = *,
   strong = __`, where `iscan_marked_open` stopped being provable:
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

4. **Threading.** The table is a fixed `Definition config`, so a
   configuration is chosen at build time. Mechanical, and what makes
   every statement quantify over the family rather than over djot.

**Where the width-two build now stops.** Every general statement in
`Inline.v` and every file downstream of it -- `Wf.v`, `Roundtrip.v`,
`Parser.v`, the renderer -- compiles under `emph = *, strong = __`.
Measured by truncating `Inline.v`'s pinned examples and building the
rest: what fails at width two is exactly the examples, which spell djot's
`_a_` and are supposed to be about djot. So the roundtrip theorems are
already theorems about a two-character strong delimiter; what piece 4
buys is saying so in the statements rather than by rebuilding.

**Settled so far:**

- *The extension is non-conservative.* By the baseline above, `__a__` is
  already a valid djot document meaning nested emphasis. Enabling `__`
  as strong changes its meaning. So the theorem cannot be "we extend
  djot"; it is "djot's table and the extension table are both
  inhabitants of a family satisfying the same invariants".
- *The sufficient condition has a name, and is now stated and proved.*
  "Strong character differs from emphasis character" is one instance of
  the whole table being unambiguous: no two rows that are switched on
  claim the same character. That is `dconfig_ok`, a decidable check on a
  table, and `dstyle_at_dchar` is what it buys -- a row's own character
  finds that row again, which is the only fact about the table the
  scanner needs. `djot_config_ok` and `swapped_config_ok` check it;
  `clashing_config_not_ok` shows it has teeth, and
  `clashing_config_ok_when_off` shows switching a row off frees its
  character.

- *A row can be switched off.* `dsyntax` is three-valued -- off, braces
  required, braces optional -- where the old `dbare` was a boolean.
  Djot's rows are all on: braces required for `{= =}` and `{+ +}`,
  optional for the rest. Off is what makes "which containers exist" a
  setting rather than a fixed list.

**The open sub-questions, now measured.** All three are settled, and by
the same run: `check/Wide.v` is a file of `Example`s built against a
wide table, with the two-step recipe in its header (set `config`,
truncate `Inline.v`'s djot-specific examples, compile). No oracle can
adjudicate any of this -- djot.js has no doubled row -- so the evidence
is what our own table does, which is why it is pinned rather than
described.

- `___a___` gives `<strong>_a</strong>_`. A run *is* cut from the left,
  and the remainder's fate is **not symmetric**: the leading extra `_`
  lands inside the span, because it is read after the opener has been
  taken; the trailing one lands outside, because the closer is taken
  first. `_____a_____` is the same shape one level deeper.
- `____a____` nests, one level per *token* rather than per character --
  the same answer a one-character row gives to four `_`, restated at the
  right granularity. `__a____b__` is a close followed by an open.
- `____` is literal, and so are `__`, `___`, `__ __` and `{__}`. This is
  the half that was open, and it needed no restatement at all:
  `oclose_go` asks whether the *top scope is empty*, not how far the
  opener ended from `pos`, so djot.js's `opener.endpos !== pos - 1` --
  which measures a one-character gap and would have had to become
  `opener.endpos + length(delim) - 1` -- has no counterpart here. The
  exclusion generalizes for free because it was never stated in
  positions.
- `__a_` and `_a__` are literal, as the compatibility note predicted.
  Note the *shape* of the incompatibility: documents whose meaning the
  extension changes go literal rather than parsing differently, so the
  change is visible in the output rather than silent.

Two more facts worth having: the braced spelling works at width two
(`{__a__}` is strong, and `{_a_}` / `{__a_}` are literal with the `{`
back in front), and the canonical view roundtrips there -- `{__a__}` and
`{__a{*b*}__}` both parse back to what rendered them, which is the
behavioural half of what the proofs say.

**Decided by construction, where it used to be open:** whether `_`
remains available as emphasis when `__` is strong. It does not, and this
is no longer a preference. A character belongs to one row (`dconfig_ok`,
with `dstyle_at_dchar` the fact the scanner uses) and a row's width is a
field rather than something negotiated per run, so "a delimiter at one
length only" is what the table *can* express, not what we chose to
allow. `wide_half_token_is_text` is the behaviour: a lone `_` is
literal. That is also what keeps the run arithmetic out, which the
baseline section names as the extension's cost.

## Deferred asks

From [[beyond-djot]], not inline and not this file's business yet:
setext headings, optional blank line before a sublist (with its
list-uniformity question), link references. They get entries here only if
they turn out to need a decision no oracle can settle.
