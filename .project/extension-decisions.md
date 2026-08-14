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

The remaining work is in two named pieces. The table is a fixed
`Definition config` rather than an argument, so a configuration is chosen
at build time; threading it is mechanical and is what makes every
statement quantify over the family. And a row's delimiter is still one
character, so `__` for strong needs the row to carry a *token*.

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

**Open sub-questions, each needing an example before it is settled:**

- `___a___` under `emph=*, strong=__`. Longest-match from the left gives
  `__` then a literal `_`. Not yet argued for.
- `____a____`. Checked first, as flagged. **Half-answered.** For a single
  character the exclusion does generalize to arbitrary run length: four
  `_` around content nest four deep and a bare `____` is literal, both
  now pinned (`emph_run_four`, `emph_run_bare_four`). So the rule "an
  empty top opener declines to close" is length-independent, which is the
  reassuring half. The open half is unchanged and is genuinely about
  *multi-character* delimiters: with `strong=__`, the exclusion has to be
  phrased on the delimiter's own extent rather than on `pos - 1`, since
  `opener.endpos !== pos - 1` measures a one-character gap. The
  restatement is `opener.endpos + length(delim) - 1 !== pos - 1`, and it
  needs an example before it is settled.
- `__a_` becomes literal (no closer) where djot gives `_<em>a</em>`.
  Consequence of the above, not an independent choice, but it belongs in
  the compatibility note.

**Explicitly not decided here:** whether `_` remains available as
emphasis when `__` is strong. Allowing both reintroduces exactly the run
arithmetic the baseline section says is the cost, so the default should
be that a character is a delimiter at one length only, but that is a
claim about conflict-freeness and it should be *proved* rather than
declared.

## Deferred asks

From [[beyond-djot]], not inline and not this file's business yet:
setext headings, optional blank line before a sublist (with its
list-uniformity question), link references. They get entries here only if
they turn out to need a decision no oracle can settle.
