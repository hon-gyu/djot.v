---
ai-disclosure: ai-generated
---
# The inline grammar

A grammar for the precedence rules, the third statement of them beside
`valid` (the rules as conditions on a reading) and `ref_read` (a stack
machine), both in `theories/Precedence.v`, with their proofs in
`theories/PrecedenceFacts.v`.  It is the one to learn the
rules from: each rule is a clause of the syntax reference, and a
paragraph's reading is a derivation you can write by hand.

**Status: proved** (2026-10-12).  The grammar
is the relation `seq` in `theories/PrecedenceGrammar.v`, and
`theories/PrecedenceGrammarFacts.v` proves, for every string:

| Theorem | Statement |
| --- | --- |
| `parses_ref_read` | `parses s r <-> r = ref_read s` |
| `parses_valid` | a parse is a valid reading |
| `valid_parses` | the valid reading has a parse, with its pairs and its openers |
| `parses_unique` | two parses are the same reading |

There is no condition on the alphabet: the grammar reads tokens, and
the theorems hold of whatever `tok_at` gives.

## Maintenance

The grammar reads a token only through `opens_as`, `closes_as` and where
its region ends.  A new token kind that neither opens nor closes adds a
case to `rstep` that returns the state, and the proofs go through
unchanged.  A new kind of opener, closer or region changes `rstep` and
`chain_next`, and with them a rule here, a constructor of `seq` and the
lemmas `rstep_text`, `rstep_open`, `rstep_close` and `rstep_cases`.

## What it reads

A paragraph's tokens (`tok_at`), not its bytes.  A parse walks them by
byte offset as a reading's chain does: from where the last token ended, or from past a region.  The
lexer has already settled what each token *may* do:

- a delimiter may open, close, or both (flanking, M2; braces, P3; a
  bare single quote opens only where no apostrophe can be meant, Q1),
  and its kind is its style and whether it is braced (P4), so `{_` and
  `_` never pair;
- `[` may open, and so may `![`, an image's bracket of the same kind;
  `]` may close when a region follows it that closes: `(` and a
  destination to its first `)` that closes no `(` inside it, `[` and a
  label to the next `]` not escaped, or `{` and an attribute spec (a
  span).  Any other `]` is text, and so is any other `!`;
- a verbatim, a backtick run and the bytes to the next run of its
  length or to the paragraph's end, is one token, with any dollars
  before it (math) and a raw spec after it; so is an autolink candidate,
  a symbol, an attribute spec that closes, a footnote reference
  (`[^`, a label and its `]`), a run of periods, and a run of hyphens,
  which before a `}` leaves its last hyphen to be a closer;
- these, escapes, breaks and other bytes are text.

The grammar decides what each token does.

## The rules

A level of the paragraph is `Seq(S, F, p)`:

| | Meaning |
| --- | --- |
| `S` | kinds with a live opener; a closer of one must close |
| `F` | the kind of the pair this is the content of; empty at the top |
| `p` | the kind of a live opener right before, if any |

```
paragraph ::= Seq(∅, ∅, -)

Seq(S, F, p) ::=
  R0  ε                                     at the paragraph's end, or at a closer of F
  R1  text                                  Seq(S, F, -)
  R2  close_k                               Seq(S, F, -)    k ∉ S, or p = k for a delimiter
  R3  open_k                                Seq(S+k, F, k)  k ≠ F
  R4  open_k  Seq(S+k, k, k)  close_k       Seq(S, F, -)    a delimiter: content non-empty
  R5  [  Seq(S+[, [, [)  ]  region          Seq(S, F, -)    the region the `]` was lexed with
```

A token that may both open and close is a closer first: in R2 it closes
nothing and is then read as an opener (R3 to R5).  A closer of a kind in
`S` that is not right after its opener fits no rule at its level: only
R4 and R5 consume it, as the end of a pair's content.  A region is
source: nothing in it opens or closes.

A `](`, `][` or `]{` whose region never closes is text (R1), so a
delimiter after it may close one opened before the `[`, and a later `]`
may close the `[`.  This is the reference's precedence rule applied to
the `(` or `[` as an opener that is never closed, not a rule of its
own.

## As stated in Rocq

| Rule | Constructor of `seq` |
| --- | --- |
| R0 | `seq_end` at the paragraph's end, `seq_stop` at a closer of `F` |
| R1, R2 | `seq_text` |
| R3 | `seq_open` |
| R4, R5 | `seq_pair`; `past` says where the level goes on |

`free` is R2's condition: the token closes nothing, so it is read as an
opener if it may open and as text if not.  A parse lists its pairs and
its openers latest first, as `ref_read` does, so the two are equal as
lists.

Both directions of the proof go through `ref_read`.  A derivation is a
run: the machine follows each rule (`seq_run`).  A run is a derivation:
each opener on the stack heads a level whose tokens so far are settled,
and whether it is R3, R4 or R5 is decided when a closer takes it or
the paragraph ends (`base`, `ginv_step`).  What makes the second
direction work is that a level's tokens between two unmatched openers
are text or whole pairs, and their rules do not mention `F`
(`stretch`).

## Why each part

| Reference (syntax.md, "Precedence") | Grammar |
| --- | --- |
| "the first opener that gets closed takes precedence ... openers between the opener and the closer get marked as regular text" | R4 and R5 continue with the `S` from before the pair: an opener left unmatched inside it is no longer live |
| "Containers can't overlap" | `S` passes into content, so a closer inside cannot be left over while an opener outside is live, and one of the two readings fails |
| "the closest one is used" | `F` in content: no opener of the pair's kind is left unmatched between its ends |
| "some characters besides the delimiter character between the opener and the closer" (M3) | R4's non-empty content, and `p` in R2 |
| `{_` and `_}` (P3), marked with marked (P4) | in the lexer: the token's capabilities and its kind |
| a destination or label after `](`, `][` is part of the link | R5's region |
| a destination or label that never closes | in the lexer: its `]` is text |

`S` passes down and `F` does not: an opener left unmatched outside is
still live inside, but one left unmatched in deeper content dies when
that content's pair closes, before this level's closer.

## Worked examples

`_This is *regular_ not strong* emphasis`, with tokens `_₁ *₂ _₃ *₄`:

```
Seq(∅,∅,-)
├─ R4  _₁ ... _₃             content Seq({_},{_},_): "This is ", R3 *₂, "regular"
├─ R1  " not strong"
└─ R2  *₄                    S is ∅ again: it closes nothing
```

Leaving `_₁` unmatched (R3) puts `_` in `S`, and then `_₃` fits no rule
at the top.  Pairing `*₂` with `*₄` puts `_₃` in content where `_` is in
`S`, and it fits no rule there either.

`*not strong *strong*`: `*₀` by R3, then `*₁ ... *₂` by R4.  With `*₀`
by R4, `*₁` is in content where `F` is `*`, so it cannot be left
unmatched, and pairing it leaves `*₀` no closer.

`__emphasis inside_ emphasis_`: `_₀` by R4.  `_₁` may close, but its
only live opener is right before it (`p`), so it closes nothing and
opens: by R4, since `F` forbids R3.

`*x [u](a* b`: the destination never closes, so the `]` is text.  `*₀`
by R4 with `*₁`, and the content is `x `, `[` by R3, then text.

## Is it a context-free grammar

Over the tokens, yes: `F` and `p` range over finitely many values and
`S` over the subsets of finitely many kinds, so `Seq(S, F, p)` is
finitely many nonterminals with ordinary productions.  Whether a region
closes is decided in the lexer, by a lookahead over bytes.

## How it relates to the other two

| `ref_read` (`rstep`) | `valid` | Grammar |
| --- | --- | --- |
| the kinds on the stack | `live`, `closest_live` | `S` |
| an opener above another of its kind | `closest_live` | `F` |
| the check `tok_end s p < i` | `needs_content`, clause 2 | `p` |
| cutting the stack to `below` on a pair | `dead` | R4 and R5 restoring `S` |
| `rgo` stepping by `chain_next` | `chain` | R5's region |
