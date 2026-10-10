---
ai-disclosure: ai-generated
---
# The inline grammar

A grammar for the precedence rules, the third statement of them beside
`valid` (the rules as conditions on a reading) and `ref_read` (a stack
machine), both in `theories/Precedence.v`.  It is the one to learn the
rules from: each rule is a clause of the syntax reference, and a
paragraph's reading is a derivation you can write by hand.

**Status: not proved.**  It is checked by computation:
`dev/InlineGrammar.v` runs it as an enumerator of parses, and `make
check-grammar` (`test/grammar.ml`) requires every paragraph over the
precedence alphabet to have exactly one parse, with the pairs and the
openers of `ref_read`.  An equivalence with `valid` is to be proved once
the inline specification is complete
(`261007.plan.inline-specification.md`), not stage by stage.

## Maintenance

The grammar covers what `valid` covers, no more.  Each stage of the
inline specification that widens `over_alphabet` extends the grammar
with it: write the new rules here and in `dev/InlineGrammar.v`, add the
new bytes to the pieces in `test/grammar.ml`, and keep `make
check-grammar` at zero differences.  Writing a stage's rules here first
is a cheap way to find their shape before `valid` is extended.

## What it reads

A paragraph's tokens (`tok_at`), read straight through the paragraph by
`para_toks` in `dev/InlineGrammar.v`, not its bytes; a parse's
positions are turned into byte offsets to compare with `ref_read`.  The
lexer has already settled what each token *may* do:

- a delimiter may open, close, or both (flanking, M2; braces, P3), and
  its kind is its style and whether it is braced (P4), so `{_` and `_`
  never pair;
- `[` may open, and `]` may close when `(` or `[` follows it; any other
  `]` is text;
- escapes, breaks and other bytes are text.

The grammar decides what each token does.

## The rules

A level of the paragraph is `Seq(S, F, p, B)`:

| | Meaning |
| --- | --- |
| `S` | kinds with a live opener; a closer of one must close |
| `F` | the kind of the pair this is the content of; empty at the top |
| `p` | the kind of a live opener right before, if any |
| `B` | kinds barred by a destination that does not close |

```
paragraph ::= Seq(∅, ∅, -, ∅)

Seq(S, F, p, B) ::=
  R0  ε                                           at the paragraph's end, or at a closer of F
  R1  text                                        Seq(S, F, -, B)
  R2  close_k                                     Seq(S, F, -, B)      k ∉ S, or p = k for a delimiter
  R2' close_k                                     Seq(S, F, -, B)      k ∉ S, k ∈ B: text, does not open
  R3  open_k                                      Seq(S+k, F, k, B)    k ≠ F
  R4  open_k  Seq(S+k, k, k, B)  close_k          Seq(S, F, -, B)      a delimiter: content non-empty
  R5  [  Seq(S+[, [, [, B)  ]  region             Seq(S, F, -, B)      region: ( ... the balancing ), or [ ... the next ]
  R6  [  Seq(S+[, [, [, B)  ](  Seq(∅, F, -, B∪S)                      no balancing ) ahead; to the paragraph's end
  R7  [  Seq(S+[, [, [, B)  ][  source                                 no ] ahead; the rest is the label
```

A token that may both open and close is a closer first: in R2 or R2' it
closes nothing and is then read as an opener (R3 to R7), except that a
barred one is text.  A closer of a kind in `S` that is not right after
its opener fits no rule at its level: only R4 to R7 consume it, as the
end of a pair's content.  A region is source: nothing in it opens or
closes, and it ends where `region_end` says.

## Why each part

| Reference (syntax.md, "Precedence") | Grammar |
| --- | --- |
| "the first opener that gets closed takes precedence ... openers between the opener and the closer get marked as regular text" | R4 to R7 continue with the `S` from before the pair: an opener left unmatched inside it is no longer live |
| "Containers can't overlap" | `S` passes into content, so a closer inside cannot be left over while an opener outside is live, and one of the two readings fails |
| "the closest one is used" | `F` in content: no opener of the pair's kind is left unmatched between its ends |
| "some characters besides the delimiter character between the opener and the closer" (M3) | R4's non-empty content, and `p` in R2 |
| `{_` and `_}` (P3), marked with marked (P4) | in the lexer: the token's capabilities and its kind |
| a destination or label after `](`, `][` is part of the link | R5's region |
| a destination with no `)` (djot.js, `inline.ts:150-158`) | R6: the rest of the paragraph, where a closer of a kind live before it is text |

`S` passes down and `F` does not: an opener left unmatched outside is
still live inside, but one left unmatched in deeper content dies when
that content's pair closes, before this level's closer.

After R6 no enclosing pair can close, since its closer would be barred;
in the grammar, R6 runs to the paragraph's end, so an enclosing R4
finds no closer.

## Worked examples

`_This is *regular_ not strong* emphasis`, with tokens `_₁ *₂ _₃ *₄`:

```
Seq(∅,∅,-,∅)
├─ R4  _₁ ... _₃             content Seq({_},{_},_,∅): "This is ", R3 *₂, "regular"
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

`*a [b](c *d*`: `*₀` by R3; `[b](` by R6, the destination never closing;
after it `B` is `{*}` and `S` is empty, so `*d*` pairs within itself and
`*₀` stays text.

## Is it a context-free grammar

R0 to R5 and R7, yes: `F`, `p` and `B` range over finitely many values
and `S` over the subsets of finitely many kinds, so `Seq(S, F, p, B)` is
finitely many nonterminals with ordinary productions.  R6's condition,
no balancing `)` ahead, is a lookahead the productions do not express;
it is the one side condition.  Neither matters for its use here.

## How it relates to the other two

| `ref_read` (`rstep`) | `valid` | Grammar |
| --- | --- | --- |
| the kinds on the stack | `live`, `closest_live` | `S` |
| an opener above another of its kind | `closest_live` | `F` |
| the check `S p < i` | `needs_content`, clause 2 | `p` |
| cutting the stack to `below` on a pair | `dead` | R4 to R7 restoring `S` |
| `LBar`, `PBarred` | `behind`, `barred` | R6, `B` |
| `RInert` | `inert` | R5's region, R7 |

## The enumerator

`seq` in `dev/InlineGrammar.v` follows the rules, with one shortcut that
is not a rule: R4 to R7 are tried only when a closer of the kind lies
ahead.  It backtracks and does not memoize, so an opener with a closer
ahead doubles the work, and a long line of mixed delimiters is
exponential.  `test/grammar.ml` therefore checks every one-line paragraph
of up to five pieces from a small set, and random paragraphs of up to
three lines of up to eight pieces from a larger one.

The check was tested by breaking the grammar (2026-10-08).  On a short
run, letting R3 leave `F` unmatched gave 92 differences, dropping `p`
1050, and not barring `S` in R6 only 2: the barrier is the rule the
pools reach least.
