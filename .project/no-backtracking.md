---
ai-disclosure: ai-generated
---
# What no backtracking means here

This is the project's authoritative interpretation of djot's
no-backtracking goal. Historical plans may describe stricter scanner
shapes or treat a replay used by djot.js as proof that its observable
behaviour requires replay; this note supersedes those readings.

## Where the claim comes from

The broad claim is design goal 1 in the djot repository README:

> It should be possible to parse djot markup in linear time, with no
> backtracking.

It was present in the initial djot commit
[`b95dc83`](https://github.com/jgm/djot/commit/b95dc83ca7d233fb466c432d489cad5a09ce2200)
on 2022-07-11. The syntax reference makes a narrower and more precise
statement about blocks:

> Blocks can be parsed line by line with no backtracking. The
> contribution a line makes to block-level structure never depends on a
> future line.

`Beyond Markdown` supplies the earlier motivation -- simpler parsing,
local link recognition, and avoidance of indefinite lookahead -- but
does not itself state a no-backtracking property.

The inline scope is nevertheless intentional. The djot.js inline parser
opens with the objective "parse without backtracking" and explains its
opener stack as the mechanism. In discussion #247, John MacFarlane also
calls failed attribute recovery backtracking and says eliminating it
would be desirable because reparsing failed special regions can lead to
quadratic or worse behaviour.

These sources have different authority:

- the syntax reference specifies block behaviour;
- the README states an existential implementation and performance goal
  for djot markup as a whole;
- djot.js specifies the edge-case behaviour this project compares
  against, but its implementation is not automatically a witness for
  every design goal.

## The interpretation

A parser backtracks when it commits to an interpretation, consumes a
region, discovers from later input that the interpretation failed, then
moves back and submits that consumed region to parsing again under a
different interpretation.

The main input cursor must therefore advance monotonically. The parser
may still:

- inspect bounded local lookahead or lookbehind without moving the cursor;
- record potential openers and resolve them when a closer arrives;
- rewrite annotations or abandon scopes already represented in state;
- buffer source for later construction of a literal node;
- defer commitment by carrying candidate interpretations in a compound
  state and update them as each new byte arrives;
- perform a later semantic resolution pass over an already classified
  tree.

The compound-state case matters. Running an attribute machine and an
ordinary-inline shadow state together is one transition of a product
automaton, not a rewind. On success it keeps the attribute branch; on
failure it keeps the inline branch. Each branch sees new input as it
arrives, and neither is restarted on an earlier suffix.

What is forbidden is buffering a failed region and later calling the
scanner on that buffer, or resetting the scanner cursor to the region's
start. "One active interpretation per byte" would be a stronger property
that djot does not state, so this project does not adopt it.

## Three properties, not one

The source material supports three separate obligations.

### Block prefix determinism

The syntax reference's block claim is semantic: future lines do not
change the contribution an earlier line makes to block structure. Tables
may refine a row's role and whole-document passes may add identifiers,
so the theorem is about block shape rather than every later annotation.

### Monotone source consumption

The implementation claim is operational: the parser never restarts on a
consumed source region. For inlines, opener stacks and compound states
can satisfy it. This property should cover malformed input too if the
formalized parser claims djot.js-compatible recovery for all strings.

`Inline.iscan_str_no_reread` certifies that the current outer scan spends
one source-dispatch unit per byte. It does not establish that every
possible conforming implementation has the current state's shape, and it
does not make a djot.js behaviour impossible merely because djot.js
implements that behaviour with replay.

### Linear time

The README explicitly claims that a linear-time parser should be
possible. No-backtracking supports that goal but does not prove it: a
single monotone scan can still do work proportional to opener-stack depth
at each byte. Conversely, bounded replay can remain linear while still
being backtracking.

A linear-time theorem therefore needs an explicit cost model and any
necessary amortization argument. It must not be inferred from
`iscan_str_no_reread` alone.

## Consequences for conformance

`attributes.test:370` shows that djot.js itself replays buffered
attribute slices with attribute recognition disabled. That implementation
backtracks. Its output does not require backtracking: a product state
initialized from the scanner state before `{` can keep the ordinary
inline alternative current, including its interaction with scopes opened
before the attribute candidate.

This construction establishes compatibility with monotone source
consumption, not linear time. If nested candidates create multiple live
shadows, a linear bound needs a representation, sharing argument, or
amortization proof that prevents repeated work from growing
superlinearly.

The same distinction applies to a failed autolink candidate. A raw
candidate recognizer and an ordinary-inline shadow can advance together;
the `>` chooses the candidate only if it is valid, otherwise the shadow
continues. The fact that djot.js uses lookahead followed by an ordinary
scan diagnoses its algorithm, not an impossibility result for the
behaviour.

Accordingly, neither recovery required weakening no-backtracking: the
inline-attribute and destination cases now use live alternative readings.
The one remaining exact-HTML corpus difference is the block-attribute
version, which is still open conformance work. Its roundtrip impact is a
separate question from its compatibility verdict.

## Proof-design rule

Before declaring a djot.js difference necessary for no-backtracking,
separate these questions:

1. Does djot.js rewind or replay source?
2. Does the observable result inherently require rewind, or can a
   compound state compute it while input advances?
3. Which theorem states the intended property, and over which inputs?
4. Is a claimed linear bound actually proved by a cost model?

Only the second question can justify a semantic divergence, and an
implementation trace alone cannot answer it.

## Sources

- [djot README](https://github.com/jgm/djot#rationale),
  Rationale goal 1
- [djot syntax reference](https://github.com/jgm/djot/blob/main/doc/syntax.md),
  Block syntax
- [Beyond Markdown](https://johnmacfarlane.net/beyond-markdown.html)
- [`djot.js/src/inline.ts`](../djot.js/src/inline.ts), parser strategy and
  `reparseAttributes`
- <https://github.com/jgm/djot/discussions/247>
