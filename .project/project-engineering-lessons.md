---
ai-disclosure: ai-generated
aliases: [ decision-making-lessons ]
---
# Project engineering lessons (decision-making lessons)

Persistent and cumulative.

**Scope**: how to decide, not how to code. Every entry is a case where a
minute of cheap evidence beat an hour of confident reasoning — an
estimate that should have come from an invariant, a theorem that could
have been refuted by `Compute`, a semantic question the oracle already
answers, a test suite trusted without checking what it covers. Some fire
at planning time and some mid-task; what they share is the moment just
before committing to a direction.

**The bar for an entry is high**: it must have changed a decision, be
specific enough to act on, and be likely to recur in *this* project. Generic engineering advice does not qualify — a lesson
that would apply to any codebase teaches nothing here. Most session
incidents are not lessons; they are just bugs, and they belong in the
dated notes or in other files. It also has be to related to general decision making, trading off between different options, not just technical ones.

Each entry: what happened (historical account), the general form, what to do instead.

## Probe a theorem's shape before proposing it

**What happened.** A padding-simulation theorem was proposed on the
reasoning that `Nat.ltb` is invariant under adding the same amount to both
sides — true, but the states being compared were not uniformly shifted,
so the theorem was false. This was discovered only after writing ~200
lines of proof and hitting a unification failure. A three-line `Compute`
comparing the two states would have shown it in a minute.

**General form.** A theorem statement about a program is a *claim about
what the program computes*. It is checkable by computation long before it
is provable by tactics, and the parser here is executable.

**What to do instead.** For any non-obvious statement about `step`,
`parse_lines` or the renderer, write the smallest `Compute` that would
distinguish true from false and run it first. Keep the probe if it is
informative — a failing-by-construction `Example` is a better record of a
boundary than a paragraph of prose. (`pad_nested_list_unshifted` was such
an example, and its deletion when the bug was fixed was the confirmation
that the fix was real.)

## Ask the oracle; do not reason about what djot "should" do

**What happened.** `feed_lazy` kept a lazy continuation line's leading
whitespace while every other continuation path stripped it. Both
behaviours are defensible from the prose spec. One `node` invocation
against `djot.js` settled it in under a minute: the oracle strips.

**General form.** This project has two executable specifications sitting
in the repo. Semantic questions about djot's behaviour are empirical, not
a matter of taste or of reading the prose reference — which is, on record,
behind the implementation (see the tilde-fence and table-trimming
SPEC-GAPs).

**What to do instead.** Any "what should the parser do here" question gets
an oracle run before it gets an argument. If the two oracles disagree,
that is an `oracle-disagreements.md` entry, not a judgement call. If both
agree and we differ, we are wrong — that is how the nested-list bug was
adjudicated.

## Coverage, not granularity, is what catches structural bugs

**What happened.** The nested-list bug (`- - b` / `  - c`) went unnoticed
through a 287-case corpus. Two reasons, and only one of them was fixed by
`make shape`: the corpus comparison was too coarse *and* the corpus does
not contain the shape. Zero of 26 test files have a marker-line nested
list followed by an indented sibling. `--shape` fixed the granularity;
the coverage hole is still open.

**General form.** The djot.js corpus is that project's regression suite —
it covers what its authors got wrong or thought worth pinning. It is not a
systematic exploration of the grammar, and nothing forces it to contain
the product of "nesting position" x "has continuation".

**What to do instead.** For any block-structure property, ask first
whether an input exercising it exists at all, then whether the comparison
would show it. Finer instrumentation of the oracles (djot.js's
`parseEvents` carries per-event `startpos`, which is exactly the column
this bug got wrong) does not help with the first question. Generated
inputs do — and `cblock` + `cb_lines` is already a typed generator of
canonical documents. Phase 1 item 4 of the plan called for exactly this
and has not been done.