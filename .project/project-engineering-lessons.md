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
dated notes or in other files.

Each entry: what happened (historical account), the general form, what to do instead.

---

## Estimate from invariants, not from diffs

**What happened.** Threading a column offset through `step_fuel`
(`954bcd1`) was estimated three times. First "8 call sites", from counting
references to the six changed lemmas. Then "a reformulation of ~60
lemmas", from counting the 39 `bullet_cont ++` occurrences whose meaning
the change altered. Both were wrong. The real cost was five lemmas gaining
one hypothesis.

**Why.** Both estimates measured the *diff* — how many places textually
mention the changed thing. The question that decides the cost is: **which
invariants actually carry the thing that changed?** Only `PList` records a
column. Every other state is fixed by the shift, so the change was
invisible to almost all of the code that mentioned it. Better still, an
existing predicate (`list_content_safe`, which excludes `CList` for
unrelated reasons) already guaranteed the condition, so it cost a
hypothesis rather than a proof.

**What to do instead.** Before estimating a change to a definition, ask
which fields of which states it can reach, and which existing predicates
already constrain those. Grep counts are an upper bound that is usually
wildly loose in a proof codebase, because most lemmas are generic in the
part you are changing. If the estimate and the invariant disagree, the
invariant is right.

---

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

---

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

---

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

---

## A projection used as an equality oracle drops the field under test

**What happened.** To find canonical blocks that `cb_ok` rejects but that
roundtrip anyway, the first screen compared `render_djot (parse ...)`
with `render_djot (cb_ast ...)`: string equality, decidable, and
rendering is faithful. It reported 983 candidates at depth 2, including
22 blamed on the spacing condition. All 22 were false positives.
`CList Tight [[CPara ["a"]]]` and `CList Loose [[CPara ["a"]]]` both
render to `- a`. The genuine tight/loose defect stayed invisible until the
screen was augmented with a spacing-tag comparison.

**General form.** Every projection we reach for as a cheap comparison is
lossy by construction, and the loss is never random: a projection is
adopted *because* it discards what seemed irrelevant. The field under
test is the one most likely to be in that set, because it is the field
whose behaviour was not yet understood.

**What to do instead.** Before using any projection as an oracle, name
what it drops and check the property under test is not in that set.
`render_djot` drops list spacing, positions and attributes; the harness's
`--shape` drops inline content. Both are fine for what they were built
for and neither is a roundtrip oracle. When a projection reports a
finding, verify the finding exactly before counting it. A screen whose
*negatives* are sound (a difference implies a real difference) is still
useful for locating candidates -- just never for confirming them.

---

## The conservative predicate may be replaceable by the lemma's precondition

**What happened.** `list_content_safe` is a structural predicate over
`cblock` that bans code blocks and (until now) nested lists inside a list
item. Three separate plans described the next step as "relax its `CList`
case". Probing the obligation that relaxation would create -- that the
predicate implies `run_pad_safe`, the actual hypothesis of the pad
lemmas -- showed the implication holds but is very loose: 1944 of 2315
generated blocks satisfy `run_pad_safe` without satisfying
`list_content_safe`. Defining the predicate *as* `run_pad_safe (cb_lines
c) (PPara [])` admits more (671 vs 632 at depth 2), closes an
acknowledged gap, and deletes the implication obligation rather than
discharging it.

**General form.** A hand-written predicate guarding a proof usually
started life as a conservative sketch of some lemma's real precondition.
Over time the lemma acquires an exact, computable hypothesis and the
sketch stays. Relaxing the sketch case by case treats the sketch as the
thing to be preserved; the lemma's precondition is the thing that was
actually meant.

**What to do instead.** When a plan says "relax predicate P's case for
X", first find the lemma whose hypothesis P exists to discharge and ask
whether P can simply *be* that hypothesis. The check is cheap: enumerate
and compare the two as booleans. If the gap is large, the relaxation is
the wrong move. `cb_ok` has several conjuncts of this shape --
`item_marker_ok`, `no_adjacent_lists` -- and each is worth the same
question.

