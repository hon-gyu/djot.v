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

There is now a tool for the part of this that was awkward. The expensive
step was never the computing, it was having to guess the input first, so
`check/Probe.v` runs the guess over a curated pool of reachable states
and line shapes: add a `Compute` and run `make probe` (~0.5s). Two rules
for reading it. A `None` is not a proof, only "no counterexample in the
pool". And for a conditional candidate use `guarded`, then read `t_pass`
before anything else: a probe whose guard discarded every input reports a
clean pass while having tested nothing.

## Probe the definitions a theorem already constrains, too

**What happened.** Block attributes. `PAttr` was written recording the
column its brace sits at as `indent_of l`, on the reasoning that all
lines in a container are measured the same way, so a line-local column
works. That reasoning is correct about *behaviour* and beside the point:
`step_fuel_pad` says padding a line and shifting the offset are the same
descent, so any column a state records has to be absolute
(`off + indent_of l`, as `ls_indent` already was). The line-local
spelling makes the two disagree. It surfaced only after the state, six
`step` branches and two proof cases were written, as a unification
failure — and the repair was structural, not local: `open_attr` had to
come out of `open_kind`, `direct_open` had to exclude `KAttr`, and two
new step equations had to be written to replace the ones `open_kind`
users got for free.

Two lines would have decided it:

```coq
Compute snd (step "  {#i" (PPara [])).      (* PAttr [] 2 ... *)
Compute snd (step_at 2 "{#i" (PPara [])).   (* PAttr [] 2 ... *)
```

Line-local, those read `2` and `0`.

**General form.** [[#Probe a theorem's shape before proposing it]] pointed
the other way: there the theorem was the proposal and `Compute` refuted
it. Here the theorems already existed and the *definition* was the
proposal. The parser carries two representations of the same nesting — a
column offset, and a blank prefix on the line — and `step_fuel_shift` and
`step_fuel_pad` are the statements that they agree. Those two theorems
are therefore a standing constraint on what any new state may record, and
the constraint is invisible in the state's own behaviour.

**What to do instead.** Before adding a `pstate` constructor, list which
existing theorems quantify over all states — today `step_fuel_shift`,
`step_fuel_pad`, `step_blank_finish`, `finish_wf`, `finish_supported` —
and ask what each demands of the new one. For anything that records a
column, run the two-line probe above first. This fires next on ordered
lists, which record a column *and* a start number.

(The same audit found the other half of the cost: `pad_safe` guards two
lemmas that want different things of `PAttr` — a pad is invisible to it,
but a blank line indented past the opener is a continuation rather than a
close, so `step_blank_finish` fails. One predicate now excludes it for
both reasons, said so in the definition. If a third state needs one and
not the other, that predicate should split.)

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

### The clause this was missing: unrepresentable oracle behaviour

**What happened.** Block attributes. A spec that spans a blank line and
then fails to parse becomes a paragraph of the lines it ate — and djot.js
keeps the blank, so `{#i` / blank / `  <}` yields a paragraph *containing
a blank line*. The rule above, read literally, says match it. That would
have been wrong: `wf_block` excludes blank lines in a paragraph, not for
tidiness but because such a paragraph does not round-trip — render it,
parse it back, and it splits in two. Matching would have made
`roundtrip_blocks` false for a document our own parser can produce.

**General form.** The oracle settles what djot *does*. It does not settle
what *we* do when what it does is unrepresentable in the canonical AST,
because `wf_block` is not a convention — it is the set of ASTs the
roundtrip theorem quantifies over. Fidelity and a proved theorem can
conflict, and when they do the conflict is not a matter of taste either.

**What to do instead.** When the oracle produces something `wf_block`
excludes, do not relax `wf_block` and do not match the oracle by reflex.
Ask the one question that decides it: *would matching falsify
`parse (render d) = d` for a `d` the parser can reach?* If yes, diverge,
confine the divergence as narrowly as possible, and log it in
`oracle-disagreements.md` under "ours" with the roundtrip argument
spelled out. If no, the oracle wins and `wf_block` is the thing that has
to give. Here the answer was yes and `push_text` confined it to specs
that both span a blank line and fail.

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

## Predict the falsifier at the right granularity, or the prediction teaches nothing

**What happened.** Ordered lists. The plan committed to a falsifier
before starting: the classifier step would land with "no change to
`Render.v` and no change to any statement in `Section ListMarker`". Half
of that was a real, load-bearing claim — the parser never consults a
marker's width, so the renderer must not move — and it held, which is
what confirmed the step ordering was right. The other half was false on
arrival and could not have been otherwise: the whole point of the step
was to widen the state's style field, and twelve statements in that
section mention it. Both halves were written in one sentence, so the
outcome could not distinguish "the measurement was wrong" from "the
prediction was sloppy". The sharp version was available and cost nothing
to write: *no statement acquires a new hypothesis*. That is what actually
stayed true, and it is what would have been informative had it failed.

**General form.** A falsifiable prediction is only worth writing if its
failure would change what you do next. "Nothing in file X changes" fails
for two unrelated reasons — the design was wrong, or the prediction
counted the wrong things — and a prediction that cannot separate them
buys nothing. This is the same failure as stating a theorem at the wrong
scope (prefix determinism is about tree *shape*; locality is about
*classification*), moved from theorem statements to plan documents.

**What to do instead.** For each prediction, ask what its failure would
make you do. If the answer is "look again at whether I counted right",
sharpen it until the answer is a decision — reorder the steps, redo the
measurement, abandon the approach. Prefer predictions about *obligations*
(no new hypothesis, no new shared apparatus, no new predicate) over
predictions about *diffs* (this file does not change): obligations are
what the next step's cost is made of, and diffs are not.

## `cbn` on a concrete `parse_lines` is a build-time cliff

**What happened.** `Example div_indented_close_differs` was proved by
`Proof. cbn. discriminate.` over a five-line document. Widening
`line_kind` by one argument made each line about 3x more expensive to
normalize, and because the cost grows superlinearly in line count that
took `Parser.v` from **1.8 seconds for the whole file** to over ten
minutes for that one sentence. Ten minutes of an edit-and-rebuild loop
went into the diagnosis, and the fix was two words. Measured on identical
input, `cbn` was already ~80x slower than `vm_compute` at the parent
commit (0.054s vs 0.002s on a single line) — the file was sitting just
under the cliff before anything was touched.

**General form.** A concrete-evaluation `Example` is the one place the
parser's *own* definitional complexity is charged to build time, and
`cbn` is the reduction least equipped to pay it. Nothing warns before it
goes over: the cost is invisible while it is merely large, and every
constructor added to `line_kind` or `pstate` multiplies it.

**What to do instead.** Concrete `parse_lines` / `step` evaluation gets
`vm_compute`, never `cbn` — `cbn [f g]` restricted to named symbols is
fine, bare `cbn` on a closed computation is not. When a build slows
sharply after a datatype widening, do not bisect the proofs: run `coqc
-time` on the file and read the per-sentence output, which names the
sentence in one pass. Do it against the parent commit too, so "is this
normal" is answered with a number rather than an impression.

## A hanging `Qed` under instant tactics is the definition's shape, not the proof

**What happened.** The roman codec was written as thirteen nested `if`s
with the recursive call in every branch. Every tactic of
`roman_str_nonempty` ran in 0.00s and then `Qed` never returned. The
cause was not the proof: `roman_str up n` at an unknown `n` has no
normal form the kernel can reach, because sixteen levels of fuel times
thirteen branches each is 13^16 paths, and conversion walks them. Two
wrong moves were available and both looked reasonable. Lowering the
bound was one, and it fails silently: the check gets cheaper and the
hang stays, because the hang is at an unknown `n` and has nothing to do
with the range. Blaming the fuel was the other, and it is the one that
was actually taken first: fuel was cut from `n` to a constant 16 on the
prediction that it would make the range check linear. It did not. The
measurement was identical at every bound, because the real cost there is
`Nat.leb 1000 n` on a unary `nat`, which is linear in the *magnitude*
and indifferent to fuel. The fix was to lift the thirteen-way choice
into a table and a lookup, leaving one recursive call per level.

**General form.** Tactic time and kernel time are charged separately,
and only the kernel pays for conversion. A definition whose recursive
call is duplicated across `k` branches expands as `k^fuel` under
symbolic reduction, which is invisible while every closed instance is
fast -- `vm_compute` on a concrete `n` never sees it, so the range check
and every `Example` pass while any *general* lemma about the function is
unprovable.

**What to do instead.** When `Qed` hangs and the tactics did not, stop
looking at the proof and look at what the statement forces the kernel to
convert. For a fuel'd function, check the branch factor first: the
recursive call must appear once, so a multi-way choice belongs in a
separate lookup returning what to do, not inlined into the recursion.
This is the same lesson as [[#`cbn` on a concrete `parse_lines` is a
build-time cliff]] seen from the other side -- there the reduction was
too eager for a closed term, here the term has no normal form at all --
and it fires next on the inline parser, which will want exactly this
shape for its delimiter table.
