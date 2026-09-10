---
ai-disclosure: ai-generated
aliases: [ decision-making-lessons ]
---
# Project engineering lessons (decision-making lessons)

Persistent and cumulative.

**Scope**: how to decide, not how to code. An entry earns its place only
if it changed a decision, names something specific enough to act on, and
is likely to come up again in *this* project. Advice that would apply to
any codebase teaches nothing here, and most session incidents are not
lessons — they are bugs, and they belong in the dated notes.

Each entry: what happened, the general form, what to do instead.

## Probe a theorem's shape before proposing it

**What happened.** A padding-simulation theorem was proposed on the
reasoning that `Nat.ltb` is invariant under adding the same amount to
both sides — true, but the states being compared were not uniformly
shifted, so the theorem was false. It took ~200 lines of proof and a
unification failure to find that out. A three-line `Compute` comparing
the two states would have shown it in a minute.

**General form.** A theorem about a program is a claim about what the
program computes, and this parser is executable, so it is refutable long
before it is provable.

**What to do instead.** For any non-obvious statement about `step`,
`parse_lines` or the renderer, write the smallest `Compute` that
distinguishes true from false and run it first. Keep the probe if it is
informative: a failing-by-construction `Example` records a boundary
better than a paragraph of prose, and its deletion when the bug is fixed
is the confirmation that the fix was real
(`pad_nested_list_unshifted` was one).

`dev/check/Probe.v` does the part that was awkward, which was never the
computing but having to guess the input: it runs a candidate over a
curated pool of reachable states and line shapes (`make probe`, ~0.5s).
Two rules for reading it. `None` is not a proof, only "no counterexample
in the pool". And for a conditional candidate use `guarded` and read
`t_pass` first — a probe whose guard discarded every input reports a
clean pass while having tested nothing.

## Probe the definitions a theorem already constrains, too

**What happened.** Block attributes. `PAttr` was written recording the
column its brace sits at as `indent_of l`, on the reasoning that all
lines in a container are measured the same way. That reasoning is
correct about *behaviour* and beside the point: `step_fuel_pad` says
padding a line and shifting the offset are the same descent, so any
column a state records has to be absolute (`off + indent_of l`). The
line-local spelling makes the two disagree. It surfaced only after the
state, six `step` branches and two proof cases were written, and the
repair was structural rather than local: `open_attr` had to come out of
`open_kind`, `direct_open` had to exclude `KAttr`, and two new step
equations replaced the ones `open_kind` users got for free.

Two lines would have decided it:

```coq
Compute snd (step "  {#i" (PPara [])).      (* PAttr [] 2 ... *)
Compute snd (step_at 2 "{#i" (PPara [])).   (* PAttr [] 2 ... *)
```

Line-local, those read `2` and `0`.

**General form.** [[#Probe a theorem's shape before proposing it]] points
the other way: there the theorem was the proposal and `Compute` refuted
it. Here the theorems already existed and the *definition* was the
proposal. The parser carries two representations of the same nesting — a
column offset, and a blank prefix on the line — and `step_fuel_shift` and
`step_fuel_pad` are the statements that they agree. Those two are a
standing constraint on what any new state may record, and the constraint
is invisible in the state's own behaviour.

**What to do instead.** Before adding a `pstate` constructor or a field
to one, list which existing theorems quantify over all states — today
`step_fuel_shift`, `step_fuel_pad`, `step_blank_finish`, `finish_wf`,
`finish_supported` — and ask what each demands of the new one. For
anything that records a column, run the two-line probe above first.

**The same list exists for `cblock`, and it is shorter.** A canonical
constructor's design was once settled by asking only what the *parse*
side needs, and the table step paid for it: a source-shaped `CTable`
carrying `Line.trow`s made the parse trivial and `render_cb_lines`
impossible, because that lemma says the *renderer* recovers `cb_lines`
from `cb_ast` -- so a constructor holding data the AST does not determine
cannot be canonical, whatever `cb_ok` asks. Non-injective `cb_ast` is
the tell. The standing quantifiers over all cblocks are
`render_cb_lines`, `cb_ok_lines_ok`, `cb_lines_first_line_ok`,
`nonlist_cblock_first` and `cb_ast_pristine`; check the first before
choosing the data, since it is the one that constrains the *shape* rather
than the side conditions.

**And when the standing theorems disagree with each other.** The code
fence later took the same field, and here `Compute` decides nothing: an
absolute column and one relative to the offset agree on every input the
container prefixes can produce. `step_fuel_shift` is true only of the
absolute spelling, the pad-and-shift composite only of the relative one.
Absolute won because `step_fuel_shift` is what every descent goes
through, while the side condition the other theorem then needs
(`fence_cols_ok`) travels no further than `step_pad`. Put the cost on the
theorem with the fewest users — [[#Prefer the stronger precondition when
the weaker one is viral]] one level down.

## Ask the oracle; do not reason about what djot "should" do

**What happened.** `feed_lazy` kept a lazy continuation line's leading
whitespace while every other continuation path stripped it. Both
behaviours are defensible from the prose spec. One `node` invocation
against `djot.js` settled it in under a minute: the oracle strips.

**General form.** Two executable specifications sit in the repo.
Behaviour questions are empirical, not a matter of taste or of reading
the prose reference — which is, on record, behind the implementation (the
tilde-fence and table-trimming SPEC-GAPs).

**What to do instead.** The oracle runs before the argument. Oracles
disagreeing is an `oracle-disagreements.md` entry, not a judgement call;
oracles agreeing against us means we are wrong. The interesting cases are
the two below, where knowing what djot does still does not settle what we
do.

### First check the oracle is a function

**What happened.** A sweep over the attribute alphabet reported 4610
mismatches. 4069 of them were an artefact: djot.js's `betweenMatched`
assigns to `defaultmatch`, and that binding is the enclosing call's
parameter rather than the per-scan one, so the eight delimiter rows are
built once at module load and a single `{"` or `"}` flips the smart-quote
default for every document after it in the process. `--batch` exists to
avoid node startup, so the harness ran a whole sweep in one process and
the answer depended on enumeration order. Twenty minutes went into
diagnosing a divergence that did not exist, and the real families were
underneath it: 541 after a per-document reset, 341 after the leak was
patched out of a scratch copy of the oracle.

**General form.** [[#Ask the oracle; do not reason about what djot
"should" do]] assumes the oracle answers the same question the same way
twice. A differential count is a claim about a function, and an oracle
with process-global state is not one. The failure is silent and looks
exactly like a real family -- consistent, reproducible, and clustered on
a plausible construct.

**What to do instead.** Before diagnosing anything a sweep reports, run
the first few mismatches through the oracle one document per process and
check the answers agree with the batch. It costs seconds. When they
differ, the harness is what to fix: batch mode promises nothing except
that it equals N processes, so make it equal them, and log the
underlying behaviour separately rather than deciding on the spot whether
to match it. The check is cheap enough to be reflexive and the reward is
not paying for a diagnosis of nothing.

### When the oracle's answer is unrepresentable

**What happened.** A block-attribute spec that spans a blank line and
then fails to parse becomes a paragraph of the lines it ate, and djot.js
keeps the blank — so `{#i` / blank / `  <}` yields a paragraph
*containing a blank line*. The rule above, read literally, says match it.
That would have been wrong: `wf_block` excludes blank lines in a
paragraph not for tidiness but because such a paragraph does not
round-trip, so matching would have made `roundtrip_blocks` false for a
document our own parser can produce.

**General form.** The oracle settles what djot *does*. It does not settle
what *we* do when what it does is unrepresentable in the canonical AST,
because `wf_block` is not a convention — it is the set of ASTs the
roundtrip theorem quantifies over. Fidelity and a proved theorem can
conflict, and when they do the conflict is not a matter of taste either.

**What to do instead.** Do not relax `wf_block` and do not match the
oracle by reflex. Ask the one question that decides it: *would matching
falsify `parse (render d) = d` for a `d` the parser can reach?* If yes,
diverge, confine the divergence as narrowly as possible, and log it in
`oracle-disagreements.md` under "ours" with the roundtrip argument spelled
out. If no, the oracle wins and `wf_block` is what has to give. Here the
answer was yes, and `push_text` confined the divergence to specs that
both span a blank line and fail.

### Canonical unreachability bounds a conformance gap; it does not close it

**What happened.** Direct links. djot.js keeps every matcher running
inside `](` and calls `strMatches` over the region only when the balanced
`)` arrives. Our destination accumulates literal text instead, so the
two disagree only when the destination never closes. The difference was
logged and treated as settled because canonical rendering always supplies
the close and matching would require another piece of scanner state.
The same reasoning was later used for two unattached-attribute cases:
unconditional helper lemmas were easier to keep if malformed source did
not follow djot.js's recovery.

That conclusion was backwards. Running an ordinary scan while retaining
candidate source is still one pass, and the attribute lemmas can take
side conditions that canonical callers already satisfy. Implementation
and proof cost explain why a gap remains; they do not turn it into chosen
language semantics.

**General form.** There are two independent questions. Canonical
reachability says whether a disagreement threatens roundtrip. Oracle
fidelity says whether the parser matches the designated implementation
on the source in front of it. A negative answer to the first bounds the
impact of a gap but says nothing favorable about the second. Likewise, a
theorem blocks the oracle only when the theorem states a property the
project intends on that input domain; a stronger helper lemma is allowed
to acquire the side condition its real callers can discharge.

**What to do instead.** Characterize the divergent input set. First ask
whether the oracle implementation replays source; then separately ask
whether the observable result inherently requires replay, including
whether a product state can compute it in one pass. Only the
second can justify an intentional no-backtracking boundary. Otherwise
keep the item open as conformance work even when it is noncanonical or
expensive. Name the affected lemmas and the side conditions a repair
would require; do not use proof convenience, implementation effort, or
the oracle's implementation strategy as an adjudication verdict. See
[[no-backtracking]].

## The corpus is djot.js's regression suite, not a map of the grammar

**What happened.** The nested-list bug (`- - b` / `  - c`) went unnoticed
through all 287 cases for two independent reasons: the comparison was too
coarse, *and* no test file contains the shape. Zero of 26 have a
marker-line nested list followed by an indented sibling. `--shape` fixed
the first; only generated inputs fix the second.

**General form.** The corpus covers what djot.js's authors got wrong or
thought worth pinning. Nothing forces it to contain the product of
"nesting position" x "has continuation", and no amount of instrumenting
the oracles supplies an input that is not there.

**What to do instead.** Ask whether an input exercising the property
exists before asking whether the comparison would show it. `cblock` +
`cb_lines` generates canonical documents and `make generated` runs them
against djot.js — and a property the generator cannot reach is a gap in
`cb_ok`, which is usually the more interesting finding.

### And the generator cannot reach what the renderer escapes

**What happened.** `[u]b](c)` -- a `]` whose next byte makes no
construct, which djot.js leaves as text with the `[` opener still alive
-- was wrong for the whole life of the bracket scanner. No corpus case
has the shape, and no *generated* document can: `escape_str` escapes a
`]` inside a label, which is exactly what stops the input from
existing. Both corpora were clean before the fix and clean after it, and
the exact-HTML number did not move. What found it was reading djot.js's
`]` handler while investigating a *different* gap (the unterminated
destination); what measured it was 200k documents in a bracket-shaped
alphabet run through both parsers and the oracle, 826 mismatches to 447.

**General form.** The clause above says the corpus is not the grammar
and points at the generator. But the generator emits *canonical* source,
so anything the renderer escapes, quotes or normalizes is outside its
image by construction -- and the parser's recovery on those very bytes
is where divergences live. The two corpora agree with each other about
what neither can see.

**What to do instead.** When a construct's scanner is under suspicion,
enumerate over its own alphabet -- the bytes it dispatches on, plus a
letter -- and diff against djot.js directly, rather than looking for the
shape in either corpus. `harness/main.exe --convert --batch` takes the
same length-delimited framing `djotjs.mjs --batch` does, so a sweep is
two subprocesses and 200k short documents cost about a minute. Run it
against the parent commit too: "did this regress anything" then gets a
partition -- moved onto the oracle, moved off it, changed and still
wrong -- instead of a total, and the second class is the one to explain.

## Predict the falsifier at the right granularity, or the prediction teaches nothing

**What happened.** Ordered lists. The plan predicted the classifier step
would land with "no change to `Render.v` and no change to any statement
in `Section ListMarker`". The first half was load-bearing — the parser
never consults a marker's width, so the renderer must not move — and it
held. The second was false on arrival and could not have been otherwise,
since the point of the step was to widen the state's style field, which
twelve statements mention. Written as one sentence, the outcome could not
distinguish "the design was wrong" from "the prediction counted the wrong
things". The sharp version cost nothing: *no statement acquires a new
hypothesis*, which is what actually stayed true.

**General form.** Predictions about *diffs* ("this file does not change")
fail for two unrelated reasons and separate neither. Predictions about
*obligations* — no new hypothesis, no new shared apparatus, no new
predicate — are what the next step's cost is made of, and their failure
names the thing that went wrong.

**What to do instead.** Ask what a prediction's failure would make you
do. If the answer is "check whether I counted right", it is a diff
prediction; restate it as an obligation until the answer is a decision.

## A hang or a sudden slowdown is the definition's shape, not the proof

**What happened.** Twice, and from opposite directions.

`Example div_indented_close_differs` was proved by `Proof. cbn.
discriminate.` over a five-line document. Widening `line_kind` by one
argument made each line ~3x more expensive to normalize, and since the
cost grows superlinearly in line count it took `Parser.v` from **1.8
seconds for the whole file** to over ten minutes for that one sentence.
The fix was two words; the diagnosis cost ten minutes of edit-and-rebuild.
At the parent commit `cbn` was already ~80x slower than `vm_compute` on a
single line (0.054s vs 0.002s) — the file had been sitting just under the
cliff all along.

The roman codec was thirteen nested `if`s with the recursive call in
every branch. Every tactic of `roman_str_nonempty` ran in 0.00s and then
`Qed` never returned: `roman_str up n` at an unknown `n` has no normal
form the kernel can reach, because sixteen levels of fuel times thirteen
branches is 13^16 paths and conversion walks them. Both plausible fixes
were wrong. Lowering the bound fails silently, since the hang is at an
unknown `n`. Cutting fuel to a constant was tried first and changed
nothing, since the range check's real cost was `Nat.leb 1000 n` on a
unary `nat`. The fix was to lift the thirteen-way choice into a table and
a lookup, leaving one recursive call per level.

**General form.** Tactic time and kernel time are charged separately, and
only the kernel pays for conversion. A concrete-evaluation `Example` is
the one place the parser's own definitional complexity reaches build
time, and a definition whose recursive call is duplicated across `k`
branches expands as `k^fuel` under symbolic reduction. Both are invisible
while every closed instance is fast: `vm_compute` on a concrete input
never sees the branch factor, so every `Example` passes while any
*general* lemma about the function is unprovable.

**What to do instead.** Concrete `parse_lines` / `step` evaluation gets
`vm_compute`, never bare `cbn` (`cbn [f g]` on named symbols is fine).
When a build slows sharply after a datatype widening, do not bisect the
proofs — run `coqc -time` and read the per-sentence output, against the
parent commit too, so "is this normal" gets a number. And when `Qed`
hangs while the tactics did not, stop reading the proof and look at what
the statement forces the kernel to convert: a fuel'd function must have
one recursive call, so a multi-way choice belongs in a lookup that
returns what to do, not inlined into the recursion.

## Check whether a proof uses the structure before pricing its removal

**What happened.** Generalizing away the ambiguous first marker was
scoped, in this file's own earlier note, as "a change to twelve
statements". It was three abstractions — a marker's style set to an
arbitrary set, the answer set separated from the narrowed set, the tail
handler turned into a hypothesis — each a `sed`-scale edit that compiled
on the first or second attempt, each leaving its old form as a one-line
instance. The twelve-statement estimate counted *occurrences of the
symbol*. The real cost was occurrences where the proof **used** something
the generalization would take away, which was two.

**General form.** Counting mentions of a symbol estimates the diff, not
the work. A parameter that appears everywhere but is consumed in one role
generalizes for free, and a proof that gets its conclusion entirely from
an induction hypothesis can have that conclusion abstracted without
touching a tactic. The expensive generalizations are the ones where a
proof inspects the structure being removed, and those are few and easy to
find.

**What to do instead.** Grep for the symbol, then read *only the proof
lines that mention it*, asking of each whether it uses the structure or
merely carries it. That count is the estimate, and it is also the plan:
the lines that use it are exactly the hypotheses the generalized
statement has to add.

**And check what the proof uses the structure *for*.** A marked
delimiter's scope was pushed the moment its token completed, and a `}`
after it turns out to change what the scope decays to, so the push had
to wait a byte. The visible cost was the canonical inversion chain:
`iscan_marked_open` had landed in a text state with the scope pushed and
now lands one byte earlier, and the obvious repair was a side condition
-- the next byte is not a `}` -- with a lemma that canonical text never
starts with one, threaded through four users. None of it was needed. The
chain uses *that* the scope is open, never which side its decay would
take, so the new bit could be existential: one `exists cm` in the opener
lemma, `cm` generalized in the three close lemmas, and four users that
destructure a bit they ignore.

**General form.** The clause above asks which proofs inspect a structure
being removed. This asks the same question of a field being *added*: a
proof that never reads it does not need to know its value, and a lemma
can report it existentially instead of taking a hypothesis that fixes
it. The tell that the hypothesis is unnecessary is that the fact it
would establish is never used downstream -- only its existence is.

**And check the users exist at all.** The div-closer rule was priced, in
`oracle-disagreements.md`, as "three `ListUniformity` statements have to
carry the incoming flag". Two of the three had no users anywhere and were
deleted in a line each; the third needed a replacement, not a
generalization, and the `ls_blanks ls = false` preconditions the note
called viral never moved, because the condition that discharges them
moved into `item_ok` instead. A statement with no consumers is not a cost
and not a constraint -- it is a claim about the development that nothing
is holding it to. Count users before counting hypotheses.

## Split a fix by proof cost before landing it, and look for the cheap spelling

**What happened.** The list-tightness gap turned out to be two
independent rules. A blank must not arm a list when something the item
still has open absorbs it (63 generated mismatches), and a div's closing
line must arm it because djot.js computes `isBlank` after the closers eat
the line (27, then unmeasured). Both were confirmed against the oracle in
the same hour and implemented together. The second then hit
`scan_list_content_blanks_last` and `roundtrip_blocks`, and reverting it
to land the first alone took the corpus from 3022/3085 to 3067/3094,
leaving the residue as one named family with a number on it.

The first rule had its own trap. The previous session's note said "the
faithful test is on the state *after* the descent", which is true about
djot.js and made the change look like it would ripple: as
`nested_container inner'` it needed `pad_state`-through-`step` lemmas that
`list_loose_of_pad` cannot supply. The same function has an equivalent
spelling on the state *before* — tabulate which constructors survive a
blank — and in that form it is a plain structural predicate, every pad
lemma is one line, and the whole change is a rename.

**General form.** Two corrections found together are not one step: their
measured benefit and their proof cost are independent, and landing them
as a unit prices the pair at the maximum of the two. And a rule
discovered by reading the oracle's *control flow* ("the handler runs
after the continues") arrives phrased as a claim about an intermediate
state, which can be far more expensive to formalize than an
extensionally equal phrasing. `step` is deterministic, so a predicate on
the post-state is a predicate on the pre-state whenever the transition is
constructor-determined.

**What to do instead.** When a diagnosis yields more than one rule, get a
corpus number for each *before* writing proofs, land them in cost order,
and log the rest with the obligation that stopped it — naming the lemma
that fails, not just "has a proof cost". Before formalizing a rule stated
about an intermediate state, tabulate the transition over the
constructors and check whether the same predicate can be read off the
state you already have.

### Partition a sweep by mechanism, not by verdict

**What happened.** The block-attribute sweep's residue was recorded as
"36, and it is one family", under a partition with two buckets: the
upstream bug, and ours. Picking the work up, the same sweep read 44, and
the extra twelve were not drift -- they were a second rule inside
"ours", where the recovery dropped the attribute set an earlier spec had
left pending. It was a two-line fix with three one-line lemmas, and it
had been sitting behind a bucket label for a session. The rule that
looked like the whole residue was in fact 24 of it.

**General form.** The clause above says to price each rule separately
once a diagnosis has named them. This is the step before: a partition by
*who is wrong* has one bucket for us and therefore cannot show that we
are wrong twice. The count is stable, the label is stable, and nothing
about either says a second mechanism is underneath.

**What to do instead.** Bucket a sweep's mismatches by the mechanism
that produces them -- which branch, which lost field -- and treat any
bucket you cannot name that way as unpartitioned. Re-run the sweep
before trusting a residue recorded in a previous session, and if the
number moved, the partition is what to look at first, not the parser.

## Price a parameterization by whether the parameter can stay implicit

**What happened.** Making the delimiter table a parameter was scoped from
a symbol count: `Wf.v` alone mentions inline-layer names 245 times, and a
section variable turns every one of those into a call site that needs the
argument. That number is what made the step look like a week, and it was
answering the wrong question. A type class carrying the table *and* its
side condition keeps the argument implicit, so the count that mattered
was not 245 but the number of *files*: one `Context` line each, and not a
single call site edited. What decided it was a twenty-line scratch file
with a toy table, a toy fixpoint and one `Example`, checking the only
thing that could have killed the design — that `vm_compute` still reduces
through an instance, since every concrete `Example` in `Inline.v` depends
on it. Two minutes against an estimate off by two orders of magnitude.

**General form.** For a development-wide parameterization the cost is not
how many places mention the thing being parameterized, but whether the
parameter can be inferred at those places. Explicit parameter: cost
scales with mentions. Implicit (class, canonical structure): cost scales
with files. Which one applies is a property of the *elaborator*, not of
the code being changed, so it is not derivable by reading the code.

**What to do instead.** Before pricing a "thread X through everything"
step, write the smallest file that has X as an implicit parameter, one
definition that uses it, and one `Example` that computes. If it reduces,
price the step in files; if not, price it in mentions and expect the
larger number. This is [[#Check whether a proof uses the structure before
pricing its removal]] one level up: there the question was which proofs
*use* the structure, here whether the uses have to *name* it. Both fail
the same way, by counting the diff instead of the work.

### When the parameter cannot reach, move the definition

**What happened.** Gating definition lists needed `styles_list` to read
`bdeflists`, and `styles_list` sat in `Marker.v`, below the file that
defines `bconfig`. The obvious move was an explicit bool parameter, priced
at the 36 mentions of `styles_list` and `styles_list_checked` -- most of
them statements in the uniformity chain. The four definitions had no user
inside `Marker.v` at all, so moving them into `Step.v`'s `Section
WithTable` made the argument a section variable: 36 mentions, zero call
sites edited, four proof sites total.

**General form.** The clause above asks whether a parameter can stay
implicit *where it is*. This is the prior question: a definition placed
below the configuration in the dependency order cannot have an implicit
parameter, so the choice is not "explicit or implicit" but "explicit here
or implicit one file up". The placement is usually historical rather than
forced -- `styles_list` was in `Marker.v` because it is about markers, not
because anything there used it.

**What to do instead.** Before parameterizing a definition that sits below
`Step.v`, grep for its users *within its own file*. If there are none, the
move is the cheaper change and it costs one `git mv`-shaped diff. Check the
other direction too: every file that imports the donor already imports
`Step.v` here, which is what made the move invisible to them.

### The check that a parameterization took

The failure mode is silent. A statement written after a section's `End`
still typechecks — it just quietly means the ambient instance, so
`roundtrip_doc` was a theorem about djot for an hour while its neighbours
were about the family, with nothing to indicate it. The same goes for any
file that never opened a section. `Check @thm` prints the binder or does
not, and that is the whole test; run it on every statement the step was
for, not on a sample.

## Probe the equations a new pass must preserve, not only the invariant it establishes

**What happened.** Deferring attribute attachment adds a normalizing
pass over a scope's output. The obvious risk was the well-formedness
invariant, so that is what got probed: twenty lines, first attempt,
closed under the global context. The real cost was somewhere else. The
pass *merges* adjacent text, so it is not the identity — and two
equational lemmas say that a scope built by `oemit_all` out of settled
nodes closes back to exactly those nodes. Those became false, taking a
side condition through their ten users, and a second family
(`ibreak_closed`, `iscan_closed`) became false for an unrelated reason:
an unresolved marker crossing a line break makes the line-by-line
decomposition disagree with the whole-paragraph one. Neither showed up
in a census that counted which definitions inspect the element type.

**General form.** A pass that *establishes* a property is easy to price
by proving it establishes the property. What it costs instead is every
existing statement of the form "this operation gives back exactly what
was put in", because the pass now sits between the two. Those statements
do not mention the invariant and do not mention the element type, so
neither a census nor an invariant probe finds them.

**What to do instead.** Before adding a normalizing pass, grep for
lemmas whose conclusion is an equation about the construct the pass will
wrap -- here `oclose (oemit_all ns ...) = Some (... ns ...)` -- and ask
of each whether the pass is the identity on its right-hand side. Where
it is not, the side condition that makes it so is the real diff, and its
users are the real cost. [[#Check whether a proof uses the structure
before pricing its removal]] counts the proofs that inspect a structure;
this counts the theorems that pin a value.

**And then try to make the pass an identity instead of paying.** Both
costs above were avoided, and neither by proving anything. The merge was
made conditional on one bit -- set only where a resolved spec vanished,
which is the only place two `Str`s can meet -- and resolution became the
identity on a settled list *definitionally*, so every side condition
came back out. The line-break disagreement went the same way: keeping a
refusal the old code already had (`oattach` declining a `SoftBreak`) made
the two decompositions agree. The general form is that a pass which is
the identity on the inputs the existing theorems quantify over costs
nothing, and "identity on those inputs" is usually reachable by
restricting when the pass does anything -- cheaper than carrying a
hypothesis to every user.

## Check what quantifies over a predicate before defending it

**What happened.** Dropping an unattached attribute spec made a nonblank
line able to yield no inlines, which falsified `wf_block`'s `Para`
nonemptiness clause. The plan was to defend the clause: a `para_block`
smart constructor at six sites, a caption collapse, a `key_close` guard.
That version then broke `oclose` (an emptied delimiter scope), and then
`step_empty_carriable`, where a pending attribute set would have been
carried past a blank line -- an obstruction with no cheap repair, since
the lemma quantifies over all states.

The clause did not need defending. `roundtrip_blocks` quantifies over
`cblocks_ok`, not over `wf_block`, and `wf_complete_false` says in the
file itself that `wf_block` does not characterize parser output. Nothing
imports `Wf.v`. So the clause was a claim, not a constraint: deleting it
cost two lines, matched djot.js on `<p></p>` and `<strong></strong>`,
and made the `step_empty_carriable` problem disappear rather than need
solving -- the pending set now attaches to the empty paragraph, which is
what djot.js does.

**General form.** [[#When the oracle's answer is unrepresentable]] says
to ask whether matching would falsify `parse (render d) = d` for a
reachable `d`. Answering it requires knowing which predicate the theorem
actually quantifies over, and a predicate that *sounds* like the
canonical one is easy to substitute for it. `wf_block` and `cb_ok` both
read as "the ASTs we admit"; only one is a hypothesis of the roundtrip.

**What to do instead.** When a change falsifies a clause of a
well-formedness predicate, grep for the predicate in every file *except*
its own before designing a guard. If the only occurrences are inside its
own file and in comments, it is a claim about the parser and the change
is to the claim. Reserve guards for predicates some other theorem takes
as a hypothesis. The tell that the guard was wrong here was that each
one bred another: a defended invariant that keeps finding new places to
be defended is usually not the one the development rests on.

## A parameter's laws need the parameter's own domain

**What happened.** The link codec was first written with
`l_parse self (l_spell self p) = Some p` for every path, plus `no_nl`
and `no_ws` of every spelled destination. No convention satisfies
either: a flat vault cannot spell a nested note at all, and a path with
a space in it spells a destination with a space. The repair was a
field rather than a hypothesis -- `l_ok : path -> bool`, which paths
this convention can name -- with every law quantified over it. The cost
was one side condition on the single theorem that substitutes a path,
where it reads "the new name is one this convention can spell", which is
a check an implementation runs anyway. The two admissibility conditions
were dropped instead of scoped: nothing used them, because the theorem
that will (a renamed site is still canonical) is not proved yet, so they
went into prose beside that obligation.

**General form.** When a parameter is a *convention* rather than a table
of values, its laws hold on a subset of the type, and the subset belongs
in the parameter. Quantifying over the whole type makes every real
instance unprovable; threading the subset as a hypothesis makes it viral
([[#Prefer the stronger precondition when the weaker one is viral]]). A
field is neither.

**What to do instead.** Before proving a parameterization's laws, write
the smallest real instance and check each law against it -- a flat
vault, a one-row table. A law the instance falsifies is either a wrong
instance or a law whose domain is missing, and it is usually the latter.
Then drop the laws with no users: one an unproved theorem will need is
documented next to that obligation, not carried in the predicate.

## A wrapper constructor splits the predicates, not the theorems

**What happened.** `CId` puts one source line in front of an existing
block. The plan listed the standing theorems to re-run and predicted
they would gain arms rather than change; the arms were indeed cheap, and
three *definitions* changed instead. `cb_pair_ok` asked `is_clist` of
both arguments, but its first slot means "what does this block still
have open" and its second "what does this block's first line look like"
-- one function answering two questions that a wrapper separates
(`ends_clist`, `ends_ctable`). `render_blocks_lines` rendered
`node_contents` and so dropped every node's attributes, which was
invisible while every canonical AST was `mk`-wrapped and became false
the moment one was not. `cdef_head_ok` had to exclude a named head
because `def_split` drops a term paragraph's attributes.

**General form.** A constructor that wraps rather than adds leaves every
theorem statement standing and changes what the predicates *mean*. The
standing-quantifier checklist finds the theorems, since they mention the
type; it does not find the definitions, because those still typecheck
and still compute.

**What to do instead.** Before adding a wrapper, list the definitions
that match on the constructor set and ask of each whether it is reading
the block's first line, the state it leaves behind, or its AST. Any one
whose call sites want different answers is the real diff, and it splits
in two. Then ask separately what the renderer throws away -- a
projection that was total on the old fragment is where a wrapper's
payload goes missing, and the roundtrip is the only thing that notices.

## Prefer the stronger precondition when the weaker one is viral

**What happened.** `dconfig_ok` gained conditions the scanner needs of
each table row — nonzero width, punctuation, not a reserved character.
The obvious scoping was to ask them only of rows switched *on*, since a
switched-off row is never looked up. That version cost a hypothesis:
"this row exists" had to be threaded through `dtoken_nonempty`,
`iscan_dtoken`, three `iscan_marked_*` lemmas, and then through
`iscan_productive` and `iscan_wf` — predicates quantified over *all*
states, where the row comes from the state and not from a lookup, so
there was nowhere for the hypothesis to come from. Asking the conditions
of every row instead deleted the hypothesis everywhere. The cost to a
table author is that a switched-off row still has to be spelled with
something admissible, which is no cost at all.

**General form.** A precondition's price is not its strength, it is how
far it has to travel. A weaker condition carried through a chain of
lemmas is more expensive than a stronger one that holds unconditionally —
and the chain is usually invisible when the condition is written, because
it runs through predicates that quantify over states rather than over the
construct the condition is about.

**What to do instead.** When scoping a side condition to "only the cases
that need it", ask where the *users* get it from. If any user is a
predicate over all states, over all inputs, or over an inductive the
condition does not mention, the scoping will not survive; strengthen the
condition until it is unconditional, and check that the strengthening
costs a real user something. Here nothing was lost, and the one place
that genuinely needs "this row exists" — `dstyle_of` — kept its
hypothesis and pays for it in exactly one lemma.

### The other direction: a precondition weaker than the truth

**What happened.** Attribute attachment. `iattr_attach` could not ask
"what did this scope last emit", because `oout_app` splices a previous
line's output underneath and a scope that has emitted nothing would see
*that* line's last node. The plan's recipe, written a month earlier, was
to add an invariant to `iscan`: a non-whitespace `prev` implies either
pending text or something emitted. That invariant is false — `[` sets
`prev` to `[` and pushes a scope with empty output — and it was aimed at
the wrong object, since `prev` is the previous source byte and "has this
scope emitted anything" is a different question that merely correlates.

The real obstruction was one hypothesis. The twenty `_app` lemmas carried
`starts_str base = false`, chosen because it is what the seam merge in
`osnoc_nonstr` needs. The suffix is in fact always a previous line
*headed by the `SoftBreak` that ended it* — which `osnoc_nonstr`'s own
comment states in prose, and then says is "discharged by construction
rather than carried". Carrying it instead cost twenty renames, one
derivation lemma and a `reflexivity` at the single call site, and the
query became answerable, because a `SoftBreak` head is one `oattach`
declines exactly as it declines an empty scope.

**General form.** The lesson above is about a condition scoped too
narrowly across *lemmas*. This is the same mistake across *time*: a
hypothesis picked as "the weakest thing this proof needs" is right until
a later definition needs to ask a question the stronger fact would have
settled. The tell is a comment that states the stronger fact in prose and
then declines to carry it — that is a fact the development knows and
cannot use.

**What to do instead.** When a new definition cannot be written because
some query is not stable under a composition lemma, look at that lemma's
hypothesis before adding an invariant anywhere. Ask what is *actually*
true of its argument at the call sites, not what the proof happened to
need. If the answer is stronger than the hypothesis and the call sites
can discharge it, the fix is a rename. Grep for prose of the form "by
construction rather than carried" — each one is a candidate.
