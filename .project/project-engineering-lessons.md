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

### The other clause: matchable, but only at a price

**What happened.** Direct links. djot.js has no destination *mode*: it
keeps every matcher running inside `](` and calls `strMatches` over the
region only when the balanced `)` arrives, turning what it matched into
literal text retroactively. Our destination accumulates literal text
instead, and the corpus caught the difference immediately -- one case in
`links_and_images` got worse on the step that added +11 overall. Nothing
forbade matching the oracle here: no theorem was at stake, and the
canonical view can never produce such a document. The reflex was to go
implement `strMatches`. What stopped it was asking which inputs actually
reach the difference: when the destination closes, djot.js str-ifies
everything anyway and the two agree, so the gap is confined to a `](`
that never finds its `)`. Matching that one shape would have meant
running the ordinary scan *and* accumulating source alongside it, then
discarding one at the close -- a third retroactive disposition, in the
middle of a step about dispatch.

**General form.** The clause above is about oracle behaviour we *cannot*
represent. This is the more common case: behaviour we could match, at a
cost, where the deciding fact is neither fidelity nor provability but the
*reachable set* of the divergence. A gap confined to inputs the canonical
view excludes is a corpus number; a gap on inputs the parser meets
routinely is a bug. The corpus reports both as one line.

**What to do instead.** When a step makes some case worse, characterize
the inputs that reach it before deciding anything. State the boundary as
a sentence -- "we agree whenever the destination closes" -- and check it
against the oracle. If the divergent set is one the canonical view
excludes, log it under "ours" with that sentence and move on; the fix
belongs with the construct that needs the machinery anyway. This fires
next on spans and footnote references, which bring the two dispositions
the scope-stack probe named and this one makes three.

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

## Check whether a proof uses the structure before pricing its removal

**What happened.** The ambiguous first marker was scoped, in this file's
own earlier note, as "a change to twelve statements", and I re-scoped it
as a refactor of `ListUniformity.v`'s core induction. It was three
abstractions, each of which cost nothing and each of which left its old
form as a one-line instance:

- `mk_styles m0` -> `S` in `parse_item_and_tail` and `parse_list_tail`.
  `m0` was used in exactly two ways, as a set with a head and as a source
  of `mk_styles_nonempty`. Nothing needed it to come from a marker.
- `S'` -> `Sout` in `parse_item_and_tail_narrow`, separating the answer
  set the IH reports from the set the item narrows to. The conclusion
  always came entirely from the IH, so the two had been the same variable
  for no reason.
- The tail handler in `parse_list_tail_head_narrow`, abstracted into a
  hypothesis. One peel and two peels then became instances of one lemma.

Each was a `sed`-scale edit that compiled on the first or second attempt.
The twelve-statement estimate counted *occurrences of the symbol*; the
real cost was occurrences where the proof **used** something the
generalization would take away, which was two.

**General form.** Counting mentions of a symbol estimates the diff, not
the work. A parameter that appears everywhere but is consumed in one
role generalizes for free, and a proof that gets its conclusion entirely
from an induction hypothesis can have that conclusion abstracted without
touching a tactic. The expensive generalizations are the ones where a
proof inspects the structure being removed -- and those are usually few
and easy to find.

**What to do instead.** Before pricing a generalization, grep for the
symbol and then read *only the proof lines that mention it*, asking of
each whether it uses the structure or merely carries it. That count is
the estimate. It is also the plan: the lines that use it are exactly the
hypotheses the generalized statement has to add. This fires next on the
inline parser, whose delimiter machinery will want the same treatment.

## Split a fix by proof cost before landing it, and look for the cheap spelling

**What happened.** The list-tightness gap turned out to be two
independent rules, not one. A blank must not arm a list when something
the item still has open absorbs it (63 generated mismatches), and a
div's closing line must arm it because djot.js computes `isBlank` after
the closers eat the line (27, then unmeasured). Both were confirmed
against the oracle in the same hour and implemented together. The second
one then hit `scan_list_content_blanks_last`, the `ls_blanks ls = false`
precondition that `parse_list_tail` *uses* rather than carries, and
`roundtrip_blocks` -- a canonical `CList Tight [[CDiv [...]]; [...]]`
renders exactly its shape. Reverting it and landing the first alone took
the corpus from 3022/3085 to 3067/3094 and left the residue as one named
family with a number on it.

The first rule had its own trap. The note from the previous session said
"the faithful test is on the state *after* the descent", which is true
about djot.js and made the change look like it would ripple: written as
`nested_container inner'` it needed `pad_state`-through-`step` lemmas,
and `list_loose_of_pad` has no `pad_safe` hypothesis to supply them. The
same function has an equivalent spelling on the state *before* --
tabulate which constructors survive a blank, which is `nested_container`
minus `PQuote` -- and in that form it is a plain structural predicate,
every pad lemma is one line, `step_list_blank` keeps its shape, and the
whole change is a rename.

**General form.** Two corrections found together are not one step. Their
measured benefit and their proof cost are independent, and landing them
as a unit prices the pair at the maximum of the two. Separately: a rule
discovered by reading the oracle's *control flow* ("the handler runs
after the continues") arrives phrased as a claim about an intermediate
state, and that phrasing can be much more expensive to formalize than an
extensionally equal one. `step` is deterministic, so a predicate on the
post-state is a predicate on the pre-state whenever the transition is
constructor-determined -- which for blank lines it is.

**What to do instead.** When a diagnosis yields more than one rule, get a
corpus number for each *before* writing proofs, then land them in cost
order and log the rest with the obligation that stopped it -- naming the
lemma that fails, not just "has a proof cost". And before formalizing a
rule stated about an intermediate state, tabulate the transition over the
constructors and check whether the same predicate can be read off the
state you already have; the oracle's control flow is evidence about
behaviour, not a specification of where the test belongs. This fires next
on footnote references and on tables, which both add a container and will
face the same "does a blank close it" question.

## Price a parameterization by whether the parameter can stay implicit

**What happened.** Making the delimiter table a parameter was scoped from
a symbol count: `Wf.v` alone mentions inline-layer names 245 times, and
a section variable turns every one of those into a call site that needs
the argument. That number is what made the step look like a week. The
number was answering the wrong question. A type class carrying the table
*and* its side condition keeps the argument implicit, so the count that
mattered was not 245 but the number of *files*: one `Context` line each,
and not a single call site edited. What decided it was a twenty-line
scratch file with a toy table, a toy fixpoint and one `Example`, checking
the only thing that could have killed the design -- that `vm_compute`
still reduces through an instance, since every concrete `Example` in
`Inline.v` depends on it. Two minutes against an estimate that was off by
two orders of magnitude.

**General form.** For a development-wide parameterization, the cost is
not how many places mention the thing being parameterized. It is whether
the parameter can be inferred at those places. Explicit parameter: cost
scales with mentions. Implicit (class, canonical structure): cost scales
with files. The two differ by a factor of a hundred here, and which one
applies is decided by a property of the *elaborator*, not of the code
being changed -- so it is not derivable by reading the code at all.

**What to do instead.** Before pricing a "thread X through everything"
step, write the smallest file that has X as an implicit parameter, one
definition that uses it, and one `Example` that computes. If it reduces,
price the step in files. If it does not, price it in mentions and expect
the larger number. This is [[#Check whether a proof uses the structure
before pricing its removal]] one level up: there the question was which
proofs *use* the structure, here it is whether the uses have to *name*
it. Both fail the same way, by counting the diff instead of the work.

### The check that a parameterization took

The failure mode is silent. A statement written after a section's `End`
still typechecks -- it just quietly means the ambient instance, so
`roundtrip_doc` was a theorem about djot for an hour while its
neighbours were about the family, with nothing to indicate it. The same
goes for any file that never opened a section. `Check @thm` prints the
binder or does not, and that is the whole test; run it on every statement
the step was for, not on a sample.

## Prefer the stronger precondition when the weaker one is viral

**What happened.** `dconfig_ok` gained conditions that the scanner needs
of each table row -- nonzero width, punctuation, not a reserved
character. The obvious scoping was to ask them only of rows that are
switched *on*, since a switched-off row is never looked up. That version
cost a hypothesis: "this row exists" had to be threaded through
`dtoken_nonempty`, then `iscan_dtoken`, `iscan_marked_close_step`,
`iscan_marked_flush`, `iscan_marked_close_emit`, and then through
`iscan_productive` and `iscan_wf` -- predicates quantified over *all*
states, where the row comes from the state and not from a lookup, so
there was nowhere for the hypothesis to come from. Asking the conditions
of every row instead, enabled or not, deleted the hypothesis everywhere.
The cost to a table author is that a row they have switched off still
has to be spelled with something admissible, which is no cost at all.

**General form.** A precondition's price is not its strength, it is how
far it has to travel. A weaker condition that must be carried through a
chain of lemmas is more expensive than a stronger one that holds
unconditionally -- and the chain is usually invisible when the condition
is written, because it runs through predicates that quantify over states
rather than over the construct the condition is about.

**What to do instead.** When scoping a side condition to "only the cases
that need it", ask where the *users* get it from. If any user is a
predicate over all states, over all inputs, or over an inductive the
condition does not mention, the scoping will not survive; strengthen the
condition until it is unconditional and check that the strengthening
costs a real user something. Here nothing was lost, and the one place
that genuinely needs "this row exists" -- `dstyle_of`, where a
switched-off row is really not found -- kept its hypothesis and pays for
it in exactly one lemma.

### The other direction: a precondition weaker than the truth

**What happened.** Attribute attachment. `iattr_attach` could not ask
"what did this scope last emit", because `oout_app` splices a previous
line's output underneath and a scope that has emitted nothing would see
*that* line's last node. The plan's recipe, written a month earlier, was
to add an invariant to `iscan`: a non-whitespace `prev` implies either
pending text or something emitted. That invariant is false -- `[` sets
`prev` to `[` and pushes a scope with empty output -- and it was aimed
at the wrong object, since `prev` is the previous source byte, which the
delimiter open rules need, and "has this scope emitted anything" is a
different question that merely correlates.

The real obstruction was one hypothesis. The twenty `_app` lemmas
carried `starts_str base = false`, chosen because it is what the seam
merge in `osnoc_nonstr` needs. The suffix is in fact always a previous
line *headed by the `SoftBreak` that ended it* -- which `osnoc_nonstr`'s
own comment states in prose, and then says is "discharged by
construction rather than carried". Carrying it instead cost twenty
renames, one derivation lemma and a `reflexivity` at the single call
site, and the query became answerable, because a `SoftBreak` head is one
`oattach` declines exactly as it declines an empty scope.

**General form.** The lesson above is about a condition scoped too
narrowly across *lemmas*. This is the same mistake across *time*: a
hypothesis picked as "the weakest thing this proof needs" is right until
a later definition needs to ask a question the stronger fact would have
settled. The tell is a comment that states the stronger fact in prose
and then declines to carry it -- that is a fact the development knows
and cannot use.

**What to do instead.** When a new definition cannot be written because
some query is not stable under a composition lemma, look at that
lemma's hypothesis before adding an invariant anywhere. Ask what is
*actually* true of its argument at the call sites, not what the proof
happened to need. If the answer is stronger than the hypothesis and the
call sites can discharge it, the fix is a rename. Grep the file for
prose of the form "by construction rather than carried" -- each one is a
candidate. This fires next on footnote references and tables, which will
both want to read the current scope for the same reason attributes did.
