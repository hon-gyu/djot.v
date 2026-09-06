---
ai-disclosure: ai-generated
date: 2026-08-02
---
# Formalizing djot in Rocq

Research notes, 2026-08-02. Covers what a Rocq formalization of djot would be,
which reference materials anchor it, which properties are provable and at what
cost, how the knob-extension question decomposes, and what prior art transfers.

Status: exploratory. Nothing here has been attempted. Literature claims are
marked by whether they were verified.

## 1. The Question

Two questions, in dependency order:

1. Does djot actually have the properties it is designed around — container
   uniformity, render roundtrip, local link classification, block prefix
   determinism, and no-backtracking parsing?
2. Given those properties, **how far can djot be extended before they break?**

The second is the real goal. The working complaint is that djot is too
restrictive: it bought its properties with blunt instruments (no indented code,
no setext headings, no paragraph interruption, mandatory space after `>`), and
there is no argument that those instruments were the cheapest available.

There is a prior attempt at question 1 by other means: **oymarkit**, an OCaml
implementation whose parser threads an options record of ~50 knobs (indented
code on/off, emphasis flanking rules, lazy continuation, …), tested with a
QCheck property harness — a generator of ASTs, runtime well-formedness
predicates that filter the generator's output, and roundtrip/uniformity
properties checked by sampling. That work is question 1 empirically, and its
~50 knobs are the search space for question 2. Where this note says "the
QCheck attempt," that project is what is meant; several of its pain points
(generator correctness, roundtrip canonicalization) turn out to be artifacts
of testing rather than proving, and disappear under formalization (§4.1).

## 2. The Reference Materials

Four artifacts, playing different roles:

- **The prose spec** — `doc/syntax.md` in the djot repo (mirrored at
  `reference/djot-syntax-reference.md`). Normative, informal. Crucially, it
  makes explicit design commitments (§4 below) that can be formalized as
  theorem statements.
- **The djot README rationale** — mirrored at
  `reference/djot-repo-readme.md`. It states the broader design goal that it
  should be possible to parse djot markup in linear time without
  backtracking. This is an existential implementation and performance claim,
  not the block grammar rule the syntax reference states.
- **djot.js** — the reference implementation, ~4,300 LOC TypeScript. The
  authority on edge cases. Not a viable verification *target*: there is no
  mechanized TS semantics, so no path from that source to a Rocq theorem.
- **djoths** — jgm's Haskell implementation, ~3,600 LOC pure Haskell
  (`Blocks.hs` 1151, `Inlines.hs` 527, `Djot.hs` 495, `AST.hs` 449,
  `Parse.hs` 400, `Html.hs` 350, `Attributes.hs` 187, `Options.hs` 25).
  The right *model* to transcribe (§3).

The strategy: write a knob-indexed parser in Gallina, modeled on djoths's
architecture; formalize the prose spec's normative commitments as the theorem
statements; extract to OCaml and differential-test against **both** djot.js and
djoths on the existing corpora (djot.js's 26 `.test` files plus jest specs;
djoths's test suite). Disagreements between the two oracles are themselves
spec data — file them upstream or record a decision.

Two framings for the theorems, and both are available:

- **Spec conformance.** The prose spec is an external authority. Formalize its
  normative statements as a relational spec in Gallina and prove the parser
  satisfies it — the CompCert move (prose standard → mechanized spec →
  verified implementation). The formalization of the prose is the trust
  boundary, and it is auditable.
- **Meta-properties.** Termination, totality, roundtrip, uniformity, locality —
  properties *of* the parser that need no external spec. These are where the
  extension question lives.

The prose spec is informal enough that most of the value is in the
meta-properties, but conformance framing keeps the theorems honest: several
meta-properties turn out to be things the spec already promises (§4), so the
theorem is "djot keeps its word," not "here is a property I invented."

## 3. The Model: djoths

Facts from reading the source, relevant to feasibility.

- **The parser is already a state monad.**
  `Parser s a = ParserState s -> Maybe (ParserState s, a)` (`Parse.hs:57`).
  Direct Gallina transcription — no mutable-state reconstruction needed.
- **No regexes.** `Parse.hs` is a ~400-line hand-rolled combinator library
  (`satisfyByte`, `byteString`, `lookahead`, `peekBack`, …), each combinator a
  few lines of transcribable code. This eliminates what would otherwise be the
  largest trust gap: djot.js's 33 sticky-flag JS regexes would need either
  ~300 lines of unverified hand-translation or a mechanized ECMAScript regex
  semantics sitting under every theorem.
- **No UTF-16.** djoths parses UTF-8 bytes directly. No surrogate-pair model.
  (djot.js mixes `charCodeAt`/`codePointAt` with Unicode-aware regex classes
  and would force a UTF-16 code-unit model.)
- **Containers are first-class specs.** `Blocks.hs` organizes block types as
  `BlockSpec` records — `blockStart` / `blockContinue` / `blockClose` /
  `blockFinalize` — dispatched over a container stack. This is exactly the
  seam needed for per-container uniformity proofs and for knob
  parameterization (§6): a knob that adds or modifies a container is a change
  to one record, not to a parser's control flow.
- **A djot renderer is included.** `Djot.hs` renders the AST back to djot
  source — a ready-made roundtrip oracle for §4.1, not just a parse oracle.

Obstacles:

- **Combinator backtracking.** djoths uses `Alternative`/`<|>` with
  `lookahead` and even `peekBack`. djot.js's ordinary delimiter strategy is a
  better starting point: one left-to-right pass, an opener stack, and
  resolution by annotating an earlier match. It is not itself a complete
  witness for the goal, because `reparseAttributes` re-feeds failed attribute
  slices. The Gallina parser should preserve djot.js behaviour with monotone
  source consumption, using compound state where a special parse
  needs an ordinary-inline fallback. See `.project/no-backtracking.md`.
- **`many`/`some` termination.** The classic Rocq annoyance with combinator
  parsers: each repetition needs a progress argument (consumes input or
  fails). Well-trodden — this is precisely what the verified-PEG literature
  handles (§8.2) — but it is where the termination-measure effort lives.
- **Block loop measure.** The container open/continue/close interaction needs
  a lexicographic measure over (input position, container-stack depth). Line-
  level progress is easy; the stack interaction is the fiddly part.

Out of scope: HTML rendering fidelity (`Html.hs`), djot.js's `pandoc.ts` /
`filter.ts` / `cli.ts`. Filters mutate the AST under dynamic dispatch — least
verification-friendly code in either repo, and no interesting properties
attach.

## 4. The Properties

Ordered by value per unit effort. A recurring pattern: the strongest properties
are *stated in the prose spec* as design commitments, so proving them is
conformance, not invention.

### 4.1 Roundtrip and Uniformity — Rocq is strictly better than QCheck

The QCheck attempt encodes well-formedness as *runtime predicates* filtering
a generator after the fact: no empty paragraphs, no empty block sequences, no
empty lists, no trailing blank lines in blocks, no leading blank prefix in
list items.

In Rocq these become **indices on an inductive family**: a `wf_block` whose
constructors cannot build `Paragraph ∅` or `Blocks []`. Two consequences:

- **The generator becomes free.** Any inhabitant of `wf_block` is well-formed
  by construction, eliminating the question the QCheck attempt's
  generator-correctness tests exist to answer.
- **The canonicalization quotient may disappear.** The QCheck harness has a
  canonicalization step for terminal blank-line ownership, carrying a 30-line
  comment explaining why that ownership is ambiguous. That is a
  symptom of the AST being too loose. Make ownership canonical in the type and
  roundtrip becomes exact equality. Where multiple renderings are genuinely
  valid, use the Narcissus framing (§8.3): specify the format as a relation
  over all valid encodings and prove the parser inverts it.

**Uniformity is a corollary, not a separate theorem** — and it has two
pedigrees worth connecting. The QCheck attempt tests block-quote uniformity
and list-item uniformity independently, one wrap/unwrap property each. But
uniformity was named as a design principle in *Beyond Markdown* ("the contents
of a list item should have the same meaning they would have outside the list
item"), and djot purchases it with one structural fact the spec states
normatively: block structure is discernible line by line from prefixes alone,
before inline parsing, with no future-line dependence. Prove that **prefix
determinism** lemma once and uniformity follows for every container —
including ones not yet added.

One subtlety in stating it. In pipe tables, a separator line retroactively
makes the *previous* row a header, and its alignments flow to subsequent rows.
Block *structure* still never depends on a future line, but a line's
*role/attributes* do. The lemma must quantify over tree shape, not the full
parse result, or the table rule falsifies it. Likewise heading
auto-identifiers and implicit heading references are a whole-document second
pass and must be excluded from any locality statement (§4.3).

### 4.2 No-backtracking — the honest form of the performance claim

Two source claims had previously been conflated here. The README explicitly
says that it should be possible to parse djot markup in linear time without
backtracking. The syntax reference states a narrower semantic rule: blocks
can be parsed line by line, and a line's contribution to block structure does
not depend on a future line. The first covers the whole parser as an
existential design goal; the second directly supports a block prefix theorem.

Here, backtracking means consuming a region, discovering later that a
speculative interpretation failed, then submitting that consumed region to
parsing again. It does not forbid opener-stack annotation, delayed decisions,
or a product state whose alternatives advance together on each new
byte. In particular, djot.js's `reparseAttributes` backtracks, but its
observable recovery can be reproduced without replay by maintaining an
ordinary-inline shadow while the attribute candidate is open. The full source
interpretation and its consequences are recorded in
`.project/no-backtracking.md`.

The provable theorems, in order of strength:

1. **Block prefix determinism** (what the syntax reference promises): future
   lines do not change an earlier line's contribution to block shape.
2. **Monotone source consumption** (a witness for the README goal): the
   parser never restarts tokenization on a consumed region. For inlines this
   permits opener stacks and compound states, but not buffered replay.
3. **A step-count bound**, via a cost-counting state monad
   (`steps (parse s) ≤ f |s|`), if wanted later. Gallina has no cost model
   and extraction erases complexity, but the parser is pure, so no Iris or
   time credits are needed. The README's linear-time goal is not discharged
   by monotone consumption alone: closer resolution may inspect opener-stack
   depth, so a separate amortization or counterexample analysis is required.

### 4.3 Locality of inline classification — djot's most distinctive claim

The spec: "the parsing of the link is 'local' and does not depend on whether
the label is defined." This is fix #2 in *Beyond Markdown* — reference links
recognizable by shape alone, motivated by syntax highlighting and single-pass
parsing, and the reason shortcut references were removed. It generalizes:

> **Locality.** The classification of any inline element is a function of the
> inline text alone — independent of the reference map, the note map, and the
> rest of the document.

Formally: parse the same inline sequence in two documents with different
reference/footnote definitions; the ASTs differ only in resolved targets,
never in structure. This is cheap to state, moderately cheap to prove given
the two-phase architecture (classification happens before resolution), and it
is *the* property that distinguishes djot from CommonMark. Scope it to
classification, not resolution: heading auto-identifiers, implicit heading
references, and attribute transfer from reference definitions are legitimately
whole-document.

### 4.4 Termination and totality

Cheap relative to the others, and prerequisites for everything else. Totality
(no crash on any input) is free once the parser is a total Gallina function;
termination is the measure work in §3. Note the spec's **Nesting limits**
section explicitly licenses bounded nesting (a limit of 512 is called
"perfectly safe"), so a fuel-indexed parser with a proven bound is
spec-conforming — a simpler termination story is available if the measure
gets ugly.

### 4.5 Small combinatorial specs worth writing down

Low-effort, high-precision targets the implementations agree on but nobody has
stated exactly:

- **Hyphen division**: sequences of hyphens divide into em/en/hyphens,
  "uniformly if possible, preferring em-dashes when uniformity can be achieved
  either way" (4 → two en; 6 → two em). A ten-line decidable function and a
  uniqueness proof.
- **List-type ambiguity**: `i.` then `j.` resolves the first item to
  lower-alpha "so as to continue the list." An item's type depends on its
  *siblings* — a deliberate, bounded exception to per-item locality that any
  uniformity statement over list items must accommodate.
- **Smart punctuation** quote-direction heuristics: "pretty good about
  figuring out from context" is the spec's entire statement. Formalizing the
  actual rule (from the implementations) would be a small contribution to the
  spec itself.

## 5. The Invariant Decomposition

The move that makes the extension question tractable.

1. Identify a small set of **structural invariants** `I`: prefix determinism;
   single-pass inline scanning; delimiter-run disjointness;
   blank-line-only paragraph termination; locality of classification.
2. Prove `I ⟹ P` **once**, for each property `P` of §4.
3. For each knob `k`, prove `preserves k I` — ~50 *local* obligations.
4. Prove a **frame lemma**: knobs whose trigger sets (the characters and
   contexts where they alter the parse) are disjoint compose automatically.

Step 4 is the payoff and is exactly what the knob project has always wanted:
knobs that provably interact well with each other, with no ambiguity.

Disjointness is mechanically checkable. `colon_symbols` triggers on `:`,
`block_id` on `^`, `tilde_code_fences` on `~` — provably non-interacting. The
interesting residue is the small set that *does* overlap:

- **Emphasis cluster:** `emphasis_delims`, `strong_emphasis_delims`,
  `intraword_emphasis`, `simple_emphasis_flanking`, `marked_emphasis_delims`,
  `strong_emphasis_width` — all fight over delimiter-run classification.
  History says this cluster deserves the attention: *Beyond Markdown*
  proposed `~`-based intraword emphasis, and shipped djot dropped it for
  `{_..._}` braces — the one part of the design that visibly churned between
  rationale and release.
- **Line-prefix cluster:** `indented_code`, `list_indent`,
  `lazy_continuation`, `block_quote_marker_space`,
  `blocks_interrupt_paragraph`.

Three or four clusters of four or five knobs each: small enough to verify
exhaustively, and it tells you precisely where design attention belongs.

djoths's `BlockSpec` architecture (§3) is the implementation shape that keeps
step 3 local: a knob should be a change to one spec record or one decision
point, never a thread through control flow.

## 6. The Extension Question

Once `I ⟹ P` is proved, hunt for **cheaper purchases of the same invariant**.
For each restrictive djot choice, the proof obligation exposes the *weakest*
precondition, and djot's actual setting is usually strictly stronger.

Worked example, now checkable against the recorded rationale.
`blocks_interrupt_paragraph` is all-or-nothing and djot sets it false — no
block start interrupts a paragraph. *Beyond Markdown* records why: accidental
list creation ("…maybe even / 220. But he was no more than five feet tall")
and the uniformity principle jointly forced CommonMark into an "ugly
heuristic" (only ordered lists starting at 1 interrupt), and djot chose the
blunt total ban instead. But interruption only threatens prefix determinism
for constructs whose start marker is ambiguous with paragraph continuation
text. A fence or `>`-with-space is unambiguous at line start; a bare ordinal
like `220.` is precisely the ambiguous case jgm was worried about. So the ban
is strictly stronger than the invariant requires, and the proof-guided knob —
"interruptible by unambiguous-marker constructs only" — is *more permissive
than djot while provably immune to the exact accident the rationale cites*.

`list_marker_interrupts_paragraph` already exists as a partial refinement of
exactly this. It was guessed. The proof would give the *maximal* safe
refinement.

## 7. Relationship to the Oracles

The output is a *verified djot*: theorems hold of the Gallina parser, and its
relationship to the ecosystem is established by differential testing, not
proof.

- **djot.js** is the reference; its corpus (26 `.test` files + jest specs) is
  the primary conformance suite.
- **djoths** is a second oracle with its own test suite and, via `Djot.hs`, a
  roundtrip oracle.
- Extract to OCaml, run all corpora against the extract and both oracles.
  Any three-way disagreement is a finding: either a bug in one oracle, an
  underspecified corner of the prose spec, or a transcription error — all
  worth knowing, and the first two worth filing upstream.

## 8. Related Work

Verified by search on 2026-07-30 unless marked otherwise.

### 8.1 The gap is real

No mechanized verification of Markdown, CommonMark, djot, reStructuredText, or
AsciiDoc was found. "Formal spec" in this space has meant conformance suites:
CommonMark's spec is prose plus ~650 executable examples, and GitHub's
[formal GFM spec](https://github.blog/engineering/user-experience/a-formal-spec-for-github-markdown/)
is a grammar plus a cmark fork.

Relevant context: **djot exists because of this.** jgm built it after
CommonMark precisely because CommonMark's emphasis and container rules
resisted clean specification — *Beyond Markdown* is the design document, and
each of its six "fixes" is a provability-motivated restriction adopted without
a proof establishing how far it needed to go. That is the gap this work
targets.

### 8.2 Verified parsing — mature, pick a technique

- [TRX](https://arxiv.org/pdf/1105.2576) — formally verified PEG parser
  interpreter in Coq (Koprowski & Binsztok, ESOP 2010). Closest to the
  combinator-with-lookahead style, and the reference point for the
  `many`/`some` progress obligations in §3.
- Menhir's Coq-validated LR parser in CompCert (Jourdan, Pottier, Leroy) — the
  production-hardened point in the design space. *Not re-verified this
  session.*
- CompCert's larger methodology — prose standard formalized as the spec,
  implementation proven against it — is the template for the conformance
  framing in §2.

(With djoths as the model, the ECMAScript-regex-semantics contingency that a
djot.js-shaped formalization would need is moot: there are no regexes to
model.)

### 8.3 Roundtrip proofs — Narcissus is the closest match

[Narcissus](http://adam.chlipala.net/papers/NarcissusICFP19/NarcissusICFP19.pdf)
(Delaware, Suriyakarn, Pit-Claudel, Ye, Chlipala; ICFP 2019) specifies a
format as a **nondeterministic relation** capturing all valid encodings of a
value, then derives a decoder proven inverse to it.

This is the principled version of the QCheck harness's terminal-blank
canonicalization: that step exists because one AST has many valid renderings.
Rather than
canonicalizing after the fact, state in the spec that these renderings are all
valid, and prove the parser inverts the relation.

### 8.4 Modular composition — the frame lemma, already done for LALR

[Schwerdfeger & Van Wyk, PLDI 2009](https://www-users.cse.umn.edu/~evw/pubs/schwerdfeger09pldi/schwerdfeger09pldi.pdf),
*Verifiable Composition of Deterministic Grammars*. Each extension is analyzed
**in isolation** against the host grammar; any extension passing the test
composes with any other passing extension, guaranteed conflict-free.

That is step 4 of §5, including the part that looked like the research
contribution. **Read this first** — it shows what the isolation condition has
to look like. Follow-ups:
[parse table composition](https://link.springer.com/chapter/10.1007/978-3-642-12107-4_15),
[modular well-definedness for attribute grammars](https://www-users.cse.umn.edu/~evw/pubs/kaminski12sle/kaminski12sle.pdf).

### 8.5 The 2⁵⁰ problem has a name: family-based analysis

Thüm, Apel, Kästner, Schaefer & Saake, *A Classification and Survey of
Analysis Strategies for Software Product Lines*, ACM CSUR 47(1), 2014. Plus a
[formal framework](https://www.se.cs.uni-saarland.de/publications/docs/CTA+21.pdf)
formalizing the strategies.

The taxonomy maps onto the knobs directly:

| Strategy | Meaning here | Verdict |
|---|---|---|
| product-based | test each config | what QCheck does; hopeless at 2⁵⁰ |
| feature-based | verify each knob in isolation | §5 steps 3–4 |
| family-based | one analysis over a variability-annotated artifact, covering all configs | likely lower friction |

Family-based means a single knob-indexed parser in Gallina with proofs
quantified over the config record. Since the oymarkit parser already threads
an options record end to end, this may be the better route. The literature has
the tradeoffs worked out.

### 8.6 Unverified pointer

Hosoya & Pierce's **XDuce** and **CDuce** use regular tree automata as *types*
for XML documents — arguably the closest ancestor of the QCheck attempt's
well-formedness predicates. From memory, **not** verified this session.

## 9. What Is Novel, and What Could Go Wrong

**Novel:** not the techniques — all four literatures above exist. The target.
Every precedent assumes a context-free or PEG-shaped grammar, where
composition is analyzed via parse tables or derivatives. Markdown-family
languages are not context-free (delimiter-run matching, container line
prefixes, reference resolution as a separate pass), so neither the LALR
conflict test nor standard variability-aware type checking applies off the
shelf. The prefix-determinism invariant is the substitute for "no LALR
conflict," and finding the right invariant for a non-context-free document
format is the contribution.

**Main risk:** §5 step 3 requires the parser to be *parameterized* by the knob
record in Gallina. If knobs turn out to be deeply entangled in control flow
rather than localized to decision points, the ~50 local obligations degrade
back toward exponential. oymarkit's stated discipline of gating each feature
behind a centralized module-level flag is the right instinct — **worth
auditing whether that discipline actually holds across all ~50 knobs before
committing**, and worth adopting djoths's `BlockSpec` shape where it does not.

**Secondary risks:**

- The README's linear-time goal (§4.2) needs a cost model and may need an
  amortization argument; monotone source consumption alone is insufficient.
- The oracles may disagree with each other in corners the prose spec leaves
  open. Budget for adjudicating these rather than being surprised by them.
- Theorem-statement traps: prefix determinism must be about tree shape (the
  pipe-table header rule), and locality must be about classification, not
  resolution (auto-identifiers, implicit references, attribute transfer).
  Getting these scopes wrong means proving a falsehood is unprovable, slowly.

## 10. Staging

| Step | Deliverable | Effort |
|---|---|---|
| 1 | `wf_block` inductive family — well-formedness as types | 2–4 wk |
| 2 | Renderer in Gallina + roundtrip on `wf_block` (djoths `Djot.hs` as model and oracle) | 1–2 mo |
| 3 | Prefix-determinism lemma → uniformity for all containers; locality of classification | 1–2 mo |
| 4 | Knob-indexed parser (djoths architecture, djot.js inline strategy) + ~50 `preserves k I` obligations | 3–6 mo |
| 5 | Frame lemma for disjoint trigger sets | the research |
| — | Cost-monad complexity bound | deferred; requires separate cost and amortization analysis |

Steps 1–2 pay for themselves even if the effort stops there: they eliminate
the generator-correctness testing burden and the canonicalization quotient,
both live costs in the QCheck harness today. Step 3 adds the two theorems that are
djot's actual design commitments — the syntax reference's block prefix rule,
the README's no-backtracking goal, and the spec's locality promise — at which
point the formalization is already saying
something true and citable about djot itself. Step 5 is where this stops being
engineering.
