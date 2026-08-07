---
ai-disclosure: autonomous
date: 2026-08-07
author: claude/sonnet-5
---
# Lists' canonical roundtrip fragment: where it landed, and the one piece left

Written across a long session that started by estimating "nested lists
need a new theorem," found that estimate wrong twice (once too
optimistic, once too pessimistic), and ended with a real, committed
result — everything *except* `parse_cblock`'s own list case. Read this
before touching lists' roundtrip coverage again; it has the exact shape
of what's left and why the rest doesn't need re-deriving.

## What actually landed (compiles, axiom-free, zero `Admitted`)

- **`Strings.v`/`Line.v`**: general facts that `classify`, `indent_of`,
  and `is_thematic` are invariant under an all-whitespace prefix
  (`classify_ws_prefix`, `indent_of_ws_prefix`, `is_thematic_ws_prefix`,
  `drop_leading_ws_ws_prefix`, `is_blank_ws_prefix`), plus the canonical-
  line facts a bullet marker and its continuation indent need
  (`classify_bullet_open`, `classify_bullet_cont`,
  `indent_of_bullet_open`, `indent_of_bullet_cont`), and the same for a
  *padded* quote/heading prefix (`classify_canonical_quote_pad`,
  `classify_canonical_heading_pad`) — see below for why padded quote
  facts turned out to matter.
- **`Parser.v`**: the `PList` step-equation lemmas quotes already had and
  lists never did — `step_list_blank`, `step_list_indented`,
  `step_list_sibling`, `step_list_diffstyle`, `step_list_lazy`,
  `step_list_close`. Also: padded analogues of every quote/heading seed
  lemma (`parse_lines_quote_cont_pad`, `parse_lines_quote_pad`,
  `quote_uniformity_pad`, `parse_lines_heading_seed_pad`), each
  generalized over an arbitrary blank *separator* (not hardcoded
  `EmptyString`) — needed once a padded block turned out to be followed
  by something other than a literal empty line (see below).
- **`Render.v`**: `CList (sp : list_spacing) (items : list (list cblock))`
  in `cblock`; its rendering (`cb_lines`, `indent_lines`, `list_lines`);
  `cblock_ind2` extended to a three-predicate induction (`P`/`Q`/`R`,
  `R` = "a list of item lists," built from `Q` per item); `cb_ok`'s
  spacing condition derived *structurally* from the item tree
  (`item_forces_loose`/`items_force_loose`) instead of replaying
  djot.js's event-driven flag — checked against the real state machine
  and now proof-checked via `cb_ok_lines_ok`, which is fully proven.
  Two exclusion predicates, both load-bearing and both explained inline
  where they're defined: `list_content_safe` (no code fence *or* nested
  list anywhere inside an item) and the weaker `no_nested_list` (no
  nested list, full stop — code fences elsewhere are untouched).
- **`Roundtrip.v`**: `cb_ok_lines_ok` covers `CList` completely — every
  canonical list rendering satisfies `lines_ok`. `parse_cblock_pad` is
  the actual payoff of tonight's work: a from-scratch, fully proven
  generalization of `parse_cblock` that shows an arbitrary whitespace
  pad in front of every line of a `list_content_safe` cblock doesn't
  change what it parses to — restricted to `list_content_safe` because
  that's exactly the set for which the proof goes through (see the two
  sections below). `parse_cblock` itself, the *original* theorem,
  compiles again, extended with a `no_nested_list` hypothesis whose only
  effect is a vacuous `CList` case — every other construct (paragraph,
  thematic break, code block, heading, quote-of-anything-except-a-
  nested-list) is proven exactly as before tonight, unchanged.
  `parse_sep`, `render_cb_lines`, `render_djot_cblocks`, `roundtrip_blocks`,
  `roundtrip_doc` all carry the same hypothesis through mechanically.

Net effect: **lists still don't have roundtrip coverage through
`roundtrip_blocks`/`roundtrip_doc`** (same as before this session), but
everything *adjacent* to that gap — the canonical form, `cb_ok`, and the
single hardest supporting lemma (`parse_cblock_pad`) — is now built,
proven, and committed. What's left is one induction, described precisely
below.

## Two findings that changed the estimate, in the order they were found

**Finding 1 — the nesting problem is real, but only for the common case.**
A list nested on its own physical line, immediately after its parent's
marker (`"- - a"`), is free: the parent's own marker-stripping hands the
child list its *exact*, residue-free first line, so the child's
`ls_indent` comes out identical to standalone parsing. A list nested the
normal way — its own line, separated by a blank (`"- a"` / blank /
`"  - b"`) — is not free: that line reaches the parser with the parent
item's indent still attached (`PList`'s "indented, recurse unchanged"
branch never strips anything), so the child's `ls_indent` genuinely
comes out shifted by the parent's contribution. Proving that shift never
changes a routing decision is a real, self-contained theorem (a
`quote_uniformity`-style induction generalized by a `Nat.ltb`-shift
argument) — not yet built. This is why lists don't get quotes' free ride
on nesting, and it's *specific to nesting* — flat lists (no `CList`
directly or transitively inside any item) never form a second `PList`,
so this problem doesn't apply to them at all.

**Finding 2 — even flat lists need almost the same amount of new machinery,
just not the shift argument.** The naive hope was "flat lists only need
what's already proven, generalized trivially." Two things pushed back:

- A list item's own continuation lines (second and later lines of its
  first block, and every line of any *later* block in a multi-block
  item) get `bullet_cont` ("  ") in front. For the *later blocks*, this
  needs `parse_cblock`'s whole machinery re-derived under an arbitrary
  pad — not because any single case is hard (each one turned out to be a
  near-mechanical copy of the unpadded proof, just inserting one
  `classify_ws_prefix`/`is_thematic_ws_prefix` rewrite per case), but
  because the *statement itself* has to be re-proven from scratch via
  its own `cblock_ind2` induction. That induction is `parse_cblock_pad`,
  and it took the bulk of tonight's remaining time — not because any
  step was conceptually hard, but because getting each rewrite's
  argument order and scope annotations (`%string` vs `%list` — a
  known trap, see `djot-v-setup` memory) exactly right, interactively,
  line by line, is real work.
- The separator between two blocks *inside* a padded item is not
  `EmptyString` — `map (pad ++) (cb_lines c ++ EmptyString :: rest)`
  distributes the pad onto the separator too, turning it into
  `pad` (still blank, since `pad ++ "" = pad` and `pad` is
  all-whitespace, but not literally empty). `parse_cblock`'s original
  statement hardcodes `EmptyString` as the tail's head throughout —
  every seed lemma it leans on (`parse_lines_blank_cons`,
  `parse_lines_heading_close`, the quote-close base case buried in
  `parse_lines_quote_cont`) needed generalizing from "closes on
  `EmptyString`" to "closes on any line that classifies `KBlank`." This
  turned out to be mechanical too (those lemmas were already stated
  generically over the *closing* line's identity; only the pad-variant
  quote lemmas needed a genuine second generalization pass), but it's
  the reason `parse_cblock_pad`'s statement carries an explicit `sep`
  parameter instead of a bare `tail`.

Net: flat and nested lists both need `parse_cblock_pad`. Nesting adds
the shift theorem on top; flat lists don't. That's the actual size
difference — smaller than "flat is easy, nested is a project," bigger
than "both are nearly free."

## Code fences: still excluded, for the reason already on record

Fence content is verbatim (`fence_close` is the *only* test ever applied
to a line inside a fence — Parser.v). `PList` hands a line to its item's
state unchanged, so a fence nested in a list item keeps the item's
`"  "` baked into its content on reparse. This is the same,
already-documented gap as indented fences inside quotes
(`260802-handover.md` thread 5) — not new, not list-specific in its
root cause, deliberately not fixed here. `list_content_safe` encodes the
exclusion; `parse_cblock_pad` requires it; nothing about tonight's work
changes the size or shape of that separate thread.

## What's actually left: `parse_cblock`'s own `CList` case

Concretely, the missing piece is one lemma with roughly this shape —
an item-sequencing induction over `items : list (list cblock)`,
threading a `PList` state:

- **Open**: the first item's first line is `bullet_open ++ <content>`.
  `classify_bullet_open` (Line.v, already proven) extracts `<content>`
  residue-free; `item_marker_ok` (already required by `cb_ok`) rules out
  the one djot.js-order gotcha (`"- " ++ content` reading as a thematic
  break). `step_list_open` (Parser.v, already proven) does the actual
  transition.
- **Item content**: the item's own remaining lines, via
  `parse_lines_cont_seed` / `parse_lines_heading_seed_pad` /
  `parse_lines_quote_cont_pad` for its first cblock's continuation, and
  `parse_cblock_pad` (pad = `bullet_cont`) for any later cblock in a
  multi-block item. All three pieces exist and are proven; what's
  missing is threading them together across item boundaries.
- **Sibling vs. close**: `step_list_sibling` / `step_list_diffstyle` /
  `step_list_close` (Parser.v, already proven) handle the transition at
  each item boundary — the remaining work is showing the flags
  `list_next`/`list_blank`/`list_content` compute along the way land on
  exactly what `item_forces_loose`/`items_force_loose` (Render.v,
  already proven equivalent to `cb_ok`'s own spacing condition) predict
  structurally.

None of this needs new lemmas in Parser.v or Line.v — the equation-lemma
layer is complete. It needs one careful induction in Roundtrip.v tying
pieces that already exist together, plus (for nesting specifically) the
shift theorem from Finding 1 if that scope is ever revisited.

## Where the exclusions live, and how to remove them later

Two hypotheses were threaded through the affected lemmas so nothing had
to be faked or left `Admitted`:

- `list_content_safe` (Render.v) — required by `parse_cblock_pad`,
  hence by whatever eventually proves `parse_cblock`'s `CList` case for
  items. Drop it (replacing with "no restriction") only once the
  fence-dedent thread (separate, pre-existing) is fixed.
- `no_nested_list` (Render.v) — required by `parse_cblock` /
  `parse_sep` / `render_cb_lines` / `render_djot_cblocks` /
  `roundtrip_blocks` / `roundtrip_doc`, purely because `parse_cblock`'s
  own `CList` case doesn't exist yet. The moment that case is proven
  (using `parse_cblock_pad` plus the induction sketched above),
  `no_nested_list`'s hypothesis on all six lemmas becomes vacuously
  `true` for every cblock and can just be deleted along with the
  predicate — no other proof in the chain needs to change shape.
