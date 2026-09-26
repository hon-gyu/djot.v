---
ai-disclosure: ai-generated
---
# Performance of the extracted parser

Evergreen, per [[README]]: the mechanism and the ranked list describe the
tree now. Measurements are dated and carry the commit they were read at;
re-measure before quoting them.

Status: document-size and paragraph-length quadratics fixed (`split_lines`,
`rev_string`, `List.rev`).  `nat` is extracted to OCaml `int`, which
removed unary arithmetic and character classification through unary
`nat` and roughly halved ordinary-prose parse time.  The HTML renderer
is linear, and so is heading-identifier assignment up to a log factor.
Not production ready: two input shapes are superlinear in the parser
(ranked below).  The last comparison
against cmarkit predates the `int` change; re-measure before quoting it.

The extracted package now exposes location-on block and document parses
beside the existing semantic parser.  `line_table` and `resolve_span`
convert recorded spots to byte coordinates.  The location-on block parse
is benchmarked beside the semantic one and the incumbent in
"Locations on, against the incumbent" below, at about 10% over the
semantic parse on ordinary prose.

## The mechanism

`ExtrOcamlNativeString` maps a Gallina `string` to a flat OCaml `string`,
but a match on `String c s'` still has to produce `s'`. It extracts to

```ocaml
(fun f0 f1 s ->
   let l = String.length s in
   if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))
```

and `String.sub` copies the tail. A structural recursion over a string of
length n therefore copies n-1, n-2, ... bytes: O(n^2). Building a string
with `String c acc` extracts to `String.make 1 c ^ acc` and has the same
cost on the accumulator. Neither is visible in Rocq, where both are O(1).

Three more costs have the same character, invisible under `vm_compute`
and quadratic or worse once extracted (all three are now fixed):

- Stdlib `rev` is `rev l' ++ [x]`, O(n^2), and `app` is not tail
  recursive.
- Stdlib `String.length` is a structural recursion: a tail copy per
  character, a unary result, and a stack frame per character.
- Unary `nat`: `nat_of_ascii` goes through an 8-bit `N` and expands to up
  to 255 cells per character classified, and arithmetic recurses once
  per unit, not in tail position.  A nine-digit list start
  (`123456789. ok`) overflowed the stack.

A deep non-tail recursion also costs the GC: every minor collection scans
the whole stack, so a recursion n frames deep makes the collector's share
grow with n.

## Fixed

`split_lines` ran over the whole document before anything else
(`Step.parse_blocks`), so every parse started with O(document^2) copying:
about 325 GB of `memmove` for an 806 KB input.

`extraction/Extract.v` replaces `Strings.split_lines`, `Strings.rev_string`,
`List.rev`, and `String.length` with native OCaml by `Extract Constant`.
These are **trusted, not proved**: the theorems are about the Gallina
definitions, and the OCaml is asserted equal to them.  The native
`String.length` still builds a unary `nat`, but does so tail-recursively
without copying the string.

How the equality was checked (2026-09-13):

- `split_lines` and `rev_string` against the previous extraction, taken
  from `git show 223cbf0:dist/src/Strings.ml`: every string over
  `{a, b, space, \n, \t, \r}` up to length 6, plus 20000 random strings at
  each length 7 to 12. 419593 strings, no difference.
- test suite 287/287 and generated 6167/6167 exact HTML, as before.
- depth-3 roundtrip: 43857 documents, no mismatch.

How the additions were checked (2026-09-16):

- extracted `String.length` against the previous extraction on every string
  over `{a, b, space, \n, \t, \r}` up to length 6, every one-byte string,
  and 20000 deterministic random byte strings at each length 7 to 12;
  176243 strings, no difference;
- extracted `List.rev` against the previous extraction on every list over
  `{0, 1, 2}` up to length 10; 88573 lists, no difference;
- test suite 287/287 and generated 6167/6167 exact HTML;
- depth-3 roundtrip: 43857 documents, no mismatch;
- the committed extracted package matched the extraction.

`nat` as OCaml `int` (2026-09-26).  `Extract Inductive nat` maps `nat`
to `int`; `add`, `mul`, `sub`, `pred`, `eqb`, `leb`, `ltb`, `div` and
`modulo` of both `Init.Nat` and `PeanoNat.Nat` are OCaml arithmetic, with
`sub` truncated at zero and division by zero as Gallina defines it;
`nat_of_ascii` is `Char.code`, `ascii_of_nat` keeps the low eight bits,
and `Strings.nat_str` is `string_of_int`.  `int` wraps at `max_int`
where `nat` does not.  The parser's numbers are lengths, positions,
counts, and numerals read from the input; a roman numeral is at most
1000 per character, and a decimal list start is the one numeral that
could otherwise grow without bound.  The theories now take no decimal
marker longer than 18 digits (`Line.dec_digits_max`), and
`Marker.dec_start_bound` proves every start the parser reads is below
10^18.  The renderer's side condition `ck_ok` asks the same of a decimal
list's last number (`Marker.dec_fits`).

How the substitution was checked (2026-09-26), old extraction against new:

- every realized operation on all pairs of operands up to 150, every
  byte for `nat_of_ascii`, 0 to 2000 for `ascii_of_nat`, 0 to 20000 for
  `nat_str`;
- `Html.convert` on the djot.js test files and benchmark inputs, every
  string over `{1, 9, ., ), (, space, a, i, \n, -}` up to length 6, every
  string over a 22-character marker alphabet up to length 4, and 4000
  random strings at each length 5 to 60; 1539344 inputs, no difference;
- test suite 287/287 and generated 6167/6167 exact HTML; depth-3
  roundtrip 43857/43857; located bounds 44150/44150.

The HTML renderer (2026-09-26).  Three quadratics, now linear:

- `render_inlines_foot` and `render_blocks_foot` folded with `out ++ s`,
  copying the output so far once per node.  They are now right
  recursions, like the inner renderers; `render_inlines_foot` replaced
  the proof-only `render_ils_foot`, which had the same definition.
- `serialize` joins with right-nested `++`.  It stays the specification;
  `render_html` uses `serialize_flat`, which prepends pieces to an
  accumulator and joins once with `String.concat` (native under
  `ExtrOcamlNativeString`), and `serialize_flat_serialize` proves the two
  equal.
- `Html.escape` and `Html.escape_attr` are realized by a `Buffer` loop.
  Trusted, like the substitutions above.

Checked (2026-09-26): both escapers against the previous extraction on
every byte, every string over `{&, <, >, ", a, '}` up to length 6, and
200 random byte strings at each length 2 to 300 (116043 checks, no
difference); `Html.convert` on the 1539343-input differential above, no
difference; test suite, generated, roundtrip and located bounds as
before.  A 5 MB file of short paragraphs converts in 2.35 s (dev
profile, including process start), where it did not finish in ten
minutes; djot.js takes 323 ms on it.

Heading identifiers (2026-09-26).  `unique_id` tried `base`, `base-1`,
... from 0 for every heading, each against the whole list of taken ids:
cubic in the number of headings sharing a text (20 KB of one heading
repeated took 10.1 s).  `unique_id` stays the specification.  The pass
state (`Document.id_state`) also carries the taken ids as a balanced
tree (`StrSet`, stdlib `MSetAVL`), the labels with an implicit reference
likewise, and per base the index below which every candidate is taken
(`StrMap`, stdlib `FMapAVL`); the search starts there.
`assign_heading_id_spec` proves the pass assigns `unique_id` whenever
`id_inv` holds, and `Ids.of_block_inv` / `Ids.of_list_inv` that the
pass keeps it.  The same input now takes 6.7 ms, growing about 5x per
4x.  `String.compare` and `OrdersEx.String_as_OT.compare`, the trees'
order, are realized by OCaml's `String.compare` (trusted; the Gallina
ones copy a tail per character).  The stdlib trees add fifteen
extracted modules to the package.

Checked (2026-09-26): 200000 random documents of headings, explicit ids
that collide with generated ones, empty headings, headings in
containers and implicit references, old extraction against new, no
difference; both orders against a transcription of the Gallina order on
every pair of strings over four characters (including 0 and 255) up to
length 4, 116281 pairs, no difference; the 1539343-input `Html.convert`
differential and the suites as before.

Any further `Extract Constant` joins this list and gets the same check.

Unclosed inline openers (2026-09-26).  The old `oflatten` repeatedly
appended a growing list while abandoning frames at paragraph end.  It
remains the specification.  `oflatten_rev` builds the same result in a
reversed accumulator with work proportional to each frame's items;
`oapp_rev_correct`, `oflatten_rev_correct`, and `oitems_of_spec` prove
equality, including text and source-span merges at each seam.  No
native substitution was added.  An empty frame stack returns the
outermost items directly.  On the dev profile, wrapped unclosed
brackets took 4.1, 16.8, and 30.8 ms to parse at 20, 80, and 160 KB;
unclosed emphasis took 3.7, 16.2, and 32.6 ms.  The previous 40/160 KB
release measurements are below and are not directly comparable.

## Measurements

2026-09-13, `223cbf0` plus the change above, OCaml 5.4 release profile,
Apple Silicon. Input is djot.js's `bench/readme.dj` (12.6 KB) joined k
times with newlines. The cmarkit column is oymarkit (a fork that has djot extensions) 
with its djot settings on. Times are parse only; HTML adds 15-20%.

| k | bytes | before | after | cmarkit | djot.js parse+html |
| --- | --- | --- | --- | --- | --- |
| 1 | 12601 | 18.8 ms | 3.8 ms | 0.18 ms | 0.26 ms |
| 4 | 50407 | 217 ms | 15.0 ms | 1.0 ms | 0.99 ms |
| 16 | 201631 | 2965 ms | 61.7 ms | 4.6 ms | 4.2 ms |
| 64 | 806527 | 40135 ms | 258 ms | 20.1 ms | 17.7 ms |

Linear in document size now, at about 13x cmarkit.

Synthetic shapes, after the fix, parse time:

| shape | 10 KB | 40 KB | 160 KB | growth per 4x |
| --- | --- | --- | --- | --- |
| 40-byte paragraphs, blank-separated | 2.7 ms | 12.1 ms | 83 ms | ~7x |
| one paragraph of 40-byte lines | 3.3 ms | 22.9 ms | 290 ms | ~13x |
| one line of `a` | 40 ms | 665 ms | 12494 ms | ~19x |

This table predates the 2026-09-16 substitutions below.  Its long-paragraph
quadratic was `List.rev`, now fixed.  The long-line shape combined recursive
`String.length`, now fixed, with the structural scans that remain open below.
The blank-separated shape should be remeasured before drawing a scaling claim
from its old numbers.

End-to-end `convert` medians on 2026-09-16, immediately before and after the
native `List.rev` and `String.length` substitutions (three runs, same machine
and release build; these include HTML and shell startup and are comparable
only within this table):

| shape | before | after |
| --- | --- | --- |
| one paragraph, 4000 40-byte lines | 0.76 s | 0.47 s |
| one 60 KB line of `a` | 2.53 s | 2.06 s |
| `readme.dj` x64 | 0.32 s | 0.31 s |

`readme.dj` x64 again on 2026-09-21, before and after routing every
paragraph, heading and definition term through `para_inlines_at`: 0.47 s
against 0.47 s (three runs each, dev profile, so not comparable with the
release numbers above, only with each other).  Nothing was expected to
move and nothing did: at `semantic_pos` the new entry point takes its
`else` branch and is `para_inlines_off` of the same texts, which is the
point of asking the policy before reading the lines.

The paragraph improvement is the removed `List.rev` quadratic.  The long-line
improvement removes recursive `String.length`, but the remaining structural
string scans below keep that shape quadratic.  Ordinary prose barely moves;
its largest measured constant cost remains character classification.

### Locations on, against the incumbent

2026-09-21, `64b0724`, dev profile, same machine as the tables above.
Inputs are `djot.js/bench/readme.dj` and the same file joined 64 times
with newlines, as in the first table.  Both sides are best of 20, in
process: ours through `dune exec test/convert.exe -- --time 20`, the
incumbent through a node driver over the same `djot.js/lib/index.js`
`test/djotjs/` scripts import.  Node startup is about 0.4 s, so a shell
timing would measure that and not the parse; `--parse-only` on the two
djot.js scripts is the same call with the render or the tree walk
removed, and is what the driver's loop stands in for at 20 repeats.

| input | bytes | ours `parse_blocks` | ours `parse_blocks_located` | djot.js `parse` | djot.js `parse` + sourcePositions |
| --- | --- | --- | --- | --- | --- |
| `readme.dj` | 12601 | 3.61 ms | 3.99 ms | 0.35 ms | 0.39 ms |
| `readme.dj` x64 | 806527 | 262.8 ms | 290.0 ms | 16.5 ms | 21.8 ms |

Recording locations costs about 10% on both inputs (3.99 against 3.61,
290.0 against 262.8), and it is the same walk under two policies, not a
second pass.  djot.js's `sourcePositions` cost 13% at x1 and 22% to 32%
at x64 across two runs.  Ours is 10x to 16x djot.js's parse, which is
the constant factor the first table already records against cmarkit
rather than a scaling difference: both grow linearly here.

### `nat` as `int`

2026-09-26, `59a4c82` against the same tree with `nat` extracted to `int`,
release profile, same machine.  `Html.convert` (parse and HTML), best of
20 for `readme.dj` and best of 3 to 5 otherwise, both extractions linked
into one executable.

| input | unary `nat` | `int` |
| --- | --- | --- |
| `readme.dj` | 4.16 ms | 2.31 ms |
| `readme.dj` x64 | 297.9 ms | 157.8 ms |
| one paragraph, 4000 40-byte lines | 444.6 ms | 313.7 ms |
| one 20 KB line of `a` | 205.3 ms | 174.6 ms |
| `12345678. ok` | 1268.9 ms | under 0.01 ms |
| `123456789. ok` | stack overflow | under 0.01 ms |

## Open, ranked by what they cost a real document

Measured 2026-09-26 at `537dba9`, release profile, parse (`parse_doc`)
against full conversion (`Html.convert`).  djot.js figures are its
`parse` plus `renderHTML` on the same generated inputs.

### Fixed: unclosed openers were quadratic in a paragraph

| input, wrapped at 78 columns | 40 KB | 160 KB | djot.js 160 KB |
| --- | --- | --- | --- |
| `[a` repeated | 121 ms | 1951 ms | 12 ms |
| `_a ` repeated | 87 ms | 1324 ms | 15 ms |

`InlineScan.oflatten` appended the growing pending content at each
open frame, so k unclosed openers cost O(k^2).  The linear replacement
and its proof are recorded in Fixed above.

### 1. Tail copies inside a line

Per-character recursion with a tail copy: `Line` 60 occurrences,
`Inline` 27, `Strings` 11, `Attributes` 6, `Marker` 3, `Html` 3. With
lines split natively this is O(line^2) per line: one 160 KB line of
`word ` parses in 899 ms, against 89 ms at 40 KB.  Small on prose, and
a denial-of-service shape for any input with long lines.

Source positions no longer block this.  The located scan
(`InlineLocated.v`) still matches `String c rest` and carries a counted
distance to the end of the line beside it, so positions landed without
offset scanning.

Fix, either:

- scan by offset, `(s, i)` with `String.get`, in the theories; every
  lemma by induction on `String c s'` is restated for offsets;
- or extract `string` to a slice (a string and a start offset), so a
  match on `String c s'` is O(1).  No proof changes, a larger trusted
  realization, and `String c acc` construction stays a copy.

### 2. Delimiter lookup per character

`Inline.dstyle_at` is `find` over `dstyles` with two closure calls per
row (`denabled`, `dc_char`). In the `readme.dj` x64 profile,
`List0.find` 145, `djot_dsyntax` 133 and `denabled` 99 samples. A
constant factor; a precomputed character-to-style table would remove it.

### 3. Inline links

80 KB of `[a](b) ` wrapped at 78 columns parses in 34.6 ms, against
3.7 ms at 20 KB (dev profile): 9.4x per 4x, superlinear, cause not yet
located.

Linear already: nested lists and deep list nesting (160 KB in 22 ms and
45 ms), and conversion of every shape above beyond its parse.

## Order

Long lines first, then delimiter lookup and inline links.

`make bench` runs generated shapes at 20 KB and 80 KB (or `--sizes`)
through the document parse and `Html.convert` and prints the growth per
size step; a row past 8x is marked.  Run it before and after a change
that touches a scan or the renderer.
