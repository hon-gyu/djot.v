---
ai-disclosure: autonomous
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
Not production ready: some long single lines still grow superlinearly
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

The three inline line drivers (2026-09-26).  `iscan_str`, `iscan_str_off`,
and `iscan_str_located` now have trusted OCaml realizations that read
the input by offset.  In ordinary text mode they batch contiguous
letters, digits, and spaces when the active delimiter table assigns
no style to the byte, avoiding both tail copies and one pending-text
append per byte.  The located driver retains the last whitespace spot.
Other bytes still go through `istep` or `istep_at`.

The old and new extractions were linked as separate libraries in one
throwaway executable.  It compared semantic, attribute-off, and both
located scan states, plus `Html.convert`, using structural marshaling
without sharing: all 256 one-byte strings, all 2801 strings over
`{a, space, [, ], _, backslash, newline}` up to length 4, 4000
deterministic random byte strings up to length 150, and four longer
targeted strings.  All 35305 output comparisons matched.  The regular
test suite matched 287/287 and generated exact HTML matched 6167/6167;
depth-3 roundtrip passed 43857/43857, located bounds 44150/44150,
keyed roundtrip 6628/6628, and wikilink roundtrip 3725/3725.
The regenerated standalone `dist/` built, passed its tests, and matched
`check-dist`.

One line of `word `, dev profile, parse (`parse_doc`), best of up to
three runs before and after the substitution:

| bytes | old drivers | new drivers |
| --- | --- | --- |
| 20 KB | 24.3 ms | 1.7 ms |
| 40 KB | 82.8 ms | 2.8 ms |
| 80 KB | 291.9 ms | 4.8 ms |
| 160 KB | 945.7 ms | 8.2 ms |

This fixes the measured ordinary-word line.  A line of `.a` pairs
still grew superlinearly (20 KB 14.7 ms, 80 KB 148.8 ms); the next
entry fixes it.

Pending inline text (2026-09-26).  Pending text was a `string` grown by
`txt ++ piece`, so each append copied the text pending so far, and the
drivers' batch did the same with `txt ^ String.sub ...`.  The scanner is
now generic over its pending-text buffer (`TextOps`, `iscan_g`).  At
`string` it is the specification, unchanged: the instance is a literal
record, so its operations reduce to `++` and the identity, and `tred`
rewrites them where a proof unfolds.  `chunks` (a list of pieces, newest
first, joined once when read) runs it.  `InlineBuffer.v` proves the
chunk laws, that `map_text` commutes with every step, line break, and
finish, and `iscan_str_buf_spec`, `iscan_str_off_buf_spec`, and
`iscan_str_located_buf_spec`.  The three native drivers lift the state
into `chunks`, run the offset loop over the generic step, push a batch
as one chunk, and read back with `map_text`.  The trusted part is as
before: each offset loop against its Gallina buffer driver.

Checked (2026-09-26), the previous extraction (`dist/src` at `7884839`)
and the new one linked into one throwaway executable, comparing
`iscan_lines`, `iscan_lines_off`, located `para_inlines_at`, semantic
and located `parse_blocks`, and `Html.convert` by structural marshaling
without sharing: every string over a 20-character alphabet of the
scanner's special bytes up to length 4, 6000 random strings up to 200
bytes, and 18 long targeted lines; 1046634 comparisons, no difference.
A planted change to one side was caught.  Test suite 287/287, generated
6167/6167, roundtrip 43857/43857, located bounds 44150/44150, keyed
6628/6628, wikilink 3725/3725; the standalone `dist/` built and passed
its test.

`parse_doc`, dev profile, best of five, old and new extraction in one
process:

| shape | 20 KB | 40 KB | 80 KB | 160 KB |
| --- | --- | --- | --- | --- |
| `.a` on one line | 14.1 -> 2.0 ms | 46.8 -> 3.9 | 154.5 -> 8.4 | 478.2 -> 16.1 |
| `word, ` on one line | 5.5 -> 1.4 | 17.3 -> 2.8 | 54.8 -> 6.8 | 168.7 -> 12.5 |
| `word ` on one line | 1.0 -> 1.0 | 2.0 -> 2.0 | 3.8 -> 3.8 | 7.6 -> 7.6 |
| paragraph of short lines | 1.3 -> 1.3 | 2.7 -> 2.5 | 5.4 -> 5.5 | 11.2 -> 11.3 |

Wrapped brackets, emphasis, links, and short prose paragraphs moved by
0 to 7% across three runs, slower more often than not: the buffer
operations are calls through a record, and each line is lifted and read
back once.

Failed candidates (2026-09-26).  A failed autolink candidate, a failed
span spec, and a `{` read with attributes off put their source back as
text and set `prev` with `blit_prev`, which read the whole rebuilt text:
`tval` of the pending buffer, then `str_last` by structural recursion,
O(p^2) in the pending text per failure.  A line of `<a ` took 57 s at
20 KB.  `blit_prev` now reads the fragment alone; `blit_prev_fragment`
and `blit_prev_bsplit_nl` prove it agrees with the whole text, cut at a
newline or not.  The same line parses in 3.1 ms at 20 KB and 9.6 ms at
80 KB (`candidates` in `make bench`); `[a]{b ` repeated, 1.7 ms at 4 KB
and 7.4 ms at 16 KB.  Checked as above against `dist/src` at `7884839`:
1046652 comparisons, adding failed candidates across line breaks, no
difference; the suites and `dist/` as before.

Buffered inline source (2026-09-26, baseline `16e4b24`, result
`0106e92`).  The scanner now uses its existing `TextOps` buffer for
escaped whitespace, verbatim content, destination, raw-format spec,
attribute and span source,
reference and note labels, wiki region, autolink source, and symbol
alias.  At `string` it remains the specification.  At `chunks`, each
append conses the new piece; `map_text` reads the source when a rule
needs it.  `InlineBuffer.v`'s simulation and driver equations cover
these fields as well as pending text.  No admits or axioms were added.

Two close-path costs were addressed with the buffer change.  The raw
spec step used to compute `spot_before` over its growing source on
every byte; it now computes the position only when the candidate ends.
`drop_nl` remains the Gallina destination specification, and its
extraction is a linear OCaml `Buffer` loop, a new trusted realization.
Before the change, an 80 KB destination close spent about 2.45 s in
`drop_nl`, against 155 ms appending and 9 ms advancing its ordinary
shadow (separately timed, so these are diagnostic rather than additive).

Old and new extractions were linked in one throwaway executable.  A
planted difference was detected; then semantic and attribute-off scan
states, located paragraph inlines, semantic and located block parses,
and `Html.convert` matched on every string through length 4 over a
20-character scanner alphabet, 6000 random strings through 200 bytes,
and 18 targeted long lines: 1,046,634 comparisons, no difference.
The new `drop_nl` separately matched the old extraction on every byte
and 10,001 random byte strings through 500 bytes: 10,257 inputs.
The test suite matched 287/287 and generated exact HTML 6167/6167;
depth-3 roundtrip 43857/43857, located bounds 44150/44150, keyed
roundtrip 6628/6628, and wikilink roundtrip 3725/3725.  The
regenerated standalone `dist/` built, passed its tests, and matched
`check-dist`.

`parse_doc`, dev profile, best of up to three, old and new extraction
in the same process.  The first table uses one long construct; all
figures are milliseconds:

| shape | 20 KB old -> new | 40 KB old -> new | 80 KB old -> new |
| --- | ---: | ---: | ---: |
| verbatim | 16.1 -> 1.8 | 47.5 -> 3.3 | 155.8 -> 6.7 |
| destination | 89.0 -> 3.1 | 439.0 -> 6.8 | 2130.6 -> 14.4 |

The raw-format spec, at 2/4/8 KB, took 52.2/693.1/8207.0 ms before
and 0.11/0.26/0.53 ms after.  The moved position computation accounts
for most of that gain.  The native drivers still step one byte at a
time in verbatim and destination mode; both now grow near linearly at
20 to 80 KB, so batching them would add trusted code for little gain.

Other source shapes at 4 and 16 KB, before -> after in milliseconds:

| shape | 4 KB | 16 KB |
| --- | ---: | ---: |
| reference label | 1.8 -> 1.3 | 26.6 -> 18.5 |
| note label | 4.4 -> 3.9 | 100.4 -> 92.3 |
| wiki target | 1.5 -> 1.5 | 37.5 -> 37.9 |
| autolink body | 3.9 -> 4.9 | 69.2 -> 110.9 |
| symbol alias | 1.9 -> 1.5 | 36.3 -> 23.9 |
| attribute source | 3.7 -> 3.3 | 70.7 -> 61.6 |
| span source | 2.0 -> 1.9 | 35.3 -> 35.5 |
| escaped whitespace | 3.1 -> 3.6 | 67.2 -> 86.1 |

The remaining close-time structural scans dominate several of these
shapes; the buffer's join adds overhead where it does not remove the
dominant cost.  At 20/80 KB, ordinary `line` stayed 1.2/3.9 ->
1.0/3.9 ms, short-line `paragraph` 1.3/5.9 -> 1.4/6.4,
`brackets` 4.2/16.8 -> 4.1/15.5, `emphasis` 3.6/15.6 ->
3.7/16.2, and `links` 2.4/10.3 -> 2.5/10.9.  The bench now has a
shape for each source accumulator.  `isnoc` and `osnoc` remain flat
AST-string seam merges; wrapped brackets and emphasis do not show a
growth regression warranting an AST representation change here.

Linear inline close-time readers (2026-09-26, baseline `3cc9b28`,
result `9073bcf`).  `source_shape`, `wiki_split`, the autolink body,
kind, and email predicates, and `str_last` keep their Gallina definitions
for proofs; narrow native extraction realizations read flat strings by
offset.  Attribute tokens and label words grow as reversed byte lists,
with one native linear conversion at commit.  `words_spec` proves the
Gallina word builder equivalent to its prior definition, and the
identifier roundtrip proof covers the new attribute state.
`dstyle_at_fast_eq` proves the direct delimiter dispatch equal to the
table search.  `Print Assumptions` on both new lemmas was empty.  The
native readers and conversion remain trusted extraction code.

Old and new extractions, linked in one process, matched on 2,268,150
comparisons: every scanner-alphabet string through length four, 6000
random strings, direct checks of the replaced readers, semantic and
located output, blocks and HTML, and long targeted constructs.  The
targeted cases include a table with wikilinks enabled.  A planted
difference was detected.  The repository's exact-HTML 287/287 and
6167/6167, depth-3 roundtrip 43857/43857, located bounds
44150/44150, keyed roundtrip 6628/6628, and wikilink roundtrip
3725/3725 passed.  `make dist`, `make check-dist`, and standalone Dune
build and test passed.

Same-process old -> new times, dev profile, milliseconds.  The inline
column times `para_inlines`; the document column times `parse_doc`.
The wikilink document uses the same enabled table as its inline
measurement:

| input, 64 KB construct | inline | parse_doc |
| --- | ---: | ---: |
| autolink | 2022 -> 8.1 | 1971 -> 9.3 |
| escaped whitespace | 1653 -> 6.2 | 1611 -> 6.7 |
| note label | 243 -> 4.1 | 2405 -> 2351 |
| wikilink target, enabled | 873 -> 5.2 | 1975 -> 1146 |

The default Djot table disables wikilinks.  The old `wiki` benchmark
therefore measured literal brackets; `test/bench.ml` now enables the
capability for that shape.  The note and wikilink inline paths are near
linear, but their full-document 20/80 KB parse still grows by about
30x: structural string scans in the block/line path now dominate.

Other same-process `Html.convert` times at 64 KB fell from 427 to 5.2
ms for a reference label, 411 to 12.2 ms for a symbol alias, 1160 to
17.2 ms for an attribute, and 789 to 8.4 ms for a span attribute.
Delimiter lookup alone took 100.9 -> 70.0 ms over two million mixed
bytes; repeated README x64 conversion took 81.2 -> 75.3 ms.  A
seam-heavy escaped-punctuation line took 0.11/0.50/2.19 ms at
4/16/64 KB before and 0.12/0.53/2.60 after.  `isnoc`/`osnoc` have no
observed repeated-large-merge problem on that witness; their flat AST
representation was retained.

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

### 1. Remaining long-line work

Structural string matches still copy tails in `Line`, `Strings`,
`Attributes`, `Marker`, and some helper paths.  Pending and source
accumulators, the measured inline close-time readers, and label-word
normalization no longer copy their prefixes or native-string tails.
The remaining block/line path is visible on long note labels and
enabled wikilinks: their inline scans are near linear, while the whole
document parse still scales steeply.
`isnoc` and `osnoc` still merge adjacent flat `Str` nodes with
`t ++ s`.  The old 2026-09-26 code-span and destination measurements
are superseded by the buffered-source entry above.

Source positions no longer block this.  The located scan
(`InlineLocated.v`) still matches `String c rest` and carries a counted
distance to the end of the line beside it, so positions landed without
offset scanning.

For remaining tail copies, fix either:

- scan by offset, `(s, i)` with `String.get`, in the theories; every
  lemma by induction on `String c s'` is restated for offsets;
- or extract `string` to a slice (a string and a start offset), so a
  match on `String c s'` is O(1).  No proof changes, a larger trusted
  realization, and `String c acc` construction stays a copy.

### Recheck: inline links

80 KB of `[a](b) ` wrapped at 78 columns parses in 34.6 ms, against
3.7 ms at 20 KB in the earlier dev-profile measurement: 9.4x per 4x.
After the inline-driver substitution the same shape parses in 2.5,
10.4, and 23.1 ms at 20, 80, and 160 KB (4.1x, then 2.2x).
The earlier superlinear signal is not reproduced; its cause has not
been isolated.

Linear already: nested lists and deep list nesting (160 KB in 22 ms and
45 ms), and conversion of every shape above beyond its parse.

## Order

Remaining block/line long-line shapes first.  Keep inline links in the
scaling benchmark to catch a recurrence.

`make bench` runs generated shapes at 20 KB and 80 KB (or `--sizes`)
through the document parse and `Html.convert` and prints the growth per
size step; a row past 8x is marked.  Run it before and after a change
that touches a scan or the renderer.
