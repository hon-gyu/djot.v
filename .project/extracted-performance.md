---
ai-disclosure: ai-generated
---
# Performance of the extracted parser

Evergreen, per [[README]]: the mechanism and the ranked list describe the
tree now. Measurements are dated and carry the commit they were read at;
re-measure before quoting them.

Status: document-size and paragraph-length quadratics fixed (`split_lines`,
`rev_string`, `List.rev`).  Recursive `String.length` no longer copies each
suffix, but structural matches still make long lines quadratic.  The last
ordinary-prose comparison against cmarkit measured a roughly 13x constant
factor before the smaller fixes below; re-measure before quoting it.

The extracted package now exposes location-on block and document parses
beside the existing semantic parser.  `line_table` and `resolve_span`
convert recorded spots to byte coordinates.  The location-on parse has
not yet been benchmarked against the semantic parse or the incumbent;
the plan in `260916.plan.source-locations.md` tracks that measurement.

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
and quadratic or worse once extracted:

- Stdlib `rev` is `rev l' ++ [x]`, O(n^2), and `app` is not tail
  recursive.
- Stdlib `String.length` is a structural recursion: a tail copy per
  character, a unary result, and a stack frame per character.
- `nat_of_ascii` goes through an 8-bit `N` and then expands to a unary
  `nat` of up to 255 cells, per character classified.

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
- `make test`: corpus 287/287 and generated 6167/6167 exact HTML, as
  before.
- `make roundtrip`: 43857 documents, no mismatch.

How the additions were checked (2026-09-16):

- extracted `String.length` against the previous extraction on every string
  over `{a, b, space, \n, \t, \r}` up to length 6, every one-byte string,
  and 20000 deterministic random byte strings at each length 7 to 12;
  176243 strings, no difference;
- extracted `List.rev` against the previous extraction on every list over
  `{0, 1, 2}` up to length 10; 88573 lists, no difference;
- `make test`: corpus 287/287 and generated 6167/6167 exact HTML;
- `make roundtrip`: 43857 documents, no mismatch;
- `make check-dist`: the committed extracted package is current.

Any further `Extract Constant` joins this list and gets the same check.

## Measurements

2026-09-13, `223cbf0` plus the change above, OCaml 5.4 release profile,
Apple Silicon. Input is djot.js's `bench/readme.dj` (12.6 KB) joined k
times with newlines. The cmarkit column is oymarkit (the fork vendored in
oyster) with its djot settings on. Times are parse only; HTML adds
15-20%.

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

## Open, ranked by what they cost a real document

### 1. Character classification through unary `nat`

`Line.in_range lo hi c` is `Nat.leb lo (nat_of_ascii c) && ...`, and
`is_digit`, `is_lower`, `is_upper`, `is_alnum` are built on it.

Profile of `readme.dj` x64, 4327 top-of-stack samples: `Nat0.add` 826 and
`PeanoNat.leb` 792 lead. `add` is called from `N_of_digits` and
`PosDef.iter_op`, which is the `N` to `nat` conversion. `leb` is called
from `Line.in_range` and `Line.is_alnum`. This is the largest share of the
constant factor on ordinary prose.

Fix, cheapest first: define the classes by `Ascii` comparison
(`Ascii.compare` already extracts to `Char.compare`); or keep the
definitions and add `Extract Inlined Constant` for the classifiers.

### 2. Tail copies inside a line

Per-character recursion with a tail copy: `Line` 60 occurrences,
`Inline` 27, `Strings` 11, `Attributes` 6, `Marker` 3, `Html` 3. With
lines split natively this is O(line^2) per line, which is small on
prose and the reason a pathological long line stays slow even with native
`String.length`. `Inline` also has 92 string concatenations, a candidate
for paragraph cost remaining after native `List.rev`.

Fix: scan by offset, `(s, i)` with `String.get`, in the theories. Every
lemma by induction on `String c s'` has to be restated for offsets, so
this is the expensive item. It is the same change that source positions
need (`Ast.pos` exists but nothing produces `SomePos`), so do it together
with positions, not separately.

### 3. Delimiter lookup per character

`Inline.dstyle_at` is `find` over `dstyles` with two closure calls per
row (`denabled`, `dc_char`). In the `readme.dj` x64 profile,
`List0.find` 145, `djot_dsyntax` 133 and `denabled` 99 samples. A
constant factor; a precomputed character-to-style table would remove it.

## Order

Character classification is local to `Line.v` and is the next small
constant-factor target.  Offset scanning waits for positions.  Delimiter
lookup is last.
