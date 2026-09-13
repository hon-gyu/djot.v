---
ai-disclosure: ai-generated
---
# Performance of the extracted parser

Evergreen, per [[README]]: the mechanism and the ranked list describe the
tree now. Measurements are dated and carry the commit they were read at;
re-measure before quoting them.

Status: document-size quadratic fixed (`split_lines`, `rev_string`).
Paragraph-length and line-length quadratics open, and a constant factor
of roughly 13x against cmarkit remains on ordinary prose.

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

`extraction/Extract.v` replaces `Strings.split_lines` and
`Strings.rev_string` with native OCaml by `Extract Constant`. These are
**trusted, not proved**: the theorems are about the Gallina definitions,
and the OCaml is asserted equal to them.

How the equality was checked (2026-09-13):

- `split_lines` and `rev_string` against the previous extraction, taken
  from `git show 223cbf0:dist/src/Strings.ml`: every string over
  `{a, b, space, \n, \t, \r}` up to length 6, plus 20000 random strings at
  each length 7 to 12. 419593 strings, no difference.
- `make test`: corpus 287/287 and generated 6167/6167 exact HTML, as
  before.
- `make roundtrip`: 43857 documents, no mismatch.

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

The first row still grows faster than linear; the second and third are
the open quadratics below.

## Open, ranked by what they cost a real document

### 1. `List.rev` is quadratic, and `Step` reverses every accumulator

Stdlib `rev` extracts to `app (rev l') [x]`. `Step` has 31 uses (a
paragraph's lines are consed and reversed once at `finish`), `Document`
4, `Inline` 3, `Html` 2.

Profile of one 4000-line paragraph: 2005 samples in `Datatypes.app`,
entered only from `List0.rev`. It dominates that shape.

Fix: `Extract Constant List.rev => "List.rev"` (trusted, as above), or
`rev_append` in the theories, where `rev_append_rev` from Stdlib carries
the proofs across.

### 2. `String.length` on every line

`Step.step` computes its fuel as `S (length l + pstate_depth st)`, and
`Step.consumed` is `length l - length rest`, per container prefix. Both
are Stdlib's recursive `String.length`: O(line^2) copying, a unary
result, and one stack frame per character.

Profile of one 60 KB line: stacks nest `String0.length` and a `Line`
closure 500+ frames deep, and the top of stack is the GC scanning that
stack (`do_some_marking` 1559, `caml_find_frame_descr` 853,
`caml_scan_stack` 297 samples) with `memmove` at 397.

Fix: `Extract Constant String.length` to a native length converted to
`nat`. That leaves an O(n) unary allocation but removes the copies and
the depth. `consumed` would be better computed during the scan than by
subtracting two lengths.

### 3. Character classification through unary `nat`

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

### 4. Tail copies inside a line

Per-character recursion with a tail copy: `Line` 60 occurrences,
`Inline` 27, `Strings` 11, `Attributes` 6, `Marker` 3, `Html` 3. With
lines split natively this is O(line^2) per line, which is small on
prose and the reason a pathological long line stays slow after 2 is
fixed. `Inline` also has 92 string concatenations, a candidate for the
remaining paragraph growth once 1 is fixed.

Fix: scan by offset, `(s, i)` with `String.get`, in the theories. Every
lemma by induction on `String c s'` has to be restated for offsets, so
this is the expensive item. It is the same change that source positions
need (`Ast.pos` exists but nothing produces `SomePos`), so do it together
with positions, not separately.

### 5. Delimiter lookup per character

`Inline.dstyle_at` is `find` over `dstyles` with two closure calls per
row (`denabled`, `dc_char`). In the `readme.dj` x64 profile,
`List0.find` 145, `djot_dsyntax` 133 and `denabled` 99 samples. A
constant factor; a precomputed character-to-style table would remove it.

## Order

1 and 2 are one `Extract Constant` each, and together close both
remaining quadratics. 3 is local to `Line.v`. 4 waits for positions. 5
is last.
