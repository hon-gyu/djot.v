(* Extraction prelude: produces core.ml for the harness executable.
   ExtrOcamlNativeString maps Gallina strings to native OCaml strings, so
   the harness needs no conversion glue. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString.
From Stdlib Require Import String List.
From DjotV Require Import Ast Render Generate Html.
Import ListNotations.

(* The generated corpus: every `cb_ok` block the enumerator produces,
   rendered to djot source.  `main --generated` feeds these to the
   oracles, so the shapes the roundtrip admits are checked against djot
   itself and not only against our own renderer -- which a roundtrip
   theorem, being a meta-property, cannot do.

   `Eval vm_compute in` forces the list to string literals *here*, so what
   crosses into OCaml is data.  Extracting `enum_cblock` instead would drag
   the whole cblock inductive and its filters across for no benefit --
   nothing on the OCaml side needs to generate, only to read.

   Depth 2 (671 documents, 18 KB), not 3 (7151, 309 KB), and the reason is
   the build loop: this file depends on the theories, so every proof edit
   re-runs the `vm_compute` below.  Measured on 2026-08-09, depth 2 costs
   ~2s and depth 3 ~23s per rebuild.  Depth 2 already contains a list
   inside a list item, which is the shape this corpus exists to cover; the
   plan's instruction was to bound the depth hard, coverage of shapes
   being the point rather than volume.  For an occasional deeper sweep,
   change the 2 below and rebuild. *)
Definition generated_docs (d : nat) : list string :=
  map (fun c => render_djot (blocks_of_cblocks [c])) (accepted d).

Definition generated : list string := Eval vm_compute in generated_docs 2.

Extraction Language OCaml.
Extraction "core.ml" convert generated.
