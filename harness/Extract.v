(* Extraction prelude: produces core.ml for the harness executable.
   ExtrOcamlNativeString maps Gallina strings to native OCaml strings, so
   the harness needs no conversion glue. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString.
From Stdlib Require Import String List.
From DjotV Require Import Ast Inline Render Generate Html.
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

   Depth 2 (796 documents), not 3 (7151), and the reason is
   the build loop: this file depends on the theories, so every proof edit
   re-runs the `vm_compute` below.  Measured on 2026-08-09, depth 2 costs
   ~2s and depth 3 ~23s per rebuild.  Depth 2 already contains a list
   inside a list item, which is the shape this corpus exists to cover; the
   plan's instruction was to bound the depth hard, coverage of shapes
   being the point rather than volume.  For an occasional deeper sweep,
   change the 2 below and rebuild. *)
Definition render_cb (c : cblock) : string :=
  render_djot (blocks_of_cblocks [c]).

Definition generated_docs (d : nat) : list string := map render_cb (accepted d).

(* Ordered lists ride along rather than joining `enum_cblock`, for the
   reason `Generate.ordered_pool` gives: a kind changes a list's markers,
   not the shapes its items can take.  Against the oracles they are the
   half that matters most, since the marker text is what our renderer
   invents and `renderDjot` has its own opinion about. *)
Definition generated : list string :=
  Eval vm_compute in (generated_docs 2 ++ map render_cb ordered_accepted)%list.

Extraction Language OCaml.
Extraction "core.ml" convert generated.
