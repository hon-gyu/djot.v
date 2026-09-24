(* ai-disclosure: ai-generated *)

(* Test fixtures for the test/ executables: the generated corpus as
   data.  Extracted alongside the parser but kept out of the parser's
   library, so nothing a consumer links against carries a test corpus. *)

From Stdlib Require Import String List.
From DjotV Require Import Ast Inline Render.
From DjotVDev Require Import Generate.
Import ListNotations.

Definition render_cb (c : cblock) : string :=
  render_djot (blocks_of_cblocks [c]).

Definition generated_docs (d : nat) : list string := map render_cb (accepted d).

(* Every `cb_ok` block the enumerator produces, rendered to djot source,
   so that the shapes the roundtrip admits are checked against djot
   itself and not only against our own renderer.

   `Eval vm_compute in` forces the list to string literals here, so what
   crosses into OCaml is data rather than the enumerator.

   Depth 2 (796 documents) rather than 3 (7151): this file rebuilds on
   every proof edit (about 2s at depth 2, 23s at depth 3), and depth 2
   already contains a list inside a list item.

   Ordered lists ride along rather than joining `enum_cblock`, for the
   reason `Generate.ordered_pool` gives.  Against djot.js they matter
   most, since the marker text is what our renderer invents. *)
Definition generated : list string :=
  Eval vm_compute in (generated_docs 2 ++ map render_cb ordered_accepted
                      ++ map render_cb def_accepted)%list.
