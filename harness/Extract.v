(* Extraction prelude: produces core.ml for the harness executable.
   ExtrOcamlNativeString maps Gallina strings to native OCaml strings, so
   the harness needs no conversion glue. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString.
From DjotV Require Import Html.

Extraction Language OCaml.
Extraction "core.ml" convert.
