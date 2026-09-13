(* ai-disclosure: ai-generated *)

(* Extraction prelude.  `Separate Extraction` emits one OCaml module per
   Coq module rather than one flat file, so the extracted parser can be
   read against the theory it came from.  The blacklist keeps `String`,
   `List`, `Nat` and `Bool` from shadowing OCaml's own; they land as
   `String0`, `List0`, `Nat0`, `Bool0`.

   `ExtrOcamlNativeString` maps Gallina strings to native OCaml strings,
   so no conversion glue is needed on the OCaml side. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString.
From DjotV Require Import Strings Generate Html.
From DjotVDev Require Import Fixtures.

Extraction Language OCaml.
Extraction Blacklist String List Nat Bool.
Set Extraction Output Directory ".".

(* Under the native string mapping, a match on [String c s'] copies the
   tail and [String c acc] copies the accumulator, so a recursion over a
   string is quadratic in its length.  [split_lines] runs over the whole
   document, which made parsing quadratic in document size.  These two are
   replaced by native OCaml equal to the Gallina definitions; they are
   trusted, not proved. *)
Extract Constant DjotV.Strings.rev_string =>
  "(fun s -> let n = String.length s in
     String.init n (fun i -> String.get s (n - 1 - i)))".
Extract Constant DjotV.Strings.split_lines =>
  "(fun s -> match List.rev (String.split_on_char '\n' s) with
     | """" :: rest -> List.rev rest
     | parts -> List.rev parts)".

Separate Extraction convert generated accepted rt_lhs rt_rhs render_cb
  keyed_accepted keyed_rt_lhs.
