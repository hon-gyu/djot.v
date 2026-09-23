(* ai-disclosure: ai-generated *)

(* Extraction prelude.  `Separate Extraction` emits one OCaml module per
   Coq module rather than one flat file, so the extracted parser can be
   read against the theory it came from.  The blacklist keeps `String`,
   `List`, `Nat` and `Bool` from shadowing OCaml's own; they land as
   `String0`, `List0`, `Nat0`, `Bool0`.

   `ExtrOcamlNativeString` maps Gallina strings to native OCaml strings,
   so no conversion glue is needed on the OCaml side. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString.
From DjotV Require Import Strings Html Step Document.
From DjotVDev Require Import Fixtures Generate.

Extraction Language OCaml.
Extraction Blacklist String List Nat Bool.
Set Extraction Output Directory ".".

(* Under the native string mapping, a match on [String c s'] copies the
   tail and [String c acc] copies the accumulator, so a recursion over a
   string is quadratic in its length.  Gallina's [List.rev] also extracts
   through append, and [String.length] recursively takes every copied tail.
   These are replaced by native OCaml equal to the Gallina definitions; they
   are trusted, not proved.  The unary result of [String.length] remains, but
   the conversion is tail recursive and no longer copies the string. *)
Extract Constant List.rev => "List.rev".
Extract Constant String.length =>
  "(fun s ->
     let rec go n acc =
       if n = 0 then acc else go (n - 1) (Datatypes.S acc)
     in go (String.length s) Datatypes.O)".
Extract Constant DjotV.Strings.rev_string =>
  "(fun s -> let n = String.length s in
     String.init n (fun i -> String.get s (n - 1 - i)))".
Extract Constant DjotV.Strings.split_lines =>
  "(fun s -> match List.rev (String.split_on_char '\n' s) with
     | """" :: rest -> List.rev rest
     | parts -> List.rev parts)".

Separate Extraction convert generated accepted rt_lhs rt_rhs render_cb
  keyed_accepted keyed_rt_lhs wiki_accepted wiki_rt_lhs
  parse_blocks_located parse_doc_located
  line_table resolve_span.
