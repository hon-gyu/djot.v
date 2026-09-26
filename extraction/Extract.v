(* ai-disclosure: ai-generated *)

(* Extraction prelude.  `Separate Extraction` emits one OCaml module per
   Coq module rather than one flat file, so the extracted parser can be
   read against the theory it came from.  The blacklist keeps `String`,
   `List`, `Nat` and `Bool` from shadowing OCaml's own; they land as
   `String0`, `List0`, `Nat0`, `Bool0`.

   `ExtrOcamlNativeString` maps Gallina strings to native OCaml strings,
   so no conversion glue is needed on the OCaml side. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString.
From Stdlib Require OrdersEx.
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
   are trusted, not proved. *)
Extract Constant List.rev => "List.rev".
Extract Inlined Constant String.length => "String.length".

(* [nat] is OCaml's [int], and the [nat] operations the parser uses are
   OCaml's arithmetic.  Unary [nat] made every numeral cost memory
   linear in its value (a nine-digit list start overflowed the stack) and
   every character class test cost a walk up to 255 cells.

   [int] wraps at [max_int], [nat] does not.  The parser's numbers are
   lengths, positions and counts, bounded by the input's size, plus the
   numerals it reads; `Marker.dec_start_bound` bounds the one numeral
   that could grow with the input, a decimal list start.

   [Init.Nat] and [PeanoNat.Nat] each extract their own copy of these
   operations, so both are mapped.  [Nat.sub] truncates at zero, and
   [Nat.div] and [Nat.modulo] by zero return zero and [n]. *)
Extract Inductive nat => int [ "0" "Stdlib.succ" ]
  "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".

Extract Inlined Constant Init.Nat.add => "( + )".
Extract Inlined Constant Init.Nat.mul => "( * )".
Extract Constant Init.Nat.sub => "fun n m -> Stdlib.max 0 (n - m)".
Extract Constant Init.Nat.pred => "fun n -> Stdlib.max 0 (n - 1)".
Extract Inlined Constant Init.Nat.eqb => "( = )".
Extract Inlined Constant Init.Nat.leb => "( <= )".
Extract Inlined Constant Init.Nat.ltb => "( < )".
Extract Constant Init.Nat.div => "fun n m -> if m = 0 then 0 else n / m".
Extract Constant Init.Nat.modulo => "fun n m -> if m = 0 then n else n mod m".

Extract Inlined Constant PeanoNat.Nat.add => "( + )".
Extract Inlined Constant PeanoNat.Nat.mul => "( * )".
Extract Constant PeanoNat.Nat.sub => "fun n m -> Stdlib.max 0 (n - m)".
Extract Constant PeanoNat.Nat.pred => "fun n -> Stdlib.max 0 (n - 1)".
Extract Inlined Constant PeanoNat.Nat.eqb => "( = )".
Extract Inlined Constant PeanoNat.Nat.leb => "( <= )".
Extract Inlined Constant PeanoNat.Nat.ltb => "( < )".
Extract Constant PeanoNat.Nat.div => "fun n m -> if m = 0 then 0 else n / m".
Extract Constant PeanoNat.Nat.modulo =>
  "fun n m -> if m = 0 then n else n mod m".

(* [ascii_of_nat] keeps the low eight bits, as the Gallina one does. *)
Extract Inlined Constant Ascii.nat_of_ascii => "Char.code".
Extract Constant Ascii.ascii_of_nat => "fun n -> Char.chr (n land 255)".
Extract Constant DjotV.Strings.nat_str => "Stdlib.string_of_int".
(* The HTML escapers are per-character recursions with a tail copy and an
   append per character, quadratic in the length of a text node.
   ([String.concat], which `Html.serialize_flat` joins the document with,
   is already OCaml's under `ExtrOcamlNativeString`.) *)
Extract Constant DjotV.Html.escape =>
  "(fun s ->
     let b = Buffer.create (String.length s) in
     String.iter (function
       | '&' -> Buffer.add_string b ""&amp;""
       | '<' -> Buffer.add_string b ""&lt;""
       | '>' -> Buffer.add_string b ""&gt;""
       | c -> Buffer.add_char b c) s;
     Buffer.contents b)".
Extract Constant DjotV.Html.escape_attr =>
  "(fun s ->
     let b = Buffer.create (String.length s) in
     String.iter (function
       | '&' -> Buffer.add_string b ""&amp;""
       | '<' -> Buffer.add_string b ""&lt;""
       | '>' -> Buffer.add_string b ""&gt;""
       | '""' -> Buffer.add_string b ""&quot;""
       | c -> Buffer.add_char b c) s;
     Buffer.contents b)".
(* String order, for the identifier pass's balanced trees
   (`Document.StrSet`, `Document.StrMap`).  Both Gallina orders are
   lexicographic by character code with a proper prefix first, which is
   OCaml's [String.compare]. *)
Extract Constant String.compare =>
  "(fun a b -> let c = Stdlib.String.compare a b in
     if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt
     else Datatypes.Gt)".
Extract Constant OrdersEx.String_as_OT.compare =>
  "(fun a b -> let c = Stdlib.String.compare a b in
     if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt
     else Datatypes.Gt)".
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
