(* ai-disclosure: ai-generated *)

(* Haskell extraction of [convert], twice: with [string] as [String],
   then as a strict [ByteString].  [nat] is [Int] and [comparison] is
   [Ordering].  None of the realizations in ../ocaml/Extract.v are
   copied.

   Paths are relative to the repository root, where scripts/haskell.sh
   runs this file.  Extraction cannot emit imports, so the script adds
   [Data.Bits], [Data.Char] and [Data.ByteString.Char8] to every
   module. *)

From Stdlib Require Import String Extraction.
From Stdlib Require Import ExtrHaskellBasic ExtrHaskellString ExtrHaskellNatInt.
From DjotV Require Import Strings Html.

Extraction Language Haskell.

(*
Numbers and order
=================

As in ../ocaml/Extract.v: [sub] truncates at zero, and division by zero
returns what Gallina's does. *)

Extract Constant List.rev => "Prelude.reverse".

Extract Inlined Constant Init.Nat.add => "(Prelude.+)".
Extract Inlined Constant Init.Nat.mul => "(Prelude.*)".
Extract Constant Init.Nat.sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".
Extract Constant Init.Nat.pred => "(\n -> Prelude.max 0 (n Prelude.- 1))".
Extract Inlined Constant Init.Nat.eqb => "(Prelude.==)".
Extract Inlined Constant Init.Nat.leb => "(Prelude.<=)".
Extract Inlined Constant Init.Nat.ltb => "(Prelude.<)".
Extract Constant Init.Nat.div =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Init.Nat.modulo =>
  "(\n m -> if m Prelude.== 0 then n else Prelude.mod n m)".

Extract Inlined Constant PeanoNat.Nat.add => "(Prelude.+)".
Extract Inlined Constant PeanoNat.Nat.mul => "(Prelude.*)".
Extract Constant PeanoNat.Nat.sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".
Extract Constant PeanoNat.Nat.pred => "(\n -> Prelude.max 0 (n Prelude.- 1))".
Extract Inlined Constant PeanoNat.Nat.eqb => "(Prelude.==)".
Extract Inlined Constant PeanoNat.Nat.leb => "(Prelude.<=)".
Extract Inlined Constant PeanoNat.Nat.ltb => "(Prelude.<)".
Extract Constant PeanoNat.Nat.div =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant PeanoNat.Nat.modulo =>
  "(\n m -> if m Prelude.== 0 then n else Prelude.mod n m)".

Extract Inlined Constant Ascii.nat_of_ascii => "Data.Char.ord".
Extract Constant Ascii.ascii_of_nat => "(\n -> Data.Char.chr (n `Prelude.mod` 256))".

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
Extract Inlined Constant String.compare => "Prelude.compare".

(*
Strings as [String]
===================

A list of characters, so matching [String c rest] and building
[String c acc] are both constant time. *)

Extract Inlined Constant String.length => "Prelude.length".
Extract Constant DjotV.Strings.nat_str => "Prelude.show".

Set Extraction Output Directory "_build/haskell/string/src".
Separate Extraction convert.

(*
Strings as [ByteString]
=======================

[uncons] shares the tail, but [cons] copies the whole string, so
building a string a byte at a time is quadratic, as with OCaml's native
strings. *)

Extract Inductive string => "Data.ByteString.Char8.ByteString"
  ["Data.ByteString.Char8.empty" "Data.ByteString.Char8.cons"]
  "(\fnil fcons s -> case Data.ByteString.Char8.uncons s of {
      Prelude.Nothing -> fnil ();
      Prelude.Just (c, r) -> fcons c r })".
Extract Inlined Constant String.append => "Data.ByteString.Char8.append".
Extract Inlined Constant String.length => "Data.ByteString.Char8.length".
Extract Inlined Constant String.concat => "Data.ByteString.Char8.intercalate".
Extract Inlined Constant String.eqb => "(Prelude.==)".
Extract Inlined Constant String.string_dec => "(Prelude.==)".
Extract Constant DjotV.Strings.nat_str =>
  "(\n -> Data.ByteString.Char8.pack (Prelude.show n))".

Set Extraction Output Directory "_build/haskell/bytestring/src".
Separate Extraction convert.
