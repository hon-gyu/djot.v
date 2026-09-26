open Ascii
open BinNat
open BinNums
open Datatypes
open Decimal
open Hexadecimal
open Number

type __ = Obj.t

module N_as_OT = N

module Ascii_as_OT =
 struct
  (** val compare : char -> char -> comparison **)

  let compare a b =
    N_as_OT.compare (coq_N_of_ascii a) (coq_N_of_ascii b)
 end

module String_as_OT =
 struct
  type t = string

  (** val eqb : string -> string -> bool **)

  let eqb =
    (=)

  (** val eq_dec : string -> string -> bool **)

  let eq_dec x y =
    let b = (=) x y in if b then true else false

  (** val compare : string -> string -> comparison **)

  let rec compare = (fun a b -> let c = Stdlib.String.compare a b in
     if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt
     else Datatypes.Gt)
 end
