open Datatypes
open String0

module String_as_OT :
 sig
  type t = string

  val cmp : string -> string -> comparison

  val compare : string -> string -> string OrderedType.coq_Compare

  val eq_dec : string -> string -> bool
 end
