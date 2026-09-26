open Datatypes
open String0

module String_as_OT =
 struct
  type t = string

  (** val cmp : string -> string -> comparison **)

  let cmp =
    compare

  (** val compare : string -> string -> string OrderedType.coq_Compare **)

  let compare a b =
    match cmp a b with
    | Eq -> OrderedType.EQ
    | Lt -> OrderedType.LT
    | Gt -> OrderedType.GT

  (** val eq_dec : string -> string -> bool **)

  let eq_dec =
    (=)
 end
