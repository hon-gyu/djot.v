open Datatypes
open Profile

(** val wrap_safe : options -> bool **)

let wrap_safe o =
  (&&) ((&&) (negb o.o_list_interrupts) (negb o.o_setext)) (negb o.o_keyed)

(** val heading_wrap_safe : options -> bool **)

let heading_wrap_safe o =
  o.o_heading_continuation

(** val quote_uniform : options -> bool **)

let quote_uniform o =
  negb o.o_callouts

(** val lazy_uniform : options -> bool **)

let lazy_uniform o =
  negb o.o_setext

(** val shape_first : options -> bool **)

let shape_first o =
  negb o.o_keyed
