open Datatypes
open Nat0

val hd : 'a1 -> 'a1 list -> 'a1

val nth_error : 'a1 list -> int -> 'a1 option

val last : 'a1 list -> 'a1 -> 'a1

val rev : 'a1 list -> 'a1 list

val concat : 'a1 list list -> 'a1 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val list_max : int list -> int
