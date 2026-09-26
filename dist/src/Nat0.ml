
(** val pred : int -> int **)

let pred = fun n -> Stdlib.max 0 (n - 1)

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n - m)


