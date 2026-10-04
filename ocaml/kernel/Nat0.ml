
(** val pred : int -> int **)

let pred = fun n -> Stdlib.max 0 (n - 1)

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n - m)

(** val max : int -> int -> int **)

let rec max n m =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> m)
    (fun n' ->
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> n)
      (fun m' -> Stdlib.succ (max n' m'))
      m)
    n

(** val min : int -> int -> int **)

let rec min n m =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> 0)
    (fun n' ->
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> 0)
      (fun m' -> Stdlib.succ (min n' m'))
      m)
    n
