
module Nat =
 struct
  (** val sub : int -> int -> int **)

  let rec sub = fun n m -> Stdlib.max 0 (n - m)

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
        (fun _ -> divmod x' y (Stdlib.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div = fun n m -> if m = 0 then 0 else n / m

  (** val modulo : int -> int -> int **)

  let modulo = fun n m -> if m = 0 then n else n mod m
 end
