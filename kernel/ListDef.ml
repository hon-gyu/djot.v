
(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Stdlib.succ start) len0))
    len

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> [])
    (fun n0 -> match l with
               | [] -> []
               | a :: l0 -> a :: (firstn n0 l0))
    n

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> l)
    (fun n0 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n0 l0)
    n
