open Datatypes

(** val ascii_of_nat : int -> char **)

let ascii_of_nat = fun n -> Char.chr (n land 255)

(** val compare : char -> char -> comparison **)

let compare = fun c1 c2 ->
    let cmp = Char.compare c1 c2 in
    if cmp < 0 then Lt else if cmp = 0 then Eq else Gt

(** val leb : char -> char -> bool **)

let leb a b =
  match compare a b with
  | Gt -> false
  | _ -> true
