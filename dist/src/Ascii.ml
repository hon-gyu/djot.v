open BinNat
open BinNums
open Datatypes

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : positive -> char **)

let ascii_of_pos =
  let rec loop n p =
    match n with
    | O -> zero
    | S n' ->
      (match p with
       | Coq_xI p' -> shift true (loop n' p')
       | Coq_xO p' -> shift false (loop n' p')
       | Coq_xH -> one)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : coq_N -> char **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : nat -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val coq_N_of_digits : bool list -> coq_N **)

let rec coq_N_of_digits = function
| [] -> N0
| b :: l' ->
  N.add (if b then Npos Coq_xH else N0)
    (N.mul (Npos (Coq_xO Coq_xH)) (coq_N_of_digits l'))

(** val coq_N_of_ascii : char -> coq_N **)

let coq_N_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    coq_N_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> nat **)

let nat_of_ascii a =
  N.to_nat (coq_N_of_ascii a)

(** val compare : char -> char -> comparison **)

let compare = fun c1 c2 ->
    let cmp = Char.compare c1 c2 in
    if cmp < 0 then Lt else if cmp = 0 then Eq else Gt

(** val leb : char -> char -> bool **)

let leb a b =
  match compare a b with
  | Gt -> false
  | _ -> true
