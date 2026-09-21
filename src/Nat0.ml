open Datatypes
open Decimal

(** val pred : nat -> nat **)

let pred n = match n with
| O -> n
| S u -> u

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val eqb : nat -> nat -> bool **)

let rec eqb n m =
  match n with
  | O -> (match m with
          | O -> true
          | S _ -> false)
  | S n' -> (match m with
             | O -> false
             | S m' -> eqb n' m')

(** val leb : nat -> nat -> bool **)

let rec leb n m =
  match n with
  | O -> true
  | S n' -> (match m with
             | O -> false
             | S m' -> leb n' m')

(** val to_little_uint : nat -> uint -> uint **)

let rec to_little_uint n acc =
  match n with
  | O -> acc
  | S n0 -> to_little_uint n0 (Little.succ acc)

(** val to_uint : nat -> uint **)

let to_uint n =
  rev (to_little_uint n (D0 Nil))
