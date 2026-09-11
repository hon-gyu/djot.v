open BinNat
open BinNums
open Datatypes

val zero : char

val one : char

val shift : bool -> char -> char

val ascii_of_pos : positive -> char

val ascii_of_N : coq_N -> char

val ascii_of_nat : nat -> char

val coq_N_of_digits : bool list -> coq_N

val coq_N_of_ascii : char -> coq_N

val nat_of_ascii : char -> nat

val compare : char -> char -> comparison

val leb : char -> char -> bool
