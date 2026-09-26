open BinNat
open BinNums
open Datatypes

val ascii_of_nat : int -> char

val coq_N_of_digits : bool list -> coq_N

val coq_N_of_ascii : char -> coq_N

val compare : char -> char -> comparison

val leb : char -> char -> bool
