open Ascii
open Ast
open Datatypes
open Line
open List0
open ListDef
open Nat0
open PeanoNat
open Strings

(** val dec_acc : string -> int -> int **)

let rec dec_acc s acc0 =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> acc0)
    (fun c s' ->
    dec_acc s'
      (( + )
        (( * ) acc0 (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ 0)))))))))))
        (sub (Char.code c) (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          0)))))))))))))))))))))))))))))))))))))))))))))))))))
    s

(** val dec_value : string -> int **)

let dec_value s =
  dec_acc s 0

(** val digit_char : int -> char **)

let digit_char d =
  ascii_of_nat
    (( + ) (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))) d)

(** val dec_str_fuel : int -> int -> string **)

let rec dec_str_fuel fuel n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> "")
    (fun f ->
    if ( < ) n (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
         (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
         (Stdlib.succ 0))))))))))
    then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           ((digit_char n), "")
    else (^)
           (dec_str_fuel f
             (Nat.div n (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
               (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
               (Stdlib.succ (Stdlib.succ 0))))))))))))
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           ((digit_char
              (Nat.modulo n (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))))))))))),
           "")))
    fuel

(** val dec_str : int -> string **)

let dec_str n =
  dec_str_fuel (Stdlib.succ n) n

(** val dec_fits : int -> bool **)

let dec_fits n =
  ( <= ) (String.length (dec_str n)) dec_digits_max

module Roman =
 struct
  (** val digit : char -> int **)

  let digit c =
    if (||) ((=) c 'i') ((=) c 'I')
    then Stdlib.succ 0
    else if (||) ((=) c 'v') ((=) c 'V')
         then Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                0))))
         else if (||) ((=) c 'x') ((=) c 'X')
              then Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                     (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                     (Stdlib.succ (Stdlib.succ 0)))))))))
              else if (||) ((=) c 'l') ((=) c 'L')
                   then Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                          (Stdlib.succ (Stdlib.succ
                          0)))))))))))))))))))))))))))))))))))))))))))))))))
                   else if (||) ((=) c 'c') ((=) c 'C')
                        then Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ (Stdlib.succ (Stdlib.succ
                               (Stdlib.succ
                               0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        else if (||) ((=) c 'd') ((=) c 'D')
                             then Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                    (Stdlib.succ (Stdlib.succ
                                    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                             else if (||) ((=) c 'm') ((=) c 'M')
                                  then Stdlib.succ (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ (Stdlib.succ
                                         (Stdlib.succ
                                         0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  else 0

  (** val acc : string -> int -> int -> int **)

  let rec acc s prev total =
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> total)
      (fun c s' ->
      let n = digit c in
      acc s' n (if ( < ) n prev then sub total n else ( + ) total n))
      s

  (** val value : string -> int **)

  let value s =
    acc (rev_string s) 0 0

  (** val upper : int **)

  let upper =
    Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val table : bool -> (int * string) list **)

  let table = function
  | true ->
    ((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      "M") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      "CM") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      "D") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      "CD") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      "C") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      "XC") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0)))))))))))))))))))))))))))))))))))))))))))))))))),
      "L") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0)))))))))))))))))))))))))))))))))))))))),
      "XL") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0)))))))))), "X") :: (((Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0))))))))), "IX") :: (((Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))),
      "V") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))),
      "IV") :: (((Stdlib.succ 0), "I") :: []))))))))))))
  | false ->
    ((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      "m") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      "cm") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      "d") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      "cd") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      "c") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      "xc") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0)))))))))))))))))))))))))))))))))))))))))))))))))),
      "l") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0)))))))))))))))))))))))))))))))))))))))),
      "xl") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0)))))))))), "x") :: (((Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0))))))))), "ix") :: (((Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))),
      "v") :: (((Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))),
      "iv") :: (((Stdlib.succ 0), "i") :: []))))))))))))

  (** val pick : (int * string) list -> int -> (int * string) option **)

  let rec pick tbl n =
    match tbl with
    | [] -> None
    | p :: rest ->
      let (v, s) = p in if ( <= ) v n then Some (v, s) else pick rest n

  (** val of_fuel : bool -> int -> int -> string **)

  let rec of_fuel up fuel n =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> "")
      (fun f ->
      match pick (table up) n with
      | Some p -> let (v, s) = p in (^) s (of_fuel up f (sub n v))
      | None -> "")
      fuel

  (** val str : bool -> int -> string **)

  let str up n =
    of_fuel up (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0)))))))))))))))) n
 end

module Alpha =
 struct
  (** val value : bool -> string -> int **)

  let value up core =
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> Stdlib.succ 0)
      (fun c _ ->
      sub (Char.code c)
        (if up
         then Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ
                0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         else Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ
                0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      core

  (** val str : bool -> int -> string **)

  let str up n =
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      ((ascii_of_nat
         (( + )
           (if up
            then Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            else Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                   0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           n)),
      "")

  (** val upper : int **)

  let upper =
    Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0)))))))))))))))))))))))))
 end

(** val style_start : lstyle -> string -> int **)

let style_start s core =
  match s with
  | SOrd (n, _) ->
    (match n with
     | Decimal -> dec_value core
     | LetterUpper -> Alpha.value true core
     | LetterLower -> Alpha.value false core
     | _ -> Roman.value core)
  | _ -> Stdlib.succ 0

(** val with_starts : lstyle list -> string -> (lstyle * int) list **)

let with_starts sty core =
  map (fun s -> (s, (style_start s core))) sty

(** val narrow : (lstyle * int) list -> lstyle list -> (lstyle * int) list **)

let narrow old new0 =
  filter (fun p -> existsb (lstyle_eqb (fst p)) new0) old
