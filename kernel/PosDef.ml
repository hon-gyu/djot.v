open BinNums
open Datatypes

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | Coq_xI p -> Coq_xO (succ p)
  | Coq_xO p -> Coq_xI p
  | Coq_xH -> Coq_xO Coq_xH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> Coq_xO (add_carry p q)
       | Coq_xO q -> Coq_xI (add p q)
       | Coq_xH -> Coq_xO (succ p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> Coq_xI (add p q)
       | Coq_xO q -> Coq_xO (add p q)
       | Coq_xH -> Coq_xI p)
    | Coq_xH ->
      (match y with
       | Coq_xI q -> Coq_xO (succ q)
       | Coq_xO q -> Coq_xI q
       | Coq_xH -> Coq_xO Coq_xH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> Coq_xI (add_carry p q)
       | Coq_xO q -> Coq_xO (add_carry p q)
       | Coq_xH -> Coq_xI (succ p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> Coq_xO (add_carry p q)
       | Coq_xO q -> Coq_xI (add p q)
       | Coq_xH -> Coq_xO (succ p))
    | Coq_xH ->
      (match y with
       | Coq_xI q -> Coq_xI (succ q)
       | Coq_xO q -> Coq_xO (succ q)
       | Coq_xH -> Coq_xI Coq_xH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | Coq_xI p -> Coq_xI (Coq_xO p)
  | Coq_xO p -> Coq_xI (pred_double p)
  | Coq_xH -> Coq_xH

  (** val pred_N : positive -> coq_N **)

  let pred_N = function
  | Coq_xI p -> Npos (Coq_xO p)
  | Coq_xO p -> Npos (pred_double p)
  | Coq_xH -> N0

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos Coq_xH
  | IsPos p -> IsPos (Coq_xI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (Coq_xO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | Coq_xI p -> IsPos (Coq_xO (Coq_xO p))
  | Coq_xO p -> IsPos (Coq_xO (pred_double p))
  | Coq_xH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> double_mask (sub_mask p q)
       | Coq_xO q -> succ_double_mask (sub_mask p q)
       | Coq_xH -> IsPos (Coq_xO p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> succ_double_mask (sub_mask_carry p q)
       | Coq_xO q -> double_mask (sub_mask p q)
       | Coq_xH -> IsPos (pred_double p))
    | Coq_xH -> (match y with
                 | Coq_xH -> IsNul
                 | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> succ_double_mask (sub_mask_carry p q)
       | Coq_xO q -> double_mask (sub_mask p q)
       | Coq_xH -> IsPos (pred_double p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> double_mask (sub_mask_carry p q)
       | Coq_xO q -> succ_double_mask (sub_mask_carry p q)
       | Coq_xH -> double_pred_mask p)
    | Coq_xH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | Coq_xI p -> add y (Coq_xO (mul p y))
    | Coq_xO p -> Coq_xO (mul p y)
    | Coq_xH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | Coq_xI n' -> f (iter f (iter f x n') n')
  | Coq_xO n' -> iter f (iter f x n') n'
  | Coq_xH -> f x

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> compare_cont r p q
       | Coq_xO q -> compare_cont Gt p q
       | Coq_xH -> Gt)
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> compare_cont Lt p q
       | Coq_xO q -> compare_cont r p q
       | Coq_xH -> Gt)
    | Coq_xH -> (match y with
                 | Coq_xH -> r
                 | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | Coq_xI p0 -> (match q with
                    | Coq_xI q0 -> eqb p0 q0
                    | _ -> false)
    | Coq_xO p0 -> (match q with
                    | Coq_xO q0 -> eqb p0 q0
                    | _ -> false)
    | Coq_xH -> (match q with
                 | Coq_xH -> true
                 | _ -> false)

  (** val leb : positive -> positive -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive * mask) ->
      positive * mask **)

  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = Coq_xI (Coq_xO s) in
       let r' = g (f r) in
       if leb s' r'
       then ((Coq_xI s), (sub_mask r' s'))
       else ((Coq_xO s), (IsPos r'))
     | _ -> ((Coq_xO s), (sub_mask (g (f Coq_xH)) (Coq_xO (Coq_xO Coq_xH)))))

  (** val sqrtrem : positive -> positive * mask **)

  let rec sqrtrem = function
  | Coq_xI p0 ->
    (match p0 with
     | Coq_xI p1 ->
       sqrtrem_step (fun x -> Coq_xI x) (fun x -> Coq_xI x) (sqrtrem p1)
     | Coq_xO p1 ->
       sqrtrem_step (fun x -> Coq_xO x) (fun x -> Coq_xI x) (sqrtrem p1)
     | Coq_xH -> (Coq_xH, (IsPos (Coq_xO Coq_xH))))
  | Coq_xO p0 ->
    (match p0 with
     | Coq_xI p1 ->
       sqrtrem_step (fun x -> Coq_xI x) (fun x -> Coq_xO x) (sqrtrem p1)
     | Coq_xO p1 ->
       sqrtrem_step (fun x -> Coq_xO x) (fun x -> Coq_xO x) (sqrtrem p1)
     | Coq_xH -> (Coq_xH, (IsPos Coq_xH)))
  | Coq_xH -> (Coq_xH, IsNul)

  (** val sqrt : positive -> positive **)

  let sqrt p =
    fst (sqrtrem p)

  (** val coq_Nsucc_double : coq_N -> coq_N **)

  let coq_Nsucc_double = function
  | N0 -> Npos Coq_xH
  | Npos p -> Npos (Coq_xI p)

  (** val coq_Ndouble : coq_N -> coq_N **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (Coq_xO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | Coq_xI p0 ->
      (match q with
       | Coq_xI q0 -> Coq_xI (coq_lor p0 q0)
       | Coq_xO q0 -> Coq_xI (coq_lor p0 q0)
       | Coq_xH -> p)
    | Coq_xO p0 ->
      (match q with
       | Coq_xI q0 -> Coq_xI (coq_lor p0 q0)
       | Coq_xO q0 -> Coq_xO (coq_lor p0 q0)
       | Coq_xH -> Coq_xI p0)
    | Coq_xH -> (match q with
                 | Coq_xO q0 -> Coq_xI q0
                 | _ -> q)

  (** val coq_land : positive -> positive -> coq_N **)

  let rec coq_land p q =
    match p with
    | Coq_xI p0 ->
      (match q with
       | Coq_xI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | Coq_xO q0 -> coq_Ndouble (coq_land p0 q0)
       | Coq_xH -> Npos Coq_xH)
    | Coq_xO p0 ->
      (match q with
       | Coq_xI q0 -> coq_Ndouble (coq_land p0 q0)
       | Coq_xO q0 -> coq_Ndouble (coq_land p0 q0)
       | Coq_xH -> N0)
    | Coq_xH -> (match q with
                 | Coq_xO _ -> N0
                 | _ -> Npos Coq_xH)

  (** val ldiff : positive -> positive -> coq_N **)

  let rec ldiff p q =
    match p with
    | Coq_xI p0 ->
      (match q with
       | Coq_xI q0 -> coq_Ndouble (ldiff p0 q0)
       | Coq_xO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | Coq_xH -> Npos (Coq_xO p0))
    | Coq_xO p0 ->
      (match q with
       | Coq_xI q0 -> coq_Ndouble (ldiff p0 q0)
       | Coq_xO q0 -> coq_Ndouble (ldiff p0 q0)
       | Coq_xH -> Npos p)
    | Coq_xH -> (match q with
                 | Coq_xO _ -> Npos Coq_xH
                 | _ -> N0)

  (** val coq_lxor : positive -> positive -> coq_N **)

  let rec coq_lxor p q =
    match p with
    | Coq_xI p0 ->
      (match q with
       | Coq_xI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | Coq_xO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | Coq_xH -> Npos (Coq_xO p0))
    | Coq_xO p0 ->
      (match q with
       | Coq_xI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | Coq_xO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | Coq_xH -> Npos (Coq_xI p0))
    | Coq_xH ->
      (match q with
       | Coq_xI q0 -> Npos (Coq_xO q0)
       | Coq_xO q0 -> Npos (Coq_xI q0)
       | Coq_xH -> N0)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | Coq_xI p0 -> op a (iter_op op p0 (op a a))
    | Coq_xO p0 -> iter_op op p0 (op a a)
    | Coq_xH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op ( + ) x (Stdlib.succ 0)

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> Coq_xH)
      (fun x -> succ (of_succ_nat x))
      n
 end
