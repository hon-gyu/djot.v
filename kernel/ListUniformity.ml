open Ast
open Datatypes
open InlineTable
open Line
open List0
open ListDef
open Step
open Strings
open Uniformity

(** val indent_lines : string -> string -> string list -> string list **)

let indent_lines first_prefix rest_prefix = function
| [] -> []
| l :: rest -> ((^) first_prefix l) :: (map (fun x -> (^) rest_prefix x) rest)

(** val list_lines : list_spacing -> string list list -> string list **)

let rec list_lines sp = function
| [] -> []
| ls :: rest ->
  (match rest with
   | [] -> ls
   | _ :: _ ->
     app ls
       (app (match sp with
             | Tight -> []
             | Loose -> "" :: [])
         (list_lines sp rest)))

(** val run_safe : dtable -> bconfig -> string list -> pstate -> bool **)

let rec run_safe t k lines st =
  match lines with
  | [] -> blank_safe st
  | l :: rest ->
    (&&) (pad_safe st)
      (run_safe t k rest (snd (step t k semantic_line_ix semantic_pos l st)))

(** val lines_loose :
    dtable -> bconfig -> bool -> bool -> pstate -> string list -> bool **)

let rec lines_loose t k loose gap st = function
| [] -> loose
| l :: rest ->
  let st' = snd (step t k semantic_line_ix semantic_pos l st) in
  (match classify l with
   | KBlank ->
     lines_loose t k loose (if blank_absorbed st then gap else true) st' rest
   | KList (_, _, _, _) -> lines_loose t k loose (div_closer l st) st' rest
   | _ ->
     if div_closer l st
     then lines_loose t k loose true st' rest
     else lines_loose t k ((||) loose gap) false st' rest)

(** val lines_gap :
    dtable -> bconfig -> bool -> pstate -> string list -> bool **)

let rec lines_gap t k gap st = function
| [] -> gap
| l :: rest ->
  let st' = snd (step t k semantic_line_ix semantic_pos l st) in
  (match classify l with
   | KBlank ->
     lines_gap t k (if blank_absorbed st then gap else true) st' rest
   | _ -> lines_gap t k (div_closer l st) st' rest)

(** val item_loose : dtable -> bconfig -> string list -> bool **)

let item_loose t k l =
  lines_loose t k false false (PPara []) l

(** val item_gap : dtable -> bconfig -> string list -> bool **)

let item_gap t k l =
  lines_gap t k false (PPara []) l

type litem = marker * string list

(** val litem_lines : litem -> string list **)

let litem_lines it =
  indent_lines (mk_open (fst it)) (mk_cont (fst it)) (snd it)

(** val item_ok : dtable -> bconfig -> marker -> string list -> bool **)

let item_ok t k m l = match l with
| [] -> false
| l0 :: more ->
  (&&)
    ((&&)
      ((&&)
        ((&&)
          ((&&) (negb (is_thematic ((^) (mk_open m) l0)))
            (negb (task_start l0)))
          (nonblank l0))
        (run_safe t k more
          (snd (step t k semantic_line_ix semantic_pos l0 (PPara [])))))
      (match more with
       | [] -> true
       | _ :: _ -> nonblank (last more "")))
    (negb (item_gap t k l))

(** val ends_open_container : dtable -> bconfig -> string list -> bool **)

let ends_open_container t k l =
  blank_absorbed (snd (run_lines t k l (PPara [])))

(** val starts_list : string list -> bool **)

let starts_list = function
| [] -> false
| l0 :: _ -> (match classify l0 with
              | KList (_, _, _, _) -> true
              | _ -> false)

(** val seps_loosen : dtable -> bconfig -> string list list -> bool **)

let rec seps_loosen t k = function
| [] -> false
| l :: rest ->
  (match rest with
   | [] -> false
   | l2 :: _ ->
     (||) ((&&) (negb (ends_open_container t k l)) (negb (starts_list l2)))
       (seps_loosen t k rest))

(** val same_marker : marker -> string list list -> litem list **)

let same_marker m lss =
  map (fun l -> (m, l)) lss
