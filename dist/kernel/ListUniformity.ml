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
   | KList (_, _, _, _) -> lines_loose t k loose false st' rest
   | _ ->
     lines_loose t k (if foot_takes k 0 l st then loose else (||) loose gap)
       false st' rest)

(** val item_loose : dtable -> bconfig -> string list -> bool **)

let item_loose t k l =
  lines_loose t k false false (PPara []) l

type litem = marker * string list

(** val litem_lines : litem -> string list **)

let litem_lines it =
  indent_lines (mk_open (fst it)) (mk_cont (fst it)) (snd it)

(** val item_ok : dtable -> bconfig -> marker -> string list -> bool **)

let item_ok t k m = function
| [] -> false
| l0 :: more ->
  (&&)
    ((&&)
      ((&&)
        ((&&) (negb (is_thematic ((^) (mk_open m) l0)))
          (negb (task_start l0)))
        (nonblank l0))
      (run_safe t k more
        (snd (step t k semantic_line_ix semantic_pos l0 (PPara [])))))
    (match more with
     | [] -> true
     | _ :: _ -> nonblank (last more ""))

(** val ends_open_container : dtable -> bconfig -> string list -> bool **)

let ends_open_container t k l =
  blank_absorbed (snd (run_lines t k l (PPara [])))

(** val seps_loosen : dtable -> bconfig -> string list list -> bool **)

let rec seps_loosen t k = function
| [] -> false
| l :: rest ->
  (match rest with
   | [] -> false
   | _ :: _ -> (||) (negb (ends_open_container t k l)) (seps_loosen t k rest))

(** val same_marker : marker -> string list list -> litem list **)

let same_marker m lss =
  map (fun l -> (m, l)) lss
