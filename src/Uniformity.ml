open Ast
open Datatypes
open Inline
open Line
open Step
open Strings

(** val run_lines :
    dtable -> bconfig -> string list -> pstate -> blocks * pstate **)

let rec run_lines t k lines st =
  match lines with
  | [] -> ([], st)
  | l :: rest ->
    let (bs, st') = step t k l st in
    let (more, st'') = run_lines t k rest st' in ((app bs more), st'')

(** val run_div_open :
    dtable -> bconfig -> nat -> string list -> pstate -> bool **)

let rec run_div_open t k len lines st =
  match lines with
  | [] -> true
  | l :: rest ->
    (&&) (negb ((&&) (negb (in_fence st)) (div_close len l)))
      (run_div_open t k len rest (snd (step t k l st)))

(** val div_content_ok : dtable -> bconfig -> string list -> bool **)

let div_content_ok t k lines =
  (&&) (run_div_open t k (S (S (S O))) lines (PPara []))
    (negb (in_fence (snd (run_lines t k lines (PPara [])))))

(** val pend_carriable : pstate -> bool **)

let pend_carriable = function
| PPara cur -> (match cur with
                | [] -> false
                | _ :: _ -> true)
| PAttr (_, _, _, _) -> false
| PPend (_, _) -> false
| _ -> true

(** val key_carriable : pstate -> bool **)

let key_carriable st = match st with
| PPend (_, inner) -> pend_carriable inner
| _ -> pend_carriable st

(** val key_content_ok :
    dtable -> bconfig -> string list -> pstate -> bool **)

let rec key_content_ok t k ls st =
  match ls with
  | [] -> key_carriable st
  | l :: rest ->
    (&&) (negb ((&&) (is_blank l) (is_idle st)))
      (let (bs, st') = step t k l st in
       (match bs with
        | [] -> key_content_ok t k rest st'
        | _ :: _ -> true))
