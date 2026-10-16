open Ast
open AstEq
open Attributes
open Datatypes
open InlineTable
open List0
open Nat0
open Render
open Step
open String0
open Strings

(** val del : int -> string -> string **)

let rec del = (fun i s -> let n = String.length s in
     if i < n then String.sub s 0 i ^ String.sub s (i + 1) (n - i - 1) else s)

(** val stop_go : int -> int -> string -> int **)

let rec stop_go fuel p s =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> p)
    (fun f ->
    match get p s with
    | Some c ->
      (match get (Stdlib.succ p) s with
       | Some d ->
         if (&&) ((=) c '\n') ((=) d '\n')
         then p
         else stop_go f (Stdlib.succ p) s
       | None -> String.length s)
    | None -> String.length s)
    fuel

(** val para_stop : string -> int -> int **)

let para_stop s p =
  stop_go (sub (String.length s) p) p s

(** val first_at :
    (string -> 'a1 option) -> string -> int -> (string * 'a1) option **)

let first_at f s i =
  let test = fun t -> match f t with
                      | Some b -> Some (t, b)
                      | None -> None in
  (match get i s with
   | Some c ->
     if (=) c bslash
     then test (del i s)
     else if (=) c lbrace
          then let rec go m j =
                 (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                   (fun _ -> None)
                   (fun m' ->
                   match match get j s with
                         | Some d ->
                           if (=) d rbrace
                           then test (del i (del j s))
                           else None
                         | None -> None with
                   | Some r -> Some r
                   | None -> go m' (Stdlib.succ j))
                   m
               in go (sub (para_stop s (Stdlib.succ i)) (Stdlib.succ i))
                    (Stdlib.succ i)
          else None
   | None -> None)

(** val first_from :
    (string -> 'a1 option) -> string -> int -> int -> ((string * 'a1) * int)
    option **)

let rec first_from f s n i =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> None)
    (fun m ->
    match first_at f s i with
    | Some p -> Some (p, i)
    | None -> first_from f s m (Stdlib.succ i))
    n

(** val next :
    (string -> 'a1 option) -> int -> string -> ((string * 'a1) * int) option **)

let next f k s =
  match first_from f s (sub (String.length s) k) k with
  | Some r -> Some r
  | None -> first_from f s (String.length s) 0

(** val shrink_by :
    ('a1 -> string -> 'a1 option) -> int -> int -> 'a1 -> string -> string **)

let rec shrink_by test fuel k c s =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> s)
    (fun f ->
    match next (test c) k s with
    | Some p -> let (p0, i) = p in let (t, c') = p0 in shrink_by test f i c' t
    | None -> s)
    fuel

(** val same_state : pstate -> pstate -> bool **)

let same_state a b =
  match a with
  | PPara cur ->
    (match cur with
     | [] ->
       (match b with
        | PPara cur0 -> (match cur0 with
                         | [] -> true
                         | _ :: _ -> false)
        | _ -> false)
     | _ :: _ -> false)
  | _ -> false

type entry = (string * pstate) * blocks

(** val trace :
    dtable -> bconfig -> string list -> pstate -> entry list * pstate **)

let rec trace t k ls st =
  match ls with
  | [] -> ([], st)
  | l :: rest ->
    let (bs, st') = step t k semantic_line_ix semantic_pos l st in
    let (tr, fin) = trace t k rest st' in ((((l, st), bs) :: tr), fin)

(** val rest_of : dtable -> bconfig -> entry list -> pstate -> blocks **)

let rest_of t k tr fin =
  app (flat_map snd tr) (finish t k semantic_pos fin)

type known = { k_rev : string list; k_trace : entry list; k_fin : pstate }

(** val known_of : dtable -> bconfig -> string -> known **)

let known_of t k s =
  let ls = split_lines s in
  let run = trace t k ls (PPara []) in
  { k_rev = (rev ls); k_trace = (fst run); k_fin = (snd run) }

(** val resync :
    dtable -> bconfig -> int -> int -> pstate -> blocks -> blocks -> entry
    list -> entry list -> string list -> pstate -> (entry list * pstate)
    option **)

let rec resync t k d n stc cand ref acc tr ls fin =
  match tr with
  | [] ->
    let run = trace t k ls stc in
    if blocks_eqb (app cand (rest_of t k (fst run) (snd run)))
         (app ref (rest_of t k tr fin))
    then Some ((rev_append acc (fst run)), (snd run))
    else None
  | e :: tr' ->
    let (p, bs) = e in
    let (_, st) = p in
    (match ls with
     | [] ->
       let run = trace t k ls stc in
       if blocks_eqb (app cand (rest_of t k (fst run) (snd run)))
            (app ref (rest_of t k tr fin))
       then Some ((rev_append acc (fst run)), (snd run))
       else None
     | l :: ls' ->
       if (&&) (same_state stc st) (( <= ) n d)
       then if blocks_eqb cand ref
            then Some ((rev_append acc tr), fin)
            else None
       else let (bs', stc') = step t k semantic_line_ix semantic_pos l stc in
            resync t k d (pred n) stc' (app cand bs') (app ref bs) (((l, stc),
              bs') :: acc) tr' ls' fin)

(** val walk :
    dtable -> bconfig -> int -> int -> entry list -> entry list -> string list
    -> pstate -> (entry list * pstate) option **)

let rec walk t k d n acc tr ls fin =
  match tr with
  | [] -> resync t k d n fin [] [] acc tr ls fin
  | e :: tr' ->
    let (p, bs) = e in
    let (l, st) = p in
    (match ls with
     | [] -> resync t k d n st [] [] acc tr ls fin
     | l' :: ls' ->
       if (=) l l'
       then walk t k d (pred n) (((l, st), bs) :: acc) tr' ls' fin
       else resync t k d n st [] [] acc tr ls fin)

(** val common_prefix : string list -> string list -> int **)

let rec common_prefix xs ys =
  match xs with
  | [] -> 0
  | x :: xs' ->
    (match ys with
     | [] -> 0
     | y :: ys' -> if (=) x y then Stdlib.succ (common_prefix xs' ys') else 0)

(** val fast_test : dtable -> bconfig -> known -> string -> known option **)

let fast_test t k kn t0 =
  let ls = split_lines t0 in
  let rls = rev ls in
  let n = length kn.k_trace in
  let d = if ( = ) (length ls) n then common_prefix kn.k_rev rls else 0 in
  (match walk t k d n [] kn.k_trace ls kn.k_fin with
   | Some p ->
     let (tr, fin) = p in Some { k_rev = rls; k_trace = tr; k_fin = fin }
   | None -> None)

(** val render_djot_irredundant : dtable -> bconfig -> blocks -> string **)

let render_djot_irredundant t k bs =
  let s = render_djot t k bs in
  shrink_by (fast_test t k) (String.length s) 0 (known_of t k s) s
