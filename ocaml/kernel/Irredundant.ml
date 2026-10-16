open Ast
open AstEq
open Attributes
open Datatypes
open InlineTable
open List0
open ListDef
open Nat0
open PeanoNat
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

type cand = string * (int * int option)

(** val first_at :
    (cand -> 'a1 option) -> string -> int -> (cand * 'a1) option **)

let first_at f s i =
  let test = fun c -> match f c with
                      | Some b -> Some (c, b)
                      | None -> None in
  (match get i s with
   | Some c ->
     if (=) c bslash
     then test ((del i s), (i, None))
     else if (=) c lbrace
          then let rec go m j =
                 (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                   (fun _ -> None)
                   (fun m' ->
                   match match get j s with
                         | Some d ->
                           if (=) d rbrace
                           then test ((del i (del j s)), (i, (Some j)))
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
    (cand -> 'a1 option) -> string -> int -> int -> ((cand * 'a1) * int)
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
    (cand -> 'a1 option) -> int -> string -> ((cand * 'a1) * int) option **)

let next f k s =
  match first_from f s (sub (String.length s) k) k with
  | Some r -> Some r
  | None -> first_from f s (String.length s) 0

(** val shrink_by :
    ('a1 -> cand -> 'a1 option) -> int -> int -> 'a1 -> string -> string **)

let rec shrink_by test fuel k kn s =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> s)
    (fun f ->
    match next (test kn) k s with
    | Some p ->
      let (p0, i) = p in let (c, kn') = p0 in shrink_by test f i kn' (fst c)
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

(** val state_of : entry list -> pstate -> pstate **)

let state_of tr fin =
  match tr with
  | [] -> fin
  | e :: _ -> let (p, _) = e in let (_, st) = p in st

(** val rest_of : dtable -> bconfig -> entry list -> pstate -> blocks **)

let rest_of t k tr fin =
  app (flat_map snd tr) (finish t k semantic_pos fin)

type known = { k_lines : string list; k_nl : bool; k_trace : entry list;
               k_fin : pstate }

(** val ends_nl : string -> bool **)

let ends_nl s =
  match get (pred (String.length s)) s with
  | Some c -> (=) c '\n'
  | None -> false

(** val known_of : dtable -> bconfig -> string -> known **)

let known_of t k s =
  let ls = split_lines s in
  let run = trace t k ls (PPara []) in
  { k_lines = ls; k_nl = (ends_nl s); k_trace = (fst run); k_fin = (snd run) }

(** val resync :
    dtable -> bconfig -> int -> int -> pstate -> blocks -> blocks -> entry
    list -> entry list -> string list -> pstate -> (entry list * pstate)
    option **)

let rec resync t k d n stc cand0 ref acc tr ls fin =
  match tr with
  | [] ->
    let run = trace t k ls stc in
    if blocks_eqb (app cand0 (rest_of t k (fst run) (snd run)))
         (app ref (rest_of t k tr fin))
    then Some ((rev_append acc (fst run)), (snd run))
    else None
  | e :: tr' ->
    let (p, bs) = e in
    let (_, st) = p in
    (match ls with
     | [] ->
       let run = trace t k ls stc in
       if blocks_eqb (app cand0 (rest_of t k (fst run) (snd run)))
            (app ref (rest_of t k tr fin))
       then Some ((rev_append acc (fst run)), (snd run))
       else None
     | l :: ls' ->
       if (&&) (same_state stc st) (( <= ) n d)
       then if blocks_eqb cand0 ref
            then Some ((rev_append acc tr), fin)
            else None
       else let (bs', stc') = step t k semantic_line_ix semantic_pos l stc in
            resync t k d (pred n) stc' (app cand0 bs') (app ref bs) (((l,
              stc), bs') :: acc) tr' ls' fin)

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

(** val walk_test : dtable -> bconfig -> known -> string -> known option **)

let walk_test t k kn t0 =
  let ls = split_lines t0 in
  let n = length kn.k_trace in
  let d =
    if ( = ) (length ls) n then common_prefix (rev kn.k_lines) (rev ls) else 0
  in
  (match walk t k d n [] kn.k_trace ls kn.k_fin with
   | Some p ->
     let (tr, fin) = p in
     Some { k_lines = ls; k_nl = (ends_nl t0); k_trace = tr; k_fin = fin }
   | None -> None)

(** val locate : int -> string list -> (int * int) option **)

let rec locate i = function
| [] -> None
| l :: rest ->
  if ( < ) i (String.length l)
  then Some (0, i)
  else if ( = ) i (String.length l)
       then None
       else (match locate (sub i (Stdlib.succ (String.length l))) rest with
             | Some p -> let (a, c) = p in Some ((Stdlib.succ a), c)
             | None -> None)

(** val replace : int -> (string -> string) -> string list -> string list **)

let rec replace a f = function
| [] -> []
| l :: rest ->
  ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
     (fun _ -> (f l) :: rest)
     (fun a' -> l :: (replace a' f rest))
     a)

(** val del_lines :
    (int * int option) -> string list -> ((string list * int) * int) option **)

let del_lines d ls =
  let (i, o) = d in
  (match o with
   | Some j ->
     (match locate j ls with
      | Some p ->
        let (b, cj) = p in
        let ls1 = replace b (del cj) ls in
        (match locate i ls1 with
         | Some p0 ->
           let (a, ci) = p0 in
           Some (((replace a (del ci) ls1), (Nat.min a b)), (Nat.max a b))
         | None -> None)
      | None -> None)
   | None ->
     (match locate i ls with
      | Some p -> let (a, c) = p in Some (((replace a (del c) ls), a), a)
      | None -> None))

(** val ends_ok : string list -> bool -> bool **)

let ends_ok ls e =
  match ls with
  | [] -> negb e
  | _ :: _ -> (||) e (nonempty_str (last ls ""))

(** val fast_test : dtable -> bconfig -> known -> cand -> known option **)

let fast_test t k kn c =
  match del_lines (snd c) kn.k_lines with
  | Some p ->
    let (p0, hi) = p in
    let (ls, lo) = p0 in
    if ends_ok ls kn.k_nl
    then let tr = skipn lo kn.k_trace in
         let n = sub (length kn.k_trace) lo in
         let d = sub n (sub (Stdlib.succ hi) lo) in
         (match resync t k d n (state_of tr kn.k_fin) [] []
                  (rev (firstn lo kn.k_trace)) tr (skipn lo ls) kn.k_fin with
          | Some p1 ->
            let (tr', fin) = p1 in
            Some { k_lines = ls; k_nl = kn.k_nl; k_trace = tr'; k_fin = fin }
          | None -> None)
    else walk_test t k kn (fst c)
  | None -> walk_test t k kn (fst c)

(** val render_djot_irredundant : dtable -> bconfig -> blocks -> string **)

let render_djot_irredundant t k bs =
  let s = render_djot t k bs in
  shrink_by (fast_test t k) (String.length s) 0 (known_of t k s) s
