open Datatypes
open InlineTable
open List0
open ListDef
open Nat0
open Precedence

(** val kmem : key -> key list -> bool **)

let kmem k ks =
  existsb (key_eq k) ks

(** val kis : key -> key option -> bool **)

let kis k = function
| Some k' -> key_eq k k'
| None -> false

(** val closer_from : dtable -> string -> key -> int -> bool **)

let closer_from t s k p =
  existsb (fun q ->
    match tok_at t s q with
    | Some p0 -> let (u, _) = p0 in kis k (closes_as u)
    | None -> false) (seq p (sub (String.length s) p))

type gparse = (matching * int list) * int

(** val after : matching -> int list -> gparse list -> gparse list **)

let after m os rs =
  map (fun pat ->
    let (y, j) = pat in let (m', os') = y in (((app m m'), (app os os')), j))
    rs

(** val level :
    dtable -> int -> string -> int -> key list -> key option -> key option ->
    key list -> gparse list **)

let rec level t fuel s p live forb prev barred =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> [])
    (fun fuel' ->
    let r0 = (([], []), p) in
    (match tok_at t s p with
     | Some p0 ->
       let (t0, l) = p0 in
       let q = ( + ) p l in
       let text = level t fuel' s q live forb None barred in
       let opener = fun k ->
         let r3 =
           if kis k forb
           then []
           else after [] (p :: [])
                  (level t fuel' s q (k :: live) forb (Some k) barred)
         in
         let pairs =
           if negb (closer_from t s k q)
           then []
           else flat_map (fun pat ->
                  let (y, e) = pat in
                  let (m1, os1) = y in
                  (match tok_at t s e with
                   | Some p1 ->
                     let (tc, le) = p1 in
                     (match closes_as tc with
                      | Some k' ->
                        if (&&) (key_eq k k')
                             ((||) (negb (needs_content k)) (( < ) q e))
                        then let m = (p, e) :: m1 in
                             let os = p :: os1 in
                             (match tc with
                              | TText _ ->
                                after m os
                                  (level t fuel' s (( + ) e le) live forb None
                                    barred)
                              | TBreak ->
                                after m os
                                  (level t fuel' s (( + ) e le) live forb None
                                    barred)
                              | TDelim (_, _, _, _) ->
                                after m os
                                  (level t fuel' s (( + ) e le) live forb None
                                    barred)
                              | TOpen ->
                                after m os
                                  (level t fuel' s (( + ) e le) live forb None
                                    barred)
                              | TClose b ->
                                (match region_end s e b with
                                 | Some z ->
                                   after m os
                                     (level t fuel' s (Stdlib.succ z) live
                                       forb None barred)
                                 | None ->
                                   if b
                                   then filter (fun pat0 ->
                                          let (_, r) = pat0 in
                                          ( = ) r (String.length s))
                                          (after m os
                                            (level t fuel' s (( + ) e le) []
                                              forb None (app live barred)))
                                   else ((m, os), (String.length s)) :: [])
                              | TEsc _ ->
                                after m os
                                  (level t fuel' s (( + ) e le) live forb None
                                    barred)
                              | TEscWs _ ->
                                after m os
                                  (level t fuel' s (( + ) e le) live forb None
                                    barred)
                              | THard _ ->
                                after m os
                                  (level t fuel' s (( + ) e le) live forb None
                                    barred)
                              | TVerb (_, _, _, _, _) ->
                                after m os
                                  (level t fuel' s (( + ) e le) live forb None
                                    barred)
                              | TDollars _ ->
                                after m os
                                  (level t fuel' s (( + ) e le) live forb None
                                    barred)
                              | TAuto (_, _) ->
                                after m os
                                  (level t fuel' s (( + ) e le) live forb None
                                    barred))
                        else []
                      | None -> [])
                   | None -> []))
                  (level t fuel' s q (k :: live) (Some k) (Some k) barred)
         in
         app r3 pairs
       in
       let as_opener =
         match opens_as t0 with
         | Some k -> opener k
         | None -> text
       in
       let ends =
         match forb with
         | Some f ->
           (match closes_as t0 with
            | Some k ->
              (&&) (key_eq f k) (negb ((&&) (needs_content k) (kis k prev)))
            | None -> false)
         | None -> false
       in
       app (if ends then r0 :: [] else [])
         (match closes_as t0 with
          | Some k ->
            if kmem k live
            then if (&&) (needs_content k) (kis k prev) then as_opener else []
            else if kmem k barred then text else as_opener
          | None -> (match opens_as t0 with
                     | Some k -> opener k
                     | None -> text))
     | None -> r0 :: []))
    fuel

(** val grammar_read : dtable -> string -> (matching * int list) list **)

let grammar_read t s =
  flat_map (fun pat ->
    let (y, r) = pat in if ( = ) r (String.length s) then y :: [] else [])
    (level t (Stdlib.succ (Stdlib.succ (String.length s))) s 0 [] None None
      [])
