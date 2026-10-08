open Datatypes
open List0
open ListDef
open Precedence

type gparse = ((matching * int list) * int) * token list

(** val kmem : key -> key list -> bool **)

let kmem k ks =
  existsb (key_eq k) ks

(** val kis : key -> key option -> bool **)

let kis k = function
| Some k' -> key_eq k k'
| None -> false

(** val after : matching -> int list -> gparse list -> gparse list **)

let after m os rs =
  map (fun pat ->
    let (y, r) = pat in
    let (y0, j) = y in
    let (m', os') = y0 in ((((app m m'), (app os os')), j), r)) rs

(** val seq :
    int -> token list -> int -> token list -> key list -> key option -> key
    option -> key list -> gparse list **)

let rec seq fuel ts i rest live forb prev barred =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> [])
    (fun fuel' ->
    let r0 = ((([], []), i), rest) in
    (match rest with
     | [] -> r0 :: []
     | t :: more ->
       let text = seq fuel' ts (Stdlib.succ i) more live forb None barred in
       let opener = fun k ->
         let r3 =
           if kis k forb
           then []
           else after [] (i :: [])
                  (seq fuel' ts (Stdlib.succ i) more (k :: live) forb (Some k)
                    barred)
         in
         let closer_ahead = existsb (fun u -> kis k (closes_as u)) more in
         let pairs =
           if negb closer_ahead
           then []
           else flat_map (fun pat ->
                  let (y, r1) = pat in
                  let (y0, e) = y in
                  let (m1, os1) = y0 in
                  (match r1 with
                   | [] -> []
                   | tc :: r2 ->
                     (match closes_as tc with
                      | Some k' ->
                        if (&&) (key_eq k k')
                             ((||) (negb (needs_content k))
                               (( < ) (Stdlib.succ i) e))
                        then let m = (i, e) :: m1 in
                             let os = i :: os1 in
                             (match tc with
                              | TClose b ->
                                (match region_end ts e b with
                                 | Some z ->
                                   after m os
                                     (seq fuel' ts (Stdlib.succ z)
                                       (skipn (Stdlib.succ z) ts) live forb
                                       None barred)
                                 | None ->
                                   if b
                                   then filter (fun pat0 ->
                                          let (_, r) = pat0 in
                                          (match r with
                                           | [] -> true
                                           | _ :: _ -> false))
                                          (after m os
                                            (seq fuel' ts (Stdlib.succ e) r2
                                              [] forb None (app live barred)))
                                   else (((m, os), (length ts)), []) :: [])
                              | _ ->
                                after m os
                                  (seq fuel' ts (Stdlib.succ e) r2 live forb
                                    None barred))
                        else []
                      | None -> [])))
                  (seq fuel' ts (Stdlib.succ i) more (k :: live) (Some k)
                    (Some k) barred)
         in
         app r3 pairs
       in
       let as_opener = match opens_as t with
                       | Some k -> opener k
                       | None -> text
       in
       let ends =
         match forb with
         | Some f ->
           (match closes_as t with
            | Some k ->
              (&&) (key_eq f k) (negb ((&&) (needs_content k) (kis k prev)))
            | None -> false)
         | None -> false
       in
       app (if ends then r0 :: [] else [])
         (match closes_as t with
          | Some k ->
            if kmem k live
            then if (&&) (needs_content k) (kis k prev) then as_opener else []
            else if kmem k barred then text else as_opener
          | None -> (match opens_as t with
                     | Some k -> opener k
                     | None -> text))))
    fuel

(** val grammar_read : token list -> (matching * int list) list **)

let grammar_read ts =
  flat_map (fun pat ->
    let (y, r) = pat in
    let (y0, _) = y in (match r with
                        | [] -> y0 :: []
                        | _ :: _ -> []))
    (seq (Stdlib.succ (Stdlib.succ (length ts))) ts 0 ts [] None None [])
