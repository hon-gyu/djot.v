open Datatypes

(** val compare : string -> string -> comparison **)

let rec compare = (fun a b -> let c = Stdlib.String.compare a b in
     if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt
     else Datatypes.Gt)

(** val get : int -> string -> char option **)

let rec get n s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c s' ->
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> Some c)
      (fun n' -> get n' s')
      n)
    s


