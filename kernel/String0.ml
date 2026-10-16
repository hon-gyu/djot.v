open Datatypes

(** val compare : string -> string -> comparison **)

let rec compare = (fun a b -> let c = Stdlib.String.compare a b in
     if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt
     else Datatypes.Gt)

(** val get : int -> string -> char option **)

let rec get = (fun i s -> if i < String.length s then Some (String.get s i) else None)


