open Datatypes

(** val compare : string -> string -> comparison **)

let rec compare = (fun a b -> let c = Stdlib.String.compare a b in
     if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt
     else Datatypes.Gt)


