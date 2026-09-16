open Datatypes

(** val length : string -> nat **)

let rec length = (fun s ->
     let rec go n acc =
       if n = 0 then acc else go (n - 1) (Datatypes.S acc)
     in go (String.length s) Datatypes.O)


