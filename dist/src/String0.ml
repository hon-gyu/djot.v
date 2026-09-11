open Datatypes

(** val length : string -> nat **)

let rec length s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> O)
    (fun _ s' -> S (length s'))
    s


