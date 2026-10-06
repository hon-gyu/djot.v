(* ai-disclosure: ai-generated *)

let available = true

let parse (s : string) =
  match Yaml.of_string s with
  | Ok v -> Some v
  | Error _ -> None
;;

(* The emitter writes into a buffer of fixed size. *)
let print v =
  let rec go len =
    match Yaml.to_string ~len v with
    | Ok s -> Some s
    | Error _ when len < 1 lsl 28 -> go (len * 16)
    | Error _ -> None
  in
  go (1 lsl 16)
;;
