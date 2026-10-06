(* ai-disclosure: ai-generated *)

let available = true

let parse (s : string) =
  match Yaml.of_string s with
  | Ok v -> Some v
  | Error _ -> None
;;
