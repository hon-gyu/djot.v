(* ai-disclosure: ai-generated *)

(* Where the site points into the repository. *)

let repo = "https://github.com/hon-gyu/djot.v"
let tree = Printf.sprintf "%s/tree/%s" repo Versions.commit

(* A theorem's statement in the source at the built commit, if a theorem
   of that name exists. *)
let theorem name =
  Option.map
    (fun (file, line) ->
      Printf.sprintf "%s/blob/%s/%s#L%d" repo Versions.commit file line)
    (List.assoc_opt name Theorems.all)
;;
