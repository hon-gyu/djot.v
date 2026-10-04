(* ai-disclosure: ai-generated *)

(* How a status is named on the site: one word, which is also its CSS
   class. *)
let word : Djot_properties.status -> string = function
  | Proved -> "proved"
  | Proved_with_caveat _ -> "conditional"
  | Broken _ -> "broken"
  | Expected -> "conjectured"
  | Unknown -> "unknown"
  | Not_applicable _ -> "inapplicable"
;;
