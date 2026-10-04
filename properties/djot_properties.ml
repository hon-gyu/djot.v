(* ai-disclosure: ai-generated *)

module K = Djot.Kernel.Properties

type status = K.status =
  | Proved
  | Conditional of string
  | Broken of string * string
  | Conjectured
  | Unknown
  | Inapplicable of string

let status_name = function
  | Proved -> "proved"
  | Conditional _ -> "conditional"
  | Broken _ -> "broken"
  | Conjectured -> "conjectured"
  | Unknown -> "unknown"
  | Inapplicable _ -> "inapplicable"
;;

type t = K.property

let id (p : t) = p.p_id
let group (p : t) = p.p_group
let statement (p : t) = p.p_statement
let implication (p : t) = p.p_implication
let theorems (p : t) = p.p_theorems
let status (p : t) (profile : Djot.Profile.t) = p.p_status (profile :> Djot.Kernel.Profile.options)
let all = K.all
