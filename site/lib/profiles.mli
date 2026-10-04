(* ai-disclosure: ai-generated *)

(** A profile as a short string, for a URL: what differs from djot, as
    space-separated [name=value] words. A switch is [tables=off]; a delimiter is
    [strong=**:bare]. The empty string is djot. *)

val presets : (string * Djot.Profile.t) list

(** The preset equal to the profile, if any. *)
val preset : Djot.Profile.t -> string option

val to_string : Djot.Profile.t -> string
val of_string : string -> (Djot.Profile.t, string) result

(** A delimiter's spelling as [of_string] reads it: the run, then the syntax. *)
val spelling : Djot.Profile.Delimiter.t -> Djot.Profile.t -> string * string

(** [respell d run syntax p] sets one delimiter from the two strings of {!spelling}. *)
val respell
  :  Djot.Profile.Delimiter.t
  -> string
  -> string
  -> Djot.Profile.t
  -> (Djot.Profile.t, string) result
