(* ai-disclosure: ai-generated *)

(** The properties proved of the parser, and which of them a profile keeps.

    Each property names the theorems behind it in the Rocq development. Where a theorem
    has a hypothesis about the profile, {!val-status} evaluates it with the checks of
    {!Djot.Kernel.ProfileChecks}, each of which is proved there to agree with that
    hypothesis. *)

type status =
  | Proved (** The theorems hold for the profile. *)
  | Proved_with_caveat of string
  (** They hold, with a side condition on the document. *)
  | Broken of
      { reason : string
      ; example : string
      }
  (** The property fails for the profile; [example] is a source that shows it. *)
  | Expected (** Believed to hold; not proved for this profile. *)
  | Unknown (** No claim. *)
  | Not_applicable of string (** The construct the property is about is off. *)

type t

(** A stable name, e.g. ["hard-wrap-paragraph"]. *)
val id : t -> string

(** The design goal the property belongs to, e.g. ["Safe hard-wrapping"]. *)
val group : t -> string

val statement : t -> string

(** What the property gives a writer or a tool. *)
val implication : t -> string

(** The theorems, each with its file under [theories/]. *)
val theorems : t -> (string * string) list

val status : t -> Djot.Profile.t -> status

(** Every property, grouped as {!group} names them. *)
val all : t list
