(* ai-disclosure: ai-generated *)

(** The properties proved of the parser, and which of them a profile keeps.

    The list is {!Djot.Kernel.Properties}, extracted from [theories/Properties.v]. There
    each property has, beside the words given here, its statement for a profile and a
    proof of that statement wherever {!val-status} is {!Proved} or {!Conditional}. *)

type status = Djot.Kernel.Properties.status =
  | Proved (** The theorems hold for the profile. *)
  | Conditional of string (** They hold, under the stated condition on the document. *)
  | Broken of string * string
  (** [Broken (reason, example)]: the property fails for the profile; [example] is a
      source that shows it. *)
  | Conjectured (** Believed to hold; not proved for this profile. *)
  | Unknown (** No claim. *)
  | Inapplicable of string (** The construct the property is about is off. *)

(** The constructor's name in lower case: ["proved"], ["conditional"]. *)
val status_name : status -> string

type t

(** A stable name, e.g. ["hard-wrap-paragraph"]. *)
val id : t -> string

(** The design goal the property belongs to, e.g. ["Safe hard-wrapping"]. *)
val group : t -> string

val statement : t -> string

(** What the property gives a writer or a tool. *)
val implication : t -> string

(** The names of the theorems in the Rocq development. *)
val theorems : t -> string list

val status : t -> Djot.Profile.t -> status

(** Every property, grouped as {!group} names them. *)
val all : t list
