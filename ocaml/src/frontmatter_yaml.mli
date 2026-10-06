(* ai-disclosure: ai-generated *)

(** The YAML parser and printer behind frontmatter, from the optional yaml package.

    A value is [Djot.Frontmatter.value], written out here because that module comes
    after this one. *)

(** Whether the package was built with yaml. *)
val available : bool

(** The value of a YAML text, [None] when it does not parse. Always [None] when
    {!available} is [false]. *)
val parse
  :  string
  -> ([ `Null
      | `Bool of bool
      | `Float of float
      | `String of string
      | `A of 'v list
      | `O of (string * 'v) list
      ]
      as
      'v)
       option

(** A YAML text of a value, [None] when the package cannot write one. Always [None] when
    {!available} is [false]. *)
val print
  :  ([ `Null
      | `Bool of bool
      | `Float of float
      | `String of string
      | `A of 'v list
      | `O of (string * 'v) list
      ]
      as
      'v)
  -> string option
