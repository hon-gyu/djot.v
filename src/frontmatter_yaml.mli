(* ai-disclosure: ai-generated *)

(** The YAML parser behind [~frontmatter], from the optional yaml package. *)

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
