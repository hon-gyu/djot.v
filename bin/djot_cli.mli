(* ai-disclosure: ai-generated *)

(** The arguments the subcommands share. *)

(** The input file and how to read it: [FILE], [--from], [--frontmatter], [--time],
    and the syntax options. *)
val input : Common.input Cmdliner.Term.t

(** [--locs]. *)
val locs : bool Cmdliner.Term.t

(** The intro of the manual section the syntax options are listed under. A command
    taking {!input} appends it to its manual. *)
val syntax_man : Cmdliner.Manpage.block list
