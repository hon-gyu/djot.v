(* ai-disclosure: autonomous *)

(** * The reference for the extensions

   The files of [spec/] are the syntax reference for what this
   development adds to djot: what [djot/doc/syntax.md] is for djot, they
   are for the extensions.  Each is a djot document named after its
   extension.  A code block with the language [example] holds a source,
   a line with a single period, and the HTML the source renders to.

   The reference is read with the setting below of the same name: djot
   with that one extension on.  [SpecExamples.v] is written from the
   files at build time, one [Example] per example block, so an example
   that the parser does not render as the reference says fails the
   build. *)

From Stdlib Require Import String List.
From DjotV Require Import Ast Inline InlineTable Step Parser Document Profile Html.
Import ListNotations.
Local Open Scope string_scope.

(* djot's block settings, with the four extension settings given. *)
Local Definition block
  (list_interrupts setext keyed callouts : bool) : options :=
  Options djot_table list_interrupts setext true true true true true true true
    keyed callouts.

(* djot's block settings, over an inline table. *)
Local Definition inline (T : dtable) : options :=
  Options T false false true true true true true true true false false.

Definition wikilinks : options :=
  inline (DTable (with_wikilinks true djot_config) eq_refl).
Definition dollar_math : options :=
  inline (DTable (with_dollar_math true djot_config) eq_refl).
Definition custom_tags : options :=
  inline (DTable (with_inline_tags true djot_config) eq_refl).
Definition list_interruption : options := block true false false false.
Definition setext_headings : options := block false true false false.
Definition keyed_blocks : options := block false false true false.
Definition callouts : options := block false false false true.

(* By the name of the reference file. *)
Definition all : list (string * options) :=
  [ ("callouts", callouts); ("custom-tags", custom_tags);
    ("dollar-math", dollar_math); ("keyed-blocks", keyed_blocks);
    ("list-interruption", list_interruption);
    ("setext-headings", setext_headings); ("wikilinks", wikilinks) ].

(* What an example of the reference states. *)
Definition renders (o : options) (source html : string) : Prop :=
  convert_profile (profile_of o) source = html.
