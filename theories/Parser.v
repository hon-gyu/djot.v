(* ai-disclosure: ai-generated *)

(** * Parser interface

   The block parser under one name: the six files below, re-exported.

   | file               | what                                        |
   | ------------------ | ------------------------------------------- |
   | `Inline.v`         | the inline layer the block parser sits on: `para_inlines`, `inline_lines`, and the canonical `cinline` view |
   | `Marker.v`         | marker numerals, candidate styles, narrowing |
   | `Step.v`           | `pstate`, `step`, `finish`, `parse_lines`, and the shift/pad metatheory |
   | `Uniformity.v`     | fold equations, quotes, divs, locality       |
   | `ListUniformity.v` | lists                                        |
   | `OrderedList.v`    | ordered lists at the canonical rendering     |

   Concrete regressions are in `dev/ParserExamples.v`, which nothing
   requires. *)

From DjotV Require Export Inline Marker Step Uniformity ListUniformity OrderedList.
