(* ai-disclosure: ai-generated *)

(*
Setext headings, pinned
=======================

The second block setting: may a run of one character, alone on a line,
turn the paragraph above it into a heading?  djot answers no (it has no
setext headings at all), and `setext_bconfig` answers `=` at any length
for level 1, `-` at two or more for level 2.  The argument is in
`.project/extension-decisions.md` under `E3`.

Every line here was measured.
*)

From Stdlib Require Import String List Ascii.
From DjotV Require Import Ast Line Inline Parser Document Render Roundtrip.
Import ListNotations.
Open Scope string_scope.

Local Notation Djot := (@parse_blocks _ djot_bconfig _ _).
Local Notation Setext := (@parse_blocks _ setext_bconfig _ _).

(*
The baseline
------------

djot has no underline rule, so both lines are prose.  `---` is worth
pinning on its own: it is not even inert there, since smart punctuation
reads it as an em dash.
*)

Example djot_reads_equals_as_prose :
  Djot "a
===" = [mk (Para [mk (Str "a"); mk SoftBreak; mk (Str "===")])].
Proof. vm_compute. reflexivity. Qed.

Example djot_reads_dashes_as_an_em_dash :
  Djot "a
---" = [mk (Para [mk (Str "a"); mk SoftBreak; mk (Str emdash)])].
Proof. vm_compute. reflexivity. Qed.

(*
The two levels
--------------
*)

Example setext_level_one :
  Setext "a
===" = [mk (Heading 1 [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example setext_level_two :
  Setext "a
---" = [mk (Heading 2 [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

(* The whole paragraph becomes the heading, not its last line. *)
Example setext_takes_every_line :
  Setext "a b
c
===" = [mk (Heading 1 [mk (Str "a b"); mk SoftBreak; mk (Str "c")])].
Proof. vm_compute. reflexivity. Qed.

(*
Why `-` needs two
-----------------

A lone `-` is a bullet marker -- `classify "-"` is `KList`, not text --
so admitting it at length one would put one line under two settings at
once, and which of them won would depend on the order `step` tests them
in.  Excluding it is not a style choice, it is what keeps the two
independent.
*)

Example a_single_dash_is_not_an_underline :
  Setext "a
-" = [mk (Para [mk (Str "a"); mk SoftBreak; mk (Str "-")])].
Proof. vm_compute. reflexivity. Qed.

Example two_dashes_are :
  Setext "a
--" = [mk (Heading 2 [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

(*
Only an open paragraph underlines
---------------------------------

The test runs in the paragraph branch of `step` and nowhere else, so a
line that has no paragraph above it is classified exactly as it always
was.  That is what keeps a thematic break a thematic break.
*)

Example an_underline_with_nothing_above_it_is_a_paragraph :
  Setext "
===" = [mk (Para [mk (Str "===")])].
Proof. vm_compute. reflexivity. Qed.

Example a_thematic_break_survives :
  Setext "
---" = Djot "
---".
Proof. vm_compute. reflexivity. Qed.

(* And, being stated over the open paragraph rather than over the
   document, it works wherever a paragraph can be -- which is the same
   property that keeps `list_uniformity` true at every setting. *)
Example setext_inside_a_quote :
  Setext "> a
> ===" = [mk (BlockQuote [mk (Heading 1 [mk (Str "a")])])].
Proof. vm_compute. reflexivity. Qed.

(*
What the canonical view says
----------------------------

`para_ok` asks that no line of a paragraph is one a setting would cut it
at, and `bcuts` is that one question for both settings.  It costs the
roundtrip nothing for the reason the sublist setting does not: `cline`
already escapes both underline characters, so a canonical paragraph
never contains a line that could be one.
*)

Example para_ok_rejects_a_bare_underline :
  @para_ok _ setext_bconfig ["a"; "==="] = false.
Proof. vm_compute. reflexivity. Qed.

Example para_ok_takes_the_escaped_one :
  @para_ok _ setext_bconfig ["a"; "\=\=\="] = true.
Proof. vm_compute. reflexivity. Qed.

Example the_renderer_writes_the_escaped_one :
  map (@ci_line _) (map cline ["a"; "==="]) = ["a"; "\=\=\="].
Proof. vm_compute. reflexivity. Qed.

Theorem setext_roundtrip_blocks :
  forall cbs,
    @cblocks_ok _ setext_bconfig cbs = true ->
    @parse_blocks _ setext_bconfig _ _ (render_djot (blocks_of_cblocks cbs))
    = blocks_of_cblocks cbs.
Proof. exact (@roundtrip_blocks _ setext_bconfig). Qed.
