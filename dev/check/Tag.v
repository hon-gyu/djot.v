(* ai-disclosure: autonomous *)

(* Custom tag names (`.project/custom-tags.md`).  The baseline rows are
   djot's reading, checked against djot.js on 2026-10-03; they must keep
   passing in the djot profile, where names are off. *)
From Stdlib Require Import String List.
From DjotV Require Import Ast Strings Line Parser InlineTable Step Profile Render
  Roundtrip Reparse.
From DjotVDev.check Require Import Located.
Import ListNotations.
Open Scope string_scope.

Local Notation Djot := (@parse_blocks _ djot_bconfig _ _).
Local Notation S := (fun s => mk (Str s)).
Local Notation P := (fun xs => mk (Para xs)).

(*
Baseline
========
*)

Example baseline_inline_alone :
  (Djot ":kbd[Ctrl+C]", Djot ":kbd[a", Djot "[a]{:kbd}", Djot "[a]{kbd}")
  = ([P [S ":kbd[Ctrl+C]"]], [P [S ":kbd[a"]],
     [P [S "[a]{:kbd}"]], [P [S "[a]{kbd}"]]).
Proof. vm_compute. reflexivity. Qed.

Example baseline_inline_then_bracket :
  (Djot ":kbd[a]{.x}", Djot ":kbd[a](u)", Djot "a:kbd[b]{.x}")
  = ([P [S ":kbd"; Node NoPos [("class", "x")] (Span "" [S "a"])]],
     [P [S ":kbd"; mk (Link [S "a"] (Direct "u"))]],
     [P [S "a:kbd"; Node NoPos [("class", "x")] (Span "" [S "b"])]]).
Proof. vm_compute. reflexivity. Qed.

Example baseline_inline_not_a_name :
  (Djot ":kbd:[a]{.x}", Djot ":[a]{.x}", Djot ":kbd`x`")
  = ([P [mk (Symbol "kbd"); Node NoPos [("class", "x")] (Span "" [S "a"])]],
     [P [S ":"; Node NoPos [("class", "x")] (Span "" [S "a"])]],
     [P [S ":kbd"; mk (Verbatim "x")]]).
Proof. vm_compute. reflexivity. Qed.

Example baseline_div_word_is_a_class :
  Djot "::: details
x
:::" = [Node NoPos [("class", "details")] (Div "" [P [S "x"]])].
Proof. vm_compute. reflexivity. Qed.

Example baseline_two_words_is_not_an_opener :
  Djot "::: a b
x
:::" = [P [S "::: a b"; mk SoftBreak; S "x"; mk SoftBreak; S ":::"]].
Proof. vm_compute. reflexivity. Qed.

(*
Block names
===========
*)

(* Names are a mode, off in both named profiles. *)
Example names_off_in_named_profiles :
  (dc_tags (@cfg (profile_inline djot_profile)),
   @bdiv_names (profile_block djot_profile),
   dc_tags (@cfg (profile_inline markdown_like_profile)),
   @bdiv_names (profile_block markdown_like_profile))
  = (false, false, false, false).
Proof. reflexivity. Qed.

Local Definition tags_profile : profile := with_tags true djot_profile.
Local Notation Named := (parse_profile_blocks tags_profile).

Example div_word_is_a_name :
  Named "::: details
x
:::" = [mk (Div "details" [P [S "x"]])].
Proof. vm_compute. reflexivity. Qed.

(* `div` is a name like any other, not a second spelling of `:::`. *)
Example div_named_div_is_not_unnamed :
  (Named "::: div
x
:::", Named ":::
x
:::")
  = ([mk (Div "div" [P [S "x"]])], [mk (Div "" [P [S "x"]])]).
Proof. vm_compute. reflexivity. Qed.

(* A pending class and the name are separate fields, so neither
   replaces the other. *)
Example div_name_beside_a_class :
  Named "{.a}
::: b
y
:::" = [Node NoPos [("class", "a")] (Div "b" [P [S "y"]])].
Proof. vm_compute. reflexivity. Qed.

Example div_name_still_one_word :
  Named "::: a b
x
:::" = [P [S "::: a b"; mk SoftBreak; S "x"; mk SoftBreak; S ":::"]].
Proof. vm_compute. reflexivity. Qed.

(*
Inline names
============

Every baseline row with names on.  The first two move; the rest are
where a colon and a bracket meet without making a name.
*)

Local Notation T := (fun n xs => mk (Span n xs)).

Example tagged_inline_rows :
  (Named ":kbd[Ctrl+C]", Named ":kbd[a]{.x}")
  = ([P [T "kbd" [S "Ctrl+C"]]],
     [P [Node NoPos [("class", "x")] (Span "kbd" [S "a"])]]).
Proof. vm_compute. reflexivity. Qed.

(* Right after a letter, digit or colon, `:name[` is djot's reading. *)
Example tagged_not_after_a_word :
  (Named "a:kbd[b]{.x}", Named "note:see[this](url)", Named "std::vector[0]",
   Named "12:30[x]", Named "(:kbd[a]) _:kbd[b]_")
  = ([P [S "a:kbd"; Node NoPos [("class", "x")] (Span "" [S "b"])]],
     [P [S "note:see"; mk (Link [S "this"] (Direct "url"))]],
     [P [S "std::vector[0]"]],
     [P [S "12:30[x]"]],
     [P [S "("; T "kbd" [S "a"]; S ") "; mk (Emph [T "kbd" [S "b"]])]]).
Proof. vm_compute. reflexivity. Qed.

(* The rule reads the pending text, which a symbol leaves empty. *)
Example tagged_after_a_symbol :
  Named ":a::b[c]" = [P [mk (Symbol "a"); T "b" [S "c"]]].
Proof. vm_compute. reflexivity. Qed.

(* `]` closes a named bracket at once, so what follows is not a
   destination or a label. *)
Example tagged_close_is_immediate :
  (Named ":kbd[a](u)", Named ":kbd[a][r]")
  = ([P [T "kbd" [S "a"]; S "(u)"]], [P [T "kbd" [S "a"]; S "[r]"]]).
Proof. vm_compute. reflexivity. Qed.

Example tagged_not_a_name :
  (Named ":kbd:[a]{.x}", Named ":[a]{.x}", Named ":kbd`x`", Named "\:kbd[a]")
  = ([P [mk (Symbol "kbd"); Node NoPos [("class", "x")] (Span "" [S "a"])]],
     [P [S ":"; Node NoPos [("class", "x")] (Span "" [S "a"])]],
     [P [S ":kbd"; mk (Verbatim "x")]],
     [P [S ":kbd[a]"]]).
Proof. vm_compute. reflexivity. Qed.

(* An unclosed name is its text, and so is one whose `]` an inner
   bracket takes, as djot's own brackets do. *)
Example tagged_decay :
  (Named ":kbd[a", Named ":kbd[x [a] y]", Named "[a]{:kbd}")
  = ([P [S ":kbd[a"]], [P [S ":kbd[x [a] y]"]], [P [S "[a]{:kbd}"]]).
Proof. vm_compute. reflexivity. Qed.

Example tagged_nesting :
  (Named ":kbd[]", Named ":a[:b[c]]", Named ":kbd[[a](u)]", Named "[:kbd[a]](u)")
  = ([P [T "kbd" []]],
     [P [T "a" [T "b" [S "c"]]]],
     [P [T "kbd" [mk (Link [S "a"] (Direct "u"))]]],
     [P [mk (Link [T "kbd" [S "a"]] (Direct "u"))]]).
Proof. vm_compute. reflexivity. Qed.

(* A named bracket is a bracket to the delimiters: a closer inside it
   abandons an opener outside, and the reverse. *)
Example tagged_with_delimiters :
  (Named ":kbd[_a]_", Named "_:kbd[a_]")
  = ([P [T "kbd" [S "_a"]; S "_"]],
     [P [mk (Emph [S ":kbd[a"]); S "]"]]).
Proof. vm_compute. reflexivity. Qed.

(* A named bracket is never taken back for a note or a wikilink. *)
Example tagged_not_a_note :
  Named ":kbd[^x]" = [P [T "kbd" [S "^x"]]].
Proof. vm_compute. reflexivity. Qed.

(*
HTML
====
*)

Local Notation Html := (convert_profile tags_profile).

Example html_names :
  (Html ":kbd[Ctrl]", Html "::: details
x
:::")
  = ("<p><kbd>Ctrl</kbd></p>
", "<details>
<p>x</p>
</details>
").
Proof. vm_compute. reflexivity. Qed.

(* Raw-text and void elements, and names HTML does not spell, keep the
   default element. *)
Example html_fallbacks :
  (Html ":script[alert(1)]", Html ":br[x]", Html ":a_b[x]")
  = ("<p><span data-tag=""script"">alert(1)</span></p>
",
     "<p><span data-tag=""br"">x</span></p>
",
     "<p><span data-tag=""a_b"">x</span></p>
").
Proof. vm_compute. reflexivity. Qed.

(*
Source ranges
=============

A named span runs from its colon to its `]`.
*)

Definition tag_ranges (s : string) : list (nat * nat) :=
  inline_walk 40 (line_table s)
    (first_para 20 (@parse_blocks_located (profile_inline tags_profile)
                      (profile_block tags_profile) s)).

Example r_tag : tag_ranges "p :kbd[a] q" = [(0, 2); (2, 9); (7, 8); (9, 11)].
Proof. vm_compute. reflexivity. Qed.

Example r_tag_attr : tag_ranges ":kbd[a]{.c} x" = [(0, 7); (5, 6); (11, 13)].
Proof. vm_compute. reflexivity. Qed.

(*
Rendering
=========

With names on, a fence's word reads back as a name, so an unnamed div's
class stays on the attribute line.
*)

Local Notation Render :=
  (@render_djot (profile_inline tags_profile) (profile_block tags_profile)).

Example render_class_off_the_fence :
  (Render (Named "{.warn}
:::
body
:::"), Named (Render (Named "{.warn}
:::
body
:::")))
  = ("{.warn}
:::
body
:::", [Node NoPos [("class", "warn")] (Div "" [P [S "body"]])]).
Proof. vm_compute. reflexivity. Qed.

(*
The roundtrip, at this profile
==============================
*)

Theorem tag_roundtrip_blocks :
  forall cbs,
    @cblocks_ok (profile_inline tags_profile) (profile_block tags_profile) cbs = true ->
    parse_profile_blocks tags_profile
      (@render_djot (profile_inline tags_profile) (profile_block tags_profile)
         (blocks_of_cblocks cbs))
    = blocks_of_cblocks cbs.
Proof. exact (@roundtrip_blocks (profile_inline tags_profile) (profile_block tags_profile)). Qed.
