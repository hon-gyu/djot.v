(* ai-disclosure: autonomous *)

(* Custom tag names (`.project/custom-tags.md`).  The baseline rows are
   djot's reading, checked against djot.js on 2026-10-03; they must keep
   passing in the djot profile, where names are off. *)
From Stdlib Require Import String List.
From DjotV Require Import Ast Strings Line Parser InlineTable.
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
  = ([P [S ":kbd"; Node NoPos [("class", "x")] (Span [S "a"])]],
     [P [S ":kbd"; mk (Link [S "a"] (Direct "u"))]],
     [P [S "a:kbd"; Node NoPos [("class", "x")] (Span [S "b"])]]).
Proof. vm_compute. reflexivity. Qed.

Example baseline_inline_not_a_name :
  (Djot ":kbd:[a]{.x}", Djot ":[a]{.x}", Djot ":kbd`x`")
  = ([P [mk (Symbol "kbd"); Node NoPos [("class", "x")] (Span [S "a"])]],
     [P [S ":"; Node NoPos [("class", "x")] (Span [S "a"])]],
     [P [S ":kbd"; mk (Verbatim "x")]]).
Proof. vm_compute. reflexivity. Qed.

Example baseline_div_word_is_a_class :
  Djot "::: details
x
:::" = [Node NoPos [("class", "details")] (Div [P [S "x"]])].
Proof. vm_compute. reflexivity. Qed.

Example baseline_two_words_is_not_an_opener :
  Djot "::: a b
x
:::" = [P [S "::: a b"; mk SoftBreak; S "x"; mk SoftBreak; S ":::"]].
Proof. vm_compute. reflexivity. Qed.
