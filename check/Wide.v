(* ai-disclosure: autonomous *)

(*
The wide table, pinned
======================

What the delimiter family does when a row is *two characters* wide.
Every line here was measured, not predicted; between them they settle the
sub-questions [[extension-decisions]] left open about doubled strong
emphasis.

**This file does not compile against the ordinary build.**  It asks for
`theories/Inline.v`'s `config` to be

```coq
Definition config : dconfig :=
  DConfig (fun k => match k with
                    | DEmph => "*"%char | DStrong => "_"%char
                    | _ => djot_dchar k end)
          (fun k => match k with DStrong => 2 | _ => 1 end)
          djot_dsyntax.
```

with `Inline.v`'s own examples truncated -- they spell djot's `_a_` and
are about djot.  Then:

```
dune build && rocq c -R _build/default/theories DjotV check/Wide.v
```

Against djot's own table it fails on its first line, and the failure is
the baseline: `__a__` is nested emphasis there.  That is the extension
being non-conservative, in one error message.

It is out of the build for the same reason `check/Deep.v` is, and it
stops being a manual recipe once the table is threaded as a parameter:
at that point these become ordinary `Example`s over a second
configuration, which is the whole point of threading it.
*)

From Stdlib Require Import String List Ascii.
From DjotV Require Import Ast Inline.
Import ListNotations.
Open Scope string_scope.

(*
A row of two characters
-----------------------
*)

(* The extension itself: two characters open and close a strong span,
   and one is not a token at all. *)
Example wide_strong : parse_inline_line "__a__" = [mk (Strong [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example wide_half_token_is_text : parse_inline_line "_a_" = [mk (Str "_a_")].
Proof. vm_compute. reflexivity. Qed.

(* The one-character row alongside it is untouched. *)
Example wide_emph : parse_inline_line "*a*" = [mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example wide_nests_the_other_row :
  parse_inline_line "__*a*__" = [mk (Strong [mk (Emph [mk (Str "a")])])].
Proof. vm_compute. reflexivity. Qed.

Example wide_nests_inside_the_other_row :
  parse_inline_line "*__a__*" = [mk (Emph [mk (Strong [mk (Str "a")])])].
Proof. vm_compute. reflexivity. Qed.

(* Both characters still escape, one at a time. *)
Example wide_escapes : parse_inline_line "\_\_a\_\_" = [mk (Str "__a__")].
Proof. vm_compute. reflexivity. Qed.

Example wide_escape_str : escape_str "a_b*c" = "a\_b\*c".
Proof. vm_compute. reflexivity. Qed.

(*
Runs longer than the row
------------------------

The open question was whether a run is cut from the left and what
becomes of the remainder.  It is, and the answer is not symmetric: a
leading remainder lands *inside* the span, because it is read after the
opener; a trailing one lands *outside*, because the closer is taken
first.
*)

Example wide_three_splits_left :
  parse_inline_line "___a___"
  = [mk (Strong [mk (Str "_a")]); mk (Str "_")].
Proof. vm_compute. reflexivity. Qed.

Example wide_five_splits_left :
  parse_inline_line "_____a_____"
  = [mk (Strong [mk (Strong [mk (Str "_a")])]); mk (Str "_")].
Proof. vm_compute. reflexivity. Qed.

(* Four characters are two tokens, and two tokens stack -- the same
   answer one-character rows give to `____a____`, one level per token
   rather than one per character. *)
Example wide_four_nests :
  parse_inline_line "____a____"
  = [mk (Strong [mk (Strong [mk (Str "a")])])].
Proof. vm_compute. reflexivity. Qed.

(* And four in the middle are a close and an open. *)
Example wide_four_between_is_close_then_open :
  parse_inline_line "__a____b__"
  = [mk (Strong [mk (Str "a")]); mk (Strong [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

(*
An empty span still declines to close
-------------------------------------

`oclose_go` reads the top of the scope stack and asks whether it is
empty, so the exclusion needs no arithmetic on positions and generalizes
to a wider row for free.  This is the half of the `____` question that
was open: djot.js phrases it as `opener.endpos !== pos - 1`, which
measures a one-character gap and would have had to be restated.
*)

Example wide_bare_run_is_text : parse_inline_line "____" = [mk (Str "____")].
Proof. vm_compute. reflexivity. Qed.

Example wide_token_alone_is_text : parse_inline_line "__" = [mk (Str "__")].
Proof. vm_compute. reflexivity. Qed.

Example wide_three_alone_is_text : parse_inline_line "___" = [mk (Str "___")].
Proof. vm_compute. reflexivity. Qed.

Example wide_spaced_is_text : parse_inline_line "__ __" = [mk (Str "__ __")].
Proof. vm_compute. reflexivity. Qed.

Example wide_marked_empty_is_text : parse_inline_line "{__}" = [mk (Str "{__}")].
Proof. vm_compute. reflexivity. Qed.

(*
The compatibility note
----------------------

These are the documents whose meaning the extension changes, and they
change by becoming literal rather than by parsing differently: with
`__` a token, an odd `_` has nothing to pair with.
*)

Example wide_unmatched_open : parse_inline_line "__a_" = [mk (Str "__a_")].
Proof. vm_compute. reflexivity. Qed.

Example wide_unmatched_close : parse_inline_line "_a__" = [mk (Str "_a__")].
Proof. vm_compute. reflexivity. Qed.

(* Intraword still opens, as djot's rows do. *)
Example wide_intraword :
  parse_inline_line "a__b__c"
  = [mk (Str "a"); mk (Strong [mk (Str "b")]); mk (Str "c")].
Proof. vm_compute. reflexivity. Qed.

(*
The braced spelling
-------------------

The marked open spells its whole token before it pushes, and a token
that never finishes decays with its `{` back in front of it.
*)

Example wide_marked : parse_inline_line "{__a__}" = [mk (Strong [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example wide_marked_half_token : parse_inline_line "{_a_}" = [mk (Str "{_a_}")].
Proof. vm_compute. reflexivity. Qed.

Example wide_marked_half_closer : parse_inline_line "{__a_}" = [mk (Str "{__a_}")].
Proof. vm_compute. reflexivity. Qed.

(*
The canonical view
------------------

The behavioural half of what the roundtrip proof says at this table: the
renderer writes the row's token, and the scan reads it back.
*)

Example wide_canonical_source :
  ci_line [CIDelim DStrong [CIStr "a"]] = "{__a__}".
Proof. vm_compute. reflexivity. Qed.

Example wide_canonical_roundtrip :
  parse_inline_line (ci_line [CIDelim DStrong [CIStr "a"]])
  = ci_inlines [CIDelim DStrong [CIStr "a"]].
Proof. vm_compute. reflexivity. Qed.

Example wide_canonical_nested_source :
  ci_line [CIDelim DStrong [CIStr "a"; CIDelim DEmph [CIStr "b"]]]
  = "{__a{*b*}__}".
Proof. vm_compute. reflexivity. Qed.

Example wide_canonical_nested_roundtrip :
  parse_inline_line (ci_line [CIDelim DStrong [CIStr "a"; CIDelim DEmph [CIStr "b"]]])
  = ci_inlines [CIDelim DStrong [CIStr "a"; CIDelim DEmph [CIStr "b"]]].
Proof. vm_compute. reflexivity. Qed.
