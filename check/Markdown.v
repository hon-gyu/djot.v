(* ai-disclosure: autonomous *)

(*
The Markdown-like table, pinned
===============================

The second table this development means to ship: `_` for emphasis and
`**` for strong, with djot's rules unchanged.  Markdown's *spelling*,
djot's *semantics* -- no run-length arithmetic and no flanking rules,
because a character belongs to one row at one width and there is
nothing to disambiguate.

Every line here was measured, not predicted.

**This file does not compile against the ordinary build.**  It asks for
`theories/Inline.v`'s table in force to be the second one:

```coq
Definition config : dconfig := markdown_config.
```

with `Inline.v`'s own examples truncated (`head -4580`) -- they spell
djot's `*a*` as strong and are about djot.  Then:

```
dune build && rocq c -R _build/default/theories DjotV check/Markdown.v
```

Against djot's table it fails on its first line, and the failure is the
baseline: `**a**` is nested *emphasis* there, since `*` is strong at
width one.  That is the extension being non-conservative, in one error
message.

It is out of the build for the same reason `check/Deep.v` is, and it
stops being a manual recipe once the table is threaded as a parameter:
at that point these become ordinary `Example`s over the second
configuration, which is what threading it is for.
*)

From Stdlib Require Import String List Ascii.
From DjotV Require Import Ast Inline.
Import ListNotations.
Open Scope string_scope.

(*
The spelling
------------
*)

Example md_strong : parse_inline_line "**a**" = [mk (Strong [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example md_emph : parse_inline_line "_a_" = [mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example md_nested_both_ways :
  parse_inline_line "**_a_**" = [mk (Strong [mk (Emph [mk (Str "a")])])]
  /\ parse_inline_line "_**a**_" = [mk (Emph [mk (Strong [mk (Str "a")])])].
Proof. vm_compute. split; reflexivity. Qed.

Example md_two_spans :
  parse_inline_line "**a** and **b**"
  = [mk (Strong [mk (Str "a")]); mk (Str " and "); mk (Strong [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

(* Both characters still escape. *)
Example md_escapes : parse_inline_line "\*\*a\*\*" = [mk (Str "**a**")].
Proof. vm_compute. reflexivity. Qed.

Example md_escape_str : escape_str "a_b*c" = "a\_b\*c".
Proof. vm_compute. reflexivity. Qed.

(*
A single `*` is not a delimiter
-------------------------------

The row's width is fixed, so a run shorter than it is literal.  This is
where the table pays for itself: under djot's table `2*3*4` emphasizes
`3`, and here a lone asterisk is just an asterisk -- without any rule
about what surrounds it.
*)

Example md_single_star_is_text : parse_inline_line "*a*" = [mk (Str "*a*")].
Proof. vm_compute. reflexivity. Qed.

Example md_arithmetic_is_text : parse_inline_line "2*3*4" = [mk (Str "2*3*4")].
Proof. vm_compute. reflexivity. Qed.

Example md_intraword_star_is_text :
  parse_inline_line "a*b*c" = [mk (Str "a*b*c")].
Proof. vm_compute. reflexivity. Qed.

Example md_lone_star : parse_inline_line "*" = [mk (Str "*")].
Proof. vm_compute. reflexivity. Qed.

Example md_half_closer_is_text : parse_inline_line "**a*" = [mk (Str "**a*")].
Proof. vm_compute. reflexivity. Qed.

(*
djot's rules, unchanged
-----------------------

Nothing here is new; it is what djot's one-byte tests already give,
restated at width two.  Intraword *does* open -- djot has no word rule
(`opentest` is `alwaysTrue` for these rows, `inline.ts:284-315`) -- and
the braced form is how one says it explicitly, exactly as in djot.
*)

Example md_intraword_emph :
  parse_inline_line "he_ll_o"
  = [mk (Str "he"); mk (Emph [mk (Str "ll")]); mk (Str "o")].
Proof. vm_compute. reflexivity. Qed.

Example md_intraword_strong :
  parse_inline_line "he**ll**o"
  = [mk (Str "he"); mk (Strong [mk (Str "ll")]); mk (Str "o")].
Proof. vm_compute. reflexivity. Qed.

Example md_braced_intraword :
  parse_inline_line "he{_ll_}o"
  = [mk (Str "he"); mk (Emph [mk (Str "ll")]); mk (Str "o")].
Proof. vm_compute. reflexivity. Qed.

Example md_braced : parse_inline_line "{**a**}" = [mk (Strong [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

(* A brace does not conjure a token out of half a run. *)
Example md_braced_half_token : parse_inline_line "{*a*}" = [mk (Str "{*a*}")].
Proof. vm_compute. reflexivity. Qed.

Example md_braced_half_closer : parse_inline_line "{**a*}" = [mk (Str "{**a*}")].
Proof. vm_compute. reflexivity. Qed.

(* An empty span declines to close, as in djot, and needs no arithmetic
   on positions to do it: `oclose_go` asks whether the top scope is
   empty. *)
Example md_empty_is_text : parse_inline_line "**" = [mk (Str "**")].
Proof. vm_compute. reflexivity. Qed.

Example md_empty_pair_is_text : parse_inline_line "****" = [mk (Str "****")].
Proof. vm_compute. reflexivity. Qed.

(*
Runs longer than the row
------------------------

A run is cut into tokens from the left, and the remainder's fate is not
symmetric: a leading one lands *inside* the span, since it is read after
the opener has been taken, and a trailing one lands outside.  Four
characters are two tokens, and two tokens stack -- one level per token,
which is the one-character answer to `____a____` restated at the right
granularity.
*)

Example md_three_splits_left :
  parse_inline_line "***a***"
  = [mk (Strong [mk (Str "*a")]); mk (Str "*")].
Proof. vm_compute. reflexivity. Qed.

Example md_four_nests :
  parse_inline_line "****a****"
  = [mk (Strong [mk (Strong [mk (Str "a")])])].
Proof. vm_compute. reflexivity. Qed.

(*
The canonical view
------------------

The behavioural half of what the roundtrip proofs say at this table: the
renderer writes the row's token in the braced form, and the scan reads it
back.
*)

Example md_canonical_source :
  ci_line [CIDelim DStrong [CIStr "a"]] = "{**a**}".
Proof. vm_compute. reflexivity. Qed.

Example md_canonical_roundtrip :
  parse_inline_line (ci_line [CIDelim DStrong [CIStr "a"]])
  = ci_inlines [CIDelim DStrong [CIStr "a"]].
Proof. vm_compute. reflexivity. Qed.

Example md_canonical_nested_source :
  ci_line [CIDelim DEmph [CIStr "a"; CIDelim DStrong [CIStr "b"]]]
  = "{_a{**b**}_}".
Proof. vm_compute. reflexivity. Qed.

Example md_canonical_nested_roundtrip :
  parse_inline_line (ci_line [CIDelim DEmph [CIStr "a"; CIDelim DStrong [CIStr "b"]]])
  = ci_inlines [CIDelim DEmph [CIStr "a"; CIDelim DStrong [CIStr "b"]]].
Proof. vm_compute. reflexivity. Qed.
