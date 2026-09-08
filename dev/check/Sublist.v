(* ai-disclosure: ai-generated *)

(*
The sublist knob, pinned
========================

The block layer's first configuration parameter: whether a list marker
closes an open paragraph instead of extending it.  djot's answer is
never, which is the rule "a sublist must be preceded by a blank line";
`sublist_bconfig` answers yes for a bullet or the numeral `1`.

Every line here was measured.  It needs no recipe and no second build:
the knob is a parameter, so these examples name the other instance and
the ordinary build checks them.

```
dune build && rocq c -R _build/default/theories DjotV dev/check/Sublist.v
```

It is out of the dune build for the reason `dev/check/Markdown.v` is --
`vm_compute` over whole documents is not something a parser edit should
pay for.

The argument for the shape of this knob, and the measurements behind the
restriction, are in `.project/260823.phase4-block-knob.md`.
*)

From Stdlib Require Import String List Ascii.
From DjotV Require Import Ast Line Inline Parser Document Render Roundtrip
  Invariants.
Import ListNotations.
Open Scope string_scope.

(* The rejected alternative, kept here because the case that rejects it
   is one of the examples below: a knob that lets *every* marker
   interrupt. *)
Definition any_bconfig : bconfig :=
  with_marker_interrupts (fun _ _ _ _ => true) djot_bconfig.

Local Notation Djot := (@parse_blocks _ djot_bconfig).
Local Notation Sub := (@parse_blocks _ sublist_bconfig).
Local Notation Any := (@parse_blocks _ any_bconfig).

(*
The sublist
-----------
*)

(* djot reads the indented marker as more of the item's paragraph.  This
   is the behaviour the knob exists to change, pinned first. *)
Example djot_swallows_the_marker :
  Djot "- a
  - b"
  = [mk (BulletList Tight
           [[mk (Para [mk (Str "a"); mk SoftBreak; mk (Str "- b")])]])].
Proof. vm_compute. reflexivity. Qed.

Example sublist_nests_without_a_blank :
  Sub "- a
  - b"
  = [mk (BulletList Tight
           [[mk (Para [mk (Str "a")]);
             mk (BulletList Tight [[mk (Para [mk (Str "b")])]])]])].
Proof. vm_compute. reflexivity. Qed.

(* The same document djot needs a blank line to read this way, so the
   knob makes the blank optional rather than meaningful. *)
Example djot_needs_the_blank :
  Djot "- a

  - b"
  = Sub "- a
  - b".
Proof. vm_compute. reflexivity. Qed.

(*
It is not a sublist rule
------------------------

The knob is stated without reference to the enclosing container, which
is what leaves `list_uniformity` -- an item's lines parse as they would
at top level -- true at every setting.  The price is that a marker
interrupts a top-level paragraph too, and that is not conservative: the
document below is valid djot today with a different meaning.
*)

Example sublist_interrupts_at_top_level :
  Sub "p
1. one"
  = [mk (Para [mk (Str "p")]);
     mk (OrderedList {| ol_style := Decimal;
                        ol_delim := RightPeriod;
                        ol_start := 1 |} Tight
           [[mk (Para [mk (Str "one")])]])].
Proof. vm_compute. reflexivity. Qed.

Example djot_reads_that_as_prose :
  Djot "p
1. one" = [mk (Para [mk (Str "p"); mk SoftBreak; mk (Str "1. one")])].
Proof. vm_compute. reflexivity. Qed.

(*
Why the numeral is restricted
-----------------------------

`lists.test:33` is djot's own regression test for the accidental list,
and it is the only corpus case the unrestricted knob gets wrong.  It is
also the whole argument for admitting `1` and no other numeral: prose
ends in a year, not in the number one.
*)

Definition civil_war : string := "The civil war ended in
1865. And this should not start a list.".

Example any_marker_invents_a_list :
  Any civil_war
  = [mk (Para [mk (Str "The civil war ended in")]);
     mk (OrderedList {| ol_style := Decimal;
                        ol_delim := RightPeriod;
                        ol_start := 1865 |} Tight
           [[mk (Para [mk (Str "And this should not start a list.")])]])].
Proof. vm_compute. reflexivity. Qed.

Example sublist_leaves_the_year_alone :
  Sub civil_war = Djot civil_war.
Proof. vm_compute. reflexivity. Qed.

(* Roman and alpha markers are excluded with every other numeral, so a
   sentence ending in an initial stays prose.  Whether `i.` should be
   admitted is open. *)
Example sublist_leaves_an_initial_alone :
  Sub "written by
i. m. author" = Djot "written by
i. m. author".
Proof. vm_compute. reflexivity. Qed.

(* The examples above have one configuration-level statement.  Its exact
   local precondition says an interrupting policy is pointwise no more
   permissive than [prose_safe_markers]; the generic theorem proves that this
   condition is both necessary and sufficient for the installed knob. *)
Theorem sublist_is_accidental_list_immune :
  accidental_list_immune sublist_bconfig.
Proof. exact sublist_accidental_list_immune. Qed.

Theorem accidental_list_immunity_precondition_is_exact :
  forall f K,
    accidental_list_immune (with_marker_interrupts f K) <->
    marker_interrupt_precondition f.
Proof. exact with_marker_interrupts_accidental_list_immune_iff. Qed.

(*
What the canonical view says
----------------------------

`para_ok` gains one clause: an interior line must not be a marker the
knob would act on.  It is not vacuous -- it rejects the unescaped
spelling -- and it costs the roundtrip nothing, because `cline` already
escapes a line-initial marker and `\- b` classifies as text at every
setting.  That is why the accepted fragment does not move with the knob.
*)

Example para_ok_rejects_a_bare_marker_line :
  @para_ok _ sublist_bconfig ["a"; "- b"] = false.
Proof. vm_compute. reflexivity. Qed.

Example para_ok_takes_the_escaped_one :
  @para_ok _ sublist_bconfig ["a"; "\- b"] = true.
Proof. vm_compute. reflexivity. Qed.

Example the_renderer_writes_the_escaped_one :
  map (@ci_line _) (map cline ["a"; "- b"]) = ["a"; "\- b"].
Proof. vm_compute. reflexivity. Qed.

Example para_ok_keeps_the_year :
  @para_ok _ sublist_bconfig ["a"; "1865. x"] = true.
Proof. vm_compute. reflexivity. Qed.

(*
The roundtrip, at the other instance
------------------------------------

Not a rebuild and not a re-proof: the same proof term, applied to the
other knob.
*)

Theorem sublist_roundtrip_blocks :
  forall cbs,
    @cblocks_ok _ sublist_bconfig cbs = true ->
    @parse_blocks _ sublist_bconfig (render_djot (blocks_of_cblocks cbs))
    = blocks_of_cblocks cbs.
Proof. exact (@roundtrip_blocks _ sublist_bconfig). Qed.
