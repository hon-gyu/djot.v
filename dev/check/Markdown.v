(* ai-disclosure: autonomous *)

(*
The Markdown-like profile, pinned
=================================

`markdown_like_profile` is djot with Markdown spellings added: `**` for
strong, dollar-delimited math, setext headings, sublists without a blank
line, and one-line ATX headings.  Nothing djot has is taken away; each
capability is still a knob, and `Capabilities.v` pins them switched off.

Markdown's *spelling*, djot's *semantics* -- no run-length arithmetic and no
flanking rules, because a character belongs to one row at one width and
there is nothing to disambiguate.

It needs no recipe and no second build: the table is a parameter, so
these examples name the other instance and the ordinary build checks
them.
*)

From Stdlib Require Import String List Ascii.
From DjotV Require Import Ast Inline Parser Document Render Roundtrip Invariants
  Profile.
Import ListNotations.
Open Scope string_scope.

(* Everything below is read at the Markdown-like table.  Naming it here
   rather than declaring it an instance is what keeps djot's the one
   inference finds everywhere else. *)
Local Notation parse_inline_line := (@parse_inline_line markdown_like_table).
Local Notation escape_str := (@escape_str markdown_like_table).
Local Notation ci_line := (@ci_line markdown_like_table).
Local Notation MdBlocks :=
  (@parse_blocks markdown_like_table markdown_like_bconfig _ _).

(* `ci_inlines` needs no instance: the AST a canonical inline denotes is
   the same whatever the table spells it with.  Only the source and the
   acceptance predicate depend on the table -- which is the roundtrip
   read backwards. *)

(*
The spelling
------------
*)

Example md_strong : parse_inline_line "**a**" = [mk (Strong [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example md_emph : parse_inline_line "_a_" = [mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example md_dollar_math :
  parse_inline_line "$x$" = [mk (Math InlineMath "x")].
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
restated at width two.  Intraword does open, since djot has no word rule
for these rows, and the braced form is how one says it explicitly,
exactly as in djot.
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

(*
Everything else is djot's
-------------------------

The djot-only constructs keep their djot reading: the delimiter containers,
smart typography, and the block constructs.
*)

Example markdown_like_keeps_djot_inlines :
  parse_inline_line "{=a=} ^b^ a...b x{#i} $`y`"
  = @InlineScan.parse_inline_line djot_table "{=a=} ^b^ a...b x{#i} $`y`".
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_keeps_djot_blocks :
  parse_profile_blocks markdown_like_profile ":::
a
:::

: t

  d"
  = parse_profile_blocks djot_profile ":::
a
:::

: t

  d".
Proof. vm_compute. reflexivity. Qed.

(*
The block half
--------------
*)

Example md_setext_heading :
  MdBlocks "a
===" = [mk (Heading 1 [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example md_sublist_without_blank :
  MdBlocks "- a
  - b"
  = [mk (BulletList Tight
           [mk [mk (Para [mk (Str "a")]);
             mk (BulletList Tight [mk [mk (Para [mk (Str "b")])]])]])].
Proof. vm_compute. reflexivity. Qed.

Example md_adjacent_headings_stay_separate :
  MdBlocks "# a
# b"
  = [mk (Heading 1 [mk (Str "a")]); mk (Heading 1 [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

Example md_text_after_heading_is_a_paragraph :
  MdBlocks "# a
b"
  = [mk (Heading 1 [mk (Str "a")]); mk (Para [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

(* Nor does a lazy line continue it: with nothing open to continue, the
   line ends the quote. *)
Example md_lazy_line_after_quoted_heading :
  MdBlocks "> # a
b"
  = [mk (BlockQuote [mk (Heading 1 [mk (Str "a")])]); mk (Para [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

Example markdown_multiline_canonical_heading_is_disabled :
  @cb_ok markdown_like_table markdown_like_bconfig
    (CHeading 1 [[CIStr "a"]; [CIStr "b"]]) = false.
Proof. vm_compute. reflexivity. Qed.

Example markdown_single_line_canonical_heading_is_enabled :
  @cb_ok markdown_like_table markdown_like_bconfig
    (CHeading 1 [[CIStr "a"]]) = true.
Proof. vm_compute. reflexivity. Qed.

(* A named profile is a starting point, not a closed flavor enum: a writer
   who wants djot's heading continuation turns it back on and changes
   nothing else. *)
Definition markdown_with_heading_continuation : profile :=
  with_block_profile (with_heading_continuation true markdown_like_bconfig)
    markdown_like_profile.

Example customized_markdown_profile_continues_headings :
  parse_profile_blocks markdown_with_heading_continuation "# a
# b"
  = [mk (Heading 1 [mk (Str "a"); mk SoftBreak; mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

Example customized_markdown_profile_keeps_setext :
  parse_profile_blocks markdown_with_heading_continuation "a
===" = [mk (Heading 1 [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Theorem markdown_block_incremental :
  block_incremental markdown_like_table markdown_like_bconfig.
Proof. apply block_incremental_holds. Qed.

(*
The theorems, at this profile
-----------------------------

Not a rebuild and not a re-proof: the same proof term, applied to the
other instance.  The roundtrip is one theorem about the family, and
the Markdown-like profile is one of its inhabitants.
*)

Theorem md_roundtrip_blocks :
  forall cbs,
    @cblocks_ok markdown_like_table markdown_like_bconfig cbs = true ->
    @parse_blocks markdown_like_table markdown_like_bconfig _ _
      (@render_djot markdown_like_table markdown_like_bconfig (blocks_of_cblocks cbs))
    = blocks_of_cblocks cbs.
Proof. exact (@roundtrip_blocks markdown_like_table markdown_like_bconfig). Qed.

Theorem md_roundtrip_doc :
  forall cbs,
    @cblocks_ok markdown_like_table markdown_like_bconfig cbs = true ->
    Pristine.of_list (blocks_of_cblocks cbs) = true ->
    Undo.pass
      (doc_blocks
         (@parse_doc markdown_like_table markdown_like_bconfig _
            (@render_djot markdown_like_table markdown_like_bconfig (blocks_of_cblocks cbs))))
    = blocks_of_cblocks cbs.
Proof. exact (@roundtrip_doc markdown_like_table markdown_like_bconfig). Qed.
