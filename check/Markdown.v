(* ai-disclosure: autonomous *)

(*
The Markdown-like table, pinned
===============================

The Markdown-facing tables this development means to ship: `_` for emphasis
and `**` for strong, with djot's delimiter rules unchanged. `markdown_table`
isolates that spelling decision; `markdown_like_table` additionally disables
the seven delimiter containers CommonMark does not have. Markdown's
*spelling*, djot's *semantics* -- no run-length arithmetic and no flanking
rules, because a character belongs to one row at one width and there is
nothing to disambiguate.

Every line here was measured, not predicted.

It needs no recipe and no second build: the table is a parameter, so
these examples name the other instance and the ordinary build checks
them.

```
dune build && rocq c -R _build/default/theories DjotV check/Markdown.v
```

It is out of the dune build for the same reason `check/Deep.v` is --
`vm_compute` over whole documents is not something a parser edit should
pay for -- and not because it needs special treatment any more.
*)

From Stdlib Require Import String List Ascii.
From DjotV Require Import Ast Inline Parser Document Render Roundtrip Invariants
  Profile.
Import ListNotations.
Open Scope string_scope.

(* Everything below is read at the Markdown-like table.  Naming it here
   rather than declaring it an instance is what keeps djot's the one
   inference finds everywhere else. *)
Local Notation ProfileInline := (@parse_inline_line markdown_like_table).
Local Notation parse_inline_line := (@parse_inline_line markdown_table).
Local Notation escape_str := (@escape_str markdown_table).
Local Notation ci_line := (@ci_line markdown_table).
Local Notation MdBlocks := (@parse_blocks markdown_table markdown_bconfig).

(* A typography-only variant keeps djot's delimiter rows enabled.  It pins
   the interaction between literal hyphen runs and a delete closer. *)
Definition literal_typography_table : dtable :=
  DTable (with_smart_typography false djot_config) eq_refl.
Local Notation LiteralTypographyInline :=
  (@Inline.parse_inline_line literal_typography_table).

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

(* The reduced profile also switches off the scanner-level typography
   capability.  Curly quotes are separate delimiter rows; these witnesses pin
   the two hardwired rewrites that the capability controls. *)
Example markdown_like_periods_are_literal :
  ProfileInline "a...b" = [mk (Str "a...b")].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_hyphens_are_literal :
  (ProfileInline "a--b", ProfileInline "a---b")
  = ([mk (Str "a--b")], [mk (Str "a---b")]).
Proof. vm_compute. reflexivity. Qed.

Example literal_hyphens_still_give_back_a_delete_closer :
  LiteralTypographyInline "{-a---}"
  = [mk (Delete [mk (Str "a--")])].
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

(*
The narrower inline profile
---------------------------

`markdown_table` isolates the doubled-strong spelling.  The named
Markdown-like profile starts there and disables djot's seven additional
delimiter containers, leaving emphasis and strong as the only enabled rows.
*)

Example markdown_like_keeps_emphasis_and_strong :
  ProfileInline "_a_ and **b**"
  = [mk (Emph [mk (Str "a")]); mk (Str " and ");
     mk (Strong [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_reads_djot_delimiters_literally :
  ProfileInline "{=a=} {+b+} {-c-} ^d^ ~e~ 'f' ""g"""
  = [mk (Str "{=a=} {+b+} {-c-} ^d^ ~e~ 'f' ""g""")].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_rejects_disabled_canonical_nodes :
  @ci_ok markdown_like_table (CIDelim DMark [CIStr "a"]) = false.
Proof. vm_compute. reflexivity. Qed.

(* The block half names the composition of both Markdown-facing decisions,
   rather than silently inferring djot's block instance. *)
Example md_setext_heading :
  MdBlocks "a
===" = [mk (Heading 1 [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example md_sublist_without_blank :
  MdBlocks "- a
  - b"
  = [mk (BulletList Tight
           [[mk (Para [mk (Str "a")]);
             mk (BulletList Tight [[mk (Para [mk (Str "b")])]])]])].
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

Example markdown_multiline_canonical_heading_is_disabled :
  @cb_ok markdown_table markdown_bconfig
    (CHeading 1 [[CIStr "a"]; [CIStr "b"]]) = false.
Proof. vm_compute. reflexivity. Qed.

Example markdown_single_line_canonical_heading_is_enabled :
  @cb_ok markdown_table markdown_bconfig
    (CHeading 1 [[CIStr "a"]]) = true.
Proof. vm_compute. reflexivity. Qed.

Example djot_profile_keeps_divs :
  parse_profile_blocks djot_profile ":::
a
:::"
  = [mk (Div [mk (Para [mk (Str "a")])])].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_profile_reads_divs_as_text :
  parse_profile_blocks markdown_like_profile ":::
a
:::"
  = [mk (Para [mk (Str ":::"); mk SoftBreak; mk (Str "a");
               mk SoftBreak; mk (Str ":::")])].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_canonical_div_is_disabled :
  @cb_ok markdown_like_table markdown_bconfig (CDiv [CPara [[CIStr "a"]]])
  = false.
Proof. vm_compute. reflexivity. Qed.

(* A named profile is a starting point, not a closed flavor enum. *)
Definition markdown_with_divs : profile :=
  with_block_profile (with_divs true markdown_bconfig) markdown_like_profile.

Example customized_markdown_profile_restores_only_divs :
  parse_profile_blocks markdown_with_divs ":::
a
:::"
  = parse_profile_blocks djot_profile ":::
a
:::".
Proof. vm_compute. reflexivity. Qed.

(* Core CommonMark has no table construct. The classifier still recognizes
   row-shaped source, but this profile opens it as ordinary paragraph text. *)
Example markdown_like_table_source_is_prose :
  @parse_blocks markdown_like_table markdown_bconfig "| a |
|---|"
  = [mk (Para [mk (Str "| a |"); mk SoftBreak;
               mk (Str "|---|")])].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_canonical_table_is_disabled :
  @cb_ok markdown_like_table markdown_bconfig
    (CTable [CTBody [[CIStr "a"]]]) = false.
Proof. vm_compute. reflexivity. Qed.

Theorem markdown_block_incremental :
  block_incremental markdown_table markdown_bconfig.
Proof. apply block_incremental_holds. Qed.

(*
The theorems, at this table
---------------------------

Not a rebuild and not a re-proof: the same proof term, applied to the
other instance.  This is what threading the table bought that the
rebuild audit could not -- the roundtrip is one theorem about the
family, and `markdown_table` is one of its inhabitants.
*)

Theorem md_roundtrip_blocks :
  forall cbs,
    @cblocks_ok markdown_table markdown_bconfig cbs = true ->
    @parse_blocks markdown_table markdown_bconfig
      (@render_djot markdown_table (blocks_of_cblocks cbs))
    = blocks_of_cblocks cbs.
Proof. exact (@roundtrip_blocks markdown_table markdown_bconfig). Qed.

Theorem md_roundtrip_doc :
  forall cbs,
    @cblocks_ok markdown_table markdown_bconfig cbs = true ->
    undo_pass
      (doc_blocks
         (@parse_doc markdown_table markdown_bconfig
            (@render_djot markdown_table (blocks_of_cblocks cbs))))
    = blocks_of_cblocks cbs.
Proof. exact (@roundtrip_doc markdown_table markdown_bconfig). Qed.

Theorem markdown_like_roundtrip_doc :
  forall cbs,
    @cblocks_ok markdown_like_table markdown_bconfig cbs = true ->
    undo_pass
      (doc_blocks
         (@parse_doc markdown_like_table markdown_bconfig
            (@render_djot markdown_like_table (blocks_of_cblocks cbs))))
    = blocks_of_cblocks cbs.
Proof. exact (@roundtrip_doc markdown_like_table markdown_bconfig). Qed.
