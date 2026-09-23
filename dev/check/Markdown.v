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
Local Notation MdBlocks := (@parse_blocks markdown_table markdown_bconfig _).

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

(* Raw recognition keeps using the shared verbatim/spec scanner. With raw
   semantics disabled, its successful candidate takes the scanner's existing
   literal fallback: the verbatim node stands and the complete spec is text. *)
Example markdown_like_raw_inline_is_verbatim_and_text :
  ProfileInline "`<a>`{=html}"
  = [mk (Verbatim "<a>"); mk (Str "{=html}")].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_canonical_raw_inline_is_disabled :
  @ci_ok markdown_like_table (CIRaw "html" "<a>") = false.
Proof. vm_compute. reflexivity. Qed.

Definition markdown_with_raw_inline_table : dtable :=
  DTable (with_raw_inline true markdown_like_config) eq_refl.

Example customized_markdown_table_restores_raw_inline :
  @Inline.parse_inline_line markdown_with_raw_inline_table "`<a>`{=html}"
  = [mk (RawInline "html" "<a>")].
Proof. vm_compute. reflexivity. Qed.

Example with_raw_inline_preserves_other_inline_settings :
  let C := with_raw_inline false djot_config in
  (dc_smart_typography C, dc_char C DStrong, dc_width C DStrong,
   dc_syntax C DStrong)
  = (true, "*"%char, 1, DBare).
Proof. reflexivity. Qed.

(* Math is the dollar prefix on a verbatim span.  With it off the prefix is
   not dropped: the dollars join the pending text and the span they were
   about to mark is the code span it already was.  Both widths, and the
   third dollar djot itself leaves as text, survive literally. *)
Example markdown_like_math_is_code_and_text :
  (ProfileInline "$`x`", ProfileInline "$$`x`", ProfileInline "$$$`x`")
  = ([mk (Str "$"); mk (Verbatim "x")],
     [mk (Str "$$"); mk (Verbatim "x")],
     [mk (Str "$$$"); mk (Verbatim "x")]).
Proof. vm_compute. reflexivity. Qed.

(* A dollar not on a verbatim was already text at every setting, so the
   capability moves nothing here. *)
Example markdown_like_bare_dollar_is_text :
  ProfileInline "a $b$ c" = [mk (Str "a $b$ c")].
Proof. vm_compute. reflexivity. Qed.

Definition markdown_with_math_table : dtable :=
  DTable (with_math true markdown_like_config) eq_refl.

Example customized_markdown_table_restores_math :
  (@Inline.parse_inline_line markdown_with_math_table "$`x`",
   @Inline.parse_inline_line markdown_with_math_table "$$`x`")
  = ([mk (Math InlineMath "x")], [mk (Math DisplayMath "x")]).
Proof. vm_compute. reflexivity. Qed.

Example with_math_preserves_other_inline_settings :
  let C := with_math false djot_config in
  (dc_smart_typography C, dc_raw_inline C, dc_char C DStrong,
   dc_width C DStrong, dc_syntax C DStrong)
  = (true, true, "*"%char, 1, DBare).
Proof. reflexivity. Qed.

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

(* Task recognition is also a construction gate.  Disabled mode preserves
   the complete checkbox token as ordinary bullet-item text: case and the
   separator after the box are not reconstructed from the semantic status. *)
Example markdown_like_task_boxes_are_literal :
  MdBlocks "- [ ] a
- [x] b
- [X]	c"
  = [mk (BulletList Tight
           [[mk (Para [mk (Str "[ ] a")])];
            [mk (Para [mk (Str "[x] b")])];
            [mk (Para [mk (Str "[X]	c")])]])].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_canonical_task_list_is_disabled :
  @cb_ok markdown_table markdown_bconfig
    (CList (LKTask [Incomplete]) Tight [[CPara [[CIStr "a"]]]]) = false.
Proof. vm_compute. reflexivity. Qed.

Definition markdown_with_tasks : profile :=
  with_block_profile (with_tasks true markdown_bconfig) markdown_like_profile.

Example customized_markdown_profile_restores_tasks :
  parse_profile_blocks markdown_with_tasks "- [ ] a
- [x] b
- [X]	c"
  = [mk (TaskList Tight
           [(Incomplete, [mk (Para [mk (Str "a")])]);
            (Complete, [mk (Para [mk (Str "b")])]);
            (Complete, [mk (Para [mk (Str "c")])])])].
Proof. vm_compute. reflexivity. Qed.

Example with_tasks_preserves_other_block_settings :
  let K := with_tasks false djot_bconfig in
  (@btables K, @bheading_continues K, @bdivs K)
  = (true, true, true).
Proof. reflexivity. Qed.

Example djot_profile_keeps_raw_blocks :
  parse_profile_blocks djot_profile "```=html
<b>
```"
  = [mk (RawBlock "html" "<b>
")].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_raw_fence_is_code :
  parse_profile_blocks markdown_like_profile "```=html
<b>
```"
  = [mk (CodeBlock "=html" "<b>
")].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_canonical_raw_block_is_disabled :
  @cb_ok markdown_like_table markdown_bconfig (CRaw "html" ["<b>"])
  = false.
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_canonical_equal_info_code_is_enabled :
  @cb_ok markdown_like_table markdown_bconfig (CCode "=html" ["<b>"])
  = true.
Proof. vm_compute. reflexivity. Qed.

Example djot_canonical_equal_info_code_is_disabled :
  @cb_ok djot_table djot_bconfig (CCode "=html" ["<b>"]) = false.
Proof. vm_compute. reflexivity. Qed.

Definition markdown_with_raw_blocks : profile :=
  with_block_profile (with_raw_blocks true markdown_bconfig)
    markdown_like_profile.

Example customized_markdown_profile_restores_raw_blocks :
  parse_profile_blocks markdown_with_raw_blocks "```=html
<b>
```"
  = parse_profile_blocks djot_profile "```=html
<b>
```".
Proof. vm_compute. reflexivity. Qed.

Example with_raw_blocks_preserves_other_block_settings :
  let K := with_raw_blocks false djot_bconfig in
  (@btables K, @bheading_continues K, @bdivs K, @btasks K)
  = (true, true, true, true).
Proof. reflexivity. Qed.

(* Definition lists are the eighth block capability, and the only one whose
   gate is the closing projection rather than the opening one.  Recognition
   is untouched at both settings: the colon is a bullet character, the item
   is the same item, and what the capability decides is whether its content
   is split into a term and a definition. *)
Example djot_profile_keeps_definition_lists :
  parse_profile_blocks djot_profile ": t

  d"
  = [mk (DefinitionList Loose
           [([mk (Str "t")], [mk (Para [mk (Str "d")])])])].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_definition_list_is_a_bullet_list :
  parse_profile_blocks markdown_like_profile ": t

  d"
  = [mk (BulletList Loose
           [[mk (Para [mk (Str "t")]); mk (Para [mk (Str "d")])]])].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_canonical_deflist_is_disabled :
  @cb_ok markdown_like_table markdown_bconfig
    (CList LKDef Tight [[CPara [[CIStr "t"]]]]) = false.
Proof. vm_compute. reflexivity. Qed.

Example djot_canonical_deflist_is_enabled :
  @cb_ok djot_table djot_bconfig
    (CList LKDef Tight [[CPara [[CIStr "t"]]]]) = true.
Proof. vm_compute. reflexivity. Qed.

Definition markdown_with_deflists : profile :=
  with_block_profile (with_deflists true markdown_bconfig)
    markdown_like_profile.

Example customized_markdown_profile_restores_deflists :
  parse_profile_blocks markdown_with_deflists ": t

  d"
  = parse_profile_blocks djot_profile ": t

  d".
Proof. vm_compute. reflexivity. Qed.

Example with_deflists_preserves_other_block_settings :
  let K := with_deflists false djot_bconfig in
  (@btables K, @bheading_continues K, @bdivs K, @btasks K, @braw_blocks K)
  = (true, true, true, true, true).
Proof. reflexivity. Qed.

(* Block attributes are the ninth block capability.  With them off a `{...}`
   line opens nothing, so it is the paragraph text its own spelling makes and
   the block that followed keeps the attributes it was never given. *)
Example djot_profile_keeps_block_attributes :
  parse_profile_blocks djot_profile "{#id}
para"
  = [Node NoPos [("id", "id")] (Para [mk (Str "para")])].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_block_attribute_is_prose :
  parse_profile_blocks markdown_like_profile "{#id}
para"
  = [mk (Para [mk (Str "{#id}"); mk SoftBreak; mk (Str "para")])].
Proof. vm_compute. reflexivity. Qed.

Definition markdown_with_block_attrs : profile :=
  with_block_profile (with_block_attrs true markdown_bconfig)
    markdown_like_profile.

Example customized_markdown_profile_restores_block_attrs :
  parse_profile_blocks markdown_with_block_attrs "{#id}
para"
  = [Node NoPos [("id", "id")] (Para [mk (Str "para")])].
Proof. vm_compute. reflexivity. Qed.

Example with_block_attrs_preserves_other_block_settings :
  let K := with_block_attrs false djot_bconfig in
  (@btables K, @bheading_continues K, @bdivs K, @btasks K, @braw_blocks K,
   @bdeflists K)
  = (true, true, true, true, true, true).
Proof. reflexivity. Qed.

(* The inline half.  `dc_attrs` covers both things a `{` can do that are not
   a delimiter row: attach an attribute, and -- after a `]` -- open a span.
   With it off each is the literal text it spells. *)
Example markdown_like_inline_attribute_is_text :
  ProfileInline "x{#i .c}y" = [mk (Str "x{#i .c}y")].
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_span_is_text :
  ProfileInline "[s]{.c}" = [mk (Str "[s]{.c}")].
Proof. vm_compute. reflexivity. Qed.

(* Both halves together are what makes a multi-line spec read as prose: the
   block layer no longer opens it and the inline layer no longer eats the
   break, so the paragraph keeps its lines. *)
Example markdown_like_multiline_attribute_is_prose :
  parse_profile_blocks markdown_like_profile "{#i
 .c}
para"
  = [mk (Para [mk (Str "{#i"); mk SoftBreak; mk (Str ".c}");
               mk SoftBreak; mk (Str "para")])].
Proof. vm_compute. reflexivity. Qed.

(* The braced delimiter rows are a separate decision, reached from the same
   `{`: a table with attributes off and djot's rows still reads `{-x-}` as a
   delete. *)
Definition no_attrs_table : dtable :=
  DTable (with_inline_attrs false djot_config) eq_refl.

Example rows_survive_inline_attrs_off :
  (@Inline.parse_inline_line no_attrs_table "a{-b-}c",
   @Inline.parse_inline_line no_attrs_table "a{#i}c")
  = ([mk (Str "a"); mk (Delete [mk (Str "b")]); mk (Str "c")],
     [mk (Str "a{#i}c")]).
Proof. vm_compute. reflexivity. Qed.

Definition markdown_with_inline_attrs_table : dtable :=
  DTable (with_inline_attrs true markdown_like_config) eq_refl.

Example customized_markdown_table_restores_inline_attrs :
  @Inline.parse_inline_line markdown_with_inline_attrs_table "[s]{.c}"
  = [Node NoPos [("class", "c")] (Span [mk (Str "s")])].
Proof. vm_compute. reflexivity. Qed.

Example with_inline_attrs_preserves_other_inline_settings :
  let C := with_inline_attrs false djot_config in
  (dc_smart_typography C, dc_raw_inline C, dc_math C, dc_char C DStrong,
   dc_width C DStrong, dc_syntax C DStrong)
  = (true, true, true, "*"%char, 1, DBare).
Proof. reflexivity. Qed.

(*
Footnotes: one capability across two records
--------------------------------------------

A reference nothing can define and a definition nothing can reference are
not settings anyone wants, so the knob that should be reached for is the
profile-level one.  Both profiles keep footnotes on -- CommonMark lacks
them but GFM has them -- so this is pinned at a profile of its own rather
than in `markdown_like_profile`.
*)

Definition no_footnotes_profile : profile := with_footnotes false djot_profile.

Example djot_profile_keeps_footnotes :
  parse_profile_blocks djot_profile "a[^1]

[^1]: note"
  = [mk (Para [mk (Str "a"); mk (FootnoteReference "1")]);
     mk (FootnoteDef "1" [mk (Para [mk (Str "note")])])].
Proof. vm_compute. reflexivity. Qed.

Example no_footnotes_profile_reads_both_halves_as_prose :
  parse_profile_blocks no_footnotes_profile "a[^1]

[^1]: note"
  = [mk (Para [mk (Str "a[^1]")]);
     mk (Para [mk (Str "[^1]: note")])].
Proof. vm_compute. reflexivity. Qed.

Example no_footnotes_canonical_note_is_disabled :
  (@ci_ok (profile_inline no_footnotes_profile) (CINote "a"),
   @ci_ok (profile_inline djot_profile) (CINote "a"))
  = (false, true).
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_profile_keeps_footnotes :
  parse_profile_blocks markdown_like_profile "a[^1]

[^1]: note"
  = parse_profile_blocks djot_profile "a[^1]

[^1]: note".
Proof. vm_compute. reflexivity. Qed.

Example with_footnotes_preserves_other_settings :
  let P := with_footnotes false djot_profile in
  let K := profile_block P in
  let C := @cfg (profile_inline P) in
  (@btables K, @bdivs K, @btasks K, @bdeflists K, @battrs K,
   dc_math C, dc_attrs C, dc_char C DStrong)
  = (true, true, true, true, true, true, true, "*"%char).
Proof. reflexivity. Qed.

(* Core CommonMark has no table construct. The classifier still recognizes
   row-shaped source, but this profile opens it as ordinary paragraph text. *)
Example markdown_like_table_source_is_prose :
  @parse_blocks markdown_like_table markdown_bconfig _ _ "| a |
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
other instance.  The roundtrip is one theorem about the family, and
`markdown_table` is one of its inhabitants.
*)

Theorem md_roundtrip_blocks :
  forall cbs,
    @cblocks_ok markdown_table markdown_bconfig cbs = true ->
    @parse_blocks markdown_table markdown_bconfig _ _
      (@render_djot markdown_table (blocks_of_cblocks cbs))
    = blocks_of_cblocks cbs.
Proof. exact (@roundtrip_blocks markdown_table markdown_bconfig). Qed.

Theorem md_roundtrip_doc :
  forall cbs,
    @cblocks_ok markdown_table markdown_bconfig cbs = true ->
    pristine (blocks_of_cblocks cbs) = true ->
    undo_pass
      (doc_blocks
         (@parse_doc markdown_table markdown_bconfig _
            (@render_djot markdown_table (blocks_of_cblocks cbs))))
    = blocks_of_cblocks cbs.
Proof. exact (@roundtrip_doc markdown_table markdown_bconfig). Qed.

Theorem markdown_like_roundtrip_doc :
  forall cbs,
    @cblocks_ok markdown_like_table markdown_bconfig cbs = true ->
    pristine (blocks_of_cblocks cbs) = true ->
    undo_pass
      (doc_blocks
         (@parse_doc markdown_like_table markdown_bconfig _
            (@render_djot markdown_like_table (blocks_of_cblocks cbs))))
    = blocks_of_cblocks cbs.
Proof. exact (@roundtrip_doc markdown_like_table markdown_bconfig). Qed.
