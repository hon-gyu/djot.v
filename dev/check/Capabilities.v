(* ai-disclosure: autonomous *)

(*
Capabilities, switched off
==========================

Each djot construct outside the core is a capability with a knob of its
own, in `dconfig` (inline) or `bconfig` (block).  No named profile turns
any of them off, so each is pinned here against djot with that one
capability switched off: what the source reads as instead, that the
canonical view stops admitting the construct, that switching it back on
restores djot's reading, and that the knob moves no other field.
*)

From Stdlib Require Import String List Ascii.
From DjotV Require Import Ast Inline Parser Document Render Roundtrip Profile.
Import ListNotations.
Open Scope string_scope.

(* A profile that differs from djot's in its block half only. *)
Local Notation DjotWith K := (with_block_profile K djot_profile).

(*
Inline capabilities
-------------------
*)

(* Smart typography is scanner dispatch rather than a delimiter row.  Curly
   quotes are rows of their own; these pin the two hardwired rewrites the
   capability controls. *)
Definition literal_typography_table : dtable :=
  DTable (with_smart_typography false djot_config) eq_refl.
Local Notation LiteralTypographyInline :=
  (@InlineScan.parse_inline_line literal_typography_table).

Example periods_are_literal :
  LiteralTypographyInline "a...b" = [mk (Str "a...b")].
Proof. vm_compute. reflexivity. Qed.

Example hyphens_are_literal :
  (LiteralTypographyInline "a--b", LiteralTypographyInline "a---b")
  = ([mk (Str "a--b")], [mk (Str "a---b")]).
Proof. vm_compute. reflexivity. Qed.

Example literal_hyphens_still_give_back_a_delete_closer :
  LiteralTypographyInline "{-a---}"
  = [mk (Delete [mk (Str "a--")])].
Proof. vm_compute. reflexivity. Qed.

(* Raw recognition keeps using the shared verbatim/spec scanner. With raw
   semantics disabled, its successful candidate takes the scanner's existing
   literal fallback: the verbatim node stands and the complete spec is text. *)
Definition no_raw_inline_table : dtable :=
  DTable (with_raw_inline false djot_config) eq_refl.

Example raw_inline_is_verbatim_and_text :
  @InlineScan.parse_inline_line no_raw_inline_table "`<a>`{=html}"
  = [mk (Verbatim "<a>"); mk (Str "{=html}")].
Proof. vm_compute. reflexivity. Qed.

Example canonical_raw_inline_is_disabled :
  @ci_ok no_raw_inline_table (CIRaw "html" "<a>") = false.
Proof. vm_compute. reflexivity. Qed.

Definition raw_inline_restored_table : dtable :=
  DTable (with_raw_inline true (with_raw_inline false djot_config)) eq_refl.

Example raw_inline_restored :
  @InlineScan.parse_inline_line raw_inline_restored_table "`<a>`{=html}"
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
Definition no_math_table : dtable :=
  DTable (with_math false djot_config) eq_refl.
Local Notation NoMathInline := (@InlineScan.parse_inline_line no_math_table).

Example math_is_code_and_text :
  (NoMathInline "$`x`", NoMathInline "$$`x`", NoMathInline "$$$`x`")
  = ([mk (Str "$"); mk (Verbatim "x")],
     [mk (Str "$$"); mk (Verbatim "x")],
     [mk (Str "$$$"); mk (Verbatim "x")]).
Proof. vm_compute. reflexivity. Qed.

(* A dollar not on a verbatim was already text at every setting, so the
   capability moves nothing here. *)
Example bare_dollar_is_text :
  NoMathInline "a $b$ c" = [mk (Str "a $b$ c")].
Proof. vm_compute. reflexivity. Qed.

Definition math_restored_table : dtable :=
  DTable (with_math true (with_math false djot_config)) eq_refl.

Example math_restored :
  (@InlineScan.parse_inline_line math_restored_table "$`x`",
   @InlineScan.parse_inline_line math_restored_table "$$`x`")
  = ([mk (Math InlineMath "x")], [mk (Math DisplayMath "x")]).
Proof. vm_compute. reflexivity. Qed.

Example with_math_preserves_other_inline_settings :
  let C := with_math false djot_config in
  (dc_smart_typography C, dc_raw_inline C, dc_dollar_math C, dc_char C DStrong,
   dc_width C DStrong, dc_syntax C DStrong)
  = (true, true, false, "*"%char, 1, DBare).
Proof. reflexivity. Qed.

(* Dollar-delimited math is a separate capability.  The two math spellings
   can be enabled independently, and the Markdown-like profile enables
   both. *)
Definition dollar_math_table : dtable :=
  DTable (with_dollar_math true (with_math false djot_config)) eq_refl.

Example dollar_math_independent_of_djot_math :
  (@InlineScan.parse_inline_line dollar_math_table "$x$",
   @InlineScan.parse_inline_line dollar_math_table "$`x`")
  = ([mk (Math InlineMath "x")],
     [mk (Str "$"); mk (Verbatim "x")]).
Proof. vm_compute. reflexivity. Qed.

Example dollar_math_is_off_in_djot :
  @InlineScan.parse_inline_line djot_table "$x$" = [mk (Str "$x$")].
Proof. vm_compute. reflexivity. Qed.

Example dollar_math_restored :
  @InlineScan.parse_inline_line
    (DTable (with_dollar_math true (with_dollar_math false djot_config)) eq_refl)
    "$x$"
  = [mk (Math InlineMath "x")].
Proof. vm_compute. reflexivity. Qed.

Example with_dollar_math_preserves_other_inline_settings :
  let C := with_dollar_math true (with_math false djot_config) in
  (dc_math C, dc_raw_inline C, dc_attrs C, dc_char C DStrong,
   dc_width C DStrong, dc_syntax C DStrong)
  = (false, true, true, "*"%char, 1, DBare).
Proof. reflexivity. Qed.

(* `dc_attrs` covers both things a `{` can do that are not a delimiter row:
   attach an attribute, and -- after a `]` -- open a span.  With it off each
   is the literal text it spells. *)
Definition no_attrs_table : dtable :=
  DTable (with_inline_attrs false djot_config) eq_refl.
Local Notation NoAttrsInline := (@InlineScan.parse_inline_line no_attrs_table).

Example inline_attribute_is_text :
  NoAttrsInline "x{#i .c}y" = [mk (Str "x{#i .c}y")].
Proof. vm_compute. reflexivity. Qed.

Example span_is_text :
  NoAttrsInline "[s]{.c}" = [mk (Str "[s]{.c}")].
Proof. vm_compute. reflexivity. Qed.

(* The braced delimiter rows are a separate decision, reached from the same
   `{`: with attributes off, djot's rows still read `{-x-}` as a delete. *)
Example rows_survive_inline_attrs_off :
  (NoAttrsInline "a{-b-}c", NoAttrsInline "a{#i}c")
  = ([mk (Str "a"); mk (Delete [mk (Str "b")]); mk (Str "c")],
     [mk (Str "a{#i}c")]).
Proof. vm_compute. reflexivity. Qed.

Definition inline_attrs_restored_table : dtable :=
  DTable (with_inline_attrs true (with_inline_attrs false djot_config)) eq_refl.

Example inline_attrs_restored :
  @InlineScan.parse_inline_line inline_attrs_restored_table "[s]{.c}"
  = [Node NoPos [("class", "c")] (Span [mk (Str "s")])].
Proof. vm_compute. reflexivity. Qed.

Example with_inline_attrs_preserves_other_inline_settings :
  let C := with_inline_attrs false djot_config in
  (dc_smart_typography C, dc_raw_inline C, dc_math C, dc_char C DStrong,
   dc_width C DStrong, dc_syntax C DStrong)
  = (true, true, true, "*"%char, 1, DBare).
Proof. reflexivity. Qed.

(* Delimiter rows switch off one at a time, and `disable_rows` composes
   them.  With every djot-only container off, emphasis and strong are the
   only rows left and the rest read as the text they spell. *)
Definition emph_strong_only_table : dtable :=
  DTable (disable_rows [DSuper; DSub; DMark; DInsert; DDelete; DSQuote; DDQuote]
            djot_config) eq_refl.
Local Notation EmphStrongInline :=
  (@InlineScan.parse_inline_line emph_strong_only_table).

Example disabled_rows_keep_emphasis_and_strong :
  EmphStrongInline "_a_ and *b*"
  = [mk (Emph [mk (Str "a")]); mk (Str " and ");
     mk (Strong [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

Example disabled_rows_read_literally :
  EmphStrongInline "{=a=} {+b+} {-c-} ^d^ ~e~ 'f' ""g"""
  = [mk (Str "{=a=} {+b+} {-c-} ^d^ ~e~ 'f' ""g""")].
Proof. vm_compute. reflexivity. Qed.

Example canonical_disabled_row_is_rejected :
  @ci_ok emph_strong_only_table (CIDelim DMark [CIStr "a"]) = false.
Proof. vm_compute. reflexivity. Qed.

(*
Block capabilities
------------------
*)

Example djot_profile_keeps_divs :
  parse_profile_blocks djot_profile ":::
a
:::"
  = [mk (Div [mk (Para [mk (Str "a")])])].
Proof. vm_compute. reflexivity. Qed.

Example divs_off_read_as_text :
  parse_profile_blocks (DjotWith (with_divs false djot_bconfig)) ":::
a
:::"
  = [mk (Para [mk (Str ":::"); mk SoftBreak; mk (Str "a");
               mk SoftBreak; mk (Str ":::")])].
Proof. vm_compute. reflexivity. Qed.

Example canonical_div_is_disabled :
  @cb_ok djot_table (with_divs false djot_bconfig) (CDiv [CPara [[CIStr "a"]]])
  = false.
Proof. vm_compute. reflexivity. Qed.

Example divs_restored :
  parse_profile_blocks
    (DjotWith (with_divs true (with_divs false djot_bconfig))) ":::
a
:::"
  = parse_profile_blocks djot_profile ":::
a
:::".
Proof. vm_compute. reflexivity. Qed.

(* Task recognition is also a construction gate.  Disabled mode preserves
   the complete checkbox token as ordinary bullet-item text: case and the
   separator after the box are not reconstructed from the semantic status. *)
Example task_boxes_are_literal :
  parse_profile_blocks (DjotWith (with_tasks false djot_bconfig)) "- [ ] a
- [x] b
- [X]	c"
  = [mk (BulletList Tight
           [[mk (Para [mk (Str "[ ] a")])];
            [mk (Para [mk (Str "[x] b")])];
            [mk (Para [mk (Str "[X]	c")])]])].
Proof. vm_compute. reflexivity. Qed.

Example canonical_task_list_is_disabled :
  @cb_ok djot_table (with_tasks false djot_bconfig)
    (CList (LKTask [Incomplete]) Tight [[CPara [[CIStr "a"]]]]) = false.
Proof. vm_compute. reflexivity. Qed.

Example tasks_restored :
  parse_profile_blocks
    (DjotWith (with_tasks true (with_tasks false djot_bconfig))) "- [ ] a
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

Example raw_fence_is_code :
  parse_profile_blocks (DjotWith (with_raw_blocks false djot_bconfig)) "```=html
<b>
```"
  = [mk (CodeBlock "=html" "<b>
")].
Proof. vm_compute. reflexivity. Qed.

Example canonical_raw_block_is_disabled :
  @cb_ok djot_table (with_raw_blocks false djot_bconfig) (CRaw "html" ["<b>"])
  = false.
Proof. vm_compute. reflexivity. Qed.

(* The same fence the other way round: an `=` info string is a code block's
   only when raw blocks are off. *)
Example canonical_equal_info_code_follows_raw_blocks :
  (@cb_ok djot_table (with_raw_blocks false djot_bconfig) (CCode "=html" ["<b>"]),
   @cb_ok djot_table djot_bconfig (CCode "=html" ["<b>"]))
  = (true, false).
Proof. vm_compute. reflexivity. Qed.

Example with_raw_blocks_preserves_other_block_settings :
  let K := with_raw_blocks false djot_bconfig in
  (@btables K, @bheading_continues K, @bdivs K, @btasks K)
  = (true, true, true, true).
Proof. reflexivity. Qed.

(* Definition lists are the only block capability whose gate is the closing
   projection rather than the opening one.  Recognition is untouched at both
   settings: the colon is a bullet character, the item is the same item, and
   what the capability decides is whether its content is split into a term
   and a definition. *)
Example djot_profile_keeps_definition_lists :
  parse_profile_blocks djot_profile ": t

  d"
  = [mk (DefinitionList Loose
           [([mk (Str "t")], [mk (Para [mk (Str "d")])])])].
Proof. vm_compute. reflexivity. Qed.

Example definition_list_is_a_bullet_list :
  parse_profile_blocks (DjotWith (with_deflists false djot_bconfig)) ": t

  d"
  = [mk (BulletList Loose
           [[mk (Para [mk (Str "t")]); mk (Para [mk (Str "d")])]])].
Proof. vm_compute. reflexivity. Qed.

Example canonical_deflist_follows_deflists :
  (@cb_ok djot_table (with_deflists false djot_bconfig)
     (CList LKDef Tight [[CPara [[CIStr "t"]]]]),
   @cb_ok djot_table djot_bconfig
     (CList LKDef Tight [[CPara [[CIStr "t"]]]]))
  = (false, true).
Proof. vm_compute. reflexivity. Qed.

Example with_deflists_preserves_other_block_settings :
  let K := with_deflists false djot_bconfig in
  (@btables K, @bheading_continues K, @bdivs K, @btasks K, @braw_blocks K)
  = (true, true, true, true, true).
Proof. reflexivity. Qed.

(* With block attributes off a `{...}` line opens nothing: it is paragraph
   source, and the block that followed keeps the attributes it was never
   given.  The inline layer still reads the spec, which attaches to nothing
   at the start of a paragraph; `multiline_attribute_is_prose` below turns
   that half off too. *)
Example djot_profile_keeps_block_attributes :
  parse_profile_blocks djot_profile "{#id}
para"
  = [Node NoPos [("id", "id")] (Para [mk (Str "para")])].
Proof. vm_compute. reflexivity. Qed.

Example block_attribute_is_prose :
  parse_profile_blocks (DjotWith (with_block_attrs false djot_bconfig)) "{#id}
para"
  = [mk (Para [mk SoftBreak; mk (Str "para")])].
Proof. vm_compute. reflexivity. Qed.

Example with_block_attrs_preserves_other_block_settings :
  let K := with_block_attrs false djot_bconfig in
  (@btables K, @bheading_continues K, @bdivs K, @btasks K, @braw_blocks K,
   @bdeflists K)
  = (true, true, true, true, true, true).
Proof. reflexivity. Qed.

(* Both halves together are what makes a multi-line spec read as prose: the
   block layer no longer opens it and the inline layer no longer eats the
   break, so the paragraph keeps its lines. *)
Definition no_attrs_profile : profile :=
  Profile no_attrs_table (with_block_attrs false djot_bconfig).

Example multiline_attribute_is_prose :
  parse_profile_blocks no_attrs_profile "{#i
 .c}
para"
  = [mk (Para [mk (Str "{#i"); mk SoftBreak; mk (Str ".c}");
               mk SoftBreak; mk (Str "para")])].
Proof. vm_compute. reflexivity. Qed.

(* The classifier still recognizes row-shaped source; with tables off it
   opens as ordinary paragraph text. *)
Example table_source_is_prose :
  parse_profile_blocks (DjotWith (with_tables false djot_bconfig)) "| a |
| b |"
  = [mk (Para [mk (Str "| a |"); mk SoftBreak;
               mk (Str "| b |")])].
Proof. vm_compute. reflexivity. Qed.

Example canonical_table_is_disabled :
  @cb_ok djot_table (with_tables false djot_bconfig)
    (CTable [CTBody [[CIStr "a"]]]) = false.
Proof. vm_compute. reflexivity. Qed.

(*
Footnotes: one capability across two records
--------------------------------------------

A reference nothing can define and a definition nothing can reference are
not settings anyone wants, so the knob that should be reached for is the
profile-level one.
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

Example with_footnotes_preserves_other_settings :
  let P := with_footnotes false djot_profile in
  let K := profile_block P in
  let C := @cfg (profile_inline P) in
  (@btables K, @bdivs K, @btasks K, @bdeflists K, @battrs K,
   dc_math C, dc_attrs C, dc_char C DStrong)
  = (true, true, true, true, true, true, true, "*"%char).
Proof. reflexivity. Qed.
