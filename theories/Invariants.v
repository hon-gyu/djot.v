(* ai-disclosure: autonomous *)

(** * Structural guarantees and configurable extensions

   This module packages the parser properties intended to remain true across
   admitted language profiles and proves preservation results for exported
   configuration updates.

   This bundle is deliberately narrower than "everything proved about the
   parser": its three fields say exactly that the block fold commits a prefix,
   cannot revise that commitment in response to future lines, and carries no
   hidden history beyond its explicit state.  Delimiter admissibility lives
   over a different configuration domain.  The independent block-setting
   invariant below is kept separate too: it constrains prefix overlap, not the
   fold's incremental behaviour. *)

From Stdlib Require Import String List Ascii.
From DjotV Require Import Config Ast Strings Line Parser.
Import ListNotations.
Local Open Scope string_scope.

(** ** Inline scanning

   The inline guarantees are one structural
   invariant of an admissible delimiter table.  They intentionally say no
   more than the original theorems: one unit of fuel per source byte, and no
   dependence on resolution environments while classifying source. *)
Record inline_invariants (T : dtable) : Prop := {
  inline_single_pass :
    forall s st,
      @iscan_str_fuel T (String.length s) s st =
      Some (@iscan_str T s st);
  inline_classification_locality :
    forall a b l,
      @classify_inlines T a l = @classify_inlines T b l
}.

Definition inline_structural : invariant dtable := inline_invariants.

Theorem inline_structural_holds : forall T, inline_structural T.
Proof.
  intros T. constructor.
  - exact (@iscan_str_no_reread T).
  - exact (@classify_inlines_locality T).
Qed.

(* These properties come from the scanner's control-flow shape, not from any
   row value.  Consequently every total edit of an already-admissible table
   preserves them; row compatibility is needed to construct the output
   [dtable], not to re-prove either structural guarantee. *)
Theorem dtable_knob_preserves_inline_structural :
  forall k, preserves k inline_structural.
Proof. intros k T _. apply inline_structural_holds. Qed.

(** ** Incremental block parsing

    These fields state prefix determinism, independence from future input,
    and sufficiency of the explicit parser state. *)
Record incremental_invariants (T : dtable) (K : bconfig) : Prop := {
  incremental_prefix_determinism :
    forall xs ys st,
      @parse_lines T K (xs ++ ys)%list st =
      (@committed T K xs st ++
       @parse_lines T K ys (snd (@run_lines T K xs st)))%list;
  incremental_no_future_line_dependence :
    forall xs ys ys' st,
      firstn (List.length (@committed T K xs st))
        (@parse_lines T K (xs ++ ys)%list st) =
      firstn (List.length (@committed T K xs st))
        (@parse_lines T K (xs ++ ys')%list st);
  incremental_prefix_state_suffices :
    forall xs xs' ys st,
      @run_lines T K xs st = @run_lines T K xs' st ->
      @parse_lines T K (xs ++ ys)%list st =
      @parse_lines T K (xs' ++ ys)%list st
}.

Definition block_incremental (T : dtable) : invariant bconfig :=
  incremental_invariants T.

(* These guarantees are parametric in the block configuration: they follow
   from the fold's shape, not from either decision currently stored in it. *)
Theorem block_incremental_holds :
  forall T K, block_incremental T K.
Proof.
  intros T K. constructor.
  - exact (@prefix_determinism T K).
  - exact (@no_future_line_dependence T K).
  - exact (@prefix_state_suffices T K).
Qed.

(* The two behavioural block knobs preserve the bundle without a side
   condition.  Their signatures restrict them to changing the paragraph's
   local decision; neither can change the fold or add hidden history. *)
Theorem with_marker_interrupts_preserves_incremental :
  forall T f, preserves (with_marker_interrupts f) (block_incremental T).
Proof.
  intros T f K _. apply block_incremental_holds.
Qed.

Theorem with_underline_preserves_incremental :
  forall T f, preserves (with_underline f) (block_incremental T).
Proof.
  intros T f K _. apply block_incremental_holds.
Qed.

Theorem with_tables_preserves_incremental :
  forall T enabled, preserves (with_tables enabled) (block_incremental T).
Proof.
  intros T enabled K _. apply block_incremental_holds.
Qed.

Theorem with_heading_continuation_preserves_incremental :
  forall T enabled,
    preserves (with_heading_continuation enabled) (block_incremental T).
Proof. intros T enabled K _. apply block_incremental_holds. Qed.

Theorem with_divs_preserves_incremental :
  forall T enabled, preserves (with_divs enabled) (block_incremental T).
Proof. intros T enabled K _. apply block_incremental_holds. Qed.

Theorem with_tasks_preserves_incremental :
  forall T enabled, preserves (with_tasks enabled) (block_incremental T).
Proof. intros T enabled K _. apply block_incremental_holds. Qed.

Theorem with_raw_blocks_preserves_incremental :
  forall T enabled, preserves (with_raw_blocks enabled) (block_incremental T).
Proof. intros T enabled K _. apply block_incremental_holds. Qed.

(** ** Compatibility of block-prefix choices

   The only line that can answer both block decisions is a lone dash: it is
   the bullet marker with no body, and it is also a one-character underline.
   Longer dash runs are not list markers, and equals runs are never markers.
   Keeping this invariant about the settings, rather than the order in which
   [step] asks them, makes the two decisions genuinely independent. *)
Definition block_prefix_ok (K : bconfig) : bool :=
  match @bunderline_of K "-" with
  | Some _ => negb (@binterrupt K (classify "-"))
  | None => true
  end.

Definition block_prefix_admissible : invariant bconfig :=
  fun K => block_prefix_ok K = true.

(* Each field-local edit checks only its half of the lone-dash boundary. *)
Definition bmarker_update_compatible
  (f : list lstyle -> string -> option task_marker -> string -> bool)
  (K : bconfig) : bool :=
  match @bunderline K "-"%char 1 with
  | Some _ => negb (f [SBullet "-"%char] EmptyString None EmptyString)
  | None => true
  end.

Definition bunderline_update_compatible
  (f : ascii -> nat -> option nat) (K : bconfig) : bool :=
  match f "-"%char 1 with
  | Some _ =>
      negb (@bmarker_interrupts K [SBullet "-"%char] EmptyString None EmptyString)
  | None => true
  end.

Theorem with_marker_interrupts_preserves_prefix_admissible :
  forall f,
    preserves_when
      (fun K => bmarker_update_compatible f K = true)
      (with_marker_interrupts f)
      block_prefix_admissible.
Proof.
  intros f [bm bu tables headings divs tasks raw] Hcompatible _.
  unfold block_prefix_admissible, block_prefix_ok,
    bmarker_update_compatible, with_marker_interrupts in *.
  cbn [bunderline_of binterrupt configured_list_styles configured_list_rest] in *.
  destruct tasks; exact Hcompatible.
Qed.

Theorem with_underline_preserves_prefix_admissible :
  forall f,
    preserves_when
      (fun K => bunderline_update_compatible f K = true)
      (with_underline f)
      block_prefix_admissible.
Proof.
  intros f [bm bu tables headings divs tasks raw] Hcompatible _.
  unfold block_prefix_admissible, block_prefix_ok,
    bunderline_update_compatible, with_underline in *.
  cbn [bunderline_of binterrupt configured_list_styles configured_list_rest] in *.
  destruct tasks; exact Hcompatible.
Qed.

Theorem with_tables_preserves_prefix_admissible :
  forall enabled, preserves (with_tables enabled) block_prefix_admissible.
Proof. intros enabled K H. exact H. Qed.

Theorem with_heading_continuation_preserves_prefix_admissible :
  forall enabled,
    preserves (with_heading_continuation enabled) block_prefix_admissible.
Proof. intros enabled K H. exact H. Qed.

Theorem with_divs_preserves_prefix_admissible :
  forall enabled, preserves (with_divs enabled) block_prefix_admissible.
Proof. intros enabled K H. exact H. Qed.

Theorem with_tasks_preserves_prefix_admissible :
  forall enabled, preserves (with_tasks enabled) block_prefix_admissible.
Proof.
  intros enabled [bm bu tables headings divs tasks raw] H.
  destruct enabled, tasks; exact H.
Qed.

Theorem with_raw_blocks_preserves_prefix_admissible :
  forall enabled, preserves (with_raw_blocks enabled) block_prefix_admissible.
Proof. intros enabled K H. exact H. Qed.

Example djot_prefix_admissible : block_prefix_ok djot_bconfig = true.
Proof. reflexivity. Qed.

Example sublist_prefix_admissible : block_prefix_ok sublist_bconfig = true.
Proof. reflexivity. Qed.

Example setext_prefix_admissible : block_prefix_ok setext_bconfig = true.
Proof. reflexivity. Qed.

Example markdown_prefix_admissible : block_prefix_ok markdown_bconfig = true.
Proof. reflexivity. Qed.

Example lone_dash_overlap_rejected :
  block_prefix_ok
    (with_underline (fun _ _ => Some 0) sublist_bconfig) = false.
Proof. reflexivity. Qed.

(*
Accidental-list immunity
------------------------

An interrupting ordered marker is safe in ordinary prose only at the
conventional list start [1].  Bullets have an empty core and are unambiguous;
every other nonempty core includes years, initials, and other text that may
legitimately begin a continuation line.  State the boundary over the marker
policy itself, so it is independent of parser state and can be checked before
installing the knob. *)
Definition marker_interrupt_precondition
  (f : list lstyle -> string -> option task_marker -> string -> bool) : Prop :=
  forall sty core chk rest,
    f sty core chk rest = true ->
    prose_safe_markers sty core chk rest = true.

Definition accidental_list_immune : invariant bconfig :=
  fun K => marker_interrupt_precondition (@bmarker_interrupts K).

(* This is the extracted weakest precondition for the field-local update:
   because [with_marker_interrupts] replaces exactly this field, the updated
   configuration has the property iff the replacement policy satisfies the
   local condition. *)
Theorem with_marker_interrupts_accidental_list_immune_iff :
  forall f K,
    accidental_list_immune (with_marker_interrupts f K) <->
    marker_interrupt_precondition f.
Proof. reflexivity. Qed.

Theorem with_marker_interrupts_preserves_accidental_list_immunity :
  forall f,
    preserves_when
      (fun _ => marker_interrupt_precondition f)
      (with_marker_interrupts f)
      accidental_list_immune.
Proof. intros f K Hsafe _. exact Hsafe. Qed.

Theorem prose_safe_markers_is_immune :
  marker_interrupt_precondition prose_safe_markers.
Proof. intros sty core chk rest H. exact H. Qed.

(* [prose_safe_markers] is the maximally permissive immune policy: every
   policy satisfying the property is pointwise below it. *)
Theorem prose_safe_markers_maximal :
  forall f,
    marker_interrupt_precondition f ->
    forall sty core chk rest,
      f sty core chk rest = true ->
      prose_safe_markers sty core chk rest = true.
Proof. intros f Hsafe sty core chk rest H. exact (Hsafe _ _ _ _ H). Qed.

Example djot_accidental_list_immune :
  accidental_list_immune djot_bconfig.
Proof. intros sty core chk rest H. discriminate H. Qed.

Example sublist_accidental_list_immune :
  accidental_list_immune sublist_bconfig.
Proof. exact prose_safe_markers_is_immune. Qed.

Example unrestricted_markers_are_not_accidental_list_immune :
  ~ marker_interrupt_precondition (fun _ _ _ _ => true).
Proof.
  intros H.
  specialize (H [SOrd Decimal RightPeriod] "1865" None "x" eq_refl).
  vm_compute in H. discriminate H.
Qed.

(*
Hard wrapping
-------------

Djot's rationale asks that a paragraph survive being re-wrapped: moving a
line break must not turn a continuation line into a list, a heading, a
quote or a thematic break.  The parser asks one question of a continuation
line, [bcuts], and the two settings it reads are the two fields below.  A
configuration answering "no" on both cannot let any line shape reach the
block layer from inside a paragraph.

The condition is on the *fields* rather than on [bcuts] itself.  Stated
the derived way it would be a claim about the lines each setting can
reach, and [with_tasks] changes which argument tuples [bmarker_interrupts]
is asked about -- so the eight settings that touch neither field would
each need an argument instead of copying the hypothesis.  Nothing is lost:
a setting that never fires is spelled as one that never fires.  This is
[accidental_list_immunity] taken to its limit, and it implies it. *)
Definition wrap_neutral : invariant bconfig := fun K =>
  (forall sty core chk rest,
     @bmarker_interrupts K sty core chk rest = false)
  /\ (forall c n, @bunderline K c n = None).

Lemma wrap_neutral_bcuts :
  forall K, wrap_neutral K -> forall l, @bcuts K l = false.
Proof.
  intros K [Hm Hu] l. unfold bcuts, bunderline_of.
  destruct (underline_of l) as [[c n]|]; [rewrite Hu|]; unfold binterrupt;
    destruct (classify l); try reflexivity; apply Hm.
Qed.

Lemma wrap_neutral_accidental_list_immune :
  forall K, wrap_neutral K -> accidental_list_immune K.
Proof. intros K [Hm _] sty core chk rest H. rewrite Hm in H. discriminate. Qed.

(* The property itself: a text line and any run of nonblank lines after it
   are one paragraph, whatever those lines look like. *)
Theorem hard_wrap_one_para :
  forall T K, wrap_neutral K ->
  forall a ls,
    classify a = KText ->
    forallb nonblank ls = true ->
    @parse_lines T K (a :: ls) (PPara []) =
    [mk (Para (@para_inlines T (map drop_leading_ws (a :: ls))))].
Proof.
  intros T K Hn a ls Ha Hls.
  apply parse_lines_para_run; try assumption;
    [apply (wrap_neutral_bcuts _ Hn)|].
  apply forallb_forall. intros x _.
  rewrite (wrap_neutral_bcuts _ Hn). reflexivity.
Qed.

(* And the run reaches nothing after it: the blank line that ends the
   paragraph leaves the parser idle, so the document past it is parsed
   from the state it would have had anyway. *)
Theorem hard_wrap_para_then_rest :
  forall T K, wrap_neutral K ->
  forall a ls b rest,
    classify a = KText ->
    forallb nonblank ls = true ->
    is_blank b = true ->
    @parse_lines T K ((a :: ls) ++ b :: rest)%list (PPara []) =
    mk (Para (@para_inlines T (map drop_leading_ws (a :: ls))))
    :: @parse_lines T K rest (PPara []).
Proof.
  intros T K Hn a ls b rest Ha Hls Hb.
  apply parse_lines_para_run_blank; try assumption;
    [apply (wrap_neutral_bcuts _ Hn)|].
  apply forallb_forall. intros x _.
  rewrite (wrap_neutral_bcuts _ Hn). reflexivity.
Qed.

(* The two field-local settings are the only ones that can lose the
   property, and each has its own weakest precondition. *)
Theorem with_marker_interrupts_preserves_wrap_neutral :
  forall f,
    preserves_when
      (fun _ => forall sty core chk rest, f sty core chk rest = false)
      (with_marker_interrupts f) wrap_neutral.
Proof. intros f K Hf [_ Hu]. split; [exact Hf | exact Hu]. Qed.

Theorem with_underline_preserves_wrap_neutral :
  forall f,
    preserves_when (fun _ => forall c n, f c n = None)
      (with_underline f) wrap_neutral.
Proof. intros f K Hf [Hm _]. split; [exact Hm | exact Hf]. Qed.

(* Every other setting copies both fields, so it preserves the property
   with no side condition -- including [with_tasks], which is why the
   condition is on the fields. *)
Theorem with_tables_preserves_wrap_neutral :
  forall enabled, preserves (with_tables enabled) wrap_neutral.
Proof. intros enabled K H. exact H. Qed.

Theorem with_heading_continuation_preserves_wrap_neutral :
  forall enabled, preserves (with_heading_continuation enabled) wrap_neutral.
Proof. intros enabled K H. exact H. Qed.

Theorem with_divs_preserves_wrap_neutral :
  forall enabled, preserves (with_divs enabled) wrap_neutral.
Proof. intros enabled K H. exact H. Qed.

Theorem with_tasks_preserves_wrap_neutral :
  forall enabled, preserves (with_tasks enabled) wrap_neutral.
Proof. intros enabled K H. exact H. Qed.

Theorem with_raw_blocks_preserves_wrap_neutral :
  forall enabled, preserves (with_raw_blocks enabled) wrap_neutral.
Proof. intros enabled K H. exact H. Qed.

Theorem with_deflists_preserves_wrap_neutral :
  forall enabled, preserves (with_deflists enabled) wrap_neutral.
Proof. intros enabled K H. exact H. Qed.

Theorem with_block_attrs_preserves_wrap_neutral :
  forall enabled, preserves (with_block_attrs enabled) wrap_neutral.
Proof. intros enabled K H. exact H. Qed.

Theorem with_block_footnotes_preserves_wrap_neutral :
  forall enabled, preserves (with_block_footnotes enabled) wrap_neutral.
Proof. intros enabled K H. exact H. Qed.

Example djot_wrap_neutral : wrap_neutral djot_bconfig.
Proof. split; reflexivity. Qed.

(* The five shapes the rationale names, all as continuation lines. *)
Example djot_wrap_keeps_one_block :
  List.length (@parse_blocks djot_table djot_bconfig
    "text
- item
# not a heading
> not a quote
***
1. not a list
") = 1.
Proof. vm_compute. reflexivity. Qed.

(* The Markdown-facing profile is deliberately not wrap-neutral: it sets
   both fields, and a bullet on a continuation line ends the paragraph. *)
Example markdown_wrap_splits :
  List.length (@parse_blocks djot_table markdown_bconfig "text
- item
") = 2.
Proof. vm_compute. reflexivity. Qed.

(*
What wrap-neutrality does not say
---------------------------------

Only the block structure is fixed.  The paragraph's *content* is
[para_inlines] of its lines, and a line break is not a space there: a
verbatim span keeps the newline, a trailing backslash makes the break
hard, and whitespace before a break survives into the preceding [Str].
So a re-wrap that moves a break across any of these three changes the
inlines, and no statement above says otherwise.  These are the witnesses;
they are expected to keep failing. *)
Example wrap_moves_verbatim_content :
  @para_inlines djot_table ["`a"; "b`"] <> @para_inlines djot_table ["`a b`"].
Proof. intros H. vm_compute in H. discriminate. Qed.

Example wrap_moves_hard_break :
  @para_inlines djot_table ["a\"; "b"] <> @para_inlines djot_table ["a\ b"].
Proof. intros H. vm_compute in H. discriminate. Qed.

Example wrap_moves_trailing_space :
  @para_inlines djot_table ["a  "; "b"] <> @para_inlines djot_table ["a   b"].
Proof. intros H. vm_compute in H. discriminate. Qed.

(*
Where a setting is read
-----------------------

Each block setting should have an effect, and a bounded sphere of
effect.  The effect is a document whose parse changes when the setting
is turned off; the bound is that the setting is read in one named place
and is invisible everywhere else the fold looks at the configuration.

The fold reads the configuration through `open_line` (which covers
`open_kind`, `open_attr`, `open_foot` and the list-marker projections),
through `bunderline_of` and `binterrupt`, through `bheading_continues`,
and through `finish` and `fence_block`.  The eight boolean settings
divide over those: five cannot change what a line opens, five cannot
change what a state closes to, and the two that reach neither are read
only at a raw fence and at a colon bullet.

This is locality per query, not per document.  The document-level
statement -- a source with no row line anywhere parses identically with
tables off -- needs a predicate saying the trigger kind arises at no
depth of the container descent, and `step`'s descent is what would have
to carry it.  See .project/260901.knob-isolation.md. *)

Theorem with_tables_opens_only_rows :
  forall enabled K descend ind l k,
    (forall r, k <> KRow r) ->
    @open_line (with_tables enabled K) descend ind l k
    = @open_line K descend ind l k.
Proof.
  intros enabled K descend ind l k H.
  destruct k; try reflexivity. exfalso. eapply H. reflexivity.
Qed.

Theorem with_divs_opens_only_divs :
  forall enabled K descend ind l k,
    (forall len cls, k <> KDiv len cls) ->
    @open_line (with_divs enabled K) descend ind l k
    = @open_line K descend ind l k.
Proof.
  intros enabled K descend ind l k H.
  destruct k; try reflexivity. exfalso. eapply H. reflexivity.
Qed.

Theorem with_block_attrs_opens_only_attrs :
  forall enabled K descend ind l k,
    (forall ap, k <> KAttr ap) ->
    @open_line (with_block_attrs enabled K) descend ind l k
    = @open_line K descend ind l k.
Proof.
  intros enabled K descend ind l k H.
  destruct k; try reflexivity. exfalso. eapply H. reflexivity.
Qed.

Theorem with_block_footnotes_opens_only_footnotes :
  forall enabled K descend ind l k,
    (forall lbl rest, k <> KFoot lbl rest) ->
    @open_line (with_block_footnotes enabled K) descend ind l k
    = @open_line K descend ind l k.
Proof.
  intros enabled K descend ind l k H.
  destruct k; try reflexivity. exfalso. eapply H. reflexivity.
Qed.

Theorem with_tasks_opens_only_lists :
  forall enabled K descend ind l k,
    (forall sty core chk rest, k <> KList sty core chk rest) ->
    @open_line (with_tasks enabled K) descend ind l k
    = @open_line K descend ind l k.
Proof.
  intros enabled K descend ind l k H.
  destruct k; try reflexivity. exfalso. eapply H. reflexivity.
Qed.

(* The other three cannot change what any line opens, at any kind. *)
Theorem with_deflists_opens_nothing :
  forall enabled K descend ind l k,
    @open_line (with_deflists enabled K) descend ind l k
    = @open_line K descend ind l k.
Proof. intros enabled K descend ind l k. destruct k; reflexivity. Qed.

Theorem with_raw_blocks_opens_nothing :
  forall enabled K descend ind l k,
    @open_line (with_raw_blocks enabled K) descend ind l k
    = @open_line K descend ind l k.
Proof. intros enabled K descend ind l k. destruct k; reflexivity. Qed.

Theorem with_heading_continuation_opens_nothing :
  forall enabled K descend ind l k,
    @open_line (with_heading_continuation enabled K) descend ind l k
    = @open_line K descend ind l k.
Proof. intros enabled K descend ind l k. destruct k; reflexivity. Qed.

(* The other half: what a state closes to.  `finish` reads the
   configuration only through the two block builders that have a
   configured arm. *)
Lemma finish_config_ext :
  forall T K1 K2,
    (forall f content, @fence_block K1 f content = @fence_block K2 f content) ->
    (forall ls items, @list_block K1 ls items = @list_block K2 ls items) ->
    forall st, @finish T K1 st = @finish T K2 st.
Proof.
  intros T K1 K2 Hf Hl st.
  induction st; cbn [finish]; try reflexivity;
    try (rewrite IHst; try rewrite Hl; reflexivity).
  rewrite Hf. reflexivity.
Qed.

Theorem with_tables_finishes_nothing :
  forall T enabled K st, @finish T (with_tables enabled K) st = @finish T K st.
Proof. intros T enabled K. apply finish_config_ext; reflexivity. Qed.

Theorem with_divs_finishes_nothing :
  forall T enabled K st, @finish T (with_divs enabled K) st = @finish T K st.
Proof. intros T enabled K. apply finish_config_ext; reflexivity. Qed.

Theorem with_block_attrs_finishes_nothing :
  forall T enabled K st,
    @finish T (with_block_attrs enabled K) st = @finish T K st.
Proof. intros T enabled K. apply finish_config_ext; reflexivity. Qed.

Theorem with_block_footnotes_finishes_nothing :
  forall T enabled K st,
    @finish T (with_block_footnotes enabled K) st = @finish T K st.
Proof. intros T enabled K. apply finish_config_ext; reflexivity. Qed.

Theorem with_heading_continuation_finishes_nothing :
  forall T enabled K st,
    @finish T (with_heading_continuation enabled K) st = @finish T K st.
Proof. intros T enabled K. apply finish_config_ext; reflexivity. Qed.

(* The two settings that reach neither opening nor closing: each has one
   arm, and it is guarded by the construct's own spelling. *)
Theorem with_raw_blocks_only_at_raw_fences :
  forall enabled K f content,
    (forall fmt, f_info f <> String "="%char fmt) ->
    @fence_block (with_raw_blocks enabled K) f content = @fence_block K f content.
Proof.
  intros enabled K f content H. unfold fence_block.
  destruct (f_info f) as [|c rest] eqn:E; [reflexivity|].
  destruct (Ascii.eqb c "="%char) eqn:Ec.
  - apply Ascii.eqb_eq in Ec. subst c. exfalso. apply (H rest). reflexivity.
  - destruct c as [b0 b1 b2 b3 b4 b5 b6 b7];
      destruct b0, b1, b2, b3, b4, b5, b6, b7; try reflexivity; discriminate Ec.
Qed.

Theorem with_deflists_only_at_colon_bullets :
  forall enabled K S sp items,
    (forall n rest, S <> ((SBullet ":"%char), n) :: rest) ->
    @styles_list (with_deflists enabled K) S sp items
    = @styles_list K S sp items.
Proof.
  intros enabled K S sp items H.
  destruct S as [|[sty n] rest]; [reflexivity|].
  destruct sty; try reflexivity.
  cbn [styles_list]. destruct (Ascii.eqb c ":"%char) eqn:Ec; cbn [andb].
  - apply Ascii.eqb_eq in Ec. subst c. exfalso. eapply H. reflexivity.
  - reflexivity.
Qed.

(*
That each setting has an effect
-------------------------------

One document per setting, parsed with Djot's answers and with that one
answer taken away.  A setting whose witness stopped failing would be a
setting the parser had stopped reading. *)
Definition djot_off (k : bool -> bconfig -> bconfig) : bconfig :=
  k false djot_bconfig.

Example tables_have_an_effect :
  @parse_blocks djot_table djot_bconfig "| a |
" <> @parse_blocks djot_table (djot_off with_tables) "| a |
".
Proof. intros H. vm_compute in H. discriminate. Qed.

Example divs_have_an_effect :
  @parse_blocks djot_table djot_bconfig ":::
x
:::
" <> @parse_blocks djot_table (djot_off with_divs) ":::
x
:::
".
Proof. intros H. vm_compute in H. discriminate. Qed.

Example block_attrs_have_an_effect :
  @parse_blocks djot_table djot_bconfig "{#i}
para
" <> @parse_blocks djot_table (djot_off with_block_attrs) "{#i}
para
".
Proof. intros H. vm_compute in H. discriminate. Qed.

Example block_footnotes_have_an_effect :
  @parse_blocks djot_table djot_bconfig "[^1]: note
" <> @parse_blocks djot_table (djot_off with_block_footnotes) "[^1]: note
".
Proof. intros H. vm_compute in H. discriminate. Qed.

Example tasks_have_an_effect :
  @parse_blocks djot_table djot_bconfig "- [ ] x
" <> @parse_blocks djot_table (djot_off with_tasks) "- [ ] x
".
Proof. intros H. vm_compute in H. discriminate. Qed.

Example deflists_have_an_effect :
  @parse_blocks djot_table djot_bconfig ": term

  def
" <> @parse_blocks djot_table (djot_off with_deflists) ": term

  def
".
Proof. intros H. vm_compute in H. discriminate. Qed.

Example raw_blocks_have_an_effect :
  @parse_blocks djot_table djot_bconfig "```=html
<b>
```
" <> @parse_blocks djot_table (djot_off with_raw_blocks) "```=html
<b>
```
".
Proof. intros H. vm_compute in H. discriminate. Qed.

Example heading_continuation_has_an_effect :
  @parse_blocks djot_table djot_bconfig "# a
# b
" <> @parse_blocks djot_table (djot_off with_heading_continuation) "# a
# b
".
Proof. intros H. vm_compute in H. discriminate. Qed.
