(* ai-disclosure: autonomous *)

(** * The properties, and which of them a profile keeps

   One record per property.  The words in it are what the README and the
   site print.  [p_status] says what is claimed of a profile, [p_holds]
   states the property for that profile, and [p_sound] proves the
   statement wherever the status claims it.

   So a status is not free text.  A row that claims a property of every
   profile carries a proof for every profile, and stops compiling when
   the theorem behind it gains a hypothesis about the profile.

   [p_holds] states the row's main theorem.  [p_theorems] also names the
   variants and the lemmas a reader may want; those are names only. *)

From Stdlib Require Import String List Ascii Bool.
From DjotV Require Import Ast Strings Line InlineTable Inline InlineScan Step
  Uniformity ListUniformity OrderedList Tightness Render Roundtrip Reparse
  Document Html Invariants BlockShape InlinePrecedence Precedence Profile
  ProfileChecks.
Import ListNotations.
Local Open Scope string_scope.

Inductive status : Type :=
  | Proved
  (* Holds under the stated condition on the document. *)
  | Conditional (condition : string)
  (* Fails; [example] is a source that shows it. *)
  | Broken (reason example : string)
  (* Believed to hold; not proved for this profile. *)
  | Conjectured
  | Unknown
  (* The construct the property is about is off. *)
  | Inapplicable (why : string).

(* The word a status is shown as. *)
Definition status_name (s : status) : string :=
  match s with
  | Proved => "proved"
  | Conditional _ => "conditional"
  | Broken _ _ => "broken"
  | Conjectured => "conjectured"
  | Unknown => "unknown"
  | Inapplicable _ => "inapplicable"
  end.

Definition claimed (s : status) : bool :=
  match s with Proved | Conditional _ => true | _ => false end.

Record property : Type := Property {
  p_id : string;
  p_group : string;
  p_statement : string;
  p_implication : string;
  p_theorems : list string;
  p_status : options -> status;
  p_holds : options -> Prop;
  p_sound : forall o, claimed (p_status o) = true -> p_holds o
}.

(*
The statements
--------------

Each is the conclusion of its theorem, at any inline table and block
configuration.  A hypothesis about the profile is left out here: the
row's status is what discharges it.
*)

Section Statements.
Context (T : dtable) (K : bconfig).

Definition block_no_backtracking : Prop :=
  forall xs ys st,
    parse_lines (xs ++ ys)%list st
    = (committed xs st ++ parse_lines ys (snd (run_lines xs st)))%list.

Definition inline_no_backtracking : Prop :=
  forall s st, iscan_str_fuel (String.length s) s st = Some (iscan_str s st).

Definition incremental_reparse : Prop :=
  forall xs xs' ys st,
    run_lines xs st = run_lines xs' st ->
    parse_lines (xs ++ ys)%list st = parse_lines (xs' ++ ys)%list st.

Definition block_replace_holds : Prop :=
  forall pre new post,
    cblocks_ok (pre ++ new :: post)%list = true ->
    parse_blocks (render_djot (blocks_of_cblocks (pre ++ new :: post)))
    = (map cb_ast pre ++ cb_ast new :: map cb_ast post)%list.

Definition positions : Prop :=
  forall s, erase_doc (parse_doc_located s) = @parse_doc T K semantic_pos s.

Definition quote_uniform_holds : Prop :=
  forall l lines,
    parse_lines (map (fun x => "> " ++ x) (l :: lines)) (PPara [])
    = [mk (BlockQuote (parse_lines (l :: lines) (PPara [])))].

Definition list_uniform : Prop :=
  forall m0 sp L0 tail,
    marker_ok m0 = true ->
    items_ok m0 ((m0, L0) :: tail) = true ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: tail))) (PPara [])
    = [marker_list_checked m0 (list_spacing_of sp (map snd ((m0, L0) :: tail)))
         (map (fun it => mk_check (fst it)) ((m0, L0) :: tail))
         (map (fun it => parse_lines (snd it) (PPara [])) ((m0, L0) :: tail))].

Definition definition_list_uniform : Prop :=
  forall sp lss,
    lss <> [] ->
    forallb (item_ok colon) lss = true ->
    parse_lines (list_lines sp (map litem_lines (same_marker colon lss)))
      (PPara [])
    = [mk (DefinitionList (list_spacing_of sp lss)
             (def_items (map (fun L => parse_lines L (PPara [])) lss)))].

Definition div_uniform : Prop :=
  forall word content,
    div_word_ok word = true ->
    div_content_ok content = true ->
    parse_lines (div_open_line div_fence word :: content ++ [div_fence])%list
      (PPara [])
    = [div_block word (parse_lines content (PPara []))].

Definition footnote_uniform : Prop :=
  forall lines range ind lbl done inner,
    forallb (fun l => (is_blank l || Nat.ltb ind (indent_of l))%bool) lines
    = true ->
    parse_lines lines (PFoot range ind lbl done inner)
    = [foot_block lbl (rev done ++ parse_lines lines inner)%list].

(* [every] says the underline condition is not needed. *)
Definition lazy_lines (every : bool) : Prop :=
  forall l st,
    lazy_stack st -> classify l = KText ->
    (if every then True else bunderline_of l = None) ->
    step l st = ([], feed_lazy l st)
    /\ step (spine_prefix 0 st ++ l) st = step l st.

Definition list_tightness : Prop :=
  forall sp itemss,
    forallb (fun L => run_safe L (PPara []) && negb (is_blank (hd "" L)))
      itemss = true ->
    list_spacing_of sp itemss = Loose ->
    (exists L, In L itemss /\ exists i, separates L i)
    \/ (sp = Loose
        /\ exists pre L M post,
             itemss = (pre ++ L :: M :: post)%list /\ separates_after L).

Definition indent_uniform : Prop :=
  forall p lines,
    is_blank p = true ->
    specs_closed lines (PPara []) = true ->
    parse_lines (map (fun l => p ++ l) lines) (PPara [])
    = parse_lines lines (PPara []).

Definition reference_locality : Prop :=
  forall a b l, classify_inlines a l = classify_inlines b l.

Definition hard_wrap_paragraph : Prop :=
  forall a ls,
    classify a = KText ->
    forallb nonblank ls = true ->
    parse_lines (a :: ls) (PPara [])
    = [mk (Para (para_inlines (map drop_leading_ws (a :: ls))))].

Definition hard_wrap_heading : Prop :=
  forall lvl ls b rest rng cur,
    touch_extent rng = rng ->
    forallb (fun l => match classify l with KText => true | _ => false end) ls
    = true ->
    classify b = KBlank ->
    parse_lines (ls ++ b :: rest)%list (PHeading lvl rng cur)
    = (heading_block lvl
         (remember_lines (rev (map drop_leading_ws ls)) ++ cur)%list
       :: parse_lines rest (PPara []))%list.

Definition block_structure_first : Prop :=
  forall (T' : dtable) (LI : LineIx) (P : PosPolicy) s,
    Shape.of_blocks (@parse_blocks T K LI P s)
    = Shape.of_blocks (@parse_blocks T' K LI P s).

Definition inline_precedence : Prop :=
  forall ls m os,
    Forall (fun x => over_alphabet x = true) ls ->
    valid (para_tokens ls) (m, os) ->
    para_inlines ls = tree_of (para_tokens ls) m.

End Statements.

Definition reference_shape : Prop :=
  forall bs refs refs',
    map erase_helt_attrs (render_blocks refs bs)
    = map erase_helt_attrs (render_blocks refs' bs).

(*
The rows
--------
*)

Local Notation at_profile P := (fun o => P (o_inline o) (bconfig_of o)).
Local Definition always (s : status) (_ : options) : status := s.

Local Definition no_backtracking := "No backtracking".
Local Definition uniformity := "Container uniformity".
Local Definition local := "Local interpretation".
Local Definition wrapping := "Safe hard-wrapping".
Local Definition structure := "Block structure first".
Local Definition precedence := "Inline precedence".

Program Definition p_block_no_backtracking : property := {|
  p_id := "block-no-backtracking";
  p_group := no_backtracking;
  p_statement := "A later line never changes a block already parsed.";
  p_implication := "Blocks can be emitted as lines arrive.";
  p_theorems := ["prefix_determinism"; "no_future_line_dependence"];
  p_status := always Proved;
  p_holds := at_profile block_no_backtracking
|}.
Next Obligation. exact (@prefix_determinism _ _). Qed.

Program Definition p_inline_no_backtracking : property := {|
  p_id := "inline-no-backtracking";
  p_group := no_backtracking;
  p_statement := "Each byte of a paragraph is read once.";
  p_implication := "An unclosed * or [ never forces a rescan.";
  p_theorems := ["iscan_str_no_reread"];
  p_status := always Proved;
  p_holds := fun o => inline_no_backtracking (o_inline o)
|}.
Next Obligation. exact (@iscan_str_no_reread _). Qed.

Program Definition p_incremental_reparse : property := {|
  p_id := "incremental-reparse";
  p_group := no_backtracking;
  p_statement := "After an edit, reparsing can stop once the parser is back in the state it had before the edit.";
  p_implication := "An editor reparses the changed region and reuses the rest.";
  p_theorems := ["prefix_state_suffices"; "reparse_only_new"];
  p_status := always Proved;
  p_holds := at_profile incremental_reparse
|}.
Next Obligation. exact (@prefix_state_suffices _ _). Qed.

Program Definition p_block_replace : property := {|
  p_id := "block-replace";
  p_group := no_backtracking;
  p_statement := "Replacing one block leaves the parse of every other block unchanged.";
  p_implication := "An edit's effect stays within the block it touches.";
  p_theorems := ["block_replace"; "replace_at_id_parse"];
  p_status := always Proved;
  p_holds := at_profile block_replace_holds
|}.
Next Obligation. exact (@block_replace _ _). Qed.

Program Definition p_positions : property := {|
  p_id := "positions";
  p_group := no_backtracking;
  p_statement := "Recording source positions does not change the parse.";
  p_implication := "A tool that needs positions gets the same tree as everyone else.";
  p_theorems := ["parse_blocks_located_erase"; "parse_doc_located_erase"];
  p_status := always Proved;
  p_holds := at_profile positions
|}.
Next Obligation. exact (@parse_doc_located_erase _ _). Qed.

Program Definition p_linear_time : property := {|
  p_id := "linear-time";
  p_group := no_backtracking;
  p_statement := "Parsing takes linear time.";
  p_implication := "Reading each byte once does not give this: one byte can do work proportional to the number of open delimiters.";
  p_theorems := [];
  p_status := always Conjectured;
  p_holds := fun _ => True
|}.

Program Definition p_quote_uniformity : property := {|
  p_id := "quote-uniformity";
  p_group := uniformity;
  p_statement := "Text inside a block quote parses as it would at top level.";
  p_implication := "Moving text into or out of a quote does not change its meaning.";
  p_theorems := ["quote_uniformity"; "quote_uniform_sound"];
  p_status := fun o =>
    if quote_uniform o then Proved
    else Broken
      "A quote whose first line is a callout header is a callout, and the header is not part of its content."
      "> [!note] Title
> body
";
  p_holds := at_profile quote_uniform_holds
|}.
Next Obligation.
  intros l lines. apply quote_uniformity. apply quote_uniform_sound.
  destruct (quote_uniform o); [reflexivity | discriminate H].
Qed.

Program Definition p_list_uniformity : property := {|
  p_id := "list-uniformity";
  p_group := uniformity;
  p_statement := "Text inside an item of a bullet or ordered list parses as it would at top level, when indented the way the formatter writes it.";
  p_implication := "Moving text into or out of a list item does not change its meaning.";
  p_theorems := ["list_uniformity"; "ordered_uniformity"];
  p_status := always Proved;
  p_holds := at_profile list_uniform
|}.
Next Obligation. exact (@list_uniformity _ _). Qed.

Program Definition p_definition_list_uniformity : property := {|
  p_id := "definition-list-uniformity";
  p_group := uniformity;
  p_statement := "The same, for the items of a definition list.";
  p_implication := "Moving text into or out of a definition does not change its meaning.";
  p_theorems := ["definition_list_uniformity"];
  p_status := fun o =>
    if o_deflists o then Proved else Inapplicable "Definition lists are off";
  p_holds := at_profile definition_list_uniform
|}.
Next Obligation.
  intros sp lss. apply definition_list_uniformity. cbn.
  destruct (o_deflists o); [reflexivity | discriminate H].
Qed.

Program Definition p_div_uniformity : property := {|
  p_id := "div-uniformity";
  p_group := uniformity;
  p_statement := "Text inside a fenced div parses as it would at top level, unless it contains the div's own closing fence.";
  p_implication := "Moving text into or out of a div does not change its meaning.";
  p_theorems := ["div_uniformity"; "div_uniformity_tail"];
  p_status := fun o => if o_divs o then Proved else Inapplicable "Divs are off";
  p_holds := at_profile div_uniform
|}.
Next Obligation.
  intros word content. apply div_uniformity. cbn.
  destruct (o_divs o); [reflexivity | discriminate H].
Qed.

Program Definition p_footnote_uniformity : property := {|
  p_id := "footnote-uniformity";
  p_group := uniformity;
  p_statement := "Lines indented under a footnote belong to it, cannot affect anything outside it, and parse as they would at top level.";
  p_implication := "Moving text into a footnote does not change its meaning.";
  p_theorems := ["footnote_content_uniformity"; "footnote_text_uniformity";
                 "footnote_list_shift_counterexample"];
  p_status := fun o =>
    if dc_footnotes (@cfg (o_inline o))
    then Conditional "Not when the footnote's first line starts a list: the indentation of the following items is measured from the footnote marker."
    else Inapplicable "Footnotes are off";
  p_holds := at_profile footnote_uniform
|}.
Next Obligation. exact (@footnote_content_uniformity _ _). Qed.

Program Definition p_lazy_lines : property := {|
  p_id := "lazy-lines";
  p_group := uniformity;
  p_statement := "A text line that continues a paragraph may leave out the prefixes of the quotes, list items and footnotes around it, and parses as it would with them written.";
  p_implication := "Leaving out a prefix on such a line does not change the document.";
  p_theorems := ["lazy_stack_line"; "step_lazy"; "lazy_line_restore";
                 "lazy_uniform_sound"];
  p_status := fun o =>
    if lazy_uniform o then Proved
    else Conditional "Not for a line that underlines the paragraph: it makes a setext heading.";
  p_holds := fun o => lazy_lines (o_inline o) (bconfig_of o) (lazy_uniform o)
|}.
Next Obligation.
  intros l st Hs Ht Hu. apply lazy_stack_line; try assumption.
  destruct (lazy_uniform o) eqn:E; [apply (lazy_uniform_sound o E) | exact Hu].
Qed.

Program Definition p_list_tightness : property := {|
  p_id := "list-tightness";
  p_group := uniformity;
  p_statement := "A list is loose only where a blank line separates two of its items, or two blocks inside one item.";
  p_implication := "Whether a list renders with space between its items follows from where its blank lines are.";
  p_theorems := ["list_spacing_separates"];
  p_status := always (Conditional "One direction: a list the parser calls loose has such a blank line.");
  p_holds := at_profile list_tightness
|}.
Next Obligation. exact (@list_spacing_separates _ _). Qed.

Program Definition p_indent_uniformity : property := {|
  p_id := "indent-uniformity";
  p_group := uniformity;
  p_statement := "Indenting every line of a document by the same amount does not change its parse.";
  p_implication := "A document pasted at some indentation means the same thing.";
  p_theorems := ["indent_uniformity"];
  p_status := always (Conditional "As long as no block attribute spans several lines.");
  p_holds := at_profile indent_uniform
|}.
Next Obligation. exact (@indent_uniformity _ _). Qed.

Program Definition p_reference_locality : property := {|
  p_id := "reference-locality";
  p_group := local;
  p_statement := "Whether [foo][bar] is a link does not depend on whether bar is defined.";
  p_implication := "Inline syntax can be read from the paragraph alone.";
  p_theorems := ["classify_inlines_locality"];
  p_status := always Proved;
  p_holds := fun o => reference_locality (o_inline o)
|}.
Next Obligation. exact (@classify_inlines_locality _). Qed.

Program Definition p_reference_shape : property := {|
  p_id := "reference-shape";
  p_group := local;
  p_statement := "Adding, removing or changing a reference definition changes only link and image attributes in the HTML.";
  p_implication := "Resolving references never restructures the document.";
  p_theorems := ["render_blocks_reference_shape"];
  p_status := always Proved;
  p_holds := fun _ => reference_shape
|}.
Next Obligation. exact render_blocks_reference_shape. Qed.

Program Definition p_hard_wrap_paragraph : property := {|
  p_id := "hard-wrap-paragraph";
  p_group := wrapping;
  p_statement := "A line inside a paragraph never starts a new block.";
  p_implication := "Hard-wrapping a paragraph cannot create a list, heading or quote by accident.";
  p_theorems := ["hard_wrap_one_para"; "hard_wrap_para_then_rest";
                 "wrap_safe_iff"; "wrap_cut_list"; "wrap_cut_setext"];
  p_status := fun o =>
    if wrap_safe o then Proved
    else if o_list_interrupts o then
      Broken "A line that begins with a list marker starts a list."
        "A paragraph wrapped so that the next line starts with
- a hyphen.
"
    else if o_setext o then
      Broken "A line of = or - under a paragraph makes it a heading."
        "A paragraph wrapped before
===
"
    else
      Broken "A text line with a key is a keyed block, not a paragraph."
        "note: a paragraph
that goes on
";
  p_holds := at_profile hard_wrap_paragraph
|}.
Next Obligation.
  intros a ls. apply hard_wrap_one_para. apply wrap_safe_iff.
  destruct (wrap_safe o); [reflexivity|].
  destruct (o_list_interrupts o); [discriminate H|].
  destruct (o_setext o); discriminate H.
Qed.

Program Definition p_hard_wrap_heading : property := {|
  p_id := "hard-wrap-heading";
  p_group := wrapping;
  p_statement := "A heading continues on the following lines until a blank line.";
  p_implication := "Hard-wrapping a long heading keeps it one heading.";
  p_theorems := ["heading_text_wrap_then_rest"; "heading_marker_wrap_then_rest"];
  p_status := fun o =>
    if heading_wrap_safe o then Proved
    else Broken "A heading is one line."
      "# A heading wrapped
onto a second line
";
  p_holds := at_profile hard_wrap_heading
|}.
Next Obligation.
  intros lvl ls b rest rng cur. apply heading_text_wrap_then_rest.
  apply (proj1 (heading_wrap_safe_iff o)).
  destruct (heading_wrap_safe o); [reflexivity | discriminate H].
Qed.

Program Definition p_block_structure_first : property := {|
  p_id := "block-structure-first";
  p_group := structure;
  p_statement := "Which blocks a document has, and how they nest, is decided without reading inline syntax.";
  p_implication := "A tool can find the blocks of a document without an inline parser, and a bug in inline parsing cannot move a block boundary.";
  p_theorems := ["block_shape_independent"];
  p_status := fun o =>
    if shape_first o
    then Conditional "Except a table caption, which disappears when its inline content is empty."
    else Unknown;
  p_holds := at_profile block_structure_first
|}.
Next Obligation.
  intros T' LI P s. apply block_shape_independent.
  apply (proj1 (shape_first_iff o)).
  destruct (shape_first o); [reflexivity | discriminate H].
Qed.

Program Definition p_inline_precedence : property := {|
  p_id := "inline-precedence";
  p_group := precedence;
  p_statement := "When delimiters overlap, the first opener that gets closed wins, and a closer takes the closest open opener. Exactly one reading follows these rules, and the parser gives it.";
  p_implication := "Overlapping delimiters have one meaning, which can be worked out by hand.";
  p_theorems := ["para_inlines_valid"; "valid_unique"];
  p_status := always (Conditional "For emphasis-like delimiters, links and plain text. Smart quotes, spans and images are not covered.");
  p_holds := fun o => inline_precedence (o_inline o)
|}.
Next Obligation. exact (@para_inlines_valid _). Qed.

Definition all : list property :=
  [ p_block_no_backtracking; p_inline_no_backtracking; p_incremental_reparse;
    p_block_replace; p_positions; p_linear_time;
    p_quote_uniformity; p_list_uniformity; p_definition_list_uniformity;
    p_div_uniformity; p_footnote_uniformity; p_lazy_lines; p_list_tightness;
    p_indent_uniformity;
    p_reference_locality; p_reference_shape;
    p_hard_wrap_paragraph; p_hard_wrap_heading;
    p_block_structure_first;
    p_inline_precedence ].
