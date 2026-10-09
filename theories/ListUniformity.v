(* ai-disclosure: autonomous *)

(** * List uniformity

   Uniformity for lists: the rendering of a list whose items are
   canonical parses back to that list, with each item's blocks the parse
   of that item's own lines.

   Longer than the quote and div arguments for two reasons an item has
   and a quote does not: its continuation lines are *indented* rather
   than prefixed, so the padding lemmas of `Step.v` carry the weight; and
   tight/loose is decided on the event stream, so the verdict has to be
   projected out of the run (`scan_list_content`) before it can be
   rewritten. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast Attributes Inline Marker Step Uniformity Reached.
Import ListNotations.

Local Open Scope string_scope.

(* The delimiter table this file is read at.  Implicit, so nothing below
   mentions it: what it buys is that the statements quantify over the
   family rather than over djot's spelling. *)
Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
Uniformity for lists
====================
*)

(*
Projecting a run to the list state
----------------------------------

`run_lines` on an open list carries a full `pstate`; only the outer
`list_state` matters for the tight/loose verdict.  `scan_list_content` is
that projection, defined directly on lines so it can be computed and
rewritten without unfolding the parser.  `run_lines_list_cont` is the
bridge: as long as the lines are all continuations, running them agrees
with scanning them.
*)

(** The tight/loose state changes made while an already-open canonical
    list consumes continuation lines.  The item's own state rides along,
    because what a line makes of an armed blank depends on it
    (`line_fate`).  The lines are the item's, unindented, so
    `classify` reads them directly (`classify_marker_cont`) while the
    state steps on the rendered line. *)
Section ItemMarker.

(* One *item*'s marker.  A section variable rather than an explicit
   parameter: the proofs below never mention the marker's width, so they
   should not have to carry it, and `End ItemMarker` generalizes exactly
   the statements that do.

   The section closes before the list-level statements, which is the
   whole point: a renumbering list gives each item a different opener and
   a different width, so the list level quantifies over a marker *per
   item* and instantiates these facts once per item. *)
Variable mrk : marker.
Hypothesis Hmrk : marker_ok mrk = true.
Hypothesis Htasks : marker_tasks_ok (@btasks K) mrk = true.

Lemma configured_mrk_styles :
  @configured_list_styles K (mk_sty mrk) (mk_task_marker mrk) = mk_sty mrk.
Proof.
  unfold configured_list_styles. destruct (@btasks K);
    [reflexivity|].
  destruct mrk as [c|c chk|core d]; cbn [marker_tasks_ok] in Htasks.
  - reflexivity.
  - discriminate Htasks.
  - cbn [mk_sty mk_task_marker].
    destruct (styles_of_core core d) as [|x rest]; [reflexivity|].
    destruct rest as [|y ys]; destruct x; reflexivity.
Qed.

Local Lemma configured_mrk_check :
  @configured_list_check K (mk_task_marker mrk) = mk_check mrk.
Proof.
  unfold configured_list_check. destruct (@btasks K);
    [destruct mrk; reflexivity|].
  destruct mrk; cbn [marker_tasks_ok] in Htasks; try discriminate; reflexivity.
Qed.

Local Lemma configured_mrk_rest :
  forall l, @configured_list_rest K (mk_task_marker mrk) l = l.
Proof.
  intros l. unfold configured_list_rest. destruct (@btasks K);
    [reflexivity|].
  destruct mrk; cbn [marker_tasks_ok] in Htasks; try discriminate; reflexivity.
Qed.

(* A line an item may end on: one that settles a blank armed before it,
   which a blank does not, and an attribute line, which leaves it to the
   block after, does not either. *)
Definition item_end_ok (l : string) : bool :=
  match classify l with
  | KBlank | KAttr _ => false
  | _ => true
  end.

(* No spec is open where a run is `pad_safe`. *)
Lemma spec_open_pad_safe :
  forall st, pad_safe st = true -> spec_open st = false.
Proof. intros st H. destruct st; cbn in H |- *; congruence. Qed.

(* Case on the one verdict a goal mentions. *)
Local Ltac destruct_fate :=
  match goal with
  | |- context [fate_after ?s ?s' ?f] => destruct (fate_after s s' f)
  | |- context [line_fate ?a ?b ?c ?d] => destruct (line_fate a b c d)
  end.

Local Fixpoint scan_list_content (ls : list_state) (inner : pstate)
                           (lines : list string) : list_state :=
  match lines with
  | [] => ls
  | l :: rest =>
      let inner' := snd (step (mk_cont mrk ++ l) inner) in
      let ls' :=
        match classify l with
        | KBlank =>
            list_blank (list_settle (stops_waiting inner inner') ls)
        | k => list_content ls (fate_after inner inner' (line_fate 0 (mk_cont mrk ++ l) k inner))
        end in
      scan_list_content ls' inner' rest
  end.

Local Lemma run_lines_list_cont :
  forall lines ls done inner bs inner',
    ls_indent ls = 0 ->
    run_lines (map (fun l => ((mk_cont mrk) ++ l)%string) lines) inner =
      (bs, inner') ->
    run_lines (map (fun l => ((mk_cont mrk) ++ l)%string) lines)
      (PList ls done inner)
    = ([], PList (scan_list_content ls inner lines) (rev bs ++ done)%list inner').
Proof.
  induction lines as [|l lines IH]; intros ls done inner bs inner' Hind Hrun.
  - cbn [map run_lines] in Hrun |- *. inversion Hrun; subst. reflexivity.
  - cbn [map run_lines] in Hrun |- *.
    destruct (step ((mk_cont mrk) ++ l) inner) as [head inner1] eqn:Hstep.
    destruct (run_lines (map (fun l0 => (mk_cont mrk) ++ l0) lines) inner1)
      as [rest inner2] eqn:Hrest.
    inversion Hrun; subst bs inner'.
    destruct (classify l) as [| |f|dl dc|q|lvl txt|m mc chk item|kap|flbl frest|rlbl rval|krow|] eqn:Hclass.
    + rewrite (step_list_blank ((mk_cont mrk) ++ l) ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2).
      * rewrite rev_app_distr, app_assoc. reflexivity.
      * cbn [list_blank]. exact Hind.
      * exact Hrest.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) KThematic ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2)
        by (first [cbn [list_content]; exact Hind | exact Hrest]).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KFence f) ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2)
        by (first [cbn [list_content]; exact Hind | exact Hrest]).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KDiv dl dc) ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2)
        by (first [cbn [list_content]; exact Hind | exact Hrest]).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KQuote q) ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2)
        by (first [cbn [list_content]; exact Hind | exact Hrest]).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KHeading lvl txt)
                 ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2)
        by (first [cbn [list_content]; exact Hind | exact Hrest]).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KList m mc chk item)
                 ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2)
        by (first [cbn [list_content]; exact Hind | exact Hrest]).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KAttr kap)
                 ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2)
        by (first [cbn [list_content]; exact Hind | exact Hrest]).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KFoot flbl frest)
                 ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2)
        by (first [cbn [list_content]; exact Hind | exact Hrest]).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KRef rlbl rval)
                 ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2)
        by (first [cbn [list_content]; exact Hind | exact Hrest]).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KRow krow)
                 ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2)
        by (first [cbn [list_content]; exact Hind | exact Hrest]).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) KText ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2)
        by (first [cbn [list_content]; exact Hind | exact Hrest]).
      rewrite rev_app_distr, app_assoc. reflexivity.
Qed.

(*
The scan's state algebra
------------------------
*)

Local Lemma scan_list_content_fields :
  forall lines inner ls,
    ls_indent (scan_list_content ls inner lines) = ls_indent ls /\
    ls_styles (scan_list_content ls inner lines) = ls_styles ls /\
    ls_items (scan_list_content ls inner lines) = ls_items ls /\
    ls_check (scan_list_content ls inner lines) = ls_check ls /\
    ls_checks (scan_list_content ls inner lines) = ls_checks ls /\
    ls_item_extents (scan_list_content ls inner lines) = ls_item_extents ls.
Proof.
  intros lines inner ls. split; [|split; [|split; [|split; [|split]]]].
  - revert inner ls. induction lines as [|l lines IH]; intros inner ls; [reflexivity|].
    cbn [scan_list_content].
    destruct (classify l); try destruct_fate;
      rewrite IH; destruct ls; reflexivity.
  - revert inner ls. induction lines as [|l lines IH]; intros inner ls; [reflexivity|].
    cbn [scan_list_content].
    destruct (classify l); try destruct_fate;
      rewrite IH; destruct ls; reflexivity.
  - revert inner ls. induction lines as [|l lines IH]; intros inner ls; [reflexivity|].
    cbn [scan_list_content].
    destruct (classify l); try destruct_fate;
      rewrite IH; destruct ls; reflexivity.
  - revert inner ls. induction lines as [|l lines IH]; intros inner ls; [reflexivity|].
    cbn [scan_list_content].
    destruct (classify l); try destruct_fate;
      rewrite IH; destruct ls; reflexivity.
  - revert inner ls. induction lines as [|l lines IH]; intros inner ls; [reflexivity|].
    cbn [scan_list_content].
    destruct (classify l); try destruct_fate;
      rewrite IH; destruct ls; reflexivity.
  - revert inner ls. induction lines as [|l lines IH]; intros inner ls; [reflexivity|].
    cbn [scan_list_content].
    destruct (classify l); try destruct_fate;
      rewrite IH; destruct ls; reflexivity.
Qed.


(*
Item and list layout
--------------------

Where a list's lines come from.  These are layout primitives rather than
renderer policy, and the uniformity theorems below are stated in terms of
them, so they live here and `Render.v` reuses them.
*)

(* A list item's lines: the marker (`mk_open mrk`) on the first line and
   plain indent (`mk_cont mrk`) on every line after.  Not repeated per
   line like `quote_line`: `mk_cont mrk` is whitespace, and
   `Line.classify_ws_prefix` carries every recognizer through it. *)
Definition indent_lines (first_prefix rest_prefix : string) (ls : list string)
  : list string :=
  match ls with
  | [] => []
  | l :: rest => (first_prefix ++ l) :: map (fun x => rest_prefix ++ x) rest
  end.

(* Items separated by a blank line when the list is loose and
   concatenated directly when tight; `cb_ok`'s spacing condition has to
   match this. *)
Fixpoint list_lines (sp : list_spacing) (lss : list (list string))
  : list string :=
  match lss with
  | [] => []
  | [ls] => ls
  | ls :: rest =>
      (ls ++ (match sp with Loose => [EmptyString] | Tight => [] end)
       ++ list_lines sp rest)%list
  end.

(*
List-item uniformity
--------------------

The list analogue of `quote_uniformity`: an item's contents parse
exactly as they would at top level.  Two differences from the quote
case, and both are real rather than artefacts of the proof.

A quote repeats its prefix on every line, so the parser re-derives the
descent line by line.  An item's continuation is plain whitespace, so
the descent is a *column shift* instead: `step_pad_shift` is that
statement for one line, `run_lines_pad_shift` for a run.  The shift is
what makes nesting free -- a list opened inside an item records a column
two further right, and nothing else changes.

The tight/loose bit is the one thing that is *not* uniform, and
`lines_loose` is where it lives.  It is a scan of the lines, not a
function of the parsed tree: a blank line loosens the enclosing list
unless the next non-blank line opens a nested list, continues a block
the blank lay inside, or follows directly on a nested list.  A renderer-side predicate
that reads the block tree cannot express this, because the tree does not
record where the blanks sit relative to the markers.
*)

(* Padding is a shift of the state, not a no-op.  Stating it as a shift
   rather than as an equality is what makes it hold for an item whose
   content opens a list, where the pad genuinely moves a recorded
   column. *)
Local Lemma blank_safe_pad_state :
  forall k st, blank_safe (pad_state k st) = blank_safe st.
Proof.
  intros k st. induction st as [| |f ind crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    cbn [pad_state blank_safe]; try reflexivity; try exact IH.
  - rewrite IH, pad_state_is_idle. reflexivity.
  - rewrite IH, pad_state_announces_end. reflexivity.
Qed.

(* The fence side condition `step_pad` asks for is free here: `pad_state`
   has already moved every recorded column by the pad's own width, and
   column zero is left of everything. *)
Local Lemma step_pad_shift :
  forall p l st,
    is_blank p = true ->
    step (p ++ l) (pad_state (String.length p) st)
    = (fst (step l st), pad_state (String.length p) (snd (step l st))).
Proof.
  intros p l st Hp.
  rewrite (step_pad p l (pad_state (String.length p) st) Hp)
    by apply fence_cols_ok_pad.
  rewrite <- (Nat.add_0_r (String.length p)) at 1.
  rewrite step_at_shift, step_at_zero. reflexivity.
Qed.

(* The side condition along a whole run, and it is two conditions rather
   than one.  The state the run ends in meets a blank line, the item
   separator, so it must be `blank_safe`: a run may contain a code block,
   but must not end inside one.  Every state the run passes through must
   be `pad_safe`, i.e. no attribute spec is open, which is what
   `Tightness.step_fuel_ok` asks of each line; the shift itself
   (`run_lines_pad_shift`) needs neither. *)
Fixpoint run_safe (lines : list string) (st : pstate) : bool :=
  match lines with
  | [] => blank_safe st
  | l :: rest => (pad_safe st && run_safe rest (snd (step l st)))%bool
  end.

Local Lemma run_lines_pad_shift :
  forall p lines st,
    is_blank p = true ->
    run_lines (map (fun l => (p ++ l)%string) lines) (pad_state (String.length p) st)
    = (fst (run_lines lines st), pad_state (String.length p) (snd (run_lines lines st))).
Proof.
  intros p lines. induction lines as [|l rest IH]; intros st Hp.
  - reflexivity.
  - cbn [map run_lines] in *.
    rewrite (step_pad_shift p l st Hp).
    destruct (step l st) as [bs st'] eqn:Es. cbn [fst snd] in *.
    rewrite (IH st' Hp).
    destruct (run_lines rest st') as [more st''] eqn:Er. reflexivity.
Qed.

(* The marker line consumes exactly the item's content column, so this is
   `(mk_pad mrk)` and not an incidental 2: an ordered marker widens both. *)
Local Lemma consumed_marker_open :
  forall l, consumed (mk_open mrk ++ l) l = mk_pad mrk.
Proof.
  intros l. unfold consumed, mk_pad. rewrite length_append. lia.
Qed.

(* The marker line, with the item's residue parsed at the marker's
   width. *)
Local Lemma step_item_open :
  forall l0,
    is_thematic ((mk_open mrk) ++ l0) = false ->
    task_shadow mrk l0 = false ->
    step ((mk_open mrk) ++ l0) (PPara [])
    = ([], PList (list_opened ((mk_open mrk) ++ l0) 0 (mk_styles mrk) (mk_check mrk))
            (rev (fst (step l0 (PPara []))))
            (pad_state (mk_pad mrk) (snd (step l0 (PPara []))))).
Proof.
  intros l0 Hth Hts.
  destruct (step l0 (PPara [])) as [bs inner] eqn:Es. cbn [fst snd].
  rewrite <- (configured_mrk_rest l0) in Es.
  rewrite (step_list_open _ _ _ _ _ _ _
             (classify_marker_open mrk l0 Hmrk Hth Hts) Es).
  rewrite configured_mrk_styles, configured_mrk_check, configured_mrk_rest.
  rewrite (indent_of_marker_open mrk _ Hmrk), consumed_marker_open.
  reflexivity.
Qed.

(** The tight/loose verdict, read off the lines.  A blank arms the flag,
    and the next content line decides it as `step` does (`line_fate`):
    it loosens, clears, or leaves the flag for the line after.  A flag
    left to block attributes loosens once they give up waiting without a
    block: at a line or a blank that ends them, or at the end of the
    lines, as `finish` closes the list (`list_settle`).

    The scan also carries the lines' own parse state, because the
    verdict depends on what the item has open, which is why `["- b"; "";
    "t"]` leaves its enclosing list tight while `["a"; ""; "t"]` does
    not.  The state is threaded, not consulted from outside, so this is
    still a fold over the lines. *)
Fixpoint lines_loose (loose gap : bool) (st : pstate) (ls : list string) : bool :=
  match ls with
  | [] => (loose || (attr_waits st && gap))%bool
  | l :: rest =>
      let st' := snd (step l st) in
      match classify l with
      | KBlank =>
          lines_loose (loose || (stops_waiting st st' && gap))%bool true st' rest
      | k =>
          match fate_after st st' (line_fate 0 l k st) with
          | Spends => lines_loose (loose || gap)%bool false st' rest
          | Clears => lines_loose loose false st' rest
          | Waits => lines_loose loose gap st' rest
          end
      end
  end.

(** The verdict for a whole item, scanned from idle.  Every call site
    outside the scan's own induction wants this one. *)
Definition item_loose (L : list string) : bool :=
  lines_loose false false (PPara []) L.

(* A nonblank first line contributes nothing: it cannot arm the flag, and
   with nothing armed it cannot spend one either.  So the verdict for an
   item's lines is the verdict for its continuation lines, which is the
   form `list_uniformity` states and the renderer consumes. *)
Local Lemma lines_loose_cons_nonblank :
  forall a rest,
    classify a <> KBlank ->
    item_loose (a :: rest) = lines_loose false false (snd (step a (PPara []))) rest.
Proof.
  intros a rest H. unfold item_loose. cbn [lines_loose].
  destruct (classify a) eqn:E; [congruence|..]; destruct_fate; reflexivity.
Qed.

(** Whether the lines end with a blank still armed: one that no later
    line spent or cleared.  A sibling's marker spends it, so a list is
    loose when an item before the last ends this way (`list_next`). *)
Fixpoint lines_gap (gap : bool) (st : pstate) (ls : list string) : bool :=
  match ls with
  | [] => gap
  | l :: rest =>
      let st' := snd (step l st) in
      match classify l with
      | KBlank => lines_gap true st' rest
      | k =>
          match fate_after st st' (line_fate 0 l k st) with
          | Waits => lines_gap gap st' rest
          | Spends | Clears => lines_gap false st' rest
          end
      end
  end.

Definition item_gap (L : list string) : bool :=
  lines_gap false (PPara []) L.

Local Lemma item_gap_cons_nonblank :
  forall a rest,
    classify a <> KBlank ->
    item_gap (a :: rest) = lines_gap false (snd (step a (PPara []))) rest.
Proof.
  intros a rest H. unfold item_gap. cbn [lines_gap].
  destruct (classify a) eqn:E; [congruence|..]; destruct_fate; reflexivity.
Qed.

Local Lemma run_lines_snd_cons :
  forall l rest st,
    snd (run_lines (l :: rest) st) = snd (run_lines rest (snd (step l st))).
Proof.
  intros l rest st. cbn [run_lines]. destruct (step l st) as [bs st'].
  cbn [snd]. destruct (run_lines rest st'). reflexivity.
Qed.

(* A blank left armed under attributes that are still waiting when the
   lines end is spent there, so the verdict already counts it. *)
Local Lemma lines_loose_settled :
  forall L st lo g,
    (attr_waits (snd (run_lines L st)) && lines_gap g st L)%bool = true ->
    lines_loose lo g st L = true.
Proof.
  induction L as [|l rest IH]; intros st lo g H.
  - cbn [run_lines snd lines_gap] in H. cbn [lines_loose]. rewrite H.
    apply orb_true_r.
  - rewrite run_lines_snd_cons in H. cbn [lines_loose lines_gap] in *.
    destruct (classify l); try destruct_fate; apply IH; exact H.
Qed.

(* The scan and the two folds agree: the scan carries the item's state
   padded into the enclosing item, the folds carry it bare, and
   `line_fate` cannot tell the two apart.  The scan's loose flag lacks
   only what `finish` adds when the lines end under waiting attributes
   (`list_settle`), which `lines_loose` counts. *)
Local Lemma scan_flags :
  forall lines st ls,
    ls_blanks (scan_list_content ls (pad_state (mk_pad mrk) st) lines)
    = lines_gap (ls_blanks ls) st lines
    /\ (ls_loose (scan_list_content ls (pad_state (mk_pad mrk) st) lines)
        || (attr_waits (snd (run_lines lines st))
            && ls_blanks (scan_list_content ls (pad_state (mk_pad mrk) st) lines)))%bool
       = lines_loose (ls_loose ls) (ls_blanks ls) st lines.
Proof.
  induction lines as [|l rest IH]; intros st ls.
  { cbn [scan_list_content lines_gap lines_loose run_lines snd].
    split; reflexivity. }
  rewrite run_lines_snd_cons.
  cbn [scan_list_content lines_loose lines_gap].
  pose proof (step_pad_shift (mk_cont mrk) l st (marker_cont_blank mrk)) as Hsh.
  rewrite mk_cont_length in Hsh.
  pose proof (fun k => line_fate_pad_prefix (mk_cont mrk) l k st (marker_cont_blank mrk))
    as Hft.
  rewrite mk_cont_length in Hft.
  rewrite Hsh. cbn [snd].
  unfold fate_after, stops_waiting. rewrite !pad_state_attr_waits.
  destruct (classify l) eqn:E; rewrite ?Hft;
    try destruct (line_fate 0 l _ st);
    try destruct (attr_waits st && negb (attr_waits (snd (step l st))))%bool;
    match goal with
    | |- context [scan_list_content ?ls' _ rest] =>
        destruct (IH (snd (step l st)) ls') as [H1 H2]
    end;
    rewrite H2, H1; destruct ls; split; reflexivity.
Qed.

(* An item that ends on such a line, with no spec open, leaves no blank
   armed: the line either spends the flag or clears it.  A blank or an
   attribute line would leave it for a line after. *)
Local Lemma lines_gap_last :
  forall lines st g,
    run_safe lines st = true ->
    lines <> [] -> item_end_ok (last lines EmptyString) = true ->
    lines_gap g st lines = false.
Proof.
  induction lines as [|l lines IH]; intros st g Hsafe Hne Hlast; [congruence|].
  cbn [run_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hp Hrest].
  destruct lines as [|l2 lines'].
  - cbn [last lines_gap] in Hlast |- *.
    unfold item_end_ok in Hlast.
    destruct (classify l) eqn:Hclass; try discriminate Hlast;
      unfold fate_after, line_fate; rewrite (spec_open_pad_safe st Hp);
      destruct (keeps_line 0 l st); reflexivity.
  - change (last (l :: l2 :: lines') EmptyString)
      with (last (l2 :: lines') EmptyString) in Hlast.
    remember (l2 :: lines') as tl eqn:Etl. cbn [lines_gap].
    destruct (classify l); try destruct_fate;
      (apply IH; [exact Hrest|subst tl; discriminate|exact Hlast]).
Qed.

(* The list state a first item leaves behind: its marker line opens the
   list, and its continuation lines are scanned into it. *)
Local Definition item_scan (l0 : string) (rest : list string) : list_state :=
  scan_list_content (list_opened ((mk_open mrk) ++ l0) 0 (mk_styles mrk) (mk_check mrk))
    (pad_state (mk_pad mrk) (snd (step l0 (PPara [])))) rest.

(* One item's lines, run from idle: the marker opens the list and the
   continuation lines land in it, shifted by the marker's width. *)
Local Lemma run_item_open :
  forall l0 rest,
    is_thematic ((mk_open mrk) ++ l0) = false ->
    task_shadow mrk l0 = false ->
    run_lines (indent_lines (mk_open mrk) (mk_cont mrk) (l0 :: rest)) (PPara [])
    = ([], PList (item_scan l0 rest)
            (rev (fst (run_lines (l0 :: rest) (PPara []))))
            (pad_state (mk_pad mrk) (snd (run_lines (l0 :: rest) (PPara []))))).
Proof.
  intros l0 rest Hth Hts.
  cbn [indent_lines run_lines].
  rewrite (step_item_open l0 Hth Hts).
  pose proof (run_lines_pad_shift (mk_cont mrk) rest (snd (step l0 (PPara [])))
                (marker_cont_blank mrk)) as Hrun.
  rewrite mk_cont_length in Hrun.
  rewrite (run_lines_list_cont rest
             (list_opened ((mk_open mrk) ++ l0) 0 (mk_styles mrk) (mk_check mrk))
             (rev (fst (step l0 (PPara [])))) _ _ _ eq_refl Hrun).
  fold (item_scan l0 rest).
  cbn [run_lines].
  destruct (step l0 (PPara [])) as [b i] eqn:Es. cbn [fst snd].
  destruct (run_lines rest i) as [more i'] eqn:Er. cbn [fst snd app].
  rewrite rev_app_distr. reflexivity.
Qed.

(* The same, for an item that is not the first: the marker closes the
   item in progress instead of opening the list. *)
(* Stepping over a sibling marker, with the narrowing left in place.  The
   list continues exactly when the intersection is nonempty; whether it
   *moved* is not this lemma's business, which is what lets a first
   marker naming two styles be handled by the same descent. *)
Local Lemma run_item_sibling_narrow :
  forall l0 rest ls done inner,
    ls_indent ls = 0 ->
    (* the item in progress does not claim the marker line out of
       column (keyed-blocks 5) *)
    key_claims ((mk_open mrk) ++ l0) inner = false ->
    narrow (ls_styles ls) (mk_sty mrk) <> [] ->
    is_thematic ((mk_open mrk) ++ l0) = false ->
    task_shadow mrk l0 = false ->
    run_lines (indent_lines (mk_open mrk) (mk_cont mrk) (l0 :: rest)) (PList ls done inner)
    = ([], PList (scan_list_content
                    (list_next (list_narrow ls (narrow (ls_styles ls) (mk_sty mrk)))
                               (rev done ++ finish inner)%list (mk_check mrk) ((mk_open mrk) ++ l0))
                    (pad_state (mk_pad mrk) (snd (step l0 (PPara [])))) rest)
            (rev (fst (run_lines (l0 :: rest) (PPara []))))
            (pad_state (mk_pad mrk) (snd (run_lines (l0 :: rest) (PPara []))))).
Proof.
  intros l0 rest ls done inner Hind Hkc Hnar Hth Hts.
  cbn [indent_lines run_lines].
  destruct (step l0 (PPara [])) as [b i] eqn:Es.
  destruct (narrow (ls_styles ls) (mk_sty mrk)) as [|s0 ss] eqn:Hn;
    [contradiction|].
  rewrite <- configured_mrk_styles in Hn.
  rewrite <- (configured_mrk_rest l0) in Es.
  rewrite (step_list_sibling _ _ _ _ _ _ _ _ _ _ _ _
             (classify_marker_open mrk l0 Hmrk Hth Hts) Hn
             (ltac:(unfold list_takes; rewrite Hkc, Nat.add_0_l, Hind,
                      (indent_of_marker_open mrk _ Hmrk); reflexivity))
             Es).
  rewrite configured_mrk_check, configured_mrk_rest, consumed_marker_open.
  pose proof (run_lines_pad_shift (mk_cont mrk) rest i (marker_cont_blank mrk)) as Hrun.
  rewrite mk_cont_length in Hrun.
  assert (Hi0 : ls_indent (list_next (list_narrow ls (s0 :: ss))
                             (rev done ++ finish inner)%list (mk_check mrk) ((mk_open mrk) ++ l0)) = 0).
  { unfold list_next, list_narrow. cbn [ls_indent].
    exact Hind. }
  rewrite (run_lines_list_cont rest
             (list_next (list_narrow ls (s0 :: ss)) (rev done ++ finish inner)%list
                        (mk_check mrk) ((mk_open mrk) ++ l0))
             (rev b) (pad_state (mk_pad mrk) i) _ _ Hi0 Hrun).
  destruct (run_lines rest i) as [more i'] eqn:Er. cbn [fst snd app].
  rewrite rev_app_distr. reflexivity.
Qed.

(* `lines_loose` only ever accumulates with `||`, so the incoming verdict
   factors out.  This is what lets an item's contribution be read off its
   own lines, independent of what the items before it decided. *)
Local Lemma lines_loose_or :
  forall L st lo g, lines_loose lo g st L = (lo || lines_loose false g st L)%bool.
Proof.
  induction L as [|l rest IH]; intros st lo g.
  - cbn [lines_loose]. reflexivity.
  - cbn [lines_loose]. destruct (classify l).
    { rewrite IH, (IH _ (false || _)%bool). cbn [orb]. rewrite orb_assoc. reflexivity. }
    all: destruct_fate; try apply IH.
    all: cbn [orb]; rewrite (IH _ (lo || g)%bool false), (IH _ g false);
         destruct lo, g; reflexivity.
Qed.

(* What a key's block looks like after a blank, when the block produced
   nothing and so the key is still open.  A state that emitted nothing
   kept its container, so it is not idle; when it did not already hold
   an announced-end block, a blank cannot create one. *)
Lemma step_blank_inner_settled :
  forall l st, classify l = KBlank -> blank_safe st = true ->
    announces_end st = false -> is_idle st = false -> fst (step l st) = [] ->
    (is_idle (snd (step l st)) = false
     /\ announces_end (snd (step l st)) = false).
Proof.
  intros l st Hblank. induction st as
    [cur|lvl cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe Hannounce Hidle Hempty;
    try discriminate Hsafe; try discriminate Hannounce.
  all: try (destruct cur as [|c cur']; [discriminate Hidle|];
            rewrite (step_para_flush l c cur' Hblank) in Hempty; discriminate Hempty).
  all: try (rewrite (step_para_off_flush l okoff ocur Hblank) in Hempty;
            discriminate Hempty).
  all: try (rewrite (step_quote_close l KBlank qrng qhead done inner [] (PPara [])
              Hblank eq_refl eq_refl eq_refl) in Hempty; discriminate Hempty).
  all: try (destruct (step l dinner) as [bs i] eqn:Hs;
            rewrite (step_div_cont l dlen dcls drng dop ddone dinner bs i
              (div_stays_open_blank l dinner dlen (classify_kblank_blank l Hblank)) Hs);
            split; reflexivity).
  all: try (destruct (step l inner) as [bs i] eqn:Hs;
            rewrite (step_list_blank l ls done inner bs i Hblank Hs); split; reflexivity).
  all: try (unfold step; cbn [step_fuel open_line];
            rewrite (classify_kblank_blank l Hblank);
            destruct (step_fuel _ 0 l finner); split; reflexivity).
  all: try (unfold step in Hempty; cbn [step_fuel open_line] in Hempty;
            rewrite Hblank in Hempty; destruct bheading_continues;
            cbn in Hempty; discriminate Hempty).
  { cbn in Hempty |- *;
    destruct (if match indent_of l with 0 => false | S m' => (rind <=? m')%nat end
              then ref_cont l else None);
    [split; reflexivity
    |destruct (step_fuel (String.length l + 1) 0 l (PPara [])); discriminate Hempty]. }
  { cbn in Hempty |- *; rewrite (classify_kblank_blank l Hblank) in Hempty |- *;
    destruct tcap; try (destruct (caption_open l)); try (split; reflexivity);
    destruct (step_fuel (String.length l + 1) 0 l (PPara [])); discriminate Hempty. }
  { cbn [blank_safe] in Hsafe; apply andb_true_iff in Hsafe as [Hsafe Hni];
    apply negb_true_iff in Hni; cbn in Hempty |- *;
    rewrite Hblank, Hni in Hempty |- *;
    rewrite step_fuel_enough in Hempty |- * by (cbn [pstate_depth]; lia);
    destruct (step l pinner) as [bs st'] eqn:Hs; cbn [fst snd] in Hempty |- *;
    destruct bs as [|b bs'];
    [split; reflexivity
    |destruct b; cbn [pend_result fst snd decorate_head] in Hempty; discriminate Hempty]. }
  cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe _].
  destruct (is_idle kinner) eqn:Hki.
  { destruct kinner as [cur| | | | | | | | | | | |]; try discriminate Hki.
    destruct cur; [|discriminate Hki].
    rewrite (step_key_retract l krng klbl ksrc (classify_kblank_blank l Hblank)) in Hempty |- *.
    cbn [fst] in Hempty. discriminate Hempty. }
  rewrite (step_key_pass l krng klbl ksrc kinner
             ltac:(rewrite Hki, andb_false_r; reflexivity)) in Hempty |- *.
  destruct (step l kinner) as [bs st'] eqn:Hs. cbn [fst snd] in Hempty |- *.
  destruct bs as [|b bs']; cbn [key_result fst snd] in Hempty |- *;
    [split; reflexivity|discriminate Hempty].
Qed.

(* A blank leaves no attributes waiting where none were open before it:
   it drops a pending set, and a spec is excluded. *)
Lemma step_blank_attr_waits :
  forall l st, classify l = KBlank -> blank_safe st = true ->
    attr_waits (snd (step l st)) = false.
Proof.
  intros l st Hblank. induction st as
    [cur|lvl cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe; try discriminate Hsafe.
  all: try (destruct cur as [|c cur'];
            [rewrite (step_idle l KBlank Hblank eq_refl); reflexivity
            |rewrite (step_para_flush l c cur' Hblank); reflexivity]).
  all: try (rewrite (step_para_off_flush l okoff ocur Hblank); reflexivity).
  all: try (rewrite (step_quote_close l KBlank qrng qhead done inner [] (PPara [])
              Hblank eq_refl eq_refl eq_refl); reflexivity).
  all: try (destruct (step l dinner) as [bs i] eqn:Hs;
            rewrite (step_div_cont l dlen dcls drng dop ddone dinner bs i
              (div_stays_open_blank l dinner dlen (classify_kblank_blank l Hblank)) Hs);
            reflexivity).
  all: try (destruct (step l inner) as [bs i] eqn:Hs;
            rewrite (step_list_blank l ls done inner bs i Hblank Hs); reflexivity).
  all: try (unfold step; cbn [step_fuel open_line];
            rewrite (classify_kblank_blank l Hblank);
            destruct (step_fuel _ 0 l finner); reflexivity).
  - rewrite (step_heading_close l lvl cur cur0 Hblank). reflexivity.
  - rewrite (step_ref_blank l rrng rind rlbl rval Hblank). reflexivity.
  - cbn. rewrite (classify_kblank_blank l Hblank).
    destruct tcap; try destruct (caption_open l); reflexivity.
  - (* pending attributes over a block: what the blank leaves under them
       is not idle unless the block emitted, and then they are gone *)
    cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe Hni].
    apply negb_true_iff in Hni.
    unfold step. cbn [step_fuel]. rewrite Hblank, Hni.
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    fold (step l pinner).
    destruct (announces_end pinner) eqn:Ha.
    + destruct pinner as [| | | |dlen dcls drng dop ddone dinner| | | | | | | |];
        try discriminate Ha; try discriminate Hsafe.
      destruct (step l dinner) as [bs i] eqn:Hs.
      rewrite (step_div_cont l dlen dcls drng dop ddone dinner bs i
                 (div_stays_open_blank l dinner dlen (classify_kblank_blank l Hblank)) Hs).
      reflexivity.
    + pose proof (step_blank_inner_settled l pinner Hblank Hsafe Ha Hni) as Hset.
      specialize (IH Hsafe).
      destruct (step l pinner) as [bs st'] eqn:Hs. cbn [fst snd] in Hset, IH.
      destruct bs as [|b bs']; cbn [pend_result snd].
      * apply (proj1 (Hset eq_refl)).
      * exact IH.
  - cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe _].
    destruct (is_idle kinner) eqn:Hki.
    { destruct kinner as [cur| | | | | | | | | | | |]; try discriminate Hki.
      destruct cur; [|discriminate Hki].
      rewrite (step_key_retract l krng klbl ksrc (classify_kblank_blank l Hblank)).
      reflexivity. }
    rewrite (step_key_pass l krng klbl ksrc kinner
               ltac:(rewrite Hki, andb_false_r; reflexivity)).
    specialize (IH Hsafe).
    destruct (step l kinner) as [bs st'] eqn:Hs. cbn [snd] in IH.
    destruct bs as [|b bs']; cbn [key_result snd]; [reflexivity|exact IH].
Qed.

(* A blank line closes what `finish` would have closed, and emits it.
   The exception is a list, which a blank does not close -- there the
   equation holds one level down instead, which is the induction.  A
   fence and an open spec are the two states where it fails, and
   `blank_safe` excludes both. *)
Lemma step_blank_finish :
  forall l st, classify l = KBlank -> blank_safe st = true ->
    (fst (step l st) ++ finish (snd (step l st)))%list = finish st.
Proof.
  intros l st Hl.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
                  |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
                  |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe.
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hl eq_refl). cbn [open_kind fst snd finish app].
      reflexivity.
    + rewrite (step_para_flush l c cur' Hl). reflexivity.
  - rewrite (step_heading_close l lvl hrng cur Hl). reflexivity.
  - discriminate Hsafe.
  - rewrite (step_quote_close l KBlank qrng qhead done inner _ _ Hl eq_refl eq_refl
               (surjective_pairing _)).
    cbn [fst snd open_kind finish app]. reflexivity.
  - (* a blank never closes a div, so it goes straight to the contents *)
    cbn [blank_safe] in Hsafe.
    rewrite (step_div_cont l dlen dcls drng dop ddone dinner _ _
               (div_stays_open_blank l dinner dlen (classify_kblank_blank l Hl))
               (surjective_pairing _)).
    cbn [fst snd finish app].
    rewrite rev_app_distr, rev_involutive, <- app_assoc, (IH Hsafe).
    reflexivity.
  - cbn [blank_safe] in Hsafe.
    rewrite (step_list_blank l ls done inner _ _ Hl (surjective_pairing _)).
    cbn [fst snd finish app list_blank ls_loose ls_items].
    rewrite rev_app_distr, rev_involutive, <- app_assoc, (IH Hsafe).
    (* the blank only touches `ls_blanks`, which `finish` reads only
       under waiting attributes, and there are none on either side *)
    unfold stops_waiting.
    rewrite (blank_safe_attr_waits inner Hsafe), (step_blank_attr_waits l inner Hl Hsafe).
    rewrite !list_settle_false. reflexivity.
  - discriminate Hsafe.
  - (* the recovery's paragraph flushes on a blank exactly as one does *)
    rewrite (step_para_off_flush l okoff ocur Hl). reflexivity.
  - (* a reference definition: a blank line has no run to contribute, so
       it closes and the definition is emitted *)
    rewrite (step_ref_blank l rrng rind rlbl rval Hl). reflexivity.
  - (* a footnote owns blank lines, passing them to its body *)
    cbn [blank_safe] in Hsafe.
    destruct (step l finner) as [bs inner'] eqn:Hs.
    assert (Hfoot : step l (PFoot frng find flbl fdone finner) =
              ([], PFoot (touch_extent frng) find flbl (rev bs ++ fdone)%list inner')).
    { unfold step. cbn [step_fuel open_line pstate_depth].
      rewrite (classify_kblank_blank l Hl).
      rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
      rewrite Hs. reflexivity. }
    rewrite Hfoot. cbn [fst snd finish app].
    specialize (IH Hsafe). cbn [fst snd] in IH.
    rewrite rev_app_distr, rev_involutive, <- app_assoc, IH.
    reflexivity.
  - (* a table: a blank ends its rows but not the table, since a caption
       may still follow, and the table it would emit is the same either
       way -- `TOpen` and `TAfterBlank` have the same caption. *)
    pose proof (classify_kblank_blank l Hl) as Hb.
    unfold step. cbn [step_fuel open_line].
    rewrite (caption_open_blank l Hb), Hb.
    destruct tcap; cbn [finish app]; reflexivity.
  - (* pending attributes: the blank closes what is under them, and the
       decoration rides on whatever that emits *)
    cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe Hni].
    apply negb_true_iff in Hni.
    unfold step. cbn [step_fuel open_line]. rewrite Hl.
    rewrite Hni.
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    specialize (IH Hsafe).
    destruct (step l pinner) as [bs st'] eqn:Hs.
    cbn [fst snd] in IH. cbn [pend_result]; nopos.
    destruct bs as [|b bs'].
    + cbn [fst snd finish app]. rewrite <- IH. reflexivity.
    + cbn [fst snd finish]. rewrite decorate_head_cons_app, <- IH. reflexivity.
  - (* an open key: with nothing under it the blank retracts, which is
       what `finish` would have done; otherwise the blank closes what is
       under it and `key_close` wraps the first block either way *)
    cbn [blank_safe] in Hsafe.
    apply andb_true_iff in Hsafe as [Hsafe _].
    destruct (is_idle kinner) eqn:Hidle.
    { destruct kinner as [cur| | | | | | | | | | | |]; try discriminate Hidle.
      destruct cur; [|discriminate Hidle].
      rewrite (step_key_retract l krng klbl ksrc (classify_kblank_blank l Hl)).
      reflexivity. }
    rewrite (step_key_pass l krng klbl ksrc kinner
               ltac:(rewrite Hidle, andb_false_r; reflexivity)).
    specialize (IH Hsafe).
    destruct (step l kinner) as [bs st'] eqn:Hs.
    cbn [fst snd] in IH. cbn [key_result].
    destruct bs as [|b bs'].
    cbn [app] in IH.
    + cbn [fst snd]. rewrite !finish_key, IH. reflexivity.
    + cbn [fst snd]. rewrite finish_key, <- IH.
      cbn [key_close]. rewrite <- app_comm_cons. reflexivity.
Qed.

(* A blank line leaves no state a later text line could continue lazily.
   `step_list_close` needs this to route the line that closes a list. *)
(* Section 5's discharge.  A blank retracts a key that is still waiting
   and closes one whose block has produced something.  When a key holds
   a fence or div instead, its own `blank_safe` clause is false until the
   announced closer arrives.  So a safe blank leaves no key able to claim
   the next line, which lets `parse_list_close` and the item chain rule
   the override out from the hypothesis they already carry. *)
Lemma step_blank_key_claims :
  forall l st, classify l = KBlank -> blank_safe st = true ->
    forall next, key_claims next (snd (step l st)) = false.
Proof.
  intros l st Hblank. induction st as
    [cur|lvl cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe next; try discriminate Hsafe.
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hblank eq_refl). reflexivity.
    + rewrite (step_para_flush l c cur' Hblank). reflexivity.
  - unfold step. cbn [step_fuel open_line]. destruct bheading_continues;
      rewrite Hblank; reflexivity.
  - rewrite (step_quote_close l KBlank qrng qhead done inner [] (PPara [])
      Hblank eq_refl eq_refl eq_refl). reflexivity.
  - cbn [blank_safe] in Hsafe. specialize (IH Hsafe next).
    destruct (step l dinner) as [bs i] eqn:Hs.
    rewrite (step_div_cont l dlen dcls drng dop ddone dinner bs i
      (div_stays_open_blank l dinner dlen (classify_kblank_blank l Hblank)) Hs).
    cbn [snd key_claims] in *. exact IH.
  - cbn [blank_safe] in Hsafe. specialize (IH Hsafe next).
    destruct (step l inner) as [bs i] eqn:Hs.
    rewrite (step_list_blank l ls done inner bs i Hblank Hs).
    cbn [snd key_claims]. exact IH.
  - rewrite (step_para_off_flush l okoff ocur Hblank). reflexivity.
  - cbn; destruct (if match indent_of l with 0 => false | S m' => (rind <=? m')%nat end
                   then ref_cont l else None); [reflexivity|];
      rewrite step_fuel_enough by (cbn [pstate_depth]; lia);
      rewrite (step_idle l KBlank Hblank eq_refl); reflexivity.
  - cbn [blank_safe] in Hsafe. specialize (IH Hsafe next).
    unfold step; cbn [step_fuel open_line];
      rewrite (classify_kblank_blank l Hblank).
    replace (step_fuel (String.length l + S (pstate_depth finner)) 0 l finner)
      with (step l finner)
      by (unfold step; symmetry; apply step_fuel_enough; cbn [pstate_depth]; lia).
    destruct (step l finner) as [bs i] eqn:Hs.
    cbn [snd key_claims] in *. exact IH.
  - cbn; rewrite (classify_kblank_blank l Hblank); destruct tcap;
      try (destruct (caption_open l)); reflexivity.
  - cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe Hni].
    apply negb_true_iff in Hni. specialize (IH Hsafe next).
    cbn; rewrite Hblank, Hni.
    replace (step_fuel (String.length l + S (pstate_depth pinner)) 0 l pinner)
      with (step l pinner)
      by (unfold step; symmetry; apply step_fuel_enough; cbn [pstate_depth]; lia).
    destruct (step l pinner) as [bs st'] eqn:Hs. cbn [snd] in IH.
    destruct bs as [|b bs']; cbn [pend_result snd key_claims];
      [exact IH|destruct b; cbn [snd]; exact IH].
  - cbn [blank_safe] in Hsafe.
    apply andb_true_iff in Hsafe as [Hsafe Hnot].
    apply negb_true_iff in Hnot.
    destruct (is_idle kinner) eqn:Hki.
    { destruct kinner as [cur| | | | | | | | | | | |]; try discriminate Hki.
      destruct cur; [|discriminate Hki].
      rewrite (step_key_retract l krng klbl ksrc (classify_kblank_blank l Hblank)).
      reflexivity. }
    rewrite (step_key_pass l krng klbl ksrc kinner
               ltac:(rewrite Hki, andb_false_r; reflexivity)).
    pose proof (step_blank_inner_settled l kinner Hblank Hsafe Hnot Hki) as Hset.
    specialize (IH Hsafe next).
    destruct (step l kinner) as [bs st'] eqn:Hs. cbn [snd] in IH, Hset.
    destruct bs as [|b bs']; cbn [key_result snd key_claims];
      [destruct (Hset eq_refl) as [Hi Ha]; rewrite Hi; exact Ha|exact IH].
Qed.

(* `blank_safe` is what rules out an open attribute spec, whose blank
   opens the recovered paragraph rather than closing anything.  The one
   caller has the hypothesis already, for the neighbouring lemmas. *)
Lemma step_blank_lazy_false :
  forall l st, classify l = KBlank -> blank_safe st = true ->
    lazy_ok (snd (step l st)) = false.
Proof.
  intros l st Hblank. induction st as
    [cur|lvl cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe; try discriminate Hsafe.
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hblank eq_refl). reflexivity.
    + rewrite (step_para_flush l c cur' Hblank). reflexivity.
  - unfold step. cbn [step_fuel open_line]. destruct bheading_continues;
      rewrite Hblank; reflexivity.
  - rewrite (step_quote_close l KBlank qrng qhead done inner [] (PPara [])
      Hblank eq_refl eq_refl eq_refl). reflexivity.
  - destruct (step l dinner) as [bs inner'] eqn:Hstep.
    rewrite (step_div_cont l dlen dcls drng dop ddone dinner bs inner'
               (div_stays_open_blank l dinner dlen (classify_kblank_blank l Hblank)) Hstep).
    cbn [snd lazy_ok]. exact (IH Hsafe).
  - destruct (step l inner) as [bs inner'] eqn:Hstep.
    rewrite (step_list_blank l ls done inner bs inner' Hblank Hstep).
    cbn [snd lazy_ok]. exact (IH Hsafe).
  - (* the recovery's paragraph flushes, leaving the idle state *)
    rewrite (step_para_off_flush l okoff ocur Hblank). reflexivity.
  - (* a reference definition: the blank closes it, leaving the idle state *)
    rewrite (step_ref_blank l rrng rind rlbl rval Hblank). reflexivity.
  - unfold step. cbn [step_fuel open_line]. rewrite (classify_kblank_blank l Hblank).
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l finner) as [bs inner'] eqn:Hs.
    specialize (IH Hsafe). cbn [snd lazy_ok] in IH |- *. exact IH.
  - (* a table: a blank leaves either a waiting table or the idle state,
       and neither is a paragraph *)
    pose proof (classify_kblank_blank l Hblank) as Hb.
    unfold step. cbn [step_fuel open_line].
    rewrite (caption_open_blank l Hb), Hb.
    destruct tcap; reflexivity.
  - cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe _].
    unfold step. cbn [step_fuel open_line]. rewrite Hblank.
    destruct (is_idle pinner); [reflexivity|].
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l pinner) as [bs st'] eqn:Hs.
    destruct bs; cbn [pend_result snd lazy_ok]; exact (IH Hsafe).
  - (* an open key: the retraction leaves the idle state, and otherwise
       the key is still there over a state the induction covers *)
    destruct (is_idle kinner) eqn:Hidle.
    { destruct kinner as [cur| | | | | | | | | | | |]; try discriminate Hidle.
      destruct cur; [|discriminate Hidle].
      rewrite (step_key_retract l krng klbl ksrc (classify_kblank_blank l Hblank)).
      reflexivity. }
    cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe _].
    rewrite (step_key_pass l krng klbl ksrc kinner
               ltac:(rewrite Hidle, andb_false_r; reflexivity)).
    destruct (step l kinner) as [bs st'] eqn:Hs.
    destruct bs; cbn [key_result snd lazy_ok]; exact (IH Hsafe).
Qed.

(* A state that meets a blank safely meets the next one safely too, and a
   blank that emits nothing leaves a container open. *)
Lemma step_blank_safe :
  forall l st, classify l = KBlank -> blank_safe st = true ->
    blank_safe (snd (step l st)) = true
    /\ (is_idle st = false -> fst (step l st) = [] -> is_idle (snd (step l st)) = false).
Proof.
  intros l st Hblank. induction st as
    [cur|lvl cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe; try discriminate Hsafe.
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hblank eq_refl). split; [reflexivity|discriminate].
    + rewrite (step_para_flush l c cur' Hblank). split; [reflexivity|discriminate].
  - unfold step. cbn [step_fuel open_line]. rewrite Hblank.
    destruct bheading_continues; split; try reflexivity; discriminate.
  - rewrite (step_quote_close l KBlank qrng qhead done inner [] (PPara [])
      Hblank eq_refl eq_refl eq_refl). split; [reflexivity|discriminate].
  - destruct (step l dinner) as [bs inner'] eqn:Hstep.
    rewrite (step_div_cont l dlen dcls drng dop ddone dinner bs inner'
               (div_stays_open_blank l dinner dlen (classify_kblank_blank l Hblank)) Hstep).
    cbn [snd blank_safe] in *. split; [exact (proj1 (IH Hsafe))|reflexivity].
  - destruct (step l inner) as [bs inner'] eqn:Hstep.
    rewrite (step_list_blank l ls done inner bs inner' Hblank Hstep).
    cbn [snd blank_safe] in *. split; [exact (proj1 (IH Hsafe))|reflexivity].
  - rewrite (step_para_off_flush l okoff ocur Hblank). split; [reflexivity|discriminate].
  - rewrite (step_ref_blank l rrng rind rlbl rval Hblank). split; [reflexivity|discriminate].
  - unfold step. cbn [step_fuel open_line]. rewrite (classify_kblank_blank l Hblank).
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l finner) as [bs inner'] eqn:Hs.
    specialize (IH Hsafe). cbn [snd fst blank_safe] in IH |- *.
    split; [exact (proj1 IH)|reflexivity].
  - pose proof (classify_kblank_blank l Hblank) as Hb.
    unfold step. cbn [step_fuel open_line].
    rewrite (caption_open_blank l Hb), Hb.
    destruct tcap; split; try reflexivity; discriminate.
  - cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe Hni].
    apply negb_true_iff in Hni. specialize (IH Hsafe) as [IHs IHi].
    unfold step. cbn [step_fuel open_line]. rewrite Hblank, Hni.
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l pinner) as [bs st'] eqn:Hs. cbn [fst snd] in IHs, IHi.
    destruct bs as [|b bs']; cbn [pend_result fst snd].
    + cbn [blank_safe]. rewrite IHs, (IHi Hni eq_refl). split; reflexivity.
    + nopos. destruct b. cbn [fst snd]. split; [exact IHs|discriminate].
  - cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe Hnot].
    apply negb_true_iff in Hnot.
    destruct (is_idle kinner) eqn:Hki.
    { destruct kinner as [cur| | | | | | | | | | | |]; try discriminate Hki.
      destruct cur; [|discriminate Hki].
      rewrite (step_key_retract l krng klbl ksrc (classify_kblank_blank l Hblank)).
      split; [reflexivity|discriminate]. }
    rewrite (step_key_pass l krng klbl ksrc kinner
               ltac:(rewrite Hki, andb_false_r; reflexivity)).
    pose proof (step_blank_inner_settled l kinner Hblank Hsafe Hnot Hki) as Hset.
    specialize (IH Hsafe) as [IHs _].
    destruct (step l kinner) as [bs st'] eqn:Hs. cbn [fst snd] in IHs, Hset.
    destruct bs as [|b bs']; cbn [key_result fst snd].
    + destruct (Hset eq_refl) as [_ Ha]. cbn [blank_safe]. rewrite IHs, Ha.
      split; reflexivity.
    + split; [exact IHs|discriminate].
Qed.

Lemma run_safe_final :
  forall L st, run_safe L st = true -> blank_safe (snd (run_lines L st)) = true.
Proof.
  induction L as [|l rest IH]; intros st H; [exact H|].
  cbn [run_safe] in H. apply andb_prop in H as [_ Hlater].
  cbn [run_lines]. destruct (step l st) as [bs st'] eqn:Es.
  cbn [snd] in Hlater.
  specialize (IH st' Hlater). destruct (run_lines rest st') as [more st''] eqn:Er.
  cbn [snd] in IH |- *. exact IH.
Qed.

End ItemMarker.

(*
The list level
--------------

From here a list is a sequence of *items with their own markers*, since a
canonical ordered rendering renumbers: `9.` and `10.` are different
openers of different widths.  Everything above is a fact about one item
and gets instantiated once per item.
*)

(* The list's lines after its first item: each remaining item contributes
   the inter-item separator and then its own indented lines. *)
Definition item_sep (sp : list_spacing) : list string :=
  match sp with Loose => [EmptyString] | Tight => [] end.

(* An item is its marker and its lines.  The marker is per item because a
   canonical ordered rendering renumbers: `9.` and `10.` are different
   openers, of different widths. *)
Definition litem : Type := (marker * list string)%type.

Definition litem_lines (it : litem) : list string :=
  indent_lines (mk_open (fst it)) (mk_cont (fst it)) (snd it).

Local Fixpoint list_tail_lines (sp : list_spacing) (items : list litem) : list string :=
  match items with
  | [] => []
  | it :: rest => (item_sep sp ++ litem_lines it ++ list_tail_lines sp rest)%list
  end.

Local Definition item_checks (ls : list_state) (items : list litem)
  : list task_status :=
  (rev (ls_check ls :: ls_checks ls)
   ++ map (fun it => mk_check (fst it)) items)%list.

Lemma list_lines_cons2 :
  forall sp x xs, xs <> [] ->
    list_lines sp (x :: xs) = (x ++ item_sep sp ++ list_lines sp xs)%list.
Proof. intros sp x xs H. destruct xs; [congruence|reflexivity]. Qed.

Local Lemma list_lines_cons :
  forall sp it rest,
    list_lines sp (map litem_lines (it :: rest))
    = (litem_lines it ++ list_tail_lines sp rest)%list.
Proof.
  intros sp it rest. revert it. induction rest as [|y r IH]; intros it.
  - cbn [map list_lines list_tail_lines]. rewrite app_nil_r. reflexivity.
  - assert (Hne : map litem_lines (y :: r) <> []).
    { cbn [map]. intros HH. discriminate HH. }
    change (map litem_lines (it :: y :: r))
      with (litem_lines it :: map litem_lines (y :: r)).
    rewrite (list_lines_cons2 sp _ _ Hne), (IH y).
    cbn [list_tail_lines]. rewrite !app_assoc. reflexivity.
Qed.

(*
Uniformity for the whole list
-----------------------------

One statement over a list of items, and it is what removes the mutual
dependency between the roundtrip's block layer and its list layer: it
mentions no `cblock` and no acceptance predicate, only line lists, so
nothing about the canonical form has to be known to state or prove it.
One proof, every construct -- including a nested list, which is why it
subsumes the per-depth list reasoning.

The spacing is the only part that is not a plain map.  It is Loose when
some item's own lines force it, when an item before the last ends with a
blank still armed, or when the rendering separates items by a blank at
all -- which needs two items, since a one-item list emits no separator.
*)

(* What the first line of an item must satisfy for the marker line to
   open the item: it is not blank, the marker line does not form a
   thematic break, and it does not turn the marker into a task marker,
   the other way a first line can change what the opener is: a bullet
   followed by `[x] ` is a task marker. *)
Definition item_shape_ok (m : marker) (L : list string) : bool :=
  match L with
  | [] => false
  | l0 :: _ =>
      (negb (is_thematic ((mk_open m) ++ l0))
       && negb (task_start l0)
       && nonblank l0)%bool
  end.

(* The shape, and what the list's spacing is read through: no spec is
   open on a line of the item (`run_safe`, for `Tightness`), no fence is
   left open inside it, and it does not end blank or on a block
   attribute. *)
Definition item_ok (m : marker) (L : list string) : bool :=
  match L with
  | [] => false
  | l0 :: more =>
      (negb (is_thematic ((mk_open m) ++ l0))
       && negb (task_start l0)
       && nonblank l0
       && run_safe more (snd (step l0 (PPara [])))
       && match more with [] => true | _ => item_end_ok (last more EmptyString) end)%bool
  end.

Lemma item_ok_shape :
  forall m L, item_ok m L = true -> item_shape_ok m L = true.
Proof.
  intros m [|l0 more] H; [discriminate H|]. cbn [item_ok] in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. exact H.
Qed.

(* An item's own first line is a list marker, and a list marker opens no
   block whose end is announced, so no key can claim it out of column
   (5.2). *)
Local Lemma item_shape_marker_unclaimable :
  forall m l0 more, marker_ok m = true -> item_shape_ok m (l0 :: more) = true ->
    claimable (classify ((mk_open m) ++ l0)) = false.
Proof.
  intros m l0 more Hm Hok. cbn [item_shape_ok] in Hok.
  apply andb_prop in Hok as [Hok _].
  apply andb_prop in Hok as [Hth Hts].
  apply negb_true_iff in Hth. apply negb_true_iff in Hts.
  rewrite (classify_marker_open m l0 Hm Hth (task_start_shadow m l0 Hts)).
  reflexivity.
Qed.

(* Every item recognized, and every item's marker admitting the styles
   the list opened with -- which is what keeps the sibling narrowing from
   moving the set, and so from ending the list or renaming its style.  A
   renumbering decimal list satisfies it because `9.` and `10.` name the
   same style; a roman list satisfies it whenever its first numeral is
   unambiguous, since every later numeral still offers roman. *)
Definition items_ok_at (S : list (lstyle * nat)) (items : list litem) : bool :=
  forallb (fun it => marker_ok (fst it)
                     && marker_tasks_ok (@btasks K) (fst it)
                     && item_ok (fst it) (snd it)
                     && admits_styles S (fst it))%bool items.

(* The instance where the list's set is exactly its first marker's, which
   is every list whose first marker names one style. *)
Definition items_ok (m0 : marker) (items : list litem) : bool :=
  items_ok_at (mk_styles m0) items.

(* The same of the items' shape alone. *)
Definition items_shape_at (S : list (lstyle * nat)) (items : list litem) : bool :=
  forallb (fun it => marker_ok (fst it)
                     && marker_tasks_ok (@btasks K) (fst it)
                     && item_shape_ok (fst it) (snd it)
                     && admits_styles S (fst it))%bool items.

Definition items_shape_ok (m0 : marker) (items : list litem) : bool :=
  items_shape_at (mk_styles m0) items.

Lemma items_ok_at_shape :
  forall S items, items_ok_at S items = true -> items_shape_at S items = true.
Proof.
  intros S items. unfold items_ok_at, items_shape_at.
  induction items as [|it rest IH]; [reflexivity|].
  cbn [forallb]. intros H. apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [H Hadm]. apply andb_prop in H as [Hm Hok].
  rewrite Hm, (item_ok_shape _ _ Hok), Hadm, (IH Hrest). reflexivity.
Qed.

(** Whether the rendering has a separator blank: a blank between two
    items loosens the list, whatever the item before it left open, so
    the list is loose as soon as there is one.

    The last item is never the left of a pair, so a one-item list has no
    separator at all, which is why a `Loose` single item renders and
    parses back as `Tight`. *)
Definition seps_loosen (itemss : list (list string)) : bool :=
  match itemss with
  | _ :: _ :: _ => true
  | _ => false
  end.

(** The list's spacing, read off its items' lines.  Loose when an item
    forces it, or when a separator blank in the rendering is spent here
    rather than by an item's own trailing list. *)
Definition list_spacing_of (sp : list_spacing) (itemss : list (list string)) : list_spacing :=
  if (existsb (fun L => item_loose L) itemss
      || match sp with
         | Loose => seps_loosen itemss
         | Tight => false
         end)%bool
  then Loose else Tight.

(** The same for items of any lines: an item before the last that ends
    with a blank armed has it spent by the next item's marker.  Items
    `item_ok` admits never end so (`list_scan_spacing_of`). *)
Definition list_scan_spacing (sp : list_spacing) (itemss : list (list string)) : list_spacing :=
  if (existsb (fun L => item_loose L) itemss
      || existsb (fun L => item_gap L) (removelast itemss)
      || match sp with
         | Loose => seps_loosen itemss
         | Tight => false
         end)%bool
  then Loose else Tight.

(* The verdict from a point between two items: `lo` and `bl` are the
   list's flags there, `aw` whether the item just ended has attributes
   waiting, and `rest` the items still to come.  With none, `finish`
   settles the flags; otherwise the next marker spends an armed blank,
   and a separator arms one. *)
Local Definition tail_verdict (lo bl aw : bool) (sp : list_spacing)
                        (rest : list (list string)) : bool :=
  match rest with
  | [] => (lo || (aw && bl))%bool
  | _ :: _ =>
      match sp with
      | Loose => true
      | Tight => (lo || bl
                  || existsb (fun L => item_loose L) rest
                  || existsb (fun L => item_gap L) (removelast rest))%bool
      end
  end.

Local Lemma tail_verdict_cons :
  forall lo bl aw sp L rest,
    tail_verdict (match sp with Tight => (lo || bl)%bool | Loose => true end
                  || item_loose L)%bool
      (item_gap L) (attr_waits (snd (run_lines L (PPara [])))) sp rest
    = tail_verdict lo bl aw sp (L :: rest).
Proof.
  intros lo bl aw sp L rest.
  pose proof (lines_loose_settled L (PPara []) false false) as Hs.
  fold (item_gap L) (item_loose L) in Hs.
  destruct sp, rest as [|L' rest'].
  - cbn [tail_verdict existsb removelast].
    destruct (attr_waits _ && item_gap L)%bool;
      [rewrite (Hs eq_refl)|]; rewrite ?orb_true_r, ?orb_false_r; reflexivity.
  - remember (L' :: rest') as R eqn:ER.
    assert (HR : forall a b c, tail_verdict a b c Tight R
                 = (a || b || existsb (fun L => item_loose L) R
                    || existsb (fun L => item_gap L) (removelast R))%bool)
      by (intros; subst R; reflexivity).
    rewrite HR. cbn [tail_verdict].
    replace (removelast (L :: R)) with (L :: removelast R)
      by (subst R; reflexivity).
    cbn [existsb].
    destruct lo, bl, (item_loose L), (item_gap L),
      (existsb (fun L => item_loose L) R),
      (existsb (fun L => item_gap L) (removelast R)); reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Local Lemma tail_verdict_scan :
  forall sp L rest,
    (if tail_verdict (item_loose L) (item_gap L)
          (attr_waits (snd (run_lines L (PPara [])))) sp rest
     then Loose else Tight)
    = list_scan_spacing sp (L :: rest).
Proof.
  intros sp L rest. unfold list_scan_spacing.
  pose proof (lines_loose_settled L (PPara []) false false) as Hs.
  fold (item_gap L) (item_loose L) in Hs.
  destruct rest as [|L' rest'].
  - cbn [tail_verdict existsb removelast seps_loosen].
    destruct (attr_waits _ && item_gap L)%bool;
      [rewrite (Hs eq_refl)|]; destruct sp, (item_loose L); reflexivity.
  - cbn [seps_loosen]. remember (L' :: rest') as R eqn:ER.
    replace (removelast (L :: R)) with (L :: removelast R)
      by (subst R; reflexivity).
    assert (HR : forall a b c s, tail_verdict a b c s R
                 = match s with
                   | Loose => true
                   | Tight => (a || b || existsb (fun L => item_loose L) R
                               || existsb (fun L => item_gap L) (removelast R))%bool
                   end)
      by (intros a b c s; subst R; destruct s; reflexivity).
    rewrite HR. cbn [existsb].
    destruct sp, (item_loose L), (item_gap L),
      (existsb (fun L => item_loose L) R),
      (existsb (fun L => item_gap L) (removelast R)); reflexivity.
Qed.

(* The state an item's lines leave, as the list holds it. *)
Local Definition item_final (it : litem) : pstate :=
  pad_state (mk_pad (fst it)) (snd (run_lines (snd it) (PPara []))).

(* The state the last of `items` ends in, `inner` when there are none. *)
Local Fixpoint list_end (inner : pstate) (items : list litem) : pstate :=
  match items with
  | [] => inner
  | it :: rest => list_end (item_final it) rest
  end.

Local Lemma last_cons_default :
  forall {A : Type} (a d : A) l, last (a :: l) d = last l a.
Proof.
  intros A a d l. revert a d. induction l as [|b l IH]; intros a d; [reflexivity|].
  change (last (a :: b :: l) d) with (last (b :: l) d).
  rewrite !IH. reflexivity.
Qed.

Local Lemma list_end_last :
  forall it rest, list_end (item_final it) rest = item_final (last (it :: rest) it).
Proof.
  intros it rest. revert it. induction rest as [|it' rest IH]; intros it; [reflexivity|].
  cbn [list_end]. rewrite IH, !last_cons_default. reflexivity.
Qed.

Local Lemma list_end_Forall :
  forall (P : pstate -> Prop) items inner,
    P inner -> Forall (fun it => P (item_final it)) items -> P (list_end inner items).
Proof.
  intros P items. induction items as [|it rest IH]; intros inner Hi Hs; [exact Hi|].
  exact (IH _ (Forall_inv Hs) (Forall_inv_tail Hs)).
Qed.

(* What the list asks of the state an item ends in.  The next item's
   marker, directly or after the separator blank, is not claimed by a
   key the item left open; and the separator blank changes nothing the
   item closes to. *)
Local Definition closes (st : pstate) : Prop :=
  (forall l, claimable (classify l) = false ->
     key_claims l st = false
     /\ key_claims l (snd (step EmptyString st)) = false)
  /\ (fst (step EmptyString st) ++ finish (snd (step EmptyString st)))%list
     = finish st.

Local Lemma blank_safe_closes :
  forall st, blank_safe st = true -> closes st.
Proof.
  intros st H. split.
  - intros l Hl. split.
    + exact (key_claims_not_claimable l st Hl H).
    + exact (step_blank_key_claims EmptyString st
               (classify_blank EmptyString eq_refl) H l).
  - exact (step_blank_finish EmptyString st (classify_blank EmptyString eq_refl) H).
Qed.

Local Lemma reached_closes :
  bkeyed = false -> forall st, reached st = true -> closes st.
Proof.
  intros Hk st H. split.
  - intros l _. split.
    + exact (reached_key_claims l st H).
    + exact (reached_key_claims l _ (step_reached Hk EmptyString st H)).
  - exact (reached_blank_finish Hk st H).
Qed.

(* The scan's flags, as the verdict reads them. *)
Local Lemma scan_verdict :
  forall m more st ls sp rest,
    tail_verdict
      (ls_loose (scan_list_content m ls (pad_state (mk_pad m) st) more))
      (ls_blanks (scan_list_content m ls (pad_state (mk_pad m) st) more))
      (attr_waits (pad_state (mk_pad m) (snd (run_lines more st)))) sp rest
    = tail_verdict (lines_loose (ls_loose ls) (ls_blanks ls) st more)
        (lines_gap (ls_blanks ls) st more)
        (attr_waits (snd (run_lines more st))) sp rest.
Proof.
  intros m more st ls sp rest.
  destruct (scan_flags m more st ls) as [H1 H2].
  rewrite pad_state_attr_waits, <- H2, <- H1.
  destruct rest as [|L' rest']; [|destruct sp; [|reflexivity]];
    cbn [tail_verdict];
    destruct (ls_loose _), (ls_blanks _), (attr_waits _); reflexivity.
Qed.

(*
The induction over the items
----------------------------

`Q` is what is known of the state each item ends in.  The induction
needs only that it `closes`: `blank_safe` for the theorems under
`item_ok`, `reached` for the shape alone.  `Q_end` is what the ending asks of
the state the last item ends in (`list_end`): nothing at the end of the
input, and for a line that closes the list after a blank, that the
blank closes what the item has open (`parse_list_close`).

`post` and `out` are what follows the list in the input and in the
output: the lemmas say nothing about how the list ends, so one induction
serves both endings.
*)
Section Items.
Variable Q : pstate -> Prop.
Hypothesis Q_closes : forall st, Q st -> closes st.
Variable Q_end : pstate -> Prop.

Local Lemma parse_item_and_tail_narrow :
  forall S S' Sout m sp l0 more rest post out ls done inner,
    S' <> [] -> marker_ok m = true -> marker_tasks_ok (@btasks K) m = true ->
    narrow S (mk_sty m) = S' ->
    ls_indent ls = 0 -> ls_styles ls = S ->
    key_claims ((mk_open m) ++ l0) inner = false ->
    item_shape_ok m (l0 :: more) = true ->
    (forall ls2 done2,
       ls_indent ls2 = 0 -> ls_styles ls2 = S' ->
       parse_lines (list_tail_lines sp rest ++ post)%list
         (PList ls2 done2 (item_final (m, l0 :: more)))
       = styles_list_checked Sout
           (if tail_verdict (ls_loose ls2) (ls_blanks ls2)
                 (attr_waits (item_final (m, l0 :: more))) sp (map snd rest)
            then Loose else Tight)
           (item_checks ls2 rest)
           (rev (ls_items ls2)
            ++ (rev done2 ++ finish (item_final (m, l0 :: more)))%list
            :: map (fun it => parse_lines (snd it) (PPara [])) rest) :: out) ->
    parse_lines (litem_lines (m, l0 :: more)
                 ++ (list_tail_lines sp rest ++ post))%list (PList ls done inner)
    = styles_list_checked Sout
        (if tail_verdict (ls_loose ls || ls_blanks ls || item_loose (l0 :: more))
              (item_gap (l0 :: more))
              (attr_waits (snd (run_lines (l0 :: more) (PPara []))))
              sp (map snd rest)
         then Loose else Tight)
        (item_checks ls ((m, l0 :: more) :: rest))
        (rev (ls_items ls) ++ (rev done ++ finish inner)%list
         :: parse_lines (l0 :: more) (PPara [])
         :: map (fun it => parse_lines (snd it) (PPara [])) rest) :: out.
Proof.
  intros S S' Sout m sp l0 more rest post out ls done inner
         HS' Hm Htasks Hsty Hind Hmark Hkc Hok IH.
  unfold litem_lines. cbn [fst snd].
  cbn [item_shape_ok] in Hok.
  apply andb_prop in Hok as [Hok Hnb].
  apply andb_prop in Hok as [Hth Hts].
  apply negb_true_iff in Hts. apply (task_start_shadow m) in Hts.
  apply negb_true_iff in Hth.
  assert (Hnb' : is_blank l0 = false).
  { unfold nonblank in Hnb. apply negb_true_iff in Hnb. exact Hnb. }
  assert (Hcl : classify l0 <> KBlank).
  { intros E. apply classify_kblank_blank in E. rewrite E in Hnb'. discriminate. }
  rewrite parse_lines_app_run.
  rewrite (run_item_sibling_narrow m Hm Htasks l0 more ls done inner Hind Hkc
             (ltac:(rewrite Hmark, Hsty; exact HS'))
             Hth Hts).
  rewrite Hmark, Hsty.
  cbn [fst snd app].
  set (item := (rev done ++ finish inner)%list).
  set (ls0 := list_next (list_narrow ls S') item (mk_check m) ((mk_open m) ++ l0)).
  set (ls1 := scan_list_content m ls0
                (pad_state (mk_pad m) (snd (step l0 (PPara [])))) more).
  set (R := run_lines (l0 :: more) (PPara [])).
  change (pad_state (mk_pad m) (snd R)) with (item_final (m, l0 :: more)).
  pose proof (scan_list_content_fields m more
                (pad_state (mk_pad m) (snd (step l0 (PPara [])))) ls0)
    as [Hf1 [Hf2 [Hf3 [Hf4 [Hf5 _]]]]].
  assert (Hitems : ls_items ls1 = item :: ls_items ls).
  { unfold ls1. rewrite Hf3. reflexivity. }
  assert (Hchecks : item_checks ls1 rest
                    = item_checks ls ((m, l0 :: more) :: rest)).
  { unfold item_checks, ls1. rewrite Hf4, Hf5.
    unfold ls0, list_next, list_narrow. cbn [ls_check ls_checks map fst].
    cbn [rev]. rewrite <- app_assoc. reflexivity. }
  assert (Hind1 : ls_indent ls1 = 0).
  { unfold ls1. rewrite Hf1. exact Hind. }
  assert (Hmark1 : ls_styles ls1 = S').
  { unfold ls1. rewrite Hf2. reflexivity. }
  assert (Hv : tail_verdict (ls_loose ls1) (ls_blanks ls1)
                 (attr_waits (item_final (m, l0 :: more))) sp (map snd rest)
               = tail_verdict
                   (ls_loose ls || ls_blanks ls || item_loose (l0 :: more))
                   (item_gap (l0 :: more)) (attr_waits (snd R)) sp (map snd rest)).
  { unfold ls1, item_final, R. cbn [fst snd].
    rewrite run_lines_snd_cons, scan_verdict.
    unfold ls0, list_next, list_narrow. cbn [ls_loose ls_blanks].
    rewrite lines_loose_or, <- (lines_loose_cons_nonblank l0 more Hcl),
      <- (item_gap_cons_nonblank l0 more Hcl).
    reflexivity. }
  assert (Hdone1 : (rev (rev (fst R)) ++ finish (item_final (m, l0 :: more)))%list
                   = parse_lines (l0 :: more) (PPara [])).
  { unfold item_final. cbn [fst snd]. rewrite rev_involutive, pad_state_finish.
    unfold R. symmetry. apply parse_lines_run, surjective_pairing. }
  rewrite (IH ls1 (rev (fst R)) Hind1 Hmark1).
  rewrite Hitems, Hchecks, Hv, Hdone1.
  cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

(* One item of the tail, with the separator in front of it. *)
Local Lemma parse_item_peel :
  forall S S' Sout sp mi l0 more rest post out ls done inner,
    S' <> [] -> marker_ok mi = true -> marker_tasks_ok (@btasks K) mi = true ->
    narrow S (mk_sty mi) = S' ->
    item_shape_ok mi (l0 :: more) = true ->
    (forall ls2 done2,
       ls_indent ls2 = 0 -> ls_styles ls2 = S' ->
       parse_lines (list_tail_lines sp rest ++ post)%list
         (PList ls2 done2 (item_final (mi, l0 :: more)))
       = styles_list_checked Sout
           (if tail_verdict (ls_loose ls2) (ls_blanks ls2)
                 (attr_waits (item_final (mi, l0 :: more))) sp (map snd rest)
            then Loose else Tight)
           (item_checks ls2 rest)
           (rev (ls_items ls2)
            ++ (rev done2 ++ finish (item_final (mi, l0 :: more)))%list
            :: map (fun it => parse_lines (snd it) (PPara [])) rest) :: out) ->
    ls_indent ls = 0 -> ls_styles ls = S -> Q inner ->
    parse_lines (list_tail_lines sp ((mi, l0 :: more) :: rest) ++ post)%list
                (PList ls done inner)
    = styles_list_checked Sout
        (if tail_verdict (ls_loose ls) (ls_blanks ls) (attr_waits inner) sp
              (map snd ((mi, l0 :: more) :: rest))
         then Loose else Tight)
        (item_checks ls ((mi, l0 :: more) :: rest))
        (rev (ls_items ls) ++ (rev done ++ finish inner)%list
         :: map (fun it => parse_lines (snd it) (PPara []))
                ((mi, l0 :: more) :: rest)) :: out.
Proof.
  intros S S' Sout sp mi l0 more rest post out ls done inner
         HS' Hmi Htasks Hstyeq HL IH Hind Hmark HQ.
  destruct (Q_closes inner HQ) as [Hkey Hfin].
  destruct (Hkey _ (item_shape_marker_unclaimable mi l0 more Hmi HL))
    as [Hk0 Hk1].
  cbn [map snd]. rewrite <- (tail_verdict_cons _ _ (attr_waits inner)).
  cbn [list_tail_lines]. rewrite <- !app_assoc. destruct sp.
  - cbn [item_sep app].
    exact (parse_item_and_tail_narrow S S' Sout mi Tight l0 more rest post out
             ls done inner HS' Hmi Htasks Hstyeq Hind Hmark Hk0 HL IH).
  - change (item_sep Loose ++ (litem_lines (mi, l0 :: more)
                               ++ (list_tail_lines Loose rest ++ post)))%list
      with (EmptyString :: (litem_lines (mi, l0 :: more)
                            ++ (list_tail_lines Loose rest ++ post)))%list.
    rewrite (parse_lines_step _ _ _ _ _
               (step_list_blank EmptyString ls done inner _ _
                  (classify_blank EmptyString eq_refl) (surjective_pairing _))).
    cbn [app].
    rewrite (parse_item_and_tail_narrow S S' Sout mi Loose l0 more rest post out
               (list_blank (list_settle _ ls))
               (rev (fst (step EmptyString inner)) ++ done)%list
               (snd (step EmptyString inner))
               HS' Hmi Htasks Hstyeq
               ltac:(cbn [list_blank list_settle ls_indent]; exact Hind)
               ltac:(cbn [list_blank list_settle ls_styles]; exact Hmark)
               Hk1 HL IH).
    change (item_checks (list_blank (list_settle ?b ls)) ?its)
      with (item_checks ls its).
    cbn [list_blank list_settle ls_loose ls_blanks ls_items].
    rewrite rev_app_distr, rev_involutive, <- app_assoc, Hfin.
    rewrite orb_true_r. reflexivity.
Qed.

(* `Hclose` is the whole of what the ending contributes: from any list
   state the parser has reached, `post` emits that list and then whatever
   `out` is.  Both endings satisfy it -- `parse_lines_nil` for end of
   input, `parse_list_close` for a closing line. *)
Local Lemma parse_list_tail :
  forall S sp items post out ls done inner,
    S <> [] ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> Q_end inner2 ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    ls_indent ls = 0 -> ls_styles ls = S -> Q inner ->
    items_shape_at S items = true ->
    Forall (fun it => Q (item_final it)) items ->
    Q_end (list_end inner items) ->
    parse_lines (list_tail_lines sp items ++ post)%list (PList ls done inner)
    = styles_list_checked S
        (if tail_verdict (ls_loose ls) (ls_blanks ls) (attr_waits inner) sp
              (map snd items)
         then Loose else Tight)
        (item_checks ls items)
        (rev (ls_items ls) ++ (rev done ++ finish inner)%list
         :: map (fun it => parse_lines (snd it) (PPara [])) items) :: out.
Proof.
  intros S sp items. induction items as [|it rest IH];
    intros post out ls done inner HS Hclose Hind Hmark HQ Hok HQs HE.
  - cbn [list_tail_lines app map]. rewrite (Hclose ls done inner Hind HE).
    cbn [finish rev app tail_verdict].
    rewrite (list_block_styles S (list_settle (attr_waits inner) ls) _
               ltac:(cbn [list_settle ls_styles]; exact Hmark)).
    unfold item_checks. cbn [map list_settle ls_loose ls_check ls_checks ls_items].
    rewrite app_nil_r. cbn [rev app]. reflexivity.
  - destruct it as [mi L]. destruct L as [|l0 more];
      [cbn [items_shape_at forallb item_shape_ok fst snd] in Hok;
       rewrite ?andb_false_r in Hok; discriminate|].
    cbn [items_shape_at forallb] in Hok. apply andb_prop in Hok as [HL Hrest].
    change (forallb _ rest) with (items_shape_at S rest) in Hrest.
    cbn [fst snd] in HL.
    apply andb_prop in HL as [HL Hstyeq].
    apply andb_prop in HL as [Hmi HL].
    apply andb_prop in Hmi as [Hmi Htasks].
    apply narrow_admits_styles in Hstyeq.
    pose proof (Forall_inv HQs) as HQi. pose proof (Forall_inv_tail HQs) as HQrest.
    apply (parse_item_peel S S S sp mi l0 more rest post out ls done inner
             HS Hmi Htasks Hstyeq HL); try assumption.
    intros ls2 done2 H1 H2.
    exact (IH post out ls2 done2 _ HS Hclose H1 H2 HQi Hrest HQrest HE).
Qed.

(* One peel: the set resolves at this item and the rest holds it.  This
   is all the ambiguous first marker needs, because a candidate set has
   at most two members -- one narrowing settles it and nothing later
   moves it. *)
Local Lemma parse_list_tail_head_narrow :
  forall S S' sp mi l0 more rest post out ls done inner,
    S' <> [] -> marker_ok mi = true -> marker_tasks_ok (@btasks K) mi = true ->
    narrow S (mk_sty mi) = S' ->
    item_shape_ok mi (l0 :: more) = true ->
    items_shape_at S' rest = true ->
    Forall (fun it => Q (item_final it)) ((mi, l0 :: more) :: rest) ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> Q_end inner2 ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    ls_indent ls = 0 -> ls_styles ls = S -> Q inner ->
    Q_end (list_end inner ((mi, l0 :: more) :: rest)) ->
    parse_lines (list_tail_lines sp ((mi, l0 :: more) :: rest) ++ post)%list
                (PList ls done inner)
    = styles_list_checked S'
        (if tail_verdict (ls_loose ls) (ls_blanks ls) (attr_waits inner) sp
              (map snd ((mi, l0 :: more) :: rest))
         then Loose else Tight)
        (item_checks ls ((mi, l0 :: more) :: rest))
        (rev (ls_items ls) ++ (rev done ++ finish inner)%list
         :: map (fun it => parse_lines (snd it) (PPara []))
                ((mi, l0 :: more) :: rest)) :: out.
Proof.
  intros S S' sp mi l0 more rest post out ls done inner
         HS' Hmi Htasks Hstyeq HL Hrest HQs Hclose Hind Hmark HQ HE.
  pose proof (Forall_inv HQs) as HQi. pose proof (Forall_inv_tail HQs) as HQrest.
  apply (parse_item_peel S S' S' sp mi l0 more rest post out ls done inner
           HS' Hmi Htasks Hstyeq HL); try assumption.
  intros ls2 done2 H1 H2.
  exact (parse_list_tail S' sp rest post out ls2 done2 _
           HS' Hclose H1 H2 HQi Hrest HQrest HE).
Qed.

(* The first item: its marker line opens the list.  What the list state
   holds after it, in the terms the tail lemmas conclude in. *)
Local Lemma run_first_item :
  forall m0 l0 more,
    marker_ok m0 = true -> marker_tasks_ok (@btasks K) m0 = true ->
    item_shape_ok m0 (l0 :: more) = true ->
    exists ls1 done1,
      run_lines (litem_lines (m0, l0 :: more)) (PPara [])
      = ([], PList ls1 done1 (item_final (m0, l0 :: more)))
      /\ ls_indent ls1 = 0 /\ ls_styles ls1 = mk_styles m0 /\ ls_items ls1 = []
      /\ (forall rest, item_checks ls1 rest
                       = mk_check m0 :: map (fun it => mk_check (fst it)) rest)
      /\ (forall sp rest,
            (if tail_verdict (ls_loose ls1) (ls_blanks ls1)
                  (attr_waits (item_final (m0, l0 :: more))) sp rest
             then Loose else Tight)
            = list_scan_spacing sp ((l0 :: more) :: rest))
      /\ (rev done1 ++ finish (item_final (m0, l0 :: more)))%list
         = parse_lines (l0 :: more) (PPara []).
Proof.
  intros m0 l0 more Hm0 Htasks Hok.
  cbn [item_shape_ok] in Hok.
  apply andb_prop in Hok as [Hok Hnb].
  apply andb_prop in Hok as [Hth Hts].
  apply negb_true_iff in Hts. apply (task_start_shadow m0) in Hts.
  apply negb_true_iff in Hth.
  assert (Hcl : classify l0 <> KBlank).
  { intros E. apply classify_kblank_blank in E.
    unfold nonblank in Hnb. rewrite E in Hnb. discriminate. }
  exists (item_scan m0 l0 more), (rev (fst (run_lines (l0 :: more) (PPara [])))).
  pose proof (scan_list_content_fields m0 more
                (pad_state (mk_pad m0) (snd (step l0 (PPara []))))
                (list_opened ((mk_open m0) ++ l0) 0 (mk_styles m0) (mk_check m0)))
    as [Hf1 [Hf2 [Hf3 [Hf4 [Hf5 _]]]]].
  fold (item_scan m0 l0 more) in Hf1, Hf2, Hf3, Hf4, Hf5.
  split; [|split; [exact Hf1|split; [exact Hf2|split; [exact Hf3|split; [|split]]]]].
  - unfold litem_lines. cbn [fst snd].
    exact (run_item_open m0 Hm0 Htasks l0 more Hth Hts).
  - intros rest. unfold item_checks. rewrite Hf4, Hf5. reflexivity.
  - intros sp rest. rewrite <- tail_verdict_scan.
    unfold item_scan, item_final. cbn [fst snd].
    rewrite run_lines_snd_cons, scan_verdict.
    cbn [list_opened ls_loose ls_blanks].
    rewrite <- (lines_loose_cons_nonblank l0 more Hcl),
      <- (item_gap_cons_nonblank l0 more Hcl), <- run_lines_snd_cons.
    reflexivity.
  - unfold item_final. cbn [fst snd]. rewrite rev_involutive, pad_state_finish.
    symmetry. apply parse_lines_run, surjective_pairing.
Qed.

(* The whole list, with the ending left open: the three forms differ in
   how many of the first markers it takes to settle the list's style. *)
Local Lemma list_gen :
  forall m0 sp L0 tail post out,
    marker_ok m0 = true ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> Q_end inner2 ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    items_shape_ok m0 ((m0, L0) :: tail) = true ->
    Forall (fun it => Q (item_final it)) ((m0, L0) :: tail) ->
    Q_end (list_end (PPara []) ((m0, L0) :: tail)) ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: tail))
                 ++ post)%list (PPara [])
    = marker_list_checked m0 (list_scan_spacing sp (map snd ((m0, L0) :: tail)))
             (map (fun it => mk_check (fst it)) ((m0, L0) :: tail))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: tail)) :: out.
Proof.
  intros m0 sp L0 tail post out Hm0 Hclose Hok HQs HE.
  destruct L0 as [|l0 more];
    [cbn [items_shape_ok items_shape_at forallb item_shape_ok fst snd] in Hok;
     rewrite ?andb_false_r in Hok; discriminate|].
  cbn [items_shape_ok items_shape_at forallb] in Hok.
  apply andb_prop in Hok as [HL Htail].
  change (forallb _ tail) with (items_shape_at (mk_styles m0) tail) in Htail.
  cbn [fst snd] in HL.
  apply andb_prop in HL as [HL _].
  apply andb_prop in HL as [HLmi HL].
  apply andb_prop in HLmi as [_ Htasks].
  pose proof (Forall_inv HQs) as HQ0. pose proof (Forall_inv_tail HQs) as HQtail.
  destruct (run_first_item m0 l0 more Hm0 Htasks HL)
    as (ls1 & done1 & Hrun & Hind & Hsty & Hitems & Hchecks & Hv & Hdone).
  rewrite list_lines_cons, <- app_assoc, parse_lines_app_run, Hrun.
  cbn [fst snd app].
  rewrite (parse_list_tail (mk_styles m0) sp tail post out ls1 done1 _
             (mk_styles_nonempty m0 Hm0) Hclose Hind Hsty HQ0 Htail HQtail HE).
  rewrite Hitems, Hchecks, Hv, Hdone. reflexivity.
Qed.

Local Lemma list_gen_narrow :
  forall m0 m1 S' sp L0 L1 tail post out,
    marker_ok m0 = true -> marker_ok m1 = true ->
    marker_tasks_ok (@btasks K) m0 = true ->
    marker_tasks_ok (@btasks K) m1 = true ->
    S' <> [] -> narrow (mk_styles m0) (mk_sty m1) = S' ->
    item_shape_ok m0 L0 = true -> item_shape_ok m1 L1 = true ->
    items_shape_at S' tail = true ->
    Forall (fun it => Q (item_final it)) ((m0, L0) :: (m1, L1) :: tail) ->
    Q_end (list_end (PPara []) ((m0, L0) :: (m1, L1) :: tail)) ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> Q_end inner2 ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: (m1, L1) :: tail))
                 ++ post)%list (PPara [])
    = styles_list_checked S'
        (list_scan_spacing sp (map snd ((m0, L0) :: (m1, L1) :: tail)))
        (map (fun it => mk_check (fst it)) ((m0, L0) :: (m1, L1) :: tail))
        (map (fun it => parse_lines (snd it) (PPara []))
             ((m0, L0) :: (m1, L1) :: tail)) :: out.
Proof.
  intros m0 m1 S' sp L0 L1 tail post out Hm0 Hm1 Htasks0 Htasks1
    HS' Hnar HL0 HL1 Htail HQs HE Hclose.
  destruct L0 as [|l0 more]; [discriminate HL0|].
  destruct L1 as [|l1 more1]; [discriminate HL1|].
  pose proof (Forall_inv HQs) as HQ0. pose proof (Forall_inv_tail HQs) as HQtail.
  destruct (run_first_item m0 l0 more Hm0 Htasks0 HL0)
    as (ls1 & done1 & Hrun & Hind & Hsty & Hitems & Hchecks & Hv & Hdone).
  rewrite list_lines_cons, <- app_assoc, parse_lines_app_run, Hrun.
  cbn [fst snd app].
  rewrite (parse_list_tail_head_narrow (mk_styles m0) S' sp m1 l1 more1 tail
             post out ls1 done1 _ HS' Hm1 Htasks1 Hnar HL1 Htail HQtail
             Hclose Hind Hsty HQ0 HE).
  rewrite Hitems, Hchecks, Hv, Hdone. reflexivity.
Qed.

Local Lemma list_gen_narrow2 :
  forall m0 m1 m2 S1 S2 sp L0 L1 L2 tail post out,
    marker_ok m0 = true -> marker_ok m1 = true -> marker_ok m2 = true ->
    marker_tasks_ok (@btasks K) m0 = true ->
    marker_tasks_ok (@btasks K) m1 = true ->
    marker_tasks_ok (@btasks K) m2 = true ->
    S1 <> [] -> S2 <> [] ->
    narrow (mk_styles m0) (mk_sty m1) = S1 ->
    narrow S1 (mk_sty m2) = S2 ->
    item_shape_ok m0 L0 = true -> item_shape_ok m1 L1 = true ->
    item_shape_ok m2 L2 = true ->
    items_shape_at S2 tail = true ->
    Forall (fun it => Q (item_final it))
      ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail) ->
    Q_end (list_end (PPara []) ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail)) ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> Q_end inner2 ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    parse_lines (list_lines sp
                   (map litem_lines ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail))
                 ++ post)%list (PPara [])
    = styles_list_checked S2
        (list_scan_spacing sp
           (map snd ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail)))
        (map (fun it => mk_check (fst it))
             ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail))
        (map (fun it => parse_lines (snd it) (PPara []))
             ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail)) :: out.
Proof.
  intros m0 m1 m2 S1 S2 sp L0 L1 L2 tail post out
         Hm0 Hm1 Hm2 Htasks0 Htasks1 Htasks2
         HS1 HS2 Hnar1 Hnar2 HL0 HL1 HL2 Htail HQs HE Hclose.
  destruct L0 as [|l0 more]; [discriminate HL0|].
  destruct L1 as [|l1 more1]; [discriminate HL1|].
  destruct L2 as [|l2 more2]; [discriminate HL2|].
  pose proof (Forall_inv HQs) as HQ0. pose proof (Forall_inv_tail HQs) as HQtail.
  pose proof (Forall_inv HQtail) as HQ1. pose proof (Forall_inv_tail HQtail) as HQtail2.
  destruct (run_first_item m0 l0 more Hm0 Htasks0 HL0)
    as (ls1 & done1 & Hrun & Hind & Hsty & Hitems & Hchecks & Hv & Hdone).
  rewrite list_lines_cons, <- app_assoc, parse_lines_app_run, Hrun.
  cbn [fst snd app].
  rewrite (parse_item_peel (mk_styles m0) S1 S2 sp m1 l1 more1
             ((m2, l2 :: more2) :: tail) post out ls1 done1 _
             HS1 Hm1 Htasks1 Hnar1 HL1
             (fun a b H1 H2 =>
                parse_list_tail_head_narrow S1 S2 sp m2 l2 more2 tail post out a b _
                  HS2 Hm2 Htasks2 Hnar2 HL2 Htail HQtail2 Hclose H1 H2 HQ1 HE)
             Hind Hsty HQ0).
  rewrite Hitems, Hchecks, Hv, Hdone. reflexivity.
Qed.

End Items.

(* What closes a list: not the blank line -- that only records a gap --
   but the line after it, once that line is not blank, not a sibling
   marker, and not indented into the item.  The list is emitted whole and
   the parser restarts on that line from idle.  Of the item, three things
   are needed: the blank changes nothing the list closes to, leaves no
   paragraph `next` could continue, and leaves no key that claims `next`. *)
Local Lemma parse_list_close_by :
  forall ls done inner next tail,
    (fst (step EmptyString (PList ls done inner))
     ++ finish (snd (step EmptyString (PList ls done inner))))%list
    = finish (PList ls done inner) ->
    lazy_ok (snd (step EmptyString inner)) = false ->
    key_claims next (snd (step EmptyString inner)) = false ->
    classify next <> KBlank ->
    (forall m mc chk item, classify next <> KList m mc chk item) ->
    Nat.ltb (ls_indent ls) (indent_of next) = false ->
    parse_lines (EmptyString :: next :: tail) (PList ls done inner)
    = (finish (PList ls done inner) ++ parse_lines (next :: tail) (PPara []))%list.
Proof.
  intros ls done inner next tail Hfin0 Hlazy Hkc Hnb Hnl Hind.
  destruct (step EmptyString inner) as [bs inner'] eqn:Hb.
  cbn [snd] in Hlazy, Hkc.
  rewrite (step_list_blank EmptyString ls done inner bs inner'
             (classify_blank EmptyString eq_refl) Hb) in Hfin0.
  rewrite (parse_lines_step _ _ _ _ _
             (step_list_blank EmptyString ls done inner bs inner'
                (classify_blank EmptyString eq_refl) Hb)).
  cbn [app].
  set (ls' := list_blank (list_settle (stops_waiting inner inner') ls)).
  assert (Hfin : finish (PList ls' (rev bs ++ done)%list inner')
                 = finish (PList ls done inner))
    by exact Hfin0.
  assert (Hind' : list_takes ls' 0 next inner' = false)
    by (unfold list_takes, ls'; rewrite Hkc, Nat.add_0_l; exact Hind).
  (* the four kinds that open directly; the quote and list kinds do not *)
  assert (Hdirect : forall k,
            classify next = k -> direct_open k = true -> k <> KBlank ->
            is_lazy k inner' = false ->
            parse_lines (next :: tail)
              (PList ls' (rev bs ++ done)%list inner')
            = (finish (PList ls done inner)
               ++ parse_lines (next :: tail) (PPara []))%list).
  { intros k Hclass Hk Hkb Hkl.
    rewrite (parse_lines_step _ _ _ _ _
               (step_list_close next k ls' (rev bs ++ done)%list
                  inner' _ _ Hclass Hk Hkb Hind' Hkl (surjective_pairing _))).
    rewrite (parse_lines_step _ _ _ _ _
               (eq_trans (step_idle next k Hclass Hk) (surjective_pairing _))).
    rewrite Hfin, <- app_assoc. reflexivity. }
  destruct (classify next) as [| |f|dl dc|q|lvl txt|m mc chk listrest|kap|flbl frest|rlbl rval|krow|] eqn:Hclass.
  - congruence.
  - apply (Hdirect KThematic eq_refl eq_refl ltac:(discriminate) eq_refl).
  - (* a fence records its column, so it does not open through open_kind *)
    rewrite (parse_lines_step _ _ _ _ _
               (step_list_fence_close next f ls' (rev bs ++ done)%list
                  inner' Hclass Hind')).
    rewrite (parse_lines_step _ _ _ _ _ (step_fence_open next f Hclass)).
    rewrite Hfin. reflexivity.
  - apply (Hdirect (KDiv dl dc) eq_refl eq_refl ltac:(discriminate) eq_refl).
  - rewrite (parse_lines_step _ _ _ _ _
               (step_list_quote_close_any next q ls' (rev bs ++ done)%list
                  inner' Hclass Hind')).
    destruct (step next (PPara [])) as [opened st'] eqn:Es.
    pose proof (step_quote_open_no_blocks next q Hclass) as Hopened.
    rewrite Es in Hopened. cbn [fst] in Hopened. subst opened.
    cbn [snd app].
    rewrite (parse_lines_step _ _ _ _ _ Es), Hfin. reflexivity.
  - apply (Hdirect (KHeading lvl txt) eq_refl eq_refl ltac:(discriminate) eq_refl).
  - exfalso. apply (Hnl m mc chk listrest). reflexivity.
  - rewrite (parse_lines_step _ _ _ _ _
               (step_list_attr_close next kap ls' (rev bs ++ done)%list
                  inner' Hclass Hind')).
    rewrite (parse_lines_step _ _ _ _ _
               (eq_trans (step_attr_open next kap Hclass)
                  (surjective_pairing _))).
    rewrite Hfin, open_attr_fst. reflexivity.
  - destruct (step frest (PPara [])) as [fbs finner] eqn:Hfoot.
    rewrite (parse_lines_step _ _ _ _ _
               (step_list_foot_close next flbl frest ls'
                  (rev bs ++ done)%list inner' fbs finner Hclass Hind' Hfoot)).
    rewrite (parse_lines_step _ _ _ _ _
               (eq_trans (step_foot_open next flbl frest fbs finner Hclass Hfoot)
                  (surjective_pairing _))).
    rewrite Hfin, open_foot_fst. reflexivity.
  - rewrite (parse_lines_step _ _ _ _ _
               (step_list_ref_close next rlbl rval ls' (rev bs ++ done)%list
                  inner' Hclass Hind')).
    rewrite (parse_lines_step _ _ _ _ _ (step_ref_open next rlbl rval Hclass)).
    rewrite Hfin. reflexivity.
  - apply (Hdirect (KRow krow) eq_refl eq_refl ltac:(discriminate) eq_refl).
  - apply (Hdirect KText eq_refl eq_refl ltac:(discriminate) Hlazy).
Qed.

(* Under `blank_safe`.  A key still holding a fence or div is itself not
   `blank_safe`, so the blank retracts or closes every key (5). *)
Local Lemma parse_list_close :
  forall ls done inner next tail,
    blank_safe inner = true ->
    classify next <> KBlank ->
    (forall m mc chk item, classify next <> KList m mc chk item) ->
    Nat.ltb (ls_indent ls) (indent_of next) = false ->
    parse_lines (EmptyString :: next :: tail) (PList ls done inner)
    = (finish (PList ls done inner) ++ parse_lines (next :: tail) (PPara []))%list.
Proof.
  intros ls done inner next tail Hpad.
  pose proof (classify_blank EmptyString eq_refl) as Hb.
  exact (parse_list_close_by ls done inner next tail
           (step_blank_finish EmptyString (PList ls done inner) Hb Hpad)
           (step_blank_lazy_false EmptyString inner Hb Hpad)
           (step_blank_key_claims EmptyString inner Hb Hpad next)).
Qed.

(* Under `reached`, keys off, with no spec open in the item. *)
Local Lemma parse_list_close_reached :
  bkeyed = false ->
  forall ls done inner next tail,
    reached inner = true -> spec_open_in inner = false ->
    classify next <> KBlank ->
    (forall m mc chk item, classify next <> KList m mc chk item) ->
    Nat.ltb (ls_indent ls) (indent_of next) = false ->
    parse_lines (EmptyString :: next :: tail) (PList ls done inner)
    = (finish (PList ls done inner) ++ parse_lines (next :: tail) (PPara []))%list.
Proof.
  intros Hk ls done inner next tail Hr Ho.
  exact (parse_list_close_by ls done inner next tail
           (reached_blank_finish Hk (PList ls done inner) Hr)
           (reached_blank_lazy inner Hr Ho)
           (reached_key_claims next _ (step_reached Hk EmptyString inner Hr))).
Qed.

(*
What `item_ok` adds to the shape
--------------------------------

The state each item ends in is `blank_safe`, and no item ends with a
blank armed, so the spacing is `list_spacing_of`.
*)

Local Lemma item_ok_final :
  forall m L, item_ok m L = true -> blank_safe (item_final (m, L)) = true.
Proof.
  intros m [|l0 more] H; [discriminate H|]. cbn [item_ok] in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [_ Hsafe].
  unfold item_final. cbn [fst snd]. rewrite blank_safe_pad_state.
  apply run_safe_final. cbn [run_safe pad_safe]. exact Hsafe.
Qed.

Lemma item_ok_gap : forall m L, item_ok m L = true -> item_gap L = false.
Proof.
  intros m [|l0 more] H; [discriminate H|]. cbn [item_ok] in H.
  apply andb_prop in H as [H Hlast]. apply andb_prop in H as [H Hsafe].
  apply andb_prop in H as [_ Hnb].
  assert (Hcl : classify l0 <> KBlank).
  { intros E. apply classify_kblank_blank in E.
    unfold nonblank in Hnb. rewrite E in Hnb. discriminate. }
  rewrite (item_gap_cons_nonblank l0 more Hcl).
  destruct more as [|l1 more']; [reflexivity|].
  apply lines_gap_last; [exact Hsafe|discriminate|exact Hlast].
Qed.

Local Lemma items_ok_at_final :
  forall S items, items_ok_at S items = true ->
    Forall (fun it => blank_safe (item_final it) = true) items.
Proof.
  intros S items. unfold items_ok_at.
  induction items as [|[m L] rest IH]; intros H; [constructor|].
  cbn [forallb fst snd] in H. apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [H _]. apply andb_prop in H as [_ Hok].
  constructor; [exact (item_ok_final m L Hok)|exact (IH Hrest)].
Qed.

Local Lemma items_ok_at_gapless :
  forall S items, items_ok_at S items = true ->
    forallb (fun L => negb (item_gap L)) (map snd items) = true.
Proof.
  intros S items. unfold items_ok_at.
  induction items as [|[m L] rest IH]; intros H; [reflexivity|].
  cbn [forallb fst snd map] in H |- *. apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [H _]. apply andb_prop in H as [_ Hok].
  rewrite (item_ok_gap m L Hok), (IH Hrest). reflexivity.
Qed.

Local Lemma list_scan_spacing_gapless :
  forall sp itemss,
    forallb (fun L => negb (item_gap L)) itemss = true ->
    list_scan_spacing sp itemss = list_spacing_of sp itemss.
Proof.
  intros sp itemss H. unfold list_scan_spacing, list_spacing_of.
  assert (Hg : existsb (fun L => item_gap L) (removelast itemss) = false).
  { induction itemss as [|L rest IH]; [reflexivity|].
    cbn [forallb] in H. apply andb_prop in H as [HL Hrest].
    destruct rest as [|L' rest']; [reflexivity|].
    change (removelast (L :: L' :: rest')) with (L :: removelast (L' :: rest')).
    cbn [existsb]. apply negb_true_iff in HL. rewrite HL. exact (IH Hrest). }
  rewrite Hg, orb_false_r. reflexivity.
Qed.

(** Items `item_ok` admits: no item ends with a blank armed, so the
    spacing is `list_spacing_of`. *)
Lemma list_scan_spacing_of :
  forall S sp items,
    items_ok_at S items = true ->
    list_scan_spacing sp (map snd items) = list_spacing_of sp (map snd items).
Proof.
  intros S sp items H.
  exact (list_scan_spacing_gapless sp _ (items_ok_at_gapless S items H)).
Qed.

Local Lemma items_reached :
  bkeyed = false ->
  forall items, Forall (fun it => reached (item_final it) = true) items.
Proof.
  intros Hk items. apply Forall_forall. intros it _. unfold item_final.
  rewrite reached_pad_state. exact (run_lines_reached Hk _ (PPara []) eq_refl).
Qed.

(** Uniformity for a list: every item's contents parse exactly as they
    would at top level, and the list's spacing is a scan of those same
    lines.  Stated over line lists, so it says nothing about the
    canonical form and needs nothing from it.

    It asks only the shape of each item's first line.  An item may hold
    block attributes, end inside a code block, or end on a blank line.
    Keys are off: a key an item leaves holding a code block or a div
    claims the next item's marker (keyed-blocks 5). *)
Theorem list_uniformity_shape :
  forall m0 sp L0 tail,
    bkeyed = false ->
    marker_ok m0 = true ->
    items_shape_ok m0 ((m0, L0) :: tail) = true ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: tail))) (PPara [])
    = [marker_list_checked m0 (list_scan_spacing sp (map snd ((m0, L0) :: tail)))
             (map (fun it => mk_check (fst it)) ((m0, L0) :: tail))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: tail))].
Proof.
  intros m0 sp L0 tail Hk Hm0 Hok.
  rewrite <- (app_nil_r (list_lines sp (map litem_lines ((m0, L0) :: tail)))).
  apply (list_gen (fun st => reached st = true) (reached_closes Hk) (fun _ => True));
    [exact Hm0| |exact Hok| |exact I].
  - intros ls2 done2 inner2 _ _. rewrite parse_lines_nil, app_nil_r. reflexivity.
  - exact (items_reached Hk _).
Qed.

(** The same under `item_ok`, in any configuration, with the ending left
    open (see `parse_list_tail`); the corollaries below are the endings
    that occur. *)
Theorem list_uniformity_gen :
  forall m0 sp L0 tail post out,
    marker_ok m0 = true ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> blank_safe inner2 = true ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    items_ok m0 ((m0, L0) :: tail) = true ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: tail))
                 ++ post)%list (PPara [])
    = marker_list_checked m0 (list_spacing_of sp (map snd ((m0, L0) :: tail)))
             (map (fun it => mk_check (fst it)) ((m0, L0) :: tail))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: tail)) :: out.
Proof.
  intros m0 sp L0 tail post out Hm0 Hclose Hok.
  rewrite <- (list_scan_spacing_of _ sp _ Hok).
  pose proof (items_ok_at_final _ _ Hok) as HF.
  exact (list_gen (fun st => blank_safe st = true) blank_safe_closes
           (fun st => blank_safe st = true)
           m0 sp L0 tail post out Hm0 Hclose
           (items_ok_at_shape _ _ Hok) HF
           (list_end_Forall (fun st => blank_safe st = true) _ (PPara []) eq_refl HF)).
Qed.

Theorem list_uniformity_gen_narrow :
  forall m0 m1 S' sp L0 L1 tail post out,
    marker_ok m0 = true -> marker_ok m1 = true ->
    marker_tasks_ok (@btasks K) m0 = true ->
    marker_tasks_ok (@btasks K) m1 = true ->
    S' <> [] -> narrow (mk_styles m0) (mk_sty m1) = S' ->
    item_ok m1 L1 = true -> L1 <> [] ->
    items_ok_at S' tail = true ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> blank_safe inner2 = true ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    item_ok m0 L0 = true ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: (m1, L1) :: tail))
                 ++ post)%list (PPara [])
    = styles_list_checked S' (list_spacing_of sp (map snd ((m0, L0) :: (m1, L1) :: tail)))
             (map (fun it => mk_check (fst it)) ((m0, L0) :: (m1, L1) :: tail))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: (m1, L1) :: tail)) :: out.
Proof.
  intros m0 m1 S' sp L0 L1 tail post out Hm0 Hm1 Htasks0 Htasks1
    HS' Hnar Hok1 _ Htail Hclose HL.
  rewrite <- (list_scan_spacing_gapless sp)
    by (cbn [map snd forallb];
        rewrite (item_ok_gap m0 L0 HL), (item_ok_gap m1 L1 Hok1);
        exact (items_ok_at_gapless S' tail Htail)).
  assert (HF : Forall (fun it => blank_safe (item_final it) = true)
                ((m0, L0) :: (m1, L1) :: tail)).
  { constructor; [exact (item_ok_final m0 L0 HL)|].
    constructor; [exact (item_ok_final m1 L1 Hok1)|].
    exact (items_ok_at_final S' tail Htail). }
  apply (list_gen_narrow (fun st => blank_safe st = true) blank_safe_closes
           (fun st => blank_safe st = true));
    try assumption; try (apply item_ok_shape; assumption).
  - apply items_ok_at_shape, Htail.
  - exact (list_end_Forall (fun st => blank_safe st = true) _ (PPara []) eq_refl HF).
Qed.

Theorem list_uniformity_gen_narrow2 :
  forall m0 m1 m2 S1 S2 sp L0 L1 L2 tail post out,
    marker_ok m0 = true -> marker_ok m1 = true -> marker_ok m2 = true ->
    marker_tasks_ok (@btasks K) m0 = true ->
    marker_tasks_ok (@btasks K) m1 = true ->
    marker_tasks_ok (@btasks K) m2 = true ->
    S1 <> [] -> S2 <> [] ->
    narrow (mk_styles m0) (mk_sty m1) = S1 ->
    narrow S1 (mk_sty m2) = S2 ->
    item_ok m1 L1 = true -> L1 <> [] ->
    item_ok m2 L2 = true -> L2 <> [] ->
    items_ok_at S2 tail = true ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> blank_safe inner2 = true ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    item_ok m0 L0 = true ->
    parse_lines (list_lines sp
                   (map litem_lines ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail))
                 ++ post)%list (PPara [])
    = styles_list_checked S2
             (list_spacing_of sp (map snd ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail)))
             (map (fun it => mk_check (fst it))
                  ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail)) :: out.
Proof.
  intros m0 m1 m2 S1 S2 sp L0 L1 L2 tail post out
         Hm0 Hm1 Hm2 Htasks0 Htasks1 Htasks2
         HS1 HS2 Hnar1 Hnar2 Hok1 _ Hok2 _ Htail Hclose HL.
  rewrite <- (list_scan_spacing_gapless sp)
    by (cbn [map snd forallb];
        rewrite (item_ok_gap m0 L0 HL), (item_ok_gap m1 L1 Hok1),
          (item_ok_gap m2 L2 Hok2);
        exact (items_ok_at_gapless S2 tail Htail)).
  assert (HF : Forall (fun it => blank_safe (item_final it) = true)
                ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail)).
  { constructor; [exact (item_ok_final m0 L0 HL)|].
    constructor; [exact (item_ok_final m1 L1 Hok1)|].
    constructor; [exact (item_ok_final m2 L2 Hok2)|].
    exact (items_ok_at_final S2 tail Htail). }
  apply (list_gen_narrow2 (fun st => blank_safe st = true) blank_safe_closes
           (fun st => blank_safe st = true) m0 m1 m2 S1 S2);
    try assumption; try (apply item_ok_shape; assumption).
  - apply items_ok_at_shape, Htail.
  - exact (list_end_Forall (fun st => blank_safe st = true) _ (PPara []) eq_refl HF).
Qed.

(** The list ends the input. *)
Theorem list_uniformity :
  forall m0 sp L0 tail,
    marker_ok m0 = true ->
    items_ok m0 ((m0, L0) :: tail) = true ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: tail))) (PPara [])
    = [marker_list_checked m0 (list_spacing_of sp (map snd ((m0, L0) :: tail)))
             (map (fun it => mk_check (fst it)) ((m0, L0) :: tail))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: tail))].
Proof.
  intros m0 sp L0 tail Hm0 Hok.
  rewrite <- (app_nil_r (list_lines sp (map litem_lines ((m0, L0) :: tail)))).
  apply list_uniformity_gen; [exact Hm0 | | exact Hok].
  intros ls2 done2 inner2 _ _. rewrite parse_lines_nil, app_nil_r. reflexivity.
Qed.

(** A blank line and then a line that closes the list: the list is
    emitted and everything after it parses from idle. *)
(* ...and at end of input.  This is the ambiguous first marker: `i.`
   opens the list offering roman and alpha, the second marker decides
   which, and the block the list closes to is named by the *narrowed*
   set rather than by `m0`.  `marker_list m0` cannot state this, which is
   why `styles_list` exists. *)
Theorem list_uniformity_narrow :
  forall m0 m1 S' sp L0 L1 tail,
    marker_ok m0 = true -> marker_ok m1 = true ->
    marker_tasks_ok (@btasks K) m0 = true ->
    marker_tasks_ok (@btasks K) m1 = true ->
    S' <> [] -> narrow (mk_styles m0) (mk_sty m1) = S' ->
    item_ok m0 L0 = true -> item_ok m1 L1 = true -> L1 <> [] ->
    items_ok_at S' tail = true ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: (m1, L1) :: tail)))
                (PPara [])
    = [styles_list_checked S' (list_spacing_of sp (map snd ((m0, L0) :: (m1, L1) :: tail)))
             (map (fun it => mk_check (fst it)) ((m0, L0) :: (m1, L1) :: tail))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: (m1, L1) :: tail))].
Proof.
  intros m0 m1 S' sp L0 L1 tail Hm0 Hm1 Htasks0 Htasks1
    HS' Hnar HL0 HL1 HL1ne Htail.
  rewrite <- (app_nil_r (list_lines sp
                (map litem_lines ((m0, L0) :: (m1, L1) :: tail)))).
  apply (list_uniformity_gen_narrow m0 m1 S' sp L0 L1 tail [] []);
    [exact Hm0 | exact Hm1 | exact Htasks0 | exact Htasks1
    | exact HS' | exact Hnar | exact HL1 | exact HL1ne
    | exact Htail | | exact HL0].
  intros ls2 done2 inner2 _ _. rewrite parse_lines_nil, app_nil_r. reflexivity.
Qed.

(* The narrow form with the list closed by a following line. *)
Theorem list_uniformity_narrow_tail :
  forall m0 m1 S' sp L0 L1 items next tail,
    marker_ok m0 = true -> marker_ok m1 = true ->
    marker_tasks_ok (@btasks K) m0 = true ->
    marker_tasks_ok (@btasks K) m1 = true ->
    S' <> [] -> narrow (mk_styles m0) (mk_sty m1) = S' ->
    item_ok m0 L0 = true -> item_ok m1 L1 = true -> L1 <> [] ->
    items_ok_at S' items = true ->
    classify next <> KBlank ->
    (forall m mc chk it, classify next <> KList m mc chk it) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: (m1, L1) :: items))
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = styles_list_checked S' (list_spacing_of sp (map snd ((m0, L0) :: (m1, L1) :: items)))
             (map (fun it => mk_check (fst it)) ((m0, L0) :: (m1, L1) :: items))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: (m1, L1) :: items))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros m0 m1 S' sp L0 L1 items next tail Hm0 Hm1 Htasks0 Htasks1
         HS' Hnar HL0 HL1 HL1ne Hitems
         Hnb Hnl Hindent.
  apply (list_uniformity_gen_narrow m0 m1 S' sp L0 L1 items);
    [exact Hm0 | exact Hm1 | exact Htasks0 | exact Htasks1
    | exact HS' | exact Hnar | exact HL1 | exact HL1ne
    | exact Hitems | | exact HL0].
  intros ls2 done2 inner2 Hind2 Hpad2.
  apply parse_list_close; try assumption.
  rewrite Hind2, Hindent. reflexivity.
Qed.

(* Two peels, at end of input.  The only lists that need this are the
   ones whose *second* marker is ambiguous too -- an alpha list from `c`
   or from `l`, where `d` and `m` are themselves roman digits. *)
Theorem list_uniformity_narrow2 :
  forall m0 m1 m2 S1 S2 sp L0 L1 L2 tail,
    marker_ok m0 = true -> marker_ok m1 = true -> marker_ok m2 = true ->
    marker_tasks_ok (@btasks K) m0 = true ->
    marker_tasks_ok (@btasks K) m1 = true ->
    marker_tasks_ok (@btasks K) m2 = true ->
    S1 <> [] -> S2 <> [] ->
    narrow (mk_styles m0) (mk_sty m1) = S1 ->
    narrow S1 (mk_sty m2) = S2 ->
    item_ok m0 L0 = true ->
    item_ok m1 L1 = true -> L1 <> [] ->
    item_ok m2 L2 = true -> L2 <> [] ->
    items_ok_at S2 tail = true ->
    parse_lines (list_lines sp
                   (map litem_lines ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail)))
                (PPara [])
    = [styles_list_checked S2
         (list_spacing_of sp (map snd ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail)))
         (map (fun it => mk_check (fst it))
              ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail))
         (map (fun it => parse_lines (snd it) (PPara []))
              ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail))].
Proof.
  intros m0 m1 m2 S1 S2 sp L0 L1 L2 tail
         Hm0 Hm1 Hm2 Htasks0 Htasks1 Htasks2
         HS1 HS2 Hnar1 Hnar2 HL0 HL1 HL1ne HL2 HL2ne Htail.
  rewrite <- (app_nil_r (list_lines sp
                (map litem_lines ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail)))).
  apply (list_uniformity_gen_narrow2 m0 m1 m2 S1 S2 sp L0 L1 L2 tail [] []);
    try assumption.
  intros ls2 done2 inner2 _ _. rewrite parse_lines_nil, app_nil_r. reflexivity.
Qed.

(* ...and with the list closed by a following line. *)
Theorem list_uniformity_narrow2_tail :
  forall m0 m1 m2 S1 S2 sp L0 L1 L2 items next tail,
    marker_ok m0 = true -> marker_ok m1 = true -> marker_ok m2 = true ->
    marker_tasks_ok (@btasks K) m0 = true ->
    marker_tasks_ok (@btasks K) m1 = true ->
    marker_tasks_ok (@btasks K) m2 = true ->
    S1 <> [] -> S2 <> [] ->
    narrow (mk_styles m0) (mk_sty m1) = S1 ->
    narrow S1 (mk_sty m2) = S2 ->
    item_ok m0 L0 = true ->
    item_ok m1 L1 = true -> L1 <> [] ->
    item_ok m2 L2 = true -> L2 <> [] ->
    items_ok_at S2 items = true ->
    classify next <> KBlank ->
    (forall m mc chk it, classify next <> KList m mc chk it) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp
                   (map litem_lines ((m0, L0) :: (m1, L1) :: (m2, L2) :: items))
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = styles_list_checked S2
        (list_spacing_of sp (map snd ((m0, L0) :: (m1, L1) :: (m2, L2) :: items)))
        (map (fun it => mk_check (fst it))
             ((m0, L0) :: (m1, L1) :: (m2, L2) :: items))
        (map (fun it => parse_lines (snd it) (PPara []))
             ((m0, L0) :: (m1, L1) :: (m2, L2) :: items))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros m0 m1 m2 S1 S2 sp L0 L1 L2 items next tail
         Hm0 Hm1 Hm2 Htasks0 Htasks1 Htasks2
         HS1 HS2 Hnar1 Hnar2 HL0 HL1 HL1ne HL2 HL2ne Hitems
         Hnb Hnl Hindent.
  apply (list_uniformity_gen_narrow2 m0 m1 m2 S1 S2 sp L0 L1 L2 items);
    try assumption.
  intros ls2 done2 inner2 Hind2 Hpad2.
  apply parse_list_close; try assumption.
  rewrite Hind2, Hindent. reflexivity.
Qed.

Theorem list_uniformity_tail :
  forall m0 sp L0 items next tail,
    marker_ok m0 = true ->
    items_ok m0 ((m0, L0) :: items) = true ->
    classify next <> KBlank ->
    (forall m mc chk it, classify next <> KList m mc chk it) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: items))
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = marker_list_checked m0 (list_spacing_of sp (map snd ((m0, L0) :: items)))
             (map (fun it => mk_check (fst it)) ((m0, L0) :: items))
             (map (fun it => parse_lines (snd it) (PPara [])) ((m0, L0) :: items))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros m0 sp L0 items next tail Hm0 Hok Hnb Hnl Hindent.
  apply list_uniformity_gen; [exact Hm0 | | exact Hok].
  intros ls2 done2 inner2 Hind2 Hpad2.
  apply parse_list_close; try assumption.
  rewrite Hind2, Hindent. reflexivity.
Qed.

(** `list_uniformity_tail` for the shape alone, keys off.  Of the last
    item it asks that its lines do not end inside an attribute spec: the
    blank would fail the spec, and `next` would continue the paragraph
    recovered from it. *)
Theorem list_uniformity_shape_tail :
  forall m0 sp L0 items next tail,
    bkeyed = false ->
    marker_ok m0 = true ->
    items_shape_ok m0 ((m0, L0) :: items) = true ->
    spec_open_in (snd (run_lines (snd (last ((m0, L0) :: items) (m0, L0))) (PPara [])))
    = false ->
    classify next <> KBlank ->
    (forall m mc chk it, classify next <> KList m mc chk it) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: items))
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = marker_list_checked m0 (list_scan_spacing sp (map snd ((m0, L0) :: items)))
             (map (fun it => mk_check (fst it)) ((m0, L0) :: items))
             (map (fun it => parse_lines (snd it) (PPara [])) ((m0, L0) :: items))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros m0 sp L0 items next tail Hk Hm0 Hok Hend Hnb Hnl Hindent.
  apply (list_gen (fun st => reached st = true) (reached_closes Hk)
           (fun st => reached st = true /\ spec_open_in st = false));
    [exact Hm0| |exact Hok|exact (items_reached Hk _)|].
  - intros ls2 done2 inner2 Hind2 [Hr Ho].
    apply (parse_list_close_reached Hk); try assumption.
    rewrite Hind2, Hindent. reflexivity.
  - cbn [list_end]. rewrite list_end_last. split.
    + exact (Forall_inv (items_reached Hk [last ((m0, L0) :: items) (m0, L0)])).
    + unfold item_final. rewrite spec_open_in_pad_state. exact Hend.
Qed.

(* Every item at the same marker: the shape the bullet styles take, and
   the instantiation the three corollaries below use. *)
Definition same_marker (m : marker) (lss : list (list string)) : list litem :=
  map (fun L => (m, L)) lss.

Local Lemma items_ok_same_marker :
  forall m lss,
    marker_ok m = true -> marker_tasks_ok (@btasks K) m = true ->
    forallb (item_ok m) lss = true ->
    items_ok m (same_marker m lss) = true.
Proof.
  intros m lss Hm Htasks Hok. unfold items_ok, items_ok_at, same_marker.
  revert Hok. induction lss as [|L rest IH]; [reflexivity|].
  cbn [map forallb fst snd]. intros H. apply andb_prop in H as [HL Hrest].
  rewrite Hm, Htasks, HL, (admits_styles_refl m), (IH Hrest). reflexivity.
Qed.

Lemma map_snd_same_marker :
  forall m lss, map snd (same_marker m lss) = lss.
Proof.
  intros m lss. unfold same_marker.
  induction lss as [|L rest IH]; [reflexivity|].
  cbn [map snd]. rewrite IH. reflexivity.
Qed.

Lemma map_litem_lines_same_marker :
  forall m lss,
    map litem_lines (same_marker m lss)
    = map (indent_lines (mk_open m) (mk_cont m)) lss.
Proof.
  intros m lss. unfold same_marker.
  induction lss as [|L rest IH]; [reflexivity|].
  cbn [map]. unfold litem_lines at 1. cbn [fst snd]. rewrite IH. reflexivity.
Qed.

(* Uniformity for a list whose items all carry one marker.  This is the
   shape the bullet styles and a repeated ordered marker take; the
   theorem above is what a renumbering list needs. *)
Corollary list_uniformity_same :
  forall m sp lss,
    marker_ok m = true -> marker_tasks_ok (@btasks K) m = true -> lss <> [] ->
    forallb (item_ok m) lss = true ->
    parse_lines (list_lines sp (map (indent_lines (mk_open m) (mk_cont m)) lss))
                (PPara [])
    = [marker_list_checked m (list_spacing_of sp lss)
             (map (fun _ => mk_check m) lss)
             (map (fun L => parse_lines L (PPara [])) lss)].
Proof.
  intros m sp lss Hm Htasks Hne Hok.
  destruct lss as [|L0 rest]; [congruence|].
  pose proof (items_ok_same_marker m (L0 :: rest) Hm Htasks Hok) as Hio.
  unfold same_marker in Hio. cbn [map] in Hio.
  pose proof (list_uniformity m sp L0 (same_marker m rest) Hm Hio) as Hu.
  rewrite <- (map_litem_lines_same_marker m (L0 :: rest)).
  unfold same_marker at 1. cbn [map]. fold (same_marker m rest).
  change (litem_lines (m, L0) :: map litem_lines (same_marker m rest))
    with (map litem_lines ((m, L0) :: same_marker m rest)).
  rewrite Hu.
  cbn [map snd]. rewrite map_snd_same_marker.
  unfold same_marker. rewrite !map_map. cbn [fst snd]. reflexivity.
Qed.

Local Lemma items_shape_same_marker :
  forall m lss,
    marker_ok m = true -> marker_tasks_ok (@btasks K) m = true ->
    forallb (item_shape_ok m) lss = true ->
    items_shape_ok m (same_marker m lss) = true.
Proof.
  intros m lss Hm Htasks Hok. unfold items_shape_ok, items_shape_at, same_marker.
  revert Hok. induction lss as [|L rest IH]; [reflexivity|].
  cbn [map forallb fst snd]. intros H. apply andb_prop in H as [HL Hrest].
  rewrite Hm, Htasks, HL, (admits_styles_refl m), (IH Hrest). reflexivity.
Qed.

(* `list_uniformity_shape` at one marker. *)
Corollary list_uniformity_shape_same :
  forall m sp lss,
    bkeyed = false ->
    marker_ok m = true -> marker_tasks_ok (@btasks K) m = true -> lss <> [] ->
    forallb (item_shape_ok m) lss = true ->
    parse_lines (list_lines sp (map (indent_lines (mk_open m) (mk_cont m)) lss))
                (PPara [])
    = [marker_list_checked m (list_scan_spacing sp lss)
             (map (fun _ => mk_check m) lss)
             (map (fun L => parse_lines L (PPara [])) lss)].
Proof.
  intros m sp lss Hk Hm Htasks Hne Hok.
  destruct lss as [|L0 rest]; [congruence|].
  pose proof (items_shape_same_marker m (L0 :: rest) Hm Htasks Hok) as Hio.
  unfold same_marker in Hio. cbn [map] in Hio.
  pose proof (list_uniformity_shape m sp L0 (same_marker m rest) Hk Hm Hio) as Hu.
  rewrite <- (map_litem_lines_same_marker m (L0 :: rest)).
  unfold same_marker at 1. cbn [map]. fold (same_marker m rest).
  change (litem_lines (m, L0) :: map litem_lines (same_marker m rest))
    with (map litem_lines ((m, L0) :: same_marker m rest)).
  rewrite Hu.
  cbn [map snd]. rewrite map_snd_same_marker.
  unfold same_marker. rewrite !map_map. cbn [fst snd]. reflexivity.
Qed.

Corollary list_uniformity_tail_same :
  forall m sp lss next tail,
    marker_ok m = true -> marker_tasks_ok (@btasks K) m = true -> lss <> [] ->
    forallb (item_ok m) lss = true ->
    classify next <> KBlank ->
    (forall a b c d, classify next <> KList a b c d) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map (indent_lines (mk_open m) (mk_cont m)) lss)
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = marker_list_checked m (list_spacing_of sp lss)
             (map (fun _ => mk_check m) lss)
             (map (fun L => parse_lines L (PPara [])) lss)
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros m sp lss next tail Hm Htasks Hne Hok Hnb Hnl Hindent.
  destruct lss as [|L0 rest]; [congruence|].
  pose proof (items_ok_same_marker m (L0 :: rest) Hm Htasks Hok) as Hio.
  unfold same_marker in Hio. cbn [map] in Hio.
  pose proof (list_uniformity_tail m sp L0 (same_marker m rest) next tail
                Hm Hio Hnb Hnl Hindent) as Hu.
  rewrite <- (map_litem_lines_same_marker m (L0 :: rest)).
  unfold same_marker at 1. cbn [map]. fold (same_marker m rest).
  change (litem_lines (m, L0) :: map litem_lines (same_marker m rest))
    with (map litem_lines ((m, L0) :: same_marker m rest)).
  rewrite Hu.
  cbn [map snd]. rewrite map_snd_same_marker.
  unfold same_marker. rewrite !map_map. cbn [fst snd]. reflexivity.
Qed.

(*
The lines an item owns
----------------------

The syntax reference: a list item is a marker "followed by one or more
lines, indented relative to the list marker".  Every such line, and
every blank line, goes to the open item: it reaches the item's state
exactly as it would reach that state alone, and the list around it
changes only its spacing flags and source ranges.  This is ownership
and not uniformity: an owned line keeps its indentation, which the
contents may read (`- - a` then `    - b` puts `- b` in the inner item's
paragraph).
*)

Theorem list_item_owns :
  forall lines ls done inner,
    forallb (fun l => (is_blank l || Nat.ltb (ls_indent ls) (indent_of l))%bool)
      lines = true ->
    exists ls',
      ls_indent ls' = ls_indent ls /\ ls_styles ls' = ls_styles ls /\
      ls_items ls' = ls_items ls /\
      ls_check ls' = ls_check ls /\ ls_checks ls' = ls_checks ls /\
      run_lines lines (PList ls done inner)
      = ([], PList ls' (rev (fst (run_lines lines inner)) ++ done)%list
                       (snd (run_lines lines inner))).
Proof.
  intros lines. induction lines as [|l rest IH]; intros ls done inner Hown.
  - exists ls. repeat split.
  - cbn [forallb] in Hown. apply andb_true_iff in Hown as [Hl Hrest].
    destruct (step l inner) as [bs inner1] eqn:Hs.
    assert (Hstep : exists ls1,
      ls_indent ls1 = ls_indent ls /\ ls_styles ls1 = ls_styles ls /\
      ls_items ls1 = ls_items ls /\ ls_check ls1 = ls_check ls /\
      ls_checks ls1 = ls_checks ls /\
      step l (PList ls done inner) = ([], PList ls1 (rev bs ++ done)%list inner1)).
    { destruct (is_blank l) eqn:Hb.
      - eexists.
        rewrite (step_list_blank l ls done inner bs inner1 (classify_blank l Hb) Hs).
        split; [|split; [|split; [|split; [|split; [|reflexivity]]]]];
          reflexivity.
      - cbn [orb] in Hl.
        assert (Hk : classify l <> KBlank)
          by (intros E; rewrite (classify_kblank_blank l E) in Hb; discriminate).
        eexists.
        rewrite (step_list_indented l (classify l) ls done inner bs inner1
                   eq_refl Hk Hl Hs).
        split; [|split; [|split; [|split; [|split; [|reflexivity]]]]];
          reflexivity. }
    destruct Hstep as (ls1 & Hi & Hsty & Hit & Hc & Hcs & Hstep).
    destruct (IH ls1 (rev bs ++ done)%list inner1 ltac:(rewrite Hi; exact Hrest))
      as (ls2 & Hi2 & Hsty2 & Hit2 & Hc2 & Hcs2 & Hrun).
    exists ls2. rewrite Hi2, Hsty2, Hit2, Hc2, Hcs2, Hi, Hsty, Hit, Hc, Hcs.
    repeat split. cbn [run_lines]. rewrite Hstep, Hs, Hrun.
    destruct (run_lines rest inner1) as [more fin]. cbn [fst snd app].
    rewrite rev_app_distr, <- app_assoc. reflexivity.
Qed.

(*
Indentation
-----------

The syntax reference: "Indentation is only significant for list item or
footnote nesting."  What can be stated for every document is the
uniform case: indenting every line by the same blanks changes nothing,
lists and footnotes included, since they read columns relative to each
other.
*)

Theorem indent_uniformity :
  forall p lines,
    is_blank p = true ->
    parse_lines (map (fun l => (p ++ l)%string) lines) (PPara [])
    = parse_lines lines (PPara []).
Proof.
  intros p lines Hp.
  pose proof (run_lines_pad_shift p lines (PPara []) Hp) as R.
  cbn [pad_state] in R. rewrite (parse_lines_run _ _ _ _ R), pad_state_finish.
  symmetry. apply parse_lines_run, surjective_pairing.
Qed.

(*
A lazy line in a list item
--------------------------

`Uniformity.quote_lazy_line` for a bullet item.  The two exclusions are
where `- ` in front of `a` means something other than an item holding
`a`: `- --` is a thematic break, and `- [ ] x` a task item.
*)

Theorem list_lazy_line :
  forall a b,
    classify a = KText -> keyless a = true ->
    is_thematic ("- " ++ a) = false -> task_start a = false ->
    classify b = KText -> bunderline_of b = None ->
    parse_lines [("- " ++ a)%string; b] (PPara [])
    = [marker_list_checked bullet Tight [mk_check bullet]
         [parse_lines [a; b] (PPara [])]].
Proof.
  intros a b Ha Hk Hth Hts Hb Hu.
  assert (Hnb : forall x, classify x = KText -> nonblank x = true).
  { intros x Hx. unfold nonblank. unfold classify in Hx.
    destruct (is_blank x); [discriminate|reflexivity]. }
  assert (Ha0 : step a (PPara []) = ([], PPara [remember_line (drop_leading_ws a)])).
  { rewrite (step_idle a KText Ha eq_refl). apply open_text_keyless. exact Hk. }
  assert (Hb0 : forall c,
    step b (PPara [c]) = ([], PPara [remember_line (drop_leading_ws b); c])).
  { intros c. apply step_para_cont; [rewrite Hb; discriminate|].
    unfold bcuts. rewrite Hu, Hb. reflexivity. }
  (* The item with its continuation line indented: `list_uniformity_same`. *)
  assert (Hok : item_ok bullet [a; b] = true).
  { unfold item_ok. change bullet_open with "- ". rewrite Hth, Hts.
    cbn [run_safe]. rewrite Ha0. cbn [snd]. rewrite Hb0. cbn [snd last].
    unfold item_end_ok. rewrite (Hnb a Ha), Hb. reflexivity. }
  assert (Hsp : list_spacing_of Tight [[a; b]] = Tight).
  { unfold list_spacing_of, item_loose. cbn [existsb lines_loose].
    rewrite Ha, Hb, Ha0. cbn [snd]. rewrite Hb0. cbn [snd].
    destruct (line_fate 0 a KText (PPara [])),
             (line_fate 0 b KText (PPara [remember_line (drop_leading_ws a)]));
      reflexivity. }
  pose proof (list_uniformity_same bullet Tight [[a; b]] eq_refl eq_refl
                ltac:(discriminate)
                ltac:(cbn [forallb]; rewrite Hok; reflexivity)) as U.
  cbn [map list_lines indent_lines] in U. rewrite Hsp in U.
  change bullet_open with "- " in U. change bullet_cont with (blanks 2) in U.
  (* The lazy line is that indented line. *)
  pose proof (classify_marker_open bullet a eq_refl Hth
                (task_start_shadow bullet a Hts)) as Hc.
  change (mk_open bullet) with "- " in Hc.
  cbn [mk_sty mk_core mk_task_marker bullet] in Hc.
  assert (Hr : configured_list_rest None a = a)
    by (unfold configured_list_rest; destruct btasks; reflexivity).
  pose proof (step_list_open ("- " ++ a) [SBullet "-"%char] "" None a [] _ Hc
                ltac:(rewrite Hr; exact Ha0)) as Hopen.
  pose proof (lazy_line_spelling [("- " ++ a)%string] (blanks 2) b [] (PPara []))
    as L.
  cbn [run_lines] in L. rewrite Hopen in L. cbn [snd app rev] in L.
  rewrite <- L; [exact U | | reflexivity | exact Hb | exact Hu].
  change (blanks 2) with (blanks 2 ++ blanks 0)%string.
  apply SpList; [| cbn [pad_state]; apply SpLeaf; reflexivity].
  cbn. lia.
Qed.

End WithTable.
