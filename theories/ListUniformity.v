(* ai-disclosure: ai-generated *)

(* Uniformity for lists: the rendering of a list whose items are
   canonical parses back to that list, with each item's blocks the parse
   of that item's own lines.

   Longer than the quote and div arguments for two reasons an item has
   and a quote does not: its continuation lines are *indented* rather
   than prefixed, so the padding lemmas of `Step.v` carry the weight; and
   tight/loose is decided on the event stream, so the verdict has to be
   projected out of the run (`scan_list_content`) before it can be
   rewritten. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast Attributes Inline Marker Step Uniformity.
Import ListNotations.

Local Open Scope string_scope.

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
    because the blank's effect on the list depends on it: `list_open`
    decides whether the item has a nested list to claim the blank.  The
    lines are the item's, unindented, so `classify` reads them directly
    (`classify_marker_cont`) while the state steps on the rendered
    line. *)
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

Fixpoint scan_list_content (ls : list_state) (inner : pstate)
                           (lines : list string) : list_state :=
  match lines with
  | [] => ls
  | l :: rest =>
      let ls' :=
        match classify l with
        | KBlank => if list_open inner then ls else list_blank ls
        | k => list_content ls k
        end in
      scan_list_content ls' (snd (step (mk_cont mrk ++ l) inner)) rest
  end.

(** The item state that scan threads, on its own.  Definitionally the
    `inner` component of `scan_list_content`'s recursion, which is what
    lets the scan be cut at a line boundary. *)
Fixpoint scan_inner (inner : pstate) (lines : list string) : pstate :=
  match lines with
  | [] => inner
  | l :: rest => scan_inner (snd (step (mk_cont mrk ++ l) inner)) rest
  end.

Lemma run_lines_list_cont :
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
    destruct (classify l) as [| |f|dl dc|q|lvl txt|m mc item|kap|] eqn:Hclass.
    + rewrite (step_list_blank ((mk_cont mrk) ++ l) ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH _ (rev head ++ done)%list inner1 rest inner2).
      * rewrite rev_app_distr, app_assoc. reflexivity.
      * destruct (list_open inner); [exact Hind | cbn [list_blank]; exact Hind].
      * exact Hrest.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) KThematic ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH (list_content ls KThematic) (rev head ++ done)%list
                   inner1 rest inner2).
      * rewrite rev_app_distr, app_assoc. reflexivity.
      * cbn [list_content]. exact Hind.
      * exact Hrest.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KFence f) ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH (list_content ls (KFence f)) (rev head ++ done)%list
                   inner1 rest inner2) by (cbn [list_content]; assumption).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KDiv dl dc) ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH (list_content ls (KDiv dl dc)) (rev head ++ done)%list
                   inner1 rest inner2) by (cbn [list_content]; assumption).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KQuote q) ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH (list_content ls (KQuote q)) (rev head ++ done)%list
                   inner1 rest inner2) by (cbn [list_content]; assumption).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KHeading lvl txt)
                 ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH (list_content ls (KHeading lvl txt)) (rev head ++ done)%list
                   inner1 rest inner2) by (cbn [list_content]; assumption).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KList m mc item)
                 ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH (list_content ls (KList m mc item)) (rev head ++ done)%list
                   inner1 rest inner2) by (cbn [list_content]; assumption).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) (KAttr kap)
                 ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH (list_content ls (KAttr kap)) (rev head ++ done)%list
                   inner1 rest inner2) by (cbn [list_content]; assumption).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented ((mk_cont mrk) ++ l) KText ls done inner head inner1).
      2: { rewrite classify_marker_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_marker_cont.
           apply Nat.ltb_lt. pose proof (mk_pad_pos mrk Hmrk). lia. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass, Hstep. cbn [snd].
      rewrite (IH (list_content ls KText) (rev head ++ done)%list
                   inner1 rest inner2) by (cbn [list_content]; assumption).
      rewrite rev_app_distr, app_assoc. reflexivity.
Qed.

(*
The scan's state algebra
------------------------
*)

Lemma scan_list_content_nonblank :
  forall lines inner ind marker loose items,
    forallb nonblank lines = true ->
    scan_list_content (LSt ind marker loose false items) inner lines
    = LSt ind marker loose false items.
Proof.
  induction lines as [|l lines IH]; intros inner ind marker loose items H;
    [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hl Hrest].
  cbn [scan_list_content].
  destruct (classify l) as [| |f|dl dc|q|lvl txt|m mc rest|kap|] eqn:Hclass.
  - apply classify_kblank_blank in Hclass. unfold nonblank in Hl.
    rewrite Hclass in Hl. discriminate.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
Qed.

Lemma scan_list_content_loose :
  forall lines inner ind marker blanks items,
    ls_loose (scan_list_content (LSt ind marker true blanks items) inner lines) = true.
Proof.
  induction lines as [|l lines IH]; intros inner ind marker blanks items;
    [reflexivity|].
  cbn [scan_list_content]. destruct (classify l); try apply IH.
  destruct (list_open inner); apply IH.
Qed.

Lemma scan_list_content_app :
  forall xs ys ls inner,
    scan_list_content ls inner (xs ++ ys)%list =
    scan_list_content (scan_list_content ls inner xs) (scan_inner inner xs) ys.
Proof.
  induction xs as [|x xs IH]; intros ys ls inner; [reflexivity|].
  cbn [app scan_inner]. destruct (classify x) eqn:Hclass;
    cbn [scan_list_content]; rewrite Hclass; apply IH.
Qed.

Lemma scan_list_content_fields :
  forall lines inner ls,
    ls_indent (scan_list_content ls inner lines) = ls_indent ls /\
    ls_styles (scan_list_content ls inner lines) = ls_styles ls /\
    ls_items (scan_list_content ls inner lines) = ls_items ls.
Proof.
  intros lines inner ls. split; [|split].
  - revert inner ls. induction lines as [|l lines IH]; intros inner ls; [reflexivity|].
    cbn [scan_list_content]. destruct (classify l);
      try (rewrite IH; destruct ls; reflexivity).
    destruct (list_open inner); rewrite IH; destruct ls; reflexivity.
  - revert inner ls. induction lines as [|l lines IH]; intros inner ls; [reflexivity|].
    cbn [scan_list_content]. destruct (classify l);
      try (rewrite IH; destruct ls; reflexivity).
    destruct (list_open inner); rewrite IH; destruct ls; reflexivity.
  - revert inner ls. induction lines as [|l lines IH]; intros inner ls; [reflexivity|].
    cbn [scan_list_content]. destruct (classify l);
      try (rewrite IH; destruct ls; reflexivity).
    destruct (list_open inner); rewrite IH; destruct ls; reflexivity.
Qed.

Lemma scan_list_content_loose_ext :
  forall lines inner ind marker loose blanks done,
    ls_loose (scan_list_content (LSt ind marker loose blanks done) inner lines) =
    ls_loose (scan_list_content (LSt 0 (mk_styles mrk) loose blanks []) inner lines).
Proof.
  induction lines as [|l lines IH]; intros inner ind marker loose blanks done;
    [reflexivity|].
  cbn [scan_list_content]. destruct (classify l);
    cbn [list_blank list_content]; try apply IH.
  destruct (list_open inner); cbn [list_blank]; apply IH.
Qed.

Lemma scan_list_content_blanks_last :
  forall lines inner ls,
    lines <> [] -> nonblank (last lines EmptyString) = true ->
    ls_blanks (scan_list_content ls inner lines) = false.
Proof.
  induction lines as [|l lines IH]; intros inner ls Hne Hlast; [congruence|].
  destruct lines as [|l2 lines'].
  - cbn [last scan_list_content] in Hlast |- *.
    destruct (classify l) as [| |f|dl dc|q|lvl txt|m mc item|kap|] eqn:Hclass;
      cbn [list_blank list_content].
    all: try (apply classify_kblank_blank in Hclass; unfold nonblank in Hlast;
              rewrite Hclass in Hlast; discriminate).
    all: destruct ls; reflexivity.
  - cbn [last] in Hlast. cbn [scan_list_content].
    apply IH; [discriminate|exact Hlast].
Qed.

Lemma scan_list_content_after_blank :
  forall b rest inner ind marker items,
    classify b <> KBlank ->
    (forall m mc item, classify b <> KList m mc item) ->
    ls_loose
      (scan_list_content (list_blank (LSt ind marker false false items))
         inner (b :: rest)) = true.
Proof.
  intros b rest inner ind marker items Hblank Hlist.
  cbn [scan_list_content].
  destruct (classify b) as [| |f|dl dc|q|lvl txt|m mc item|kap|] eqn:Hclass.
  - exfalso. apply Hblank. reflexivity.
  - apply scan_list_content_loose.
  - apply scan_list_content_loose.
  - apply scan_list_content_loose.
  - apply scan_list_content_loose.
  - apply scan_list_content_loose.
  - exfalso. apply (Hlist m mc item). reflexivity.
  - apply scan_list_content_loose.
  - apply scan_list_content_loose.
Qed.

(*
Item and list layout
--------------------

Where a list's lines come from.  These are layout primitives rather than
renderer policy, and the uniformity theorems below are stated in terms of
them, so they live here and `Render.v` reuses them.
*)

(* A list item's lines: the marker (`(mk_open mrk)`, from Line.v) on the
   first line, two spaces of plain indent (`(mk_cont mrk)`) on every line
   after — not repeated per line like quote_line, since (mk_cont mrk) is
   whitespace and Line.classify_ws_prefix carries every recognizer
   through it for free. *)
Definition indent_lines (first_prefix rest_prefix : string) (ls : list string)
  : list string :=
  match ls with
  | [] => []
  | l :: rest => (first_prefix ++ l) :: map (fun x => rest_prefix ++ x) rest
  end.

(* Items separated by a blank line when the list is loose, concatenated
   directly when tight — the rendering choice `cb_ok`'s spacing condition
   has to match back up with. *)
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
unless the next non-blank line opens a list.  A renderer-side predicate
that reads the block tree cannot express this, because the tree does not
record where the blanks sit relative to the markers.
*)

(* Padding is a shift of the state, not a no-op.  Stating it as a shift
   rather than as an equality is what makes it hold for an item whose
   content opens a list, where the pad genuinely moves a recorded
   column. *)
Lemma pad_safe_pad_state :
  forall k st, pad_safe (pad_state k st) = pad_safe st.
Proof.
  intros k st. induction st as [| | |done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|ppend pinner IH];
    cbn [pad_state pad_safe]; try reflexivity; exact IH.
Qed.

Lemma step_pad_shift :
  forall p l st,
    is_blank p = true -> pad_safe st = true ->
    step (p ++ l) (pad_state (String.length p) st)
    = (fst (step l st), pad_state (String.length p) (snd (step l st))).
Proof.
  intros p l st Hp Hsafe.
  rewrite (step_pad p l (pad_state (String.length p) st) Hp)
    by (rewrite pad_safe_pad_state; exact Hsafe).
  rewrite <- (Nat.add_0_r (String.length p)) at 1.
  rewrite step_at_shift, step_at_zero. reflexivity.
Qed.

(* `pad_safe` along a whole run.  This is the theorem's only side
   condition beyond the marker line, and it says exactly "no fence is
   open directly inside the item" -- fence content is verbatim, so a pad
   in front of it is not a shift. *)
Fixpoint run_pad_safe (lines : list string) (st : pstate) : bool :=
  match lines with
  | [] => pad_safe st
  | l :: rest => (pad_safe st && run_pad_safe rest (snd (step l st)))%bool
  end.

Lemma run_lines_pad_shift :
  forall p lines st,
    is_blank p = true ->
    run_pad_safe lines st = true ->
    run_lines (map (fun l => (p ++ l)%string) lines) (pad_state (String.length p) st)
    = (fst (run_lines lines st), pad_state (String.length p) (snd (run_lines lines st))).
Proof.
  intros p lines. induction lines as [|l rest IH]; intros st Hp Hsafe.
  - reflexivity.
  - cbn [map run_lines] in *.
    apply andb_prop in Hsafe as [Hnow Hlater].
    rewrite (step_pad_shift p l st Hp Hnow).
    destruct (step l st) as [bs st'] eqn:Es. cbn [fst snd] in *.
    rewrite (IH st' Hp Hlater).
    destruct (run_lines rest st') as [more st''] eqn:Er. reflexivity.
Qed.

(* And from the idle state the shift is *invisible*: `pad_state` moves
   columns, `finish` reads none, and the emitted blocks are untouched.  So
   a blank pad in front of every line of a run changes nothing at all,
   whatever the run opens -- a nested list included.  `run_pad_safe` is
   the whole side condition. *)
Lemma run_lines_pad_invisible :
  forall p L,
    is_blank p = true ->
    run_pad_safe L (PPara []) = true ->
    run_lines (map (fun l => (p ++ l)%string) L) (PPara [])
    = (fst (run_lines L (PPara [])),
       pad_state (String.length p) (snd (run_lines L (PPara [])))).
Proof.
  intros p L Hp Hsafe. exact (run_lines_pad_shift p L (PPara []) Hp Hsafe).
Qed.

Lemma parse_lines_pad_invisible :
  forall p L,
    is_blank p = true ->
    run_pad_safe L (PPara []) = true ->
    parse_lines (map (fun l => (p ++ l)%string) L) (PPara [])
    = parse_lines L (PPara []).
Proof.
  intros p L Hp Hsafe.
  rewrite (parse_lines_run _ _ _ _ (run_lines_pad_invisible p L Hp Hsafe)).
  rewrite pad_state_finish.
  symmetry. apply parse_lines_run, surjective_pairing.
Qed.

(* The marker line consumes exactly the item's content column, so this is
   `(mk_pad mrk)` and not an incidental 2: an ordered marker widens both. *)
Lemma consumed_marker_open :
  forall l, consumed (mk_open mrk ++ l) l = mk_pad mrk.
Proof.
  intros l. unfold consumed, mk_pad. rewrite length_append. lia.
Qed.

(* The marker line, with the item's residue parsed at column 2. *)
Lemma step_item_open :
  forall l0,
    is_thematic ((mk_open mrk) ++ l0) = false ->
    step ((mk_open mrk) ++ l0) (PPara [])
    = ([], PList (LSt 0 (mk_styles mrk) false false [])
            (rev (fst (step l0 (PPara []))))
            (pad_state (mk_pad mrk) (snd (step l0 (PPara []))))).
Proof.
  intros l0 Hth.
  destruct (step l0 (PPara [])) as [bs inner] eqn:Es. cbn [fst snd].
  rewrite (step_list_open _ _ _ _ _ _ (classify_marker_open mrk l0 Hmrk Hth) Es).
  rewrite (indent_of_marker_open mrk _ Hmrk), consumed_marker_open. reflexivity.
Qed.

(** The tight/loose verdict, read off the lines.  A blank arms the flag;
    a line that opens a list spends it without loosening (djot.js's
    `+list` exemption); anything else spends it and loosens.

    The scan also carries the lines' own parse state, because a blank
    arms the flag only when the lines have no list open to claim it --
    the mirror of `step`'s `KBlank` branch, and the reason `["- b"; "";
    "t"]` leaves its enclosing list tight while `["a"; ""; "t"]` does
    not.  The state is threaded, not consulted from outside, so this is
    still a fold over the lines. *)
Fixpoint lines_loose (loose gap : bool) (st : pstate) (ls : list string) : bool :=
  match ls with
  | [] => loose
  | l :: rest =>
      let st' := snd (step l st) in
      match classify l with
      | KBlank => lines_loose loose (if list_open st then gap else true) st' rest
      | KList _ _ _ => lines_loose loose false st' rest
      | _ => lines_loose (loose || gap)%bool false st' rest
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
Lemma lines_loose_cons_nonblank :
  forall a rest,
    classify a <> KBlank ->
    item_loose (a :: rest) = lines_loose false false (snd (step a (PPara []))) rest.
Proof.
  intros a rest H. unfold item_loose. cbn [lines_loose].
  destruct (classify a) eqn:E; try reflexivity. congruence.
Qed.

(* The scan and `lines_loose` are the same fold: the scan carries the
   item's state padded into the enclosing item, `lines_loose` carries it
   bare, and `list_open` cannot tell the two apart. *)
Lemma scan_loose_eq :
  forall lines st ls,
    run_pad_safe lines st = true ->
    ls_loose (scan_list_content ls (pad_state (mk_pad mrk) st) lines)
    = lines_loose (ls_loose ls) (ls_blanks ls) st lines.
Proof.
  induction lines as [|l rest IH]; intros st ls Hsafe; [reflexivity|].
  cbn [run_pad_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hp Hrest].
  cbn [scan_list_content lines_loose].
  pose proof (step_pad_shift (mk_cont mrk) l st (marker_cont_blank mrk) Hp) as Hsh.
  rewrite mk_cont_length in Hsh.
  rewrite Hsh, pad_state_list_open.
  destruct (classify l) eqn:E; cbn [snd];
    [ destruct (list_open st); rewrite IH by exact Hrest; reflexivity
    | rewrite IH by exact Hrest; reflexivity ..].
Qed.

Lemma scan_items_eq :
  forall lines inner ls, ls_items (scan_list_content ls inner lines) = ls_items ls.
Proof.
  intros lines inner ls.
  pose proof (scan_list_content_fields lines inner ls) as [_ [_ H]]. exact H.
Qed.

(* The scan's state in closed form, once no blank is left armed.  The
   canonical setting always ends an item on a nonblank line, so this is
   the form every use wants. *)
Lemma scan_shape :
  forall lines st ls,
    run_pad_safe lines st = true ->
    ls_blanks (scan_list_content ls (pad_state (mk_pad mrk) st) lines) = false ->
    scan_list_content ls (pad_state (mk_pad mrk) st) lines
    = LSt (ls_indent ls) (ls_styles ls)
          (lines_loose (ls_loose ls) (ls_blanks ls) st lines) false (ls_items ls).
Proof.
  intros lines st ls Hsafe Hb.
  pose proof (scan_list_content_fields lines (pad_state (mk_pad mrk) st) ls) as [Hi [Hm Hit]].
  pose proof (scan_loose_eq lines st ls Hsafe) as Hlo.
  destruct (scan_list_content ls (pad_state (mk_pad mrk) st) lines) as [i m lo b its].
  cbn in Hi, Hm, Hit, Hb, Hlo. subst. reflexivity.
Qed.

(* One item's lines, run from idle: the marker opens the list and the
   continuation lines land in it, shifted two columns. *)
Lemma run_item_open :
  forall l0 rest,
    is_thematic ((mk_open mrk) ++ l0) = false ->
    run_pad_safe rest (snd (step l0 (PPara []))) = true ->
    ls_blanks (scan_list_content (LSt 0 (mk_styles mrk) false false [])
                 (pad_state (mk_pad mrk) (snd (step l0 (PPara [])))) rest) = false ->
    run_lines (indent_lines (mk_open mrk) (mk_cont mrk) (l0 :: rest)) (PPara [])
    = ([], PList (LSt 0 (mk_styles mrk)
                    (lines_loose false false (snd (step l0 (PPara []))) rest)
                    false [])
            (rev (fst (run_lines (l0 :: rest) (PPara []))))
            (pad_state (mk_pad mrk) (snd (run_lines (l0 :: rest) (PPara []))))).
Proof.
  intros l0 rest Hth Hsafe Hb.
  cbn [indent_lines run_lines].
  rewrite (step_item_open l0 Hth).
  pose proof (run_lines_pad_shift (mk_cont mrk) rest (snd (step l0 (PPara [])))
                (marker_cont_blank mrk) Hsafe) as Hrun.
  rewrite mk_cont_length in Hrun.
  rewrite (run_lines_list_cont rest (LSt 0 (mk_styles mrk) false false [])
             (rev (fst (step l0 (PPara [])))) _ _ _ eq_refl Hrun).
  rewrite (scan_shape rest _ _ Hsafe Hb).
  cbn [ls_indent ls_styles ls_loose ls_blanks ls_items].
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
Lemma run_item_sibling_narrow :
  forall l0 rest ls done inner,
    ls_indent ls = 0 ->
    narrow (ls_styles ls) (mk_sty mrk) <> [] ->
    is_thematic ((mk_open mrk) ++ l0) = false ->
    run_pad_safe rest (snd (step l0 (PPara []))) = true ->
    run_lines (indent_lines (mk_open mrk) (mk_cont mrk) (l0 :: rest)) (PList ls done inner)
    = ([], PList (scan_list_content
                    (list_next (list_narrow ls (narrow (ls_styles ls) (mk_sty mrk)))
                               (rev done ++ finish inner)%list l0)
                    (pad_state (mk_pad mrk) (snd (step l0 (PPara [])))) rest)
            (rev (fst (run_lines (l0 :: rest) (PPara []))))
            (pad_state (mk_pad mrk) (snd (run_lines (l0 :: rest) (PPara []))))).
Proof.
  intros l0 rest ls done inner Hind Hnar Hth Hsafe.
  cbn [indent_lines run_lines].
  destruct (step l0 (PPara [])) as [b i] eqn:Es.
  destruct (narrow (ls_styles ls) (mk_sty mrk)) as [|s0 ss] eqn:Hn;
    [contradiction|].
  rewrite (step_list_sibling _ _ _ _ _ _ _ _ _ _ _
             (classify_marker_open mrk l0 Hmrk Hth) Hn
             (ltac:(rewrite Hind, (indent_of_marker_open mrk _ Hmrk); reflexivity))
             Es).
  rewrite consumed_marker_open.
  pose proof (run_lines_pad_shift (mk_cont mrk) rest i (marker_cont_blank mrk)) as Hrun.
  cbn [snd] in Hsafe. specialize (Hrun Hsafe).
  rewrite mk_cont_length in Hrun.
  assert (Hi0 : ls_indent (list_next (list_narrow ls (s0 :: ss))
                             (rev done ++ finish inner)%list l0) = 0).
  { unfold list_next, list_narrow. cbn [ls_indent].
    destruct (is_blank l0); exact Hind. }
  rewrite (run_lines_list_cont rest
             (list_next (list_narrow ls (s0 :: ss)) (rev done ++ finish inner)%list l0)
             (rev b) (pad_state (mk_pad mrk) i) _ _ Hi0 Hrun).
  destruct (run_lines rest i) as [more i'] eqn:Er. cbn [fst snd app].
  rewrite rev_app_distr. reflexivity.
Qed.

(* The instance the canonical chain uses: the sibling re-offers what the
   list already has, so the narrowing is the identity and the state's set
   does not move. *)
Lemma run_item_sibling :
  forall l0 rest ls done inner,
    ls_indent ls = 0 ->
    ls_styles ls <> [] ->
    narrow (ls_styles ls) (mk_sty mrk) = ls_styles ls ->
    is_thematic ((mk_open mrk) ++ l0) = false ->
    run_pad_safe rest (snd (step l0 (PPara []))) = true ->
    run_lines (indent_lines (mk_open mrk) (mk_cont mrk) (l0 :: rest)) (PList ls done inner)
    = ([], PList (scan_list_content
                    (list_next ls (rev done ++ finish inner)%list l0)
                    (pad_state (mk_pad mrk) (snd (step l0 (PPara [])))) rest)
            (rev (fst (run_lines (l0 :: rest) (PPara []))))
            (pad_state (mk_pad mrk) (snd (run_lines (l0 :: rest) (PPara []))))).
Proof.
  intros l0 rest ls done inner Hind Hne Hnar Hth Hsafe.
  rewrite (run_item_sibling_narrow l0 rest ls done inner Hind
             ltac:(rewrite Hnar; exact Hne) Hth Hsafe).
  rewrite Hnar, list_narrow_id. reflexivity.
Qed.

(* `lines_loose` only ever accumulates with `||`, so the incoming verdict
   factors out.  This is what lets an item's contribution be read off its
   own lines, independent of what the items before it decided. *)
Lemma lines_loose_or :
  forall L st lo g, lines_loose lo g st L = (lo || lines_loose false g st L)%bool.
Proof.
  induction L as [|l rest IH]; intros st lo g.
  - cbn [lines_loose]. rewrite orb_false_r. reflexivity.
  - cbn [lines_loose]. destruct (classify l); try apply IH.
    all: cbn [orb]; rewrite (IH _ (lo || g)%bool false), (IH _ g false);
         destruct lo, g; reflexivity.
Qed.

(* A blank line closes what `finish` would have closed, and emits it.
   The exception is a list, which a blank does not close -- there the
   equation holds one level down instead, which is the induction.  A
   fence is the one state where it fails, and `pad_safe` excludes it. *)
Lemma step_blank_finish :
  forall l st, classify l = KBlank -> pad_safe st = true ->
    (fst (step l st) ++ finish (snd (step l st)))%list = finish st.
Proof.
  intros l st Hl.
  induction st as [cur|lvl cur|f acc|done inner IH|dlen dcls ddone dinner IH
                  |ls done inner IH|apend aind aap aslices|ppend pinner IH];
    intros Hsafe.
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hl eq_refl). cbn [open_kind fst snd finish app].
      reflexivity.
    + rewrite (step_para_flush l c cur' Hl). reflexivity.
  - rewrite (step_heading_close l lvl cur Hl). reflexivity.
  - discriminate Hsafe.
  - rewrite (step_quote_close l KBlank done inner _ _ Hl eq_refl eq_refl
               (surjective_pairing _)).
    cbn [fst snd open_kind finish app]. reflexivity.
  - (* a blank never closes a div, so it goes straight to the contents *)
    cbn [pad_safe] in Hsafe.
    rewrite (step_div_cont l dlen dcls ddone dinner _ _
               (div_stays_open_blank l dinner dlen (classify_kblank_blank l Hl))
               (surjective_pairing _)).
    cbn [fst snd finish app].
    rewrite rev_app_distr, rev_involutive, <- app_assoc, (IH Hsafe).
    reflexivity.
  - cbn [pad_safe] in Hsafe.
    rewrite (step_list_blank l ls done inner _ _ Hl (surjective_pairing _)).
    cbn [fst snd finish app list_blank ls_loose ls_items].
    rewrite rev_app_distr, rev_involutive, <- app_assoc, (IH Hsafe).
    (* the blank leaves the list state alone when the item claims it, and
       otherwise only touches `ls_blanks`, which `finish` does not read *)
    destruct (list_open inner); [reflexivity | destruct ls; reflexivity].
  - discriminate Hsafe.
  - (* pending attributes: the blank closes what is under them, and the
       decoration rides on whatever that emits *)
    cbn [pad_safe] in Hsafe. unfold step. cbn [step_fuel]. rewrite Hl.
    destruct (is_idle pinner) eqn:Hidle.
    { destruct pinner as [cur| | | | | | |]; try discriminate Hidle.
      destruct cur; [reflexivity|discriminate Hidle]. }
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    specialize (IH Hsafe).
    destruct (step l pinner) as [bs st'] eqn:Hs.
    cbn [fst snd] in IH. cbn [pend_result].
    destruct bs as [|b bs'].
    + cbn [fst snd finish app]. rewrite <- IH. reflexivity.
    + cbn [fst snd finish]. rewrite decorate_head_cons_app, <- IH. reflexivity.
Qed.

(* A blank line leaves no state a later text line could continue lazily.
   `step_list_close` needs this to route the line that closes a list. *)
Lemma step_blank_lazy_false :
  forall l st, classify l = KBlank -> lazy_ok (snd (step l st)) = false.
Proof.
  intros l st Hblank. induction st as
    [cur|lvl cur|f acc|done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|ppend pinner IH].
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hblank eq_refl). reflexivity.
    + rewrite (step_para_flush l c cur' Hblank). reflexivity.
  - unfold step. cbn [step_fuel]. rewrite Hblank. reflexivity.
  - destruct (fence_close f l) eqn:Hclose.
    + rewrite (step_fence_close l f acc Hclose). reflexivity.
    + rewrite (step_fence_content l f acc Hclose). reflexivity.
  - rewrite (step_quote_close l KBlank done inner [] (PPara [])
      Hblank eq_refl eq_refl eq_refl). reflexivity.
  - destruct (step l dinner) as [bs inner'] eqn:Hstep.
    rewrite (step_div_cont l dlen dcls ddone dinner bs inner'
               (div_stays_open_blank l dinner dlen (classify_kblank_blank l Hblank)) Hstep).
    cbn [snd lazy_ok]. exact IH.
  - destruct (step l inner) as [bs inner'] eqn:Hstep.
    rewrite (step_list_blank l ls done inner bs inner' Hblank Hstep).
    cbn [snd lazy_ok]. exact IH.
  - unfold step. cbn [step_fuel].
    destruct (ap_done aap).
    { rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
      unfold step. cbn [step_fuel]. rewrite Hblank. reflexivity. }
    assert (Hfall : lazy_ok (snd (step_fuel
              (String.length l + pstate_depth (PAttr apend aind aap aslices))
              0 l (PPara aslices))) = false).
    { rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
      destruct aslices as [|c cur'].
      { rewrite (step_idle l KBlank Hblank eq_refl). reflexivity. }
      rewrite (step_para_flush l c cur' Hblank). reflexivity. }
    destruct (Nat.ltb aind (0 + indent_of l));
      [destruct (ap_failed (attr_feed l aap)); [exact Hfall|reflexivity]
      |exact Hfall].
  - unfold step. cbn [step_fuel]. rewrite Hblank.
    destruct (is_idle pinner); [reflexivity|].
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l pinner) as [bs st'] eqn:Hs.
    destruct bs; cbn [pend_result snd lazy_ok]; exact IH.
Qed.

Lemma run_pad_safe_final :
  forall L st, run_pad_safe L st = true -> pad_safe (snd (run_lines L st)) = true.
Proof.
  induction L as [|l rest IH]; intros st H; [exact H|].
  cbn [run_pad_safe] in H. apply andb_prop in H as [_ Hlater].
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

Fixpoint list_tail_lines (sp : list_spacing) (items : list litem) : list string :=
  match items with
  | [] => []
  | it :: rest => (item_sep sp ++ litem_lines it ++ list_tail_lines sp rest)%list
  end.

Lemma list_lines_cons2 :
  forall sp x xs, xs <> [] ->
    list_lines sp (x :: xs) = (x ++ item_sep sp ++ list_lines sp xs)%list.
Proof. intros sp x xs H. destruct xs; [congruence|reflexivity]. Qed.

Lemma list_lines_cons :
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
some item's own lines force it, or when the rendering separates items by
a blank at all -- which needs two items, since a one-item list emits no
separator.
*)

(* What an item's lines must satisfy: the marker line does not form a
   thematic break, the item does not start blank, no fence is left open
   inside it, and it does not end blank. *)
Definition item_ok (m : marker) (L : list string) : bool :=
  match L with
  | [] => false
  | l0 :: more =>
      (negb (is_thematic ((mk_open m) ++ l0))
       && nonblank l0
       && run_pad_safe more (snd (step l0 (PPara [])))
       && match more with [] => true | _ => nonblank (last more EmptyString) end)%bool
  end.

(* Every item recognized, and every item's marker admitting the styles
   the list opened with -- which is what keeps the sibling narrowing from
   moving the set, and so from ending the list or renaming its style.  A
   renumbering decimal list satisfies it because `9.` and `10.` name the
   same style; a roman list satisfies it whenever its first numeral is
   unambiguous, since every later numeral still offers roman. *)
Definition items_ok_at (S : list (lstyle * nat)) (items : list litem) : bool :=
  forallb (fun it => marker_ok (fst it) && item_ok (fst it) (snd it)
                     && admits_styles S (fst it))%bool items.

(* The instance where the list's set is exactly its first marker's, which
   is every list whose first marker names one style. *)
Definition items_ok (m0 : marker) (items : list litem) : bool :=
  items_ok_at (mk_styles m0) items.

(** Does the item's rendering leave a list open at its end?  Then the
    separator blank that follows is that inner list's trailing blank,
    which `step`'s `KBlank` branch hands to the inner list rather than to
    the enclosing one -- so that separator does not loosen. *)
Definition ends_open_list (L : list string) : bool :=
  list_open (snd (run_lines L (PPara []))).

(* Does an item's contents open with a list marker?  djot.js excludes a
   `+list` event from spending a blank into looseness, which
   `list_content` already encodes for the lines *inside* an item.  A
   separator blank is spent by the *next* item's first line, so the same
   exclusion applies there — and that is what `list_next` implements. *)
Definition starts_list (L : list string) : bool :=
  match L with
  | [] => false
  | l :: _ => match classify l with KList _ _ _ => true | _ => false end
  end.

(** Whether any separator blank in the rendering reaches the list.  A
    separator is between two items and both of them have a say: the one
    before it must not end with a list still open (or the blank is that
    list's trailing blank, which the spec exempts), and the one after it
    must not open with a list marker (or the blank is spent by a `+list`
    event, which does not loosen).  Hence a pairwise scan rather than a
    test on each item alone.

    The last item is never the left of a pair, so a one-item list has no
    separator at all — which is why a `Loose` single item renders and
    parses back as `Tight`. *)
Fixpoint seps_loosen (itemss : list (list string)) : bool :=
  match itemss with
  | [] => false
  | L :: rest =>
      match rest with
      | [] => false
      | L2 :: _ =>
          ((negb (ends_open_list L) && negb (starts_list L2))
           || seps_loosen rest)%bool
      end
  end.

(* The verdict contributed by the items after the current one.  `inner`
   is the state the current item ended in: it decides the separator that
   sits between it and the head of `itemss`, and `seps_loosen` decides
   the separators internal to `itemss`. *)
Definition list_loose_of (sp : list_spacing) (inner : pstate)
                         (itemss : list (list string)) : bool :=
  (existsb (fun L => item_loose L) itemss
   || match sp with
      | Loose =>
          match itemss with
          | [] => false
          | L :: _ =>
              ((negb (list_open inner) && negb (starts_list L))
               || seps_loosen itemss)%bool
          end
      | Tight => false
      end)%bool.

(* `post` and `out` are what follows the list in the input and in the
   output: the lemmas below say nothing about how the list ends, so one
   induction serves both endings (end of input, and a blank plus a line
   that closes the list).  Instantiated at the two `list_uniformity`
   corollaries. *)
(* Padding shifts columns; it does not change which container is on top,
   so the separator's verdict is pad-invariant. *)
Lemma list_loose_of_pad :
  forall sp n st itemss,
    list_loose_of sp (pad_state n st) itemss = list_loose_of sp st itemss.
Proof.
  intros sp n st itemss. unfold list_loose_of.
  rewrite pad_state_list_open. reflexivity.
Qed.

Lemma parse_item_and_tail_narrow :
  forall S S' Sout m sp l0 more rest post out ls done inner,
    S' <> [] -> marker_ok m = true ->
    narrow S (mk_sty m) = S' ->
    ls_indent ls = 0 -> ls_styles ls = S ->
    item_ok m (l0 :: more) = true ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> ls_styles ls2 = S' -> ls_blanks ls2 = false ->
       pad_safe inner2 = true ->
       parse_lines (list_tail_lines sp rest ++ post)%list (PList ls2 done2 inner2)
       = styles_list Sout (if (ls_loose ls2 || list_loose_of sp inner2 (map snd rest))%bool
                         then Loose else Tight)
                (rev (ls_items ls2) ++ (rev done2 ++ finish inner2)%list
                 :: map (fun it => parse_lines (snd it) (PPara [])) rest) :: out) ->
    parse_lines (litem_lines (m, l0 :: more)
                 ++ (list_tail_lines sp rest ++ post))%list (PList ls done inner)
    = styles_list Sout
             (if ((ls_loose ls || (ls_blanks ls && negb (starts_list (l0 :: more))))
                  || item_loose (l0 :: more)
                  || list_loose_of sp (snd (run_lines (l0 :: more) (PPara []))) (map snd rest))%bool
              then Loose else Tight)
             (rev (ls_items ls) ++ (rev done ++ finish inner)%list
              :: parse_lines (l0 :: more) (PPara [])
              :: map (fun it => parse_lines (snd it) (PPara [])) rest) :: out.
Proof.
  intros S S' Sout m sp l0 more rest post out ls done inner
         HS' Hm Hsty Hind Hmark Hok IH.
  unfold litem_lines. cbn [fst snd].
  cbn [item_ok] in Hok.
  apply andb_prop in Hok as [Hok Hlast].
  apply andb_prop in Hok as [Hok Hsafe].
  apply andb_prop in Hok as [Hth Hnb].
  apply negb_true_iff in Hth.
  assert (Hnb' : is_blank l0 = false).
  { unfold nonblank in Hnb. apply negb_true_iff in Hnb. exact Hnb. }
  assert (Hcl : classify l0 <> KBlank).
  { intros E. apply classify_kblank_blank in E. rewrite E in Hnb'. discriminate. }
  rewrite parse_lines_app_run.
  rewrite (run_item_sibling_narrow m Hm l0 more ls done inner Hind
             (ltac:(rewrite Hmark, Hsty; exact HS'))
             Hth Hsafe).
  rewrite Hmark, Hsty.
  cbn [fst snd app].
  set (item := (rev done ++ finish inner)%list).
  set (ls1 := scan_list_content m (list_next (list_narrow ls S') item l0)
                (pad_state (mk_pad m) (snd (step l0 (PPara [])))) more).
  set (R := run_lines (l0 :: more) (PPara [])).
  pose proof (scan_list_content_fields m more (pad_state (mk_pad m) (snd (step l0 (PPara []))))
                (list_next (list_narrow ls S') item l0)) as [Hf1 [Hf2 Hf3]].
  assert (Hitems : ls_items ls1 = item :: ls_items ls).
  { unfold ls1. rewrite Hf3. unfold list_next, list_narrow. cbn [ls_items].
    rewrite Hnb'. reflexivity. }
  assert (Hind1 : ls_indent ls1 = 0).
  { unfold ls1. rewrite Hf1. unfold list_next, list_narrow. cbn [ls_indent].
    destruct (is_blank l0); exact Hind. }
  assert (Hmark1 : ls_styles ls1 = S').
  { unfold ls1. rewrite Hf2. unfold list_next, list_narrow. cbn [ls_styles].
    destruct (is_blank l0); reflexivity. }
  assert (Hblanks1 : ls_blanks ls1 = false).
  { unfold ls1. destruct more as [|ml ms].
    - cbn [scan_list_content]. unfold list_next, list_narrow. cbn [ls_blanks].
      rewrite Hnb'. reflexivity.
    - apply (scan_list_content_blanks_last m (ml :: ms) _ _ ltac:(discriminate) Hlast). }
  assert (Hpad1 : pad_safe (pad_state (mk_pad m) (snd R)) = true).
  { rewrite pad_safe_pad_state. unfold R. apply run_pad_safe_final.
    cbn [run_pad_safe pad_safe]. exact Hsafe. }
  assert (Hloose1 : ls_loose ls1
                    = ((ls_loose ls || (ls_blanks ls && negb (starts_list (l0 :: more))))
                       || item_loose (l0 :: more))%bool).
  { unfold ls1. rewrite (scan_loose_eq m more _ _ Hsafe).
    unfold list_next, list_narrow. rewrite Hnb'.
    cbn [ls_loose ls_blanks starts_list].
    rewrite lines_loose_or, (lines_loose_cons_nonblank l0 more Hcl).
    destruct (classify l0); cbn [negb];
      rewrite ?andb_true_r, ?andb_false_r, ?orb_false_r; reflexivity. }
  assert (Hdone1 : (rev (rev (fst R)) ++ finish (pad_state (mk_pad m) (snd R)))%list
                   = parse_lines (l0 :: more) (PPara [])).
  { rewrite rev_involutive, pad_state_finish. unfold R.
    symmetry. apply parse_lines_run, surjective_pairing. }
  rewrite (IH ls1 (rev (fst R)) (pad_state (mk_pad m) (snd R)) Hind1 Hmark1 Hblanks1 Hpad1).
  rewrite Hitems, Hloose1, Hdone1, list_loose_of_pad.
  cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

(* The instance the canonical chain uses: the item's marker leaves the
   set where it was. *)
Lemma parse_item_and_tail :
  forall S m sp l0 more rest post out ls done inner,
    S <> [] -> marker_ok m = true ->
    narrow S (mk_sty m) = S ->
    ls_indent ls = 0 -> ls_styles ls = S ->
    item_ok m (l0 :: more) = true ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> ls_styles ls2 = S -> ls_blanks ls2 = false ->
       pad_safe inner2 = true ->
       parse_lines (list_tail_lines sp rest ++ post)%list (PList ls2 done2 inner2)
       = styles_list S (if (ls_loose ls2 || list_loose_of sp inner2 (map snd rest))%bool
                         then Loose else Tight)
                (rev (ls_items ls2) ++ (rev done2 ++ finish inner2)%list
                 :: map (fun it => parse_lines (snd it) (PPara [])) rest) :: out) ->
    parse_lines (litem_lines (m, l0 :: more)
                 ++ (list_tail_lines sp rest ++ post))%list (PList ls done inner)
    = styles_list S
             (if ((ls_loose ls || (ls_blanks ls && negb (starts_list (l0 :: more))))
                  || item_loose (l0 :: more)
                  || list_loose_of sp (snd (run_lines (l0 :: more) (PPara []))) (map snd rest))%bool
              then Loose else Tight)
             (rev (ls_items ls) ++ (rev done ++ finish inner)%list
              :: parse_lines (l0 :: more) (PPara [])
              :: map (fun it => parse_lines (snd it) (PPara [])) rest) :: out.
Proof.
  intros S m sp l0 more rest post out ls done inner HS Hm Hsty Hind Hmark Hok IH.
  exact (parse_item_and_tail_narrow S S S m sp l0 more rest post out ls done inner
           HS Hm Hsty Hind Hmark Hok IH).
Qed.

(* `Hclose` is the whole of what the ending contributes: from any list
   state the parser has reached, `post` emits that list and then whatever
   `out` is.  Both endings satisfy it -- `parse_lines_nil` for end of
   input, `parse_list_close` for a closing line. *)
(* Cutting `seps_loosen` at the head: the separator after `L` exists only
   when something follows it, and then it is `L`'s trailing state that
   decides whether it loosens. *)
Lemma seps_loosen_cons :
  forall L rest,
    seps_loosen (L :: rest)
    = match rest with
      | [] => false
      | L2 :: _ =>
          ((negb (ends_open_list L) && negb (starts_list L2))
           || seps_loosen rest)%bool
      end.
Proof. intros L rest. destruct rest; reflexivity. Qed.

Lemma parse_list_tail :
  forall S sp items post out ls done inner,
    S <> [] ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> pad_safe inner2 = true ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    ls_indent ls = 0 -> ls_styles ls = S -> ls_blanks ls = false ->
    pad_safe inner = true ->
    items_ok_at S items = true ->
    parse_lines (list_tail_lines sp items ++ post)%list (PList ls done inner)
    = styles_list S (if (ls_loose ls || list_loose_of sp inner (map snd items))%bool
                      then Loose else Tight)
             (rev (ls_items ls) ++ (rev done ++ finish inner)%list
              :: map (fun it => parse_lines (snd it) (PPara [])) items) :: out.
Proof.
  intros S sp items. induction items as [|it rest IH];
    intros post out ls done inner HS Hclose Hind Hmark Hblanks Hpad Hok.
  - cbn [list_tail_lines app map]. rewrite (Hclose ls done inner Hind Hpad).
    cbn [finish rev app].
    unfold list_loose_of. cbn [existsb map fst snd].
    rewrite (list_block_styles S ls _ Hmark).
    cbn [rev app]. destruct sp; rewrite ?orb_false_r; reflexivity.
  - destruct it as [mi L]. destruct L as [|l0 more];
      [cbn [items_ok_at forallb item_ok fst snd] in Hok;
       rewrite ?andb_false_r in Hok; discriminate|].
    cbn [items_ok_at forallb] in Hok. apply andb_prop in Hok as [HL Hrest].
    change (forallb _ rest) with (items_ok_at S rest) in Hrest.
    cbn [fst snd] in HL.
    apply andb_prop in HL as [HL Hstyeq].
    apply andb_prop in HL as [Hmi HL].
    apply narrow_admits_styles in Hstyeq.
    cbn [list_tail_lines]. rewrite <- !app_assoc. destruct sp.
    + cbn [item_sep app].
      rewrite (parse_item_and_tail S mi Tight l0 more rest post out ls done inner
                 HS Hmi Hstyeq Hind Hmark HL
                 (fun a b c H1 H2 H3 H4 =>
                    IH post out a b c HS Hclose H1 H2 H3 H4 Hrest)).
      rewrite Hblanks. unfold list_loose_of. cbn [existsb orb map fst snd].
      rewrite ?orb_false_r.
      destruct (ls_loose ls), (item_loose (l0 :: more)),
               (existsb (fun L => item_loose L) (map snd rest)); reflexivity.
    + change (item_sep Loose ++ (litem_lines (mi, l0 :: more)
                                 ++ (list_tail_lines Loose rest ++ post)))%list
        with (EmptyString :: (litem_lines (mi, l0 :: more)
                              ++ (list_tail_lines Loose rest ++ post)))%list.
      rewrite (parse_lines_step _ _ _ _ _
                 (step_list_blank EmptyString ls done inner _ _
                    (classify_blank EmptyString eq_refl) (surjective_pairing _))).
      cbn [app].
      rewrite (parse_item_and_tail S mi Loose l0 more rest post out
                 (if list_open inner then ls else list_blank ls)
                 (rev (fst (step EmptyString inner)) ++ done)%list
                 (snd (step EmptyString inner))
                 HS Hmi Hstyeq
                 ltac:(destruct (list_open inner); [exact Hind|cbn [list_blank]; exact Hind])
                 ltac:(destruct (list_open inner); [exact Hmark|cbn [list_blank]; exact Hmark])
                 HL
                 (fun a b c H1 H2 H3 H4 =>
                    IH post out a b c HS Hclose H1 H2 H3 H4 Hrest)).
      assert (Hls : forall A (f : list_state -> A),
                 f (if list_open inner then ls else list_blank ls)
                 = if list_open inner then f ls else f (list_blank ls))
        by (intros A f; destruct (list_open inner); reflexivity).
      rewrite (Hls _ ls_loose), (Hls _ ls_blanks), (Hls _ ls_items).
      cbn [list_blank ls_loose ls_blanks ls_items].
      rewrite rev_app_distr, rev_involutive, <- app_assoc.
      rewrite (step_blank_finish EmptyString inner
                 (classify_blank EmptyString eq_refl) Hpad).
      unfold list_loose_of at 2. cbn [map fst snd].
      rewrite seps_loosen_cons. unfold ends_open_list.
      rewrite Hblanks. cbn [map].
      destruct rest as [|r rs].
      (* the separator's verdict now has two conjuncts, so the case split
         is over the item before it and the item after it *)
      all: unfold list_loose_of; cbn [existsb map fst snd];
           destruct (list_open inner), (ls_loose ls),
                    (starts_list (l0 :: more)), (item_loose (l0 :: more));
           cbn [orb negb andb];
           rewrite ?orb_true_r, ?orb_false_r; try reflexivity.
Qed.

(* The list's set resolving at the tail's first item: everything after it
   holds `S'` fixed, so the rest is `parse_list_tail` at `S'`.  This is
   the step case of `parse_list_tail` with the narrowing left in, and it
   is all the ambiguous first marker needs, because a candidate set has at
   most two members -- one narrowing settles it and nothing later moves
   it. *)
Lemma parse_item_peel :
  forall S S' Sout sp mi l0 more rest post out ls done inner,
    S' <> [] -> marker_ok mi = true ->
    narrow S (mk_sty mi) = S' ->
    item_ok mi (l0 :: more) = true ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> ls_styles ls2 = S' -> ls_blanks ls2 = false ->
       pad_safe inner2 = true ->
       parse_lines (list_tail_lines sp rest ++ post)%list (PList ls2 done2 inner2)
       = styles_list Sout
           (if (ls_loose ls2 || list_loose_of sp inner2 (map snd rest))%bool
            then Loose else Tight)
           (rev (ls_items ls2) ++ (rev done2 ++ finish inner2)%list
            :: map (fun it => parse_lines (snd it) (PPara [])) rest) :: out) ->
    ls_indent ls = 0 -> ls_styles ls = S -> ls_blanks ls = false ->
    pad_safe inner = true ->
    parse_lines (list_tail_lines sp ((mi, l0 :: more) :: rest) ++ post)%list
                (PList ls done inner)
    = styles_list Sout
        (if (ls_loose ls
             || list_loose_of sp inner (map snd ((mi, l0 :: more) :: rest)))%bool
         then Loose else Tight)
        (rev (ls_items ls) ++ (rev done ++ finish inner)%list
         :: map (fun it => parse_lines (snd it) (PPara []))
                ((mi, l0 :: more) :: rest)) :: out.
Proof.
  intros S S' Sout sp mi l0 more rest post out ls done inner
         HS' Hmi Hstyeq HL IH Hind Hmark Hblanks Hpad.
  cbn [list_tail_lines]. rewrite <- !app_assoc. destruct sp.
  - cbn [item_sep app].
      rewrite (parse_item_and_tail_narrow S S' Sout mi Tight l0 more rest post out ls done inner
                 HS' Hmi Hstyeq Hind Hmark HL
                 IH).
      rewrite Hblanks. unfold list_loose_of. cbn [existsb orb map fst snd].
      rewrite ?orb_false_r.
      destruct (ls_loose ls), (item_loose (l0 :: more)),
               (existsb (fun L => item_loose L) (map snd rest)); reflexivity.
  - change (item_sep Loose ++ (litem_lines (mi, l0 :: more)
                                 ++ (list_tail_lines Loose rest ++ post)))%list
        with (EmptyString :: (litem_lines (mi, l0 :: more)
                              ++ (list_tail_lines Loose rest ++ post)))%list.
      rewrite (parse_lines_step _ _ _ _ _
                 (step_list_blank EmptyString ls done inner _ _
                    (classify_blank EmptyString eq_refl) (surjective_pairing _))).
      cbn [app].
      rewrite (parse_item_and_tail_narrow S S' Sout mi Loose l0 more rest post out
                 (if list_open inner then ls else list_blank ls)
                 (rev (fst (step EmptyString inner)) ++ done)%list
                 (snd (step EmptyString inner))
                 HS' Hmi Hstyeq
                 ltac:(destruct (list_open inner); [exact Hind|cbn [list_blank]; exact Hind])
                 ltac:(destruct (list_open inner); [exact Hmark|cbn [list_blank]; exact Hmark])
                 HL
                 IH).
      assert (Hls : forall A (f : list_state -> A),
                 f (if list_open inner then ls else list_blank ls)
                 = if list_open inner then f ls else f (list_blank ls))
        by (intros A f; destruct (list_open inner); reflexivity).
      rewrite (Hls _ ls_loose), (Hls _ ls_blanks), (Hls _ ls_items).
      cbn [list_blank ls_loose ls_blanks ls_items].
      rewrite rev_app_distr, rev_involutive, <- app_assoc.
      rewrite (step_blank_finish EmptyString inner
                 (classify_blank EmptyString eq_refl) Hpad).
      unfold list_loose_of at 2. cbn [map fst snd].
      rewrite seps_loosen_cons. unfold ends_open_list.
      rewrite Hblanks. cbn [map].
      destruct rest as [|r rs].
      (* the separator's verdict now has two conjuncts, so the case split
         is over the item before it and the item after it *)
      all: unfold list_loose_of; cbn [existsb map fst snd];
           destruct (list_open inner), (ls_loose ls),
                    (starts_list (l0 :: more)), (item_loose (l0 :: more));
           cbn [orb negb andb];
           rewrite ?orb_true_r, ?orb_false_r; try reflexivity.
Qed.

(* One peel: the set resolves at this item and the rest holds it. *)
Lemma parse_list_tail_head_narrow :
  forall S S' sp mi l0 more rest post out ls done inner,
    S' <> [] -> marker_ok mi = true ->
    narrow S (mk_sty mi) = S' ->
    item_ok mi (l0 :: more) = true ->
    items_ok_at S' rest = true ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> pad_safe inner2 = true ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    ls_indent ls = 0 -> ls_styles ls = S -> ls_blanks ls = false ->
    pad_safe inner = true ->
    parse_lines (list_tail_lines sp ((mi, l0 :: more) :: rest) ++ post)%list
                (PList ls done inner)
    = styles_list S'
        (if (ls_loose ls
             || list_loose_of sp inner (map snd ((mi, l0 :: more) :: rest)))%bool
         then Loose else Tight)
        (rev (ls_items ls) ++ (rev done ++ finish inner)%list
         :: map (fun it => parse_lines (snd it) (PPara []))
                ((mi, l0 :: more) :: rest)) :: out.
Proof.
  intros S S' sp mi l0 more rest post out ls done inner
         HS' Hmi Hstyeq HL Hrest Hclose Hind Hmark Hblanks Hpad.
  apply (parse_item_peel S S' S' sp mi l0 more rest post out ls done inner
           HS' Hmi Hstyeq HL); try assumption.
  intros ls2 done2 inner2 H1 H2 H3 H4.
  exact (parse_list_tail S' sp rest post out ls2 done2 inner2
           HS' Hclose H1 H2 H3 H4 Hrest).
Qed.

(* What closes a list: not the blank line -- that only records a gap --
   but the line after it, once that line is not blank, not a sibling
   marker, and not indented into the item.  The list is emitted whole and
   the parser restarts on that line from idle. *)
Lemma parse_list_close :
  forall ls done inner next tail,
    pad_safe inner = true ->
    classify next <> KBlank ->
    (forall m mc item, classify next <> KList m mc item) ->
    Nat.ltb (ls_indent ls) (indent_of next) = false ->
    parse_lines (EmptyString :: next :: tail) (PList ls done inner)
    = (finish (PList ls done inner) ++ parse_lines (next :: tail) (PPara []))%list.
Proof.
  intros ls done inner next tail Hpad Hnb Hnl Hind.
  destruct (step EmptyString inner) as [bs inner'] eqn:Hb.
  rewrite (parse_lines_step _ _ _ _ _
             (step_list_blank EmptyString ls done inner bs inner'
                (classify_blank EmptyString eq_refl) Hb)).
  cbn [app].
  (* the blank leaves the list state alone when the item claims it *)
  set (ls' := if list_open inner then ls else list_blank ls).
  assert (Hfin : finish (PList ls' (rev bs ++ done)%list inner')
                 = finish (PList ls done inner)).
  { pose proof (step_blank_finish EmptyString (PList ls done inner)
                  (classify_blank EmptyString eq_refl) Hpad) as H.
    rewrite (step_list_blank EmptyString ls done inner bs inner'
               (classify_blank EmptyString eq_refl) Hb) in H.
    cbn [fst snd app] in H. exact H. }
  assert (Hlazy : lazy_ok inner' = false).
  { pose proof (step_blank_lazy_false EmptyString inner
                  (classify_blank EmptyString eq_refl)) as H.
    rewrite Hb in H. cbn [snd] in H. exact H. }
  assert (Hind' : Nat.ltb (ls_indent ls') (indent_of next) = false)
    by (unfold ls'; destruct (list_open inner); exact Hind).
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
  destruct (classify next) as [| |f|dl dc|q|lvl txt|m mc listrest|kap|] eqn:Hclass.
  - congruence.
  - apply (Hdirect KThematic eq_refl eq_refl ltac:(discriminate) eq_refl).
  - apply (Hdirect (KFence f) eq_refl eq_refl ltac:(discriminate) eq_refl).
  - apply (Hdirect (KDiv dl dc) eq_refl eq_refl ltac:(discriminate) eq_refl).
  - rewrite (parse_lines_step _ _ _ _ _
               (step_list_quote_close next q ls' (rev bs ++ done)%list
                  inner' _ _ Hclass Hind' (surjective_pairing _))).
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_open next q _ _ Hclass (surjective_pairing _))).
    rewrite Hfin. reflexivity.
  - apply (Hdirect (KHeading lvl txt) eq_refl eq_refl ltac:(discriminate) eq_refl).
  - exfalso. apply (Hnl m mc listrest). reflexivity.
  - rewrite (parse_lines_step _ _ _ _ _
               (step_list_attr_close next kap ls' (rev bs ++ done)%list
                  inner' Hclass Hind')).
    rewrite (parse_lines_step _ _ _ _ _ (step_attr_open next kap Hclass)).
    rewrite Hfin. reflexivity.
  - apply (Hdirect KText eq_refl eq_refl ltac:(discriminate) Hlazy).
Qed.

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

(** Uniformity for a bullet list: every item's contents parse exactly as
    they would at top level, and the list's spacing is a scan of those
    same lines.  Stated over line lists, so it says nothing about the
    canonical form and needs nothing from it.

    The general form leaves the ending open (see `parse_list_tail`); the
    two corollaries below are the endings that occur. *)
Theorem list_uniformity_gen :
  forall m0 sp L0 tail post out,
    marker_ok m0 = true ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> pad_safe inner2 = true ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    items_ok m0 ((m0, L0) :: tail) = true ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: tail))
                 ++ post)%list (PPara [])
    = marker_list m0 (list_spacing_of sp (map snd ((m0, L0) :: tail)))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: tail)) :: out.
Proof.
  intros m0 sp L0 tail post out Hm0 Hclose Hok.
  destruct L0 as [|l0 more];
    [cbn [items_ok items_ok_at forallb item_ok fst snd] in Hok;
     rewrite ?andb_false_r in Hok; discriminate|].
  cbn [items_ok items_ok_at forallb] in Hok. apply andb_prop in Hok as [HL Htail].
  change (forallb _ tail) with (items_ok_at (mk_styles m0) tail) in Htail.
  cbn [fst snd] in HL.
  apply andb_prop in HL as [HL Hstyeq].
  apply andb_prop in HL as [Hmi HL].
  apply narrow_admits in Hstyeq.
  pose proof HL as HL'. cbn [item_ok] in HL'.
  apply andb_prop in HL' as [HL' Hlast].
  apply andb_prop in HL' as [HL' Hsafe].
  apply andb_prop in HL' as [Hth Hnb].
  apply negb_true_iff in Hth.
  assert (Hnb' : is_blank l0 = false).
  { unfold nonblank in Hnb. apply negb_true_iff in Hnb. exact Hnb. }
  assert (Hcl : classify l0 <> KBlank).
  { intros E. apply classify_kblank_blank in E. rewrite E in Hnb'. discriminate. }
  assert (Hb : ls_blanks (scan_list_content m0 (LSt 0 (mk_styles m0) false false [])
                            (pad_state (mk_pad m0) (snd (step l0 (PPara [])))) more) = false).
  { destruct more as [|ml ms]; [reflexivity|].
    apply (scan_list_content_blanks_last m0 (ml :: ms) _ _ ltac:(discriminate) Hlast). }
  rewrite list_lines_cons, <- app_assoc, parse_lines_app_run.
  unfold litem_lines at 1. cbn [fst snd].
  rewrite (run_item_open m0 Hm0 l0 more Hth Hsafe Hb). cbn [fst snd app].
  assert (Hpad1 : pad_safe (pad_state (mk_pad m0) (snd (run_lines (l0 :: more) (PPara [])))) = true).
  { rewrite pad_safe_pad_state. apply run_pad_safe_final.
    cbn [run_pad_safe pad_safe]. exact Hsafe. }
  rewrite (parse_list_tail (mk_styles m0) sp tail post out
             (LSt 0 (mk_styles m0)
                (lines_loose false false (snd (step l0 (PPara []))) more) false [])
             (rev (fst (run_lines (l0 :: more) (PPara []))))
             (pad_state (mk_pad m0) (snd (run_lines (l0 :: more) (PPara []))))
             (mk_styles_nonempty m0 Hm0) Hclose eq_refl eq_refl eq_refl Hpad1 Htail).
  cbn [ls_loose ls_items rev app].
  rewrite rev_involutive, pad_state_finish.
  rewrite <- (parse_lines_run (l0 :: more) (PPara []) _ _ (surjective_pairing _)).
  rewrite list_loose_of_pad.
  unfold list_spacing_of, list_loose_of.
  cbn [existsb map fst snd].
  rewrite <- (lines_loose_cons_nonblank l0 more Hcl).
  rewrite seps_loosen_cons. unfold ends_open_list.
  destruct sp; cbn [orb];
    destruct (item_loose (l0 :: more)),
             (existsb (fun L => item_loose L) (map snd tail)),
             tail; try reflexivity.
  all: destruct (list_open (snd (run_lines (l0 :: more) (PPara [])))); reflexivity.
Qed.

Theorem list_uniformity_gen_narrow :
  forall m0 m1 S' sp L0 L1 tail post out,
    marker_ok m0 = true -> marker_ok m1 = true ->
    S' <> [] -> narrow (mk_styles m0) (mk_sty m1) = S' ->
    item_ok m1 L1 = true -> L1 <> [] ->
    items_ok_at S' tail = true ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> pad_safe inner2 = true ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    item_ok m0 L0 = true ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: (m1, L1) :: tail))
                 ++ post)%list (PPara [])
    = styles_list S' (list_spacing_of sp (map snd ((m0, L0) :: (m1, L1) :: tail)))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: (m1, L1) :: tail)) :: out.
Proof.
  intros m0 m1 S' sp L0 L1 tail post out Hm0 Hm1 HS' Hnar Hok1 HL1ne Htail Hclose HL.
  destruct L0 as [|l0 more]; [cbn [item_ok] in HL; discriminate|].
  destruct L1 as [|l1 more1]; [congruence|].
  pose proof HL as HL'. cbn [item_ok] in HL'.
  apply andb_prop in HL' as [HL' Hlast].
  apply andb_prop in HL' as [HL' Hsafe].
  apply andb_prop in HL' as [Hth Hnb].
  apply negb_true_iff in Hth.
  assert (Hnb' : is_blank l0 = false).
  { unfold nonblank in Hnb. apply negb_true_iff in Hnb. exact Hnb. }
  assert (Hcl : classify l0 <> KBlank).
  { intros E. apply classify_kblank_blank in E. rewrite E in Hnb'. discriminate. }
  assert (Hb : ls_blanks (scan_list_content m0 (LSt 0 (mk_styles m0) false false [])
                            (pad_state (mk_pad m0) (snd (step l0 (PPara [])))) more) = false).
  { destruct more as [|ml ms]; [reflexivity|].
    apply (scan_list_content_blanks_last m0 (ml :: ms) _ _ ltac:(discriminate) Hlast). }
  rewrite list_lines_cons, <- app_assoc, parse_lines_app_run.
  unfold litem_lines at 1. cbn [fst snd].
  rewrite (run_item_open m0 Hm0 l0 more Hth Hsafe Hb). cbn [fst snd app].
  assert (Hpad1 : pad_safe (pad_state (mk_pad m0) (snd (run_lines (l0 :: more) (PPara [])))) = true).
  { rewrite pad_safe_pad_state. apply run_pad_safe_final.
    cbn [run_pad_safe pad_safe]. exact Hsafe. }
  rewrite (parse_list_tail_head_narrow (mk_styles m0) S' sp m1 l1 more1 tail post out
             (LSt 0 (mk_styles m0)
                (lines_loose false false (snd (step l0 (PPara []))) more) false [])
             (rev (fst (run_lines (l0 :: more) (PPara []))))
             (pad_state (mk_pad m0) (snd (run_lines (l0 :: more) (PPara []))))
             HS' Hm1 Hnar Hok1 Htail Hclose eq_refl eq_refl eq_refl Hpad1).
  cbn [ls_loose ls_items rev app].
  rewrite rev_involutive, pad_state_finish.
  rewrite <- (parse_lines_run (l0 :: more) (PPara []) _ _ (surjective_pairing _)).
  rewrite list_loose_of_pad.
  unfold list_spacing_of, list_loose_of.
  cbn [existsb map fst snd].
  rewrite <- (lines_loose_cons_nonblank l0 more Hcl).
  rewrite seps_loosen_cons. unfold ends_open_list.
  destruct sp; cbn [orb];
    destruct (item_loose (l0 :: more)),
             (existsb (fun L => item_loose L) (map snd tail)),
             tail; try reflexivity.
  all: destruct (list_open (snd (run_lines (l0 :: more) (PPara [])))); reflexivity.
Qed.

Theorem list_uniformity_gen_narrow2 :
  forall m0 m1 m2 S1 S2 sp L0 L1 L2 tail post out,
    marker_ok m0 = true -> marker_ok m1 = true -> marker_ok m2 = true ->
    S1 <> [] -> S2 <> [] ->
    narrow (mk_styles m0) (mk_sty m1) = S1 ->
    narrow S1 (mk_sty m2) = S2 ->
    item_ok m1 L1 = true -> L1 <> [] ->
    item_ok m2 L2 = true -> L2 <> [] ->
    items_ok_at S2 tail = true ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> pad_safe inner2 = true ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    item_ok m0 L0 = true ->
    parse_lines (list_lines sp
                   (map litem_lines ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail))
                 ++ post)%list (PPara [])
    = styles_list S2
             (list_spacing_of sp (map snd ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail)))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail)) :: out.
Proof.
  intros m0 m1 m2 S1 S2 sp L0 L1 L2 tail post out
         Hm0 Hm1 Hm2 HS1 HS2 Hnar1 Hnar2 Hok1 HL1ne Hok2 HL2ne Htail Hclose HL.
  destruct L0 as [|l0 more]; [cbn [item_ok] in HL; discriminate|].
  destruct L1 as [|l1 more1]; [congruence|].
  destruct L2 as [|l2 more2]; [congruence|].
  pose proof HL as HL'. cbn [item_ok] in HL'.
  apply andb_prop in HL' as [HL' Hlast].
  apply andb_prop in HL' as [HL' Hsafe].
  apply andb_prop in HL' as [Hth Hnb].
  apply negb_true_iff in Hth.
  assert (Hnb' : is_blank l0 = false).
  { unfold nonblank in Hnb. apply negb_true_iff in Hnb. exact Hnb. }
  assert (Hcl : classify l0 <> KBlank).
  { intros E. apply classify_kblank_blank in E. rewrite E in Hnb'. discriminate. }
  assert (Hb : ls_blanks (scan_list_content m0 (LSt 0 (mk_styles m0) false false [])
                            (pad_state (mk_pad m0) (snd (step l0 (PPara [])))) more) = false).
  { destruct more as [|ml ms]; [reflexivity|].
    apply (scan_list_content_blanks_last m0 (ml :: ms) _ _ ltac:(discriminate) Hlast). }
  rewrite list_lines_cons, <- app_assoc, parse_lines_app_run.
  unfold litem_lines at 1. cbn [fst snd].
  rewrite (run_item_open m0 Hm0 l0 more Hth Hsafe Hb). cbn [fst snd app].
  assert (Hpad1 : pad_safe (pad_state (mk_pad m0) (snd (run_lines (l0 :: more) (PPara [])))) = true).
  { rewrite pad_safe_pad_state. apply run_pad_safe_final.
    cbn [run_pad_safe pad_safe]. exact Hsafe. }
  rewrite (parse_item_peel (mk_styles m0) S1 S2 sp m1 l1 more1
             ((m2, l2 :: more2) :: tail) post out
             (LSt 0 (mk_styles m0)
                (lines_loose false false (snd (step l0 (PPara []))) more) false [])
             (rev (fst (run_lines (l0 :: more) (PPara []))))
             (pad_state (mk_pad m0) (snd (run_lines (l0 :: more) (PPara []))))
             HS1 Hm1 Hnar1 Hok1
             (fun a b c H1 H2 H3 H4 =>
                parse_list_tail_head_narrow S1 S2 sp m2 l2 more2 tail post out a b c
                  HS2 Hm2 Hnar2 Hok2 Htail Hclose H1 H2 H3 H4)
             eq_refl eq_refl eq_refl Hpad1).
  cbn [ls_loose ls_items rev app].
  rewrite rev_involutive, pad_state_finish.
  rewrite <- (parse_lines_run (l0 :: more) (PPara []) _ _ (surjective_pairing _)).
  rewrite list_loose_of_pad.
  unfold list_spacing_of, list_loose_of.
  cbn [existsb map fst snd].
  rewrite <- (lines_loose_cons_nonblank l0 more Hcl).
  rewrite seps_loosen_cons. unfold ends_open_list.
  destruct sp; cbn [orb];
    destruct (item_loose (l0 :: more)),
             (existsb (fun L => item_loose L) (map snd tail)),
             tail; try reflexivity.
  all: destruct (list_open (snd (run_lines (l0 :: more) (PPara [])))); reflexivity.
Qed.

(** The list ends the input. *)
Theorem list_uniformity :
  forall m0 sp L0 tail,
    marker_ok m0 = true ->
    items_ok m0 ((m0, L0) :: tail) = true ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: tail))) (PPara [])
    = [marker_list m0 (list_spacing_of sp (map snd ((m0, L0) :: tail)))
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
    S' <> [] -> narrow (mk_styles m0) (mk_sty m1) = S' ->
    item_ok m0 L0 = true -> item_ok m1 L1 = true -> L1 <> [] ->
    items_ok_at S' tail = true ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: (m1, L1) :: tail)))
                (PPara [])
    = [styles_list S' (list_spacing_of sp (map snd ((m0, L0) :: (m1, L1) :: tail)))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: (m1, L1) :: tail))].
Proof.
  intros m0 m1 S' sp L0 L1 tail Hm0 Hm1 HS' Hnar HL0 HL1 HL1ne Htail.
  rewrite <- (app_nil_r (list_lines sp
                (map litem_lines ((m0, L0) :: (m1, L1) :: tail)))).
  apply (list_uniformity_gen_narrow m0 m1 S' sp L0 L1 tail [] []);
    [exact Hm0 | exact Hm1 | exact HS' | exact Hnar | exact HL1 | exact HL1ne
    | exact Htail | | exact HL0].
  intros ls2 done2 inner2 _ _. rewrite parse_lines_nil, app_nil_r. reflexivity.
Qed.

(* The narrow form with the list closed by a following line. *)
Theorem list_uniformity_narrow_tail :
  forall m0 m1 S' sp L0 L1 items next tail,
    marker_ok m0 = true -> marker_ok m1 = true ->
    S' <> [] -> narrow (mk_styles m0) (mk_sty m1) = S' ->
    item_ok m0 L0 = true -> item_ok m1 L1 = true -> L1 <> [] ->
    items_ok_at S' items = true ->
    classify next <> KBlank ->
    (forall m mc it, classify next <> KList m mc it) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: (m1, L1) :: items))
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = styles_list S' (list_spacing_of sp (map snd ((m0, L0) :: (m1, L1) :: items)))
             (map (fun it => parse_lines (snd it) (PPara []))
                  ((m0, L0) :: (m1, L1) :: items))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros m0 m1 S' sp L0 L1 items next tail Hm0 Hm1 HS' Hnar HL0 HL1 HL1ne Hitems
         Hnb Hnl Hindent.
  apply (list_uniformity_gen_narrow m0 m1 S' sp L0 L1 items);
    [exact Hm0 | exact Hm1 | exact HS' | exact Hnar | exact HL1 | exact HL1ne
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
    = [styles_list S2
         (list_spacing_of sp (map snd ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail)))
         (map (fun it => parse_lines (snd it) (PPara []))
              ((m0, L0) :: (m1, L1) :: (m2, L2) :: tail))].
Proof.
  intros m0 m1 m2 S1 S2 sp L0 L1 L2 tail
         Hm0 Hm1 Hm2 HS1 HS2 Hnar1 Hnar2 HL0 HL1 HL1ne HL2 HL2ne Htail.
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
    S1 <> [] -> S2 <> [] ->
    narrow (mk_styles m0) (mk_sty m1) = S1 ->
    narrow S1 (mk_sty m2) = S2 ->
    item_ok m0 L0 = true ->
    item_ok m1 L1 = true -> L1 <> [] ->
    item_ok m2 L2 = true -> L2 <> [] ->
    items_ok_at S2 items = true ->
    classify next <> KBlank ->
    (forall m mc it, classify next <> KList m mc it) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp
                   (map litem_lines ((m0, L0) :: (m1, L1) :: (m2, L2) :: items))
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = styles_list S2
        (list_spacing_of sp (map snd ((m0, L0) :: (m1, L1) :: (m2, L2) :: items)))
        (map (fun it => parse_lines (snd it) (PPara []))
             ((m0, L0) :: (m1, L1) :: (m2, L2) :: items))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros m0 m1 m2 S1 S2 sp L0 L1 L2 items next tail
         Hm0 Hm1 Hm2 HS1 HS2 Hnar1 Hnar2 HL0 HL1 HL1ne HL2 HL2ne Hitems
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
    (forall m mc it, classify next <> KList m mc it) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines ((m0, L0) :: items))
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = marker_list m0 (list_spacing_of sp (map snd ((m0, L0) :: items)))
             (map (fun it => parse_lines (snd it) (PPara [])) ((m0, L0) :: items))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros m0 sp L0 items next tail Hm0 Hok Hnb Hnl Hindent.
  apply list_uniformity_gen; [exact Hm0 | | exact Hok].
  intros ls2 done2 inner2 Hind2 Hpad2.
  apply parse_list_close; try assumption.
  rewrite Hind2, Hindent. reflexivity.
Qed.

(* Every item at the same marker: the shape the bullet styles take, and
   the instantiation the three corollaries below use. *)
Definition same_marker (m : marker) (lss : list (list string)) : list litem :=
  map (fun L => (m, L)) lss.

Lemma items_ok_same_marker :
  forall m lss,
    marker_ok m = true -> forallb (item_ok m) lss = true ->
    items_ok m (same_marker m lss) = true.
Proof.
  intros m lss Hm Hok. unfold items_ok, items_ok_at, same_marker.
  revert Hok. induction lss as [|L rest IH]; [reflexivity|].
  cbn [map forallb fst snd]. intros H. apply andb_prop in H as [HL Hrest].
  rewrite Hm, HL, (admits_styles_refl m), (IH Hrest). reflexivity.
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
    marker_ok m = true -> lss <> [] ->
    forallb (item_ok m) lss = true ->
    parse_lines (list_lines sp (map (indent_lines (mk_open m) (mk_cont m)) lss))
                (PPara [])
    = [marker_list m (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss)].
Proof.
  intros m sp lss Hm Hne Hok.
  destruct lss as [|L0 rest]; [congruence|].
  pose proof (items_ok_same_marker m (L0 :: rest) Hm Hok) as Hio.
  unfold same_marker in Hio. cbn [map] in Hio.
  pose proof (list_uniformity m sp L0 (same_marker m rest) Hm Hio) as Hu.
  rewrite <- (map_litem_lines_same_marker m (L0 :: rest)).
  unfold same_marker at 1. cbn [map]. fold (same_marker m rest).
  change (litem_lines (m, L0) :: map litem_lines (same_marker m rest))
    with (map litem_lines ((m, L0) :: same_marker m rest)).
  rewrite Hu.
  cbn [map snd]. rewrite map_snd_same_marker.
  unfold same_marker. rewrite map_map. cbn [snd]. reflexivity.
Qed.

Corollary list_uniformity_tail_same :
  forall m sp lss next tail,
    marker_ok m = true -> lss <> [] ->
    forallb (item_ok m) lss = true ->
    classify next <> KBlank ->
    (forall a b c, classify next <> KList a b c) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map (indent_lines (mk_open m) (mk_cont m)) lss)
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = marker_list m (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss)
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros m sp lss next tail Hm Hne Hok Hnb Hnl Hindent.
  destruct lss as [|L0 rest]; [congruence|].
  pose proof (items_ok_same_marker m (L0 :: rest) Hm Hok) as Hio.
  unfold same_marker in Hio. cbn [map] in Hio.
  pose proof (list_uniformity_tail m sp L0 (same_marker m rest) next tail
                Hm Hio Hnb Hnl Hindent) as Hu.
  rewrite <- (map_litem_lines_same_marker m (L0 :: rest)).
  unfold same_marker at 1. cbn [map]. fold (same_marker m rest).
  change (litem_lines (m, L0) :: map litem_lines (same_marker m rest))
    with (map litem_lines ((m, L0) :: same_marker m rest)).
  rewrite Hu.
  cbn [map snd]. rewrite map_snd_same_marker.
  unfold same_marker. rewrite map_map. cbn [snd]. reflexivity.
Qed.

