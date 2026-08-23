(* ai-disclosure: ai-generated *)

(* The fold's equation lemmas, and uniformity for block quotes and
   fenced divs: a container's contents parse exactly as they would at
   top level.

   Also the locality theorems -- `prefix_determinism`,
   `no_future_line_dependence`, `prefix_state_suffices` -- which say the
   fold is a state machine over its prefix.  Lists get the same treatment
   in `ListUniformity.v`, which is much longer because an item's lines
   are indented and the tight/loose verdict is stateful. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast Attributes Inline Marker Step.
Import ListNotations.

Local Open Scope string_scope.

(* The delimiter table this file is read at.  Implicit, so nothing below
   mentions it: what it buys is that the statements quantify over the
   family rather than over djot's spelling. *)
Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
The fold, and uniformity for quotes and divs
============================================
*)

(*
Lifting to the fold
-------------------
*)

(* The fold at a nonzero column.  Only quote and list *content* lemmas
   need it: `parse_lines` itself is the column-0 instance, and it is what
   every statement outside the block parser uses. *)
Fixpoint parse_lines_at (off : nat) (lines : list string) (st : pstate)
  : blocks :=
  match lines with
  | [] => finish st
  | l :: rest =>
      let (bs, st') := step_at off l st in
      (bs ++ parse_lines_at off rest st')%list
  end.

Lemma parse_lines_at_zero :
  forall lines st, parse_lines_at 0 lines st = parse_lines lines st.
Proof.
  induction lines as [|l lines IH]; intros st; [reflexivity|].
  cbn [parse_lines_at parse_lines]. rewrite step_at_zero.
  destruct (step l st) as [bs st'] eqn:E. rewrite IH. reflexivity.
Qed.

(** Running the fold `k` columns over, from a state shifted to match,
    gives the same blocks: the shift lives only in the state, and `finish`
    does not read columns. *)
Lemma parse_lines_at_shift :
  forall k off lines st,
    parse_lines_at (k + off) lines (pad_state k st) = parse_lines_at off lines st.
Proof.
  induction lines as [|l lines IH]; intros st.
  { cbn [parse_lines_at]. apply pad_state_finish. }
  cbn [parse_lines_at]. rewrite step_at_shift.
  destruct (step_at off l st) as [bs st'] eqn:E. cbn [fst snd].
  rewrite IH. reflexivity.
Qed.

Lemma parse_lines_shift :
  forall k lines st,
    parse_lines_at k lines (pad_state k st) = parse_lines lines st.
Proof.
  intros k lines st.
  rewrite <- (parse_lines_at_zero lines st).
  rewrite <- (parse_lines_at_shift k 0 lines st), Nat.add_0_r.
  reflexivity.
Qed.

(* A canonical quote prefix eats exactly two columns. *)
Lemma consumed_quote_prefix :
  forall l, consumed ("> " ++ l) l = quote_pad.
Proof.
  intros l. unfold consumed, quote_pad, quote_open.
  rewrite length_append. cbn [String.length]. lia.
Qed.


Lemma parse_lines_nil : forall st, parse_lines [] st = finish st.
Proof. reflexivity. Qed.

(* The workhorse: one transition, one prefix of emitted blocks. *)
Lemma parse_lines_step :
  forall l rest st bs st',
    step l st = (bs, st') ->
    parse_lines (l :: rest) st = (bs ++ parse_lines rest st')%list.
Proof. intros l rest st bs st' H. cbn [parse_lines]. rewrite H. reflexivity. Qed.

(* para_inlines_one / para_inlines_cons2 are in Inline.v, next to the
   definition they unfold. *)

Lemma parse_lines_nil_cons :
  forall c cur',
    parse_lines [] (PPara (c :: cur')) =
    [mk (Para (para_inlines (rev (c :: cur'))))].
Proof. reflexivity. Qed.

Lemma parse_lines_blank_nil :
  forall l rest, classify l = KBlank ->
  parse_lines (l :: rest) (PPara []) = parse_lines rest (PPara []).
Proof.
  intros l rest H.
  rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
Qed.

Lemma parse_lines_blank_cons :
  forall l rest c cur', classify l = KBlank ->
  parse_lines (l :: rest) (PPara (c :: cur')) =
  mk (Para (para_inlines (rev (c :: cur')))) :: parse_lines rest (PPara []).
Proof.
  intros l rest c cur' H.
  rewrite (parse_lines_step _ _ _ _ _ (step_para_flush _ _ _ H)). reflexivity.
Qed.

Lemma parse_lines_thematic_nil :
  forall l rest, classify l = KThematic ->
  parse_lines (l :: rest) (PPara []) =
  mk ThematicBreak :: parse_lines rest (PPara []).
Proof.
  intros l rest H.
  rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
Qed.

Lemma parse_lines_fence_open :
  forall l rest f, classify l = KFence f ->
  parse_lines (l :: rest) (PPara []) =
  parse_lines rest (PFence f (indent_of l) []).
Proof.
  intros l rest f H.
  rewrite (parse_lines_step _ _ _ _ _ (step_fence_open _ _ H)). reflexivity.
Qed.

Lemma parse_lines_text :
  forall l rest cur, classify l = KText ->
  parse_lines (l :: rest) (PPara cur) =
  parse_lines rest (PPara (drop_leading_ws l :: cur)).
Proof.
  intros l rest cur H. destruct cur as [|c cur'].
  - rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
  - rewrite (parse_lines_step _ _ _ _ _
               (step_para_cont _ _ _ (fun E => ltac:(rewrite H in E; discriminate))
                  ltac:(rewrite H; reflexivity))).
    reflexivity.
Qed.

(* Any nonblank line continues an open paragraph. *)
Lemma parse_lines_cont :
  forall l rest c cur',
    classify l <> KBlank -> binterrupt (classify l) = false ->
  parse_lines (l :: rest) (PPara (c :: cur')) =
  parse_lines rest (PPara (drop_leading_ws l :: c :: cur')).
Proof.
  intros l rest c cur' H Hi.
  rewrite (parse_lines_step _ _ _ _ _ (step_para_cont _ _ _ H Hi)). reflexivity.
Qed.

(*
Reference-definition equations
------------------------------
*)

Lemma parse_lines_ref_open :
  forall l rest lbl v, classify l = KRef lbl v ->
  parse_lines (l :: rest) (PPara []) = parse_lines rest (PRef (indent_of l) lbl v).
Proof.
  intros l rest lbl v H.
  rewrite (parse_lines_step _ _ _ _ _ (step_ref_open _ _ _ H)). reflexivity.
Qed.

(* A blank line ends the definition and emits it: `ref_cont` has no run to
   take from a blank line, whatever column the opener sits at. *)
Lemma parse_lines_ref_blank :
  forall l rest ind lbl v, classify l = KBlank ->
  parse_lines (l :: rest) (PRef ind lbl v) =
  ref_block lbl v :: parse_lines rest (PPara []).
Proof.
  intros l rest ind lbl v H.
  rewrite (parse_lines_step _ _ _ _ _ (step_ref_blank _ _ _ _ H)). reflexivity.
Qed.

(*
Table equations
---------------
*)

Lemma parse_lines_row_open :
  forall l rest r, classify l = KRow r ->
  parse_lines (l :: rest) (PPara []) = parse_lines rest (PTable [r] TOpen).
Proof.
  intros l rest r H.
  rewrite (parse_lines_step _ _ _ _ _ (step_row_open _ _ H)). reflexivity.
Qed.

Lemma parse_lines_table_row :
  forall l rest rows r,
    caption_open l = None -> is_blank l = false -> classify l = KRow r ->
    parse_lines (l :: rest) (PTable rows TOpen)
    = parse_lines rest (PTable (r :: rows) TOpen).
Proof.
  intros l rest rows r Hc Hb H.
  rewrite (parse_lines_step _ _ _ _ _ (step_table_row _ _ _ Hc Hb H)). reflexivity.
Qed.

Lemma parse_lines_table_blank :
  forall l rest rows, is_blank l = true ->
  parse_lines (l :: rest) (PTable rows TOpen)
  = parse_lines rest (PTable rows TAfterBlank).
Proof.
  intros l rest rows H.
  rewrite (parse_lines_step _ _ _ _ _ (step_table_blank _ _ H)). reflexivity.
Qed.

(* The line is reprocessed at the enclosing level, so the whole rule is
   "emit the table and read this line again from idle". *)
Lemma parse_lines_table_close :
  forall l rest rows, caption_open l = None -> is_blank l = false ->
  parse_lines (l :: rest) (PTable rows TAfterBlank)
  = table_block (rev rows) TAfterBlank :: parse_lines (l :: rest) (PPara []).
Proof.
  intros l rest rows Hc Hb.
  destruct (step l (PPara [])) as [bs st'] eqn:Hs.
  rewrite (parse_lines_step _ _ _ _ _ (step_table_close _ _ _ _ Hc Hb Hs)).
  rewrite (parse_lines_step _ _ _ _ _ Hs). reflexivity.
Qed.

Lemma parse_lines_table_eof :
  forall rows cap, parse_lines [] (PTable rows cap) = [table_block (rev rows) cap].
Proof. reflexivity. Qed.

(*
Fence equations
---------------
*)

Lemma parse_lines_fence_eof :
  forall f ind acc, parse_lines [] (PFence f ind acc) = [fence_block f (rev acc)].
Proof. reflexivity. Qed.

Lemma parse_lines_fence_close :
  forall l rest f ind acc, fence_close f l = true ->
  parse_lines (l :: rest) (PFence f ind acc) =
  fence_block f (rev acc) :: parse_lines rest (PPara []).
Proof.
  intros l rest f ind acc H.
  rewrite (parse_lines_step _ _ _ _ _ (step_fence_close _ _ _ _ H)). reflexivity.
Qed.

Lemma parse_lines_fence_content :
  forall l rest f ind acc, fence_close f l = false ->
  parse_lines (l :: rest) (PFence f ind acc) =
  parse_lines rest (PFence f ind (drop_ws_upto ind l :: acc)).
Proof.
  intros l rest f ind acc H.
  rewrite (parse_lines_step _ _ _ _ _ (step_fence_content _ _ _ _ H)). reflexivity.
Qed.

(*
Seed lemmas: feeding runs of lines
----------------------------------
*)

(* A run of nonblank lines accumulates (reversed, leading whitespace
   stripped) onto an open paragraph. *)
Lemma parse_lines_cont_seed :
  forall ls tail c cur',
    forallb nonblank ls = true ->
    forallb (fun l => negb (binterrupt (classify l))) ls = true ->
    parse_lines (ls ++ tail)%list (PPara (c :: cur')) =
    parse_lines tail (PPara (rev (map drop_leading_ws ls) ++ (c :: cur'))%list).
Proof.
  induction ls as [|l ls IH]; intros tail c cur' H Hi.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hl Hls].
    simpl in Hi. apply andb_true_iff in Hi as [Hi1 His].
    apply negb_true_iff in Hi1.
    unfold nonblank in Hl. apply negb_true_iff in Hl.
    change ((l :: ls) ++ tail)%list with (l :: (ls ++ tail))%list.
    rewrite parse_lines_cont
      by (first [ intros E; rewrite (classify_kblank_blank _ E) in Hl; discriminate
                | exact Hi1 ]).
    rewrite IH by (exact Hls || exact His).
    simpl rev. rewrite <- app_assoc. reflexivity.
Qed.

(* Opening a paragraph with a text line, then feeding its remaining lines. *)
Lemma parse_lines_para_seed :
  forall a ls tail,
    classify a = KText ->
    forallb nonblank ls = true ->
    forallb (fun l => negb (binterrupt (classify l))) ls = true ->
    parse_lines ((a :: ls) ++ tail)%list (PPara []) =
    parse_lines tail (PPara (rev (map drop_leading_ws (a :: ls)))).
Proof.
  intros a ls tail Ha Hls His.
  change ((a :: ls) ++ tail)%list with (a :: (ls ++ tail))%list.
  rewrite parse_lines_text by exact Ha.
  rewrite parse_lines_cont_seed by (exact Hls || exact His).
  reflexivity.
Qed.

(* A run of non-closing lines accumulates (reversed) into an open fence. *)
Lemma parse_lines_fence_seed :
  forall ls tail f ind acc,
    forallb (fun l => negb (fence_close f l)) ls = true ->
    parse_lines (ls ++ tail)%list (PFence f ind acc) =
    parse_lines tail (PFence f ind (rev (map (drop_ws_upto ind) ls) ++ acc)%list).
Proof.
  induction ls as [|l ls IH]; intros tail f ind acc H.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hl Hls].
    apply negb_true_iff in Hl.
    change ((l :: ls) ++ tail)%list with (l :: (ls ++ tail))%list.
    rewrite parse_lines_fence_content by exact Hl.
    rewrite IH by exact Hls.
    simpl rev. rewrite <- app_assoc. reflexivity.
Qed.

(*
Heading equations
-----------------
*)

Lemma step_heading_cont :
  forall l lvl txt cur,
    classify l = KHeading lvl txt ->
    step l (PHeading lvl cur) = ([], PHeading lvl (push_text txt cur)).
Proof.
  intros l lvl txt cur H. unfold step. cbn [step_fuel]. rewrite H.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma step_heading_close :
  forall l lvl cur,
    classify l = KBlank ->
    step l (PHeading lvl cur) = ([heading_block lvl cur], PPara []).
Proof.
  intros l lvl cur H. unfold step. cbn [step_fuel]. rewrite H. reflexivity.
Qed.

Lemma parse_lines_heading_open :
  forall l rest lvl txt,
    classify l = KHeading lvl txt ->
    parse_lines (l :: rest) (PPara []) =
    parse_lines rest (PHeading lvl (push_text txt [])).
Proof.
  intros l rest lvl txt H.
  rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
Qed.

Lemma parse_lines_heading_cont :
  forall l rest lvl txt cur,
    classify l = KHeading lvl txt ->
    parse_lines (l :: rest) (PHeading lvl cur) =
    parse_lines rest (PHeading lvl (push_text txt cur)).
Proof.
  intros l rest lvl txt cur H.
  rewrite (parse_lines_step _ _ _ _ _ (step_heading_cont _ _ _ _ H)).
  reflexivity.
Qed.

Lemma parse_lines_heading_close :
  forall l rest lvl cur,
    classify l = KBlank ->
    parse_lines (l :: rest) (PHeading lvl cur) =
    heading_block lvl cur :: parse_lines rest (PPara []).
Proof.
  intros l rest lvl cur H.
  rewrite (parse_lines_step _ _ _ _ _ (step_heading_close _ _ _ H)).
  reflexivity.
Qed.

(* A run of canonically-rendered heading lines accumulates (reversed,
   leading whitespace stripped) onto the open heading, exactly as
   paragraph lines do. *)
Lemma parse_lines_heading_seed :
  forall lvl ls tail cur,
    1 <= lvl ->
    forallb nonblank ls = true ->
    parse_lines (map (heading_line lvl) ls ++ tail)%list (PHeading lvl cur) =
    parse_lines tail (PHeading lvl (rev (map drop_leading_ws ls) ++ cur)%list).
Proof.
  intros lvl ls. induction ls as [|a ls IH]; intros tail cur Hlvl H.
  - reflexivity.
  - cbn [forallb] in H. apply andb_true_iff in H as [Ha Hls].
    unfold nonblank in Ha. apply negb_true_iff in Ha.
    cbn [map app].
    rewrite (parse_lines_heading_cont _ _ _ a _
               (classify_canonical_heading lvl a Hlvl)).
    unfold push_text. rewrite Ha.
    rewrite IH by assumption.
    cbn [rev map]. rewrite <- app_assoc. reflexivity.
Qed.

(* Same, seen through an all-whitespace pad: classify_canonical_heading_pad
   still extracts a clean, pad-free `a`, so push_text's own drop_leading_ws
   erases whatever's left the same as in the unpadded case — no new
   argument, just classify_canonical_heading_pad in place of
   classify_canonical_heading. *)
Lemma parse_lines_heading_seed_pad :
  forall pad, is_blank pad = true ->
  forall lvl ls tail cur,
    1 <= lvl ->
    forallb nonblank ls = true ->
    parse_lines (map (fun l => (pad ++ heading_line lvl l)%string) ls ++ tail)%list
                (PHeading lvl cur) =
    parse_lines tail (PHeading lvl (rev (map drop_leading_ws ls) ++ cur)%list).
Proof.
  intros pad Hpad lvl ls. induction ls as [|a ls IH]; intros tail cur Hlvl H.
  - reflexivity.
  - cbn [forallb] in H. apply andb_true_iff in H as [Ha Hls].
    unfold nonblank in Ha. apply negb_true_iff in Ha.
    cbn [map app].
    rewrite (parse_lines_heading_cont _ _ _ a _
               (classify_canonical_heading_pad pad lvl a Hpad Hlvl)).
    unfold push_text. rewrite Ha.
    rewrite IH by assumption.
    cbn [rev map]. rewrite <- app_assoc. reflexivity.
Qed.

(*
Uniformity of block quotes
--------------------------

The payoff of routing a quote's contents back through `step`: prefixing
every line of a document with "> " parses to exactly that document,
wrapped in a quote.  Nothing about the contents is assumed — this holds
for every construct the parser knows, including future ones and nested
quotes. *)

(* Inside an open quote, the prefixed lines drive the inner state and
   the blank line that follows closes the quote. *)
Lemma parse_lines_quote_cont :
  forall lines tail done inner,
    parse_lines (map (fun l => ("> " ++ l)%string) lines ++ EmptyString :: tail)%list
                (PQuote done (pad_state quote_pad inner))
    = mk (BlockQuote (rev done ++ parse_lines lines inner)%list)
      :: parse_lines tail (PPara []).
Proof.
  induction lines as [|l lines IH]; intros tail done inner.
  - cbn [map app].
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_close _ KBlank _ _ _ _
                  (classify_blank EmptyString eq_refl) eq_refl eq_refl eq_refl)).
    rewrite pad_state_finish. reflexivity.
  - cbn [map app].
    destruct (step l inner) as [bs inner'] eqn:Es.
    assert (Esh : step_at (consumed ("> " ++ l) l) l (pad_state quote_pad inner)
                  = (bs, pad_state quote_pad inner')).
    { rewrite consumed_quote_prefix.
      rewrite <- (Nat.add_0_r quote_pad) at 1. rewrite step_at_shift.
      rewrite step_at_zero, Es. reflexivity. }
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _ (classify_canonical_quote l) Esh)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

(* ...and the same when the input simply ends. *)
Lemma parse_lines_quote_cont_eof :
  forall lines done inner,
    parse_lines (map (fun l => ("> " ++ l)%string) lines)
                (PQuote done (pad_state quote_pad inner))
    = [mk (BlockQuote (rev done ++ parse_lines lines inner)%list)].
Proof.
  induction lines as [|l lines IH]; intros done inner.
  - cbn [map parse_lines finish]. rewrite pad_state_finish. reflexivity.
  - cbn [map].
    destruct (step l inner) as [bs inner'] eqn:Es.
    assert (Esh : step_at (consumed ("> " ++ l) l) l (pad_state quote_pad inner)
                  = (bs, pad_state quote_pad inner')).
    { rewrite consumed_quote_prefix.
      rewrite <- (Nat.add_0_r quote_pad) at 1. rewrite step_at_shift.
      rewrite step_at_zero, Es. reflexivity. }
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _ (classify_canonical_quote l) Esh)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

Lemma parse_lines_quote :
  forall l lines tail,
    parse_lines
      (map (fun x => ("> " ++ x)%string) (l :: lines) ++ EmptyString :: tail)%list
      (PPara [])
    = mk (BlockQuote (parse_lines (l :: lines) (PPara [])))
      :: parse_lines tail (PPara []).
Proof.
  intros l lines tail. cbn [map app].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote l) Es)).
  cbn [app]. rewrite consumed_quote_prefix.
  rewrite parse_lines_quote_cont, rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.

(** Uniformity for block quotes: a quote's contents parse exactly as
    they would at top level.  One proof, every construct. *)
Theorem quote_uniformity :
  forall l lines,
    parse_lines (map (fun x => ("> " ++ x)%string) (l :: lines)) (PPara [])
    = [mk (BlockQuote (parse_lines (l :: lines) (PPara [])))].
Proof.
  intros l lines. cbn [map].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote l) Es)).
  cbn [app]. rewrite consumed_quote_prefix.
  rewrite parse_lines_quote_cont_eof, rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.

(* The same four lemmas, seen through an all-whitespace pad in front of
   every "> " — verbatim copies of the proofs above with
   classify_canonical_quote_pad in place of classify_canonical_quote.
   This is what lets a quote nested inside a list item ignore the
   item's own indent entirely: the pad never reaches `rest`, so the
   recursion into the quote's contents is byte-identical to the
   unpadded case.  A nested list is not byte-identical -- its recorded
   column moves with the pad -- which is why the list side is stated as
   a shift (`run_lines_pad_shift`) rather than an equality. *)
Lemma consumed_quote_prefix_pad :
  forall pad l, consumed (pad ++ "> " ++ l) l = String.length pad + quote_pad.
Proof.
  intros pad l. unfold consumed, quote_pad, quote_open.
  rewrite !length_append. cbn [String.length]. lia.
Qed.

Lemma parse_lines_quote_cont_pad :
  forall pad, is_blank pad = true ->
  forall sep, classify sep = KBlank ->
  forall lines tail done inner,
    parse_lines (map (fun l => pad ++ "> " ++ l)%string lines ++ sep :: tail)%list
                (PQuote done (pad_state (String.length pad + quote_pad) inner))
    = mk (BlockQuote (rev done ++ parse_lines lines inner)%list)
      :: parse_lines tail (PPara []).
Proof.
  intros pad Hpad sep Hsep. induction lines as [|l lines IH]; intros tail done inner.
  - cbn [map app].
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_close _ KBlank _ _ _ _ Hsep eq_refl eq_refl eq_refl)).
    rewrite pad_state_finish. reflexivity.
  - cbn [map app].
    destruct (step l inner) as [bs inner'] eqn:Es.
    assert (Esh : step_at (consumed (pad ++ "> " ++ l) l) l
                    (pad_state (String.length pad + quote_pad) inner)
                  = (bs, pad_state (String.length pad + quote_pad) inner')).
    { rewrite consumed_quote_prefix_pad.
      rewrite <- (Nat.add_0_r (String.length pad + quote_pad)) at 1.
      rewrite step_at_shift, step_at_zero, Es. reflexivity. }
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _
                  (classify_canonical_quote_pad pad l Hpad) Esh)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

Lemma parse_lines_quote_cont_eof_pad :
  forall pad, is_blank pad = true ->
  forall lines done inner,
    parse_lines (map (fun l => pad ++ "> " ++ l)%string lines)
                (PQuote done (pad_state (String.length pad + quote_pad) inner))
    = [mk (BlockQuote (rev done ++ parse_lines lines inner)%list)].
Proof.
  intros pad Hpad. induction lines as [|l lines IH]; intros done inner.
  - cbn [map parse_lines finish]. rewrite pad_state_finish. reflexivity.
  - cbn [map].
    destruct (step l inner) as [bs inner'] eqn:Es.
    assert (Esh : step_at (consumed (pad ++ "> " ++ l) l) l
                    (pad_state (String.length pad + quote_pad) inner)
                  = (bs, pad_state (String.length pad + quote_pad) inner')).
    { rewrite consumed_quote_prefix_pad.
      rewrite <- (Nat.add_0_r (String.length pad + quote_pad)) at 1.
      rewrite step_at_shift, step_at_zero, Es. reflexivity. }
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _
                  (classify_canonical_quote_pad pad l Hpad) Esh)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

Lemma parse_lines_quote_pad :
  forall pad, is_blank pad = true ->
  forall sep, classify sep = KBlank ->
  forall l lines tail,
    parse_lines
      (map (fun x => pad ++ "> " ++ x)%string (l :: lines) ++ sep :: tail)%list
      (PPara [])
    = mk (BlockQuote (parse_lines (l :: lines) (PPara [])))
      :: parse_lines tail (PPara []).
Proof.
  intros pad Hpad sep Hsep l lines tail. cbn [map app].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote_pad pad l Hpad) Es)).
  cbn [app]. rewrite consumed_quote_prefix_pad.
  rewrite (parse_lines_quote_cont_pad pad Hpad sep Hsep), rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.

Theorem quote_uniformity_pad :
  forall pad, is_blank pad = true ->
  forall l lines,
    parse_lines (map (fun x => pad ++ "> " ++ x)%string (l :: lines)) (PPara [])
    = [mk (BlockQuote (parse_lines (l :: lines) (PPara [])))].
Proof.
  intros pad Hpad l lines. cbn [map].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote_pad pad l Hpad) Es)).
  cbn [app]. rewrite consumed_quote_prefix_pad.
  rewrite (parse_lines_quote_cont_eof_pad pad Hpad), rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.
(*
Running lines without finishing
-------------------------------
*)

(** Run a finite line prefix without applying [finish].  List proofs need
    the residual inner state at an item boundary; [parse_lines] deliberately
    hides it by finishing at end of input. *)
Fixpoint run_lines (lines : list string) (st : pstate) : blocks * pstate :=
  match lines with
  | [] => ([], st)
  | l :: rest =>
      let '(bs, st') := step l st in
      let '(more, st'') := run_lines rest st' in
      ((bs ++ more)%list, st'')
  end.

Lemma run_lines_app :
  forall xs ys st,
    run_lines (xs ++ ys)%list st =
      let '(bs, st') := run_lines xs st in
      let '(more, st'') := run_lines ys st' in
      ((bs ++ more)%list, st'').
Proof.
  induction xs as [|x xs IH]; intros ys st.
  - cbn [app run_lines]. destruct (run_lines ys st). reflexivity.
  -
  cbn [run_lines app]. destruct (step x st) as [head st1].
  rewrite (IH ys st1).
  destruct (run_lines xs st1) as [middle st2].
  destruct (run_lines ys st2) as [tail st3].
  rewrite app_assoc. reflexivity.
Qed.

Lemma run_lines_continue :
  forall xs ys st head middle tail final,
    run_lines xs st = (head, middle) ->
    run_lines ys middle = (tail, final) ->
    run_lines (xs ++ ys)%list st = ((head ++ tail)%list, final).
Proof.
  intros xs ys st head middle tail final Hxs Hys.
  rewrite run_lines_app, Hxs, Hys. reflexivity.
Qed.

Lemma parse_lines_run :
  forall lines st bs st',
    run_lines lines st = (bs, st') ->
    parse_lines lines st = (bs ++ finish st')%list.
Proof.
  induction lines as [|l lines IH]; intros st bs st' Hrun.
  - cbn [run_lines] in Hrun. inversion Hrun. reflexivity.
  - cbn [run_lines] in Hrun.
    destruct (step l st) as [head st1] eqn:Hstep.
    destruct (run_lines lines st1) as [rest st2] eqn:Hrest.
    inversion Hrun; subst bs st'.
    rewrite (parse_lines_step _ _ _ _ _ Hstep), (IH _ _ _ Hrest).
    rewrite app_assoc. reflexivity.
Qed.

Lemma parse_lines_app_run :
  forall xs ys st,
    parse_lines (xs ++ ys)%list st =
      let '(bs, st') := run_lines xs st in
      (bs ++ parse_lines ys st')%list.
Proof.
  induction xs as [|x xs IH]; intros ys st.
  - cbn [run_lines]. reflexivity.
  - cbn [app parse_lines].
    destruct (step x st) as [head st1] eqn:Hstep.
    rewrite (IH ys st1).
    cbn [run_lines]. rewrite Hstep.
    destruct (run_lines xs st1) as [rest st2].
    rewrite app_assoc. reflexivity.
Qed.

(*
Uniformity of fenced divs
-------------------------

Same payoff as the quote's, and a shorter argument, because a div strips
no prefix and shifts no column: its contents are handed the line
unchanged.  What replaces the prefix machinery is the side condition, and
that turned out to be the interesting part.

The obvious statement of it -- "no content line is a closing fence" --
is *false*, because `div_close` strips leading whitespace before it
looks.  A `:::` indented under a list item closes the div through the
list; `- a` / `  :::` / `  b` parses one way at top level and another
inside a div (`div_indented_close_differs` below pins it).  So the
condition has to reach every line of the contents, nested ones included.

But it cannot be lexical either, because of the code-block exception:
inside an open fence a `:::` line is content, not a closer, so the
condition depends on the state each line is reached in.  That makes it a
run predicate of exactly the shape `run_safe` has -- which is worth
recording, since the container-uniformity proposal predicted a div would
need no such thing (.project/260809.container-uniformity.md).

`run_div_open` is that predicate: fold `step` over the contents and check
at each line that the div does not close there.  It is decidable and
computable, and `div_code_fence_uniform` below is a document it accepts
that a lexical condition would have thrown away. *)

Fixpoint run_div_open (len : nat) (lines : list string) (st : pstate) : bool :=
  match lines with
  | [] => true
  | l :: rest =>
      negb (negb (in_fence st) && div_close len l)
      && run_div_open len rest (snd (step l st))
  end.

(* Both hypotheses of `div_uniformity` as one boolean, so a renderer-side
   `cb_ok` can carry them. *)
Definition div_content_ok (lines : list string) : bool :=
  run_div_open 3 lines (PPara [])
  && negb (in_fence (snd (run_lines lines (PPara [])))).

(* Inside an open div, contents that never close it drive the inner state,
   and the fence that follows closes the div and is consumed. *)
Lemma parse_lines_div_cont :
  forall content tail done inner,
    run_div_open 3 content inner = true ->
    in_fence (snd (run_lines content inner)) = false ->
    parse_lines (content ++ div_fence :: tail)%list
                (PDiv 3 EmptyString done inner)
    = mk (Div (rev done ++ parse_lines content inner)%list)
      :: parse_lines tail (PPara []).
Proof.
  induction content as [|l content IH]; intros tail done inner Hopen Hfence.
  - cbn [run_lines snd] in Hfence. cbn [app].
    rewrite (parse_lines_step _ _ _ _ _
               (step_div_close div_fence 3 EmptyString done inner
                  Hfence div_close_canonical)).
    reflexivity.
  - cbn [run_div_open] in Hopen. apply andb_true_iff in Hopen as [Hl Hrest].
    apply negb_true_iff in Hl.
    destruct (step l inner) as [bs inner'] eqn:Es.
    cbn [snd] in Hrest.
    cbn [run_lines] in Hfence. rewrite Es in Hfence.
    destruct (run_lines content inner') as [more inner''] eqn:Er.
    cbn [snd] in Hfence.
    cbn [app].
    rewrite (parse_lines_step _ _ _ _ _
               (step_div_cont l 3 EmptyString done inner bs inner' Hl Es)).
    cbn [app].
    rewrite (IH tail (rev bs ++ done)%list inner' Hrest
               ltac:(rewrite Er; exact Hfence)).
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

(** Uniformity for fenced divs: a div's contents parse exactly as they
    would at top level, for any contents that leave the div open. *)
Theorem div_uniformity :
  forall content,
    div_content_ok content = true ->
    parse_lines (div_fence :: content ++ [div_fence])%list (PPara [])
    = [mk (Div (parse_lines content (PPara [])))].
Proof.
  intros content Hok. unfold div_content_ok in Hok.
  apply andb_true_iff in Hok as [Hopen Hf].
  apply negb_true_iff in Hf. rename Hf into Hfence.
  rewrite (parse_lines_step _ _ _ _ _
             (step_idle div_fence (KDiv 3 EmptyString)
                classify_canonical_div eq_refl)).
  cbn [open_kind fst snd app].
  rewrite (parse_lines_div_cont content [] [] (PPara []) Hopen Hfence).
  reflexivity.
Qed.

(* The same with a document after it, which is the form the roundtrip
   proof needs: the closing fence is consumed and the separator blank
   returns the parser to idle. *)
Theorem div_uniformity_tail :
  forall content tail,
    div_content_ok content = true ->
    parse_lines (div_fence :: content ++ div_fence :: EmptyString :: tail)%list
                (PPara [])
    = mk (Div (parse_lines content (PPara []))) :: parse_lines tail (PPara []).
Proof.
  intros content tail Hok. unfold div_content_ok in Hok.
  apply andb_true_iff in Hok as [Hopen Hf]. apply negb_true_iff in Hf.
  rewrite (parse_lines_step _ _ _ _ _
             (step_idle div_fence (KDiv 3 EmptyString)
                classify_canonical_div eq_refl)).
  cbn [open_kind fst snd app].
  rewrite (parse_lines_div_cont content (EmptyString :: tail) []
             (PPara []) Hopen Hf).
  cbn [rev app].
  rewrite (parse_lines_blank_nil EmptyString tail
             (classify_blank EmptyString eq_refl)).
  reflexivity.
Qed.

(* The boundary, pinned.  Deleting either of these should break. *)

(* Why the side condition cannot be "no *top-level* content line closes
   the div": here the closing line is a list-item continuation, and the
   div takes it anyway.  Both oracles agree with the left-hand side. *)
End WithTable.

Example div_indented_close_differs :
  let content := ["- a"; "  :::"; "  b"]%list in
  parse_lines (div_fence :: content ++ [div_fence])%list (PPara [])
  <> [mk (Div (parse_lines content (PPara [])))].
Proof. vm_compute. discriminate. Qed.

Example div_indented_close_rejected :
  run_div_open 3 ["- a"; "  :::"; "  b"]%list (PPara []) = false.
Proof. reflexivity. Qed.

(* Why the side condition cannot be lexical either: a `:::` line inside an
   open code fence is content, so this document *is* uniform, and a
   `forallb` over the content lines would have thrown it away. *)
Example div_code_fence_uniform :
  let content := ["```"; ":::"; "```"]%list in
  parse_lines (div_fence :: content ++ [div_fence])%list (PPara [])
  = [mk (Div (parse_lines content (PPara [])))].
Proof. reflexivity. Qed.

Example div_code_fence_accepted :
  run_div_open 3 ["```"; ":::"; "```"]%list (PPara []) = true.
Proof. reflexivity. Qed.

(* A fence still open at the end swallows the closer, which is what the
   `in_fence` hypothesis rules out. *)
Example div_unclosed_fence_differs :
  let content := ["```"]%list in
  parse_lines (div_fence :: content ++ [div_fence])%list (PPara [])
  <> [mk (Div (parse_lines content (PPara [])))].
Proof. vm_compute. discriminate. Qed.

(*
Prefix determinism
------------------

The spec's block-level promise: "blocks can be parsed line by line ...
the contribution a line makes to block-level structure never depends on
a future line."  `Line.v` gives each line its kind; these say the fold
over those kinds commits as it goes.

`parse_lines` is a fold, so the property is true by construction rather
than by argument, and the three statements below are one rewrite each
off `parse_lines_app_run`.  They are here because "true by construction"
is a claim about the definition that a reader should not have to
reconstruct, and because a future block parser -- a `BlockSpec` record
dispatched over a container stack, say -- must keep them.

Stated at the line level, which is where the parser is incremental.
Lifting to `parse_doc` would need `split_lines` to distribute over
concatenation, and it does so only when the prefix ends at a newline:
`split_lines "a" ++ split_lines "b"` is `["a"; "b"]` while
`split_lines "ab"` is `["ab"]`.  The line-level form is the honest one.

One caveat for later.  The plan (`.project/260802.plan.autonomous.md`,
Phase 2 item 3) scopes prefix determinism to block *tree shape*, because
djot's pipe-table rule turns a paragraph into a table header
retroactively.  We have no tables, so the statements below are over full
parse results, which is strictly stronger.  Adding tables falsifies them
as written; the shape-only weakening is the fallback, and it should be a
deliberate step, not a surprise.
*)

(** What a line prefix has already emitted.  A fold over the prefix, so
    "computable line by line" is definitional. *)
(* Back into the family: the determinism theorems below are about any
   admissible table, like the fold equations above them. *)
Section WithTableDet.
Context {T : dtable}.
Context {K : bconfig}.

Definition committed (xs : list string) (st : pstate) : blocks :=
  fst (run_lines xs st).

(** The parse of a prefix followed by anything factors through the
    prefix: its blocks come out first and unmodified, and the only thing
    the prefix passes forward is one `pstate`.  Nothing is revised once
    emitted -- the right-hand side appends to `committed xs st`, it does
    not rewrite it. *)
Theorem prefix_determinism :
  forall xs ys st,
    parse_lines (xs ++ ys)%list st
    = (committed xs st ++ parse_lines ys (snd (run_lines xs st)))%list.
Proof.
  intros xs ys st. unfold committed.
  rewrite parse_lines_app_run. destruct (run_lines xs st). reflexivity.
Qed.

(** No future-line dependence, in the contrapositive form: swap the
    continuation for any other and the blocks already committed are
    unchanged. *)
Theorem no_future_line_dependence :
  forall xs ys ys' st,
    firstn (List.length (committed xs st)) (parse_lines (xs ++ ys)%list st)
    = firstn (List.length (committed xs st)) (parse_lines (xs ++ ys')%list st).
Proof.
  intros xs ys ys' st.
  rewrite !prefix_determinism, !firstn_app, Nat.sub_diag, !firstn_O, !app_nil_r,
          !firstn_all.
  reflexivity.
Qed.

(** And the state is the whole of what a prefix carries forward: two
    prefixes that run to the same pair are interchangeable under every
    continuation.  This is the bound on lookback that makes the fold a
    state machine rather than a function of the whole input. *)
Theorem prefix_state_suffices :
  forall xs xs' ys st,
    run_lines xs st = run_lines xs' st ->
    parse_lines (xs ++ ys)%list st = parse_lines (xs' ++ ys)%list st.
Proof.
  intros xs xs' ys st H.
  rewrite !prefix_determinism. unfold committed. rewrite H. reflexivity.
Qed.

Lemma app_cons_app :
  forall {A : Type} (xs : list A) x ys tail,
    ((xs ++ (x :: ys)) ++ tail)%list =
    (xs ++ (x :: (ys ++ tail)))%list.
Proof.
  intros A xs x ys tail. induction xs as [|a xs IH];
    [reflexivity|cbn; rewrite IH; reflexivity].
Qed.

End WithTableDet.
