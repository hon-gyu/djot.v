(* ai-disclosure: ai-generated *)

(** * Block uniformity and prefix determinism

   The fold's equation lemmas, and uniformity for block quotes and
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

Local Lemma parse_lines_at_zero :
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

Local Lemma parse_lines_shift :
  forall k lines st,
    parse_lines_at k lines (pad_state k st) = parse_lines lines st.
Proof.
  intros k lines st.
  rewrite <- (parse_lines_at_zero lines st).
  rewrite <- (parse_lines_at_shift k 0 lines st), Nat.add_0_r.
  reflexivity.
Qed.

(* A canonical quote prefix eats exactly two columns. *)
Local Lemma consumed_quote_prefix :
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

(** When the incoming marker has no style in common with the open list,
    the old list is emitted before the new item's list is opened.  The
    remaining lines therefore parse from that new list state, so no
    future continuation can join the two items into one list. *)
Lemma narrow_disjoint : forall old new,
  (forall p s, In p old -> In s new -> fst p <> s) ->
  narrow old new = [].
Proof.
  intros old new Hdisjoint. unfold narrow.
  induction old as [|p old IH]; [reflexivity|].
  cbn [filter].
  destruct (existsb (lstyle_eqb (fst p)) new) eqn:E.
  - apply existsb_exists in E as [s [Hin Heq]].
    apply lstyle_eqb_eq in Heq.
    exfalso. eapply (Hdisjoint p s); [left; reflexivity|exact Hin|exact Heq].
  - apply IH. intros q s Hq Hs. apply (Hdisjoint q s); [right; exact Hq|exact Hs].
Qed.

Theorem list_different_types_split :
  forall l sty core chk content ls done inner bs inner' tail,
    classify l = KList sty core chk content ->
    (forall p s, In p (ls_styles ls) ->
       In s (configured_list_styles sty chk) -> fst p <> s) ->
    list_takes ls 0 l inner = false ->
    step (configured_list_rest chk content) (PPara []) = (bs, inner') ->
    parse_lines (l :: tail) (PList ls done inner) =
      (finish (PList ls done inner) ++
       parse_lines tail
         (PList (list_opened l (indent_of l)
                   (with_starts (configured_list_styles sty chk) core)
                   (configured_list_check chk)) (rev bs)
           (pad_state (consumed l (configured_list_rest chk content)) inner')))%list.
Proof.
  intros l sty core chk content ls done inner bs inner' tail
    Hkind Hstyle Hcolumn Hcontent.
  apply parse_lines_step.
  eapply step_list_diffstyle; eauto using narrow_disjoint.
Qed.

Lemma narrow_shared : forall old new p s,
  In p old -> In s new -> fst p = s -> narrow old new <> [].
Proof.
  intros old new p s Hp Hs Heq Hnil.
  assert (Hin : In p (narrow old new)).
  { unfold narrow. apply filter_In. split; [exact Hp|].
    apply existsb_exists. exists s. split; [exact Hs|].
    rewrite Heq. apply lstyle_eqb_refl. }
  rewrite Hnil in Hin. destruct Hin.
Qed.

(** The other half of "a sequence of list items of the same type": a
    marker at the list's column that shares a style with the open list
    starts that list's next item.  Nothing is emitted.  The item so far
    joins the list's finished items, and the list keeps the styles the
    two have in common. *)
Theorem list_same_type_joins :
  forall l sty core chk content ls done inner bs inner' tail p s,
    classify l = KList sty core chk content ->
    In p (ls_styles ls) -> In s (configured_list_styles sty chk) ->
    fst p = s ->
    list_takes ls 0 l inner = false ->
    step (configured_list_rest chk content) (PPara []) = (bs, inner') ->
    exists ls',
      parse_lines (l :: tail) (PList ls done inner)
      = parse_lines tail
          (PList ls' (rev bs)
             (pad_state (consumed l (configured_list_rest chk content)) inner'))
      /\ ls_items ls' = ((rev done ++ finish inner) :: ls_items ls)%list
      /\ ls_styles ls'
         = narrow (ls_styles ls) (configured_list_styles sty chk).
Proof.
  intros l sty core chk content ls done inner bs inner' tail p s
    Hkind Hp Hs Heq Hcolumn Hcontent.
  pose proof (narrow_shared _ _ p s Hp Hs Heq) as Hne.
  destruct (narrow (ls_styles ls) (configured_list_styles sty chk))
    as [|s0 ss] eqn:Hn; [contradiction Hne; reflexivity|].
  eexists. split; [|split].
  - rewrite (parse_lines_step _ _ _ _ _
               (step_list_sibling _ _ _ _ _ _ _ _ _ _ _ _
                  Hkind Hn Hcolumn Hcontent)).
    reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma parse_lines_nil_cons :
  forall c cur',
    parse_lines [] (PPara (c :: cur')) =
    [mk (Para (para_inlines (line_texts (rev (c :: cur')))))].
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
  mk (Para (para_inlines (line_texts (rev (c :: cur')))))
  :: parse_lines rest (PPara []).
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
  parse_lines rest
    (PFence f (indent_of l) (open_extent l (indent_of l))
       (line_span_from l (indent_of l)) []).
Proof.
  intros l rest f H.
  rewrite (parse_lines_step _ _ _ _ _ (step_fence_open _ _ H)). reflexivity.
Qed.

(* A text line opens a paragraph or extends one.  The `bcuts` hypothesis
   is about the second case only -- a line that *ends* a paragraph is
   still text when there is none open, which is how `===` opens a
   paragraph of its own after a blank. *)
(* `keyless` is about the first case only, for the same reason `bcuts`
   is about the second: a line that *continues* a paragraph is never
   tested for a split (keyed-blocks 3.5), so an open paragraph swallows
   a colon that would have keyed a fresh line. *)
Local Lemma parse_lines_text :
  forall l rest cur, classify l = KText -> bcuts l = false ->
  keyless l = true ->
  parse_lines (l :: rest) (PPara cur) =
  parse_lines rest (PPara (remember_line (drop_leading_ws l) :: cur)).
Proof.
  intros l rest cur H Hc Hk. destruct cur as [|c cur'].
  - rewrite (parse_lines_step _ _ _ _ _
               (eq_trans (step_idle _ _ H eq_refl) (open_text_keyless _ Hk))).
    reflexivity.
  - rewrite (parse_lines_step _ _ _ _ _
               (step_para_cont _ _ _ (fun E => ltac:(rewrite H in E; discriminate))
                  Hc)).
    reflexivity.
Qed.

(* Any nonblank line continues an open paragraph. *)
Local Lemma parse_lines_cont :
  forall l rest c cur',
    classify l <> KBlank -> bcuts l = false ->
  parse_lines (l :: rest) (PPara (c :: cur')) =
  parse_lines rest
    (PPara (remember_line (drop_leading_ws l) :: c :: cur')).
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
  parse_lines (l :: rest) (PPara [])
  = parse_lines rest (PRef (open_extent l (indent_of l)) (indent_of l) lbl v).
Proof.
  intros l rest lbl v H.
  rewrite (parse_lines_step _ _ _ _ _ (step_ref_open _ _ _ H)). reflexivity.
Qed.

(* A blank line ends the definition and emits it: `ref_cont` has no run to
   take from a blank line, whatever column the opener sits at. *)
Lemma parse_lines_ref_blank :
  forall l rest range ind lbl v, classify l = KBlank ->
  parse_lines (l :: rest) (PRef range ind lbl v) =
  ref_block lbl v :: parse_lines rest (PPara []).
Proof.
  intros l rest range ind lbl v H.
  rewrite (parse_lines_step _ _ _ _ _ (step_ref_blank _ _ _ _ _ H)). reflexivity.
Qed.

(* A line that extends an open definition's URL: indented past the
   opener's column `ind`, and one run with no whitespace in it or after
   it. *)
Definition ref_chunk (ind : nat) (l : string) : bool :=
  (Nat.ltb ind (indent_of l) && nonempty_str (drop_leading_ws l)
   && no_ws (drop_leading_ws l))%bool.

Local Lemma concat_empty_cons : forall x xs,
  String.concat "" (x :: xs) = x ++ String.concat "" xs.
Proof.
  intros x [|y ys]; cbn [String.concat]; [rewrite append_empty_r|]; reflexivity.
Qed.

Local Lemma parse_lines_ref_chunks : forall chunks rest range ind lbl v,
  forallb (ref_chunk ind) chunks = true ->
  parse_lines (chunks ++ rest)%list (PRef range ind lbl v)
  = parse_lines rest
      (PRef (Nat.iter (List.length chunks) touch_extent range) ind lbl
         (v ++ String.concat "" (map drop_leading_ws chunks))).
Proof.
  induction chunks as [|c chunks IH]; intros rest range ind lbl v H.
  - cbn [app map String.concat List.length Nat.iter nat_rect].
    rewrite append_empty_r. reflexivity.
  - cbn [forallb] in H. apply andb_true_iff in H as [Hc H].
    unfold ref_chunk in Hc. apply andb_true_iff in Hc as [Hc Hw].
    apply andb_true_iff in Hc as [Hi Hne].
    cbn [app map parse_lines]. unfold step at 1. cbn [step_fuel Nat.add].
    rewrite Hi. unfold ref_cont. rewrite Hne, Hw. cbn [andb app].
    rewrite (IH rest _ ind lbl _ H), concat_empty_cons, append_assoc.
    cbn [List.length]. rewrite Nat.iter_succ_r. reflexivity.
Qed.

(** RD2: the lines after a definition's opener that are indented past it
    and hold one whitespace-free run are chunks of its URL, joined with
    the whitespace around them dropped.  The first line that is not one
    ends the definition and is parsed as if none were open: a chunk with
    whitespace inside or after it is such a line. *)
Theorem ref_url_chunks : forall l lbl v chunks next rest,
  classify l = KRef lbl v ->
  forallb (ref_chunk (indent_of l)) chunks = true ->
  ref_chunk (indent_of l) next = false ->
  parse_lines (l :: chunks ++ next :: rest)%list (PPara [])
  = ref_block lbl (v ++ String.concat "" (map drop_leading_ws chunks))
    :: parse_lines (next :: rest) (PPara []).
Proof.
  intros l lbl v chunks next rest Hl Hc Hn.
  rewrite (parse_lines_ref_open l _ lbl v Hl), (parse_lines_ref_chunks _ _ _ _ _ _ Hc).
  cbn [parse_lines]. unfold step at 1. cbn [step_fuel Nat.add].
  replace (if Nat.ltb (indent_of l) (indent_of next) then ref_cont next else None)
    with (@None string).
  2:{ unfold ref_chunk in Hn. unfold ref_cont.
      destruct (Nat.ltb (indent_of l) (indent_of next)); [|reflexivity].
      cbn [andb] in Hn. rewrite Hn. reflexivity. }
  rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
  destruct (step next (PPara [])) as [bs st']. reflexivity.
Qed.

(** RD2, when the document ends in the definition. *)
Theorem ref_url_chunks_end : forall l lbl v chunks,
  classify l = KRef lbl v ->
  forallb (ref_chunk (indent_of l)) chunks = true ->
  parse_lines (l :: chunks) (PPara [])
  = [ref_block lbl (v ++ String.concat "" (map drop_leading_ws chunks))].
Proof.
  intros l lbl v chunks Hl Hc.
  pose proof (parse_lines_ref_chunks chunks [] (open_extent l (indent_of l))
                (indent_of l) lbl v Hc) as E.
  rewrite app_nil_r in E.
  rewrite (parse_lines_ref_open l _ lbl v Hl), E. reflexivity.
Qed.

(*
Table equations
---------------
*)

Lemma parse_lines_row_open :
  forall l rest r, btables = true -> classify l = KRow r ->
  parse_lines (l :: rest) (PPara [])
  = parse_lines rest (PTable (open_extent l (indent_of l)) [r] (TOpen [])).
Proof.
  intros l rest r Htables H.
  rewrite (parse_lines_step _ _ _ _ _ (step_row_open _ _ Htables H)).
  reflexivity.
Qed.

Lemma parse_lines_table_row :
  forall l rest range rows parts r,
    caption_open l = None -> is_blank l = false -> classify l = KRow r ->
    parse_lines (l :: rest) (PTable range rows (TOpen parts))
    = parse_lines rest (PTable (touch_extent range) (r :: rows) (TOpen parts)).
Proof.
  intros l rest range rows parts r Hc Hb H.
  rewrite (parse_lines_step _ _ _ _ _ (step_table_row _ _ _ _ _ Hc Hb H)).
  reflexivity.
Qed.

Lemma parse_lines_table_blank :
  forall l rest range rows parts, is_blank l = true ->
  parse_lines (l :: rest) (PTable range rows (TOpen parts))
  = parse_lines rest (PTable range rows (TAfterBlank parts)).
Proof.
  intros l rest range rows parts H.
  rewrite (parse_lines_step _ _ _ _ _ (step_table_blank _ _ _ _ H)).
  reflexivity.
Qed.

(* The line is reprocessed at the enclosing level, so the whole rule is
   "emit the table and read this line again from idle". *)
Lemma parse_lines_table_close :
  forall l rest range rows parts, caption_open l = None -> is_blank l = false ->
  parse_lines (l :: rest) (PTable range rows (TAfterBlank parts))
  = table_block (rev rows) (TAfterBlank parts)
      :: parse_lines (l :: rest) (PPara []).
Proof.
  intros l rest range rows parts Hc Hb.
  destruct (step l (PPara [])) as [bs st'] eqn:Hs.
  rewrite (parse_lines_step _ _ _ _ _ (step_table_close _ _ _ _ _ _ Hc Hb Hs)).
  rewrite (parse_lines_step _ _ _ _ _ Hs). reflexivity.
Qed.

Lemma parse_lines_table_eof :
  forall range rows cap,
    parse_lines [] (PTable range rows cap) = [table_block (rev rows) cap].
Proof. reflexivity. Qed.

(*
Fence equations
---------------
*)

Local Lemma parse_lines_fence_eof :
  forall f ind range opener acc,
    parse_lines [] (PFence f ind range opener acc)
    = [fence_block f (line_texts (rev (drop_blank_lines acc)))].
Proof. reflexivity. Qed.

Lemma parse_lines_fence_close :
  forall l rest f ind range opener acc, fence_close f l = true ->
  parse_lines (l :: rest) (PFence f ind range opener acc) =
  fence_block f (line_texts (rev acc)) :: parse_lines rest (PPara []).
Proof.
  intros l rest f ind range opener acc H.
  rewrite (parse_lines_step _ _ _ _ _ (step_fence_close _ _ _ _ _ _ H)). reflexivity.
Qed.

Local Lemma parse_lines_fence_content :
  forall l rest f ind range opener acc, fence_close f l = false ->
  parse_lines (l :: rest) (PFence f ind range opener acc) =
  parse_lines rest
    (PFence f ind (touch_extent range) opener
       (remember_line (drop_ws_upto ind l) :: acc)).
Proof.
  intros l rest f ind range opener acc H.
  rewrite (parse_lines_step _ _ _ _ _ (step_fence_content _ _ _ _ _ _ H)). reflexivity.
Qed.

(*
Seed lemmas: feeding runs of lines
----------------------------------
*)

(* A run of nonblank lines accumulates (reversed, leading whitespace
   stripped) onto an open paragraph. *)
Local Lemma parse_lines_cont_seed :
  forall ls tail c cur',
    forallb nonblank ls = true ->
    forallb (fun l => negb (bcuts l)) ls = true ->
    parse_lines (ls ++ tail)%list (PPara (c :: cur')) =
    parse_lines tail
      (PPara (remember_lines (rev (map drop_leading_ws ls))
                ++ (c :: cur'))%list).
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
    simpl rev. unfold remember_lines. rewrite map_app. cbn [map].
    rewrite <- app_assoc. reflexivity.
Qed.

(* Opening a paragraph with a text line, then feeding its remaining lines. *)
Lemma parse_lines_para_seed :
  forall a ls tail,
    classify a = KText ->
    bcuts a = false ->
    keyless a = true ->
    forallb nonblank ls = true ->
    forallb (fun l => negb (bcuts l)) ls = true ->
    parse_lines ((a :: ls) ++ tail)%list (PPara []) =
    parse_lines tail
      (PPara (remember_lines (rev (map drop_leading_ws (a :: ls))))).
Proof.
  intros a ls tail Ha Hcut Hkey Hls His.
  change ((a :: ls) ++ tail)%list with (a :: (ls ++ tail))%list.
  rewrite parse_lines_text by (exact Ha || exact Hcut || exact Hkey).
  rewrite parse_lines_cont_seed by (exact Hls || exact His).
  f_equal. unfold remember_lines. cbn [map rev]. rewrite map_app. reflexivity.
Qed.

(* The paragraph run, closed.  A text line and any run of nonblank lines
   after it are one paragraph and nothing else: the lines' shapes are
   never consulted past `bcuts`, so no line in the run can open a block.
   This is what says a paragraph's block structure is decided by its
   blank lines alone. *)
Lemma parse_lines_para_run :
  forall a ls,
    classify a = KText ->
    bcuts a = false ->
    keyless a = true ->
    forallb nonblank ls = true ->
    forallb (fun l => negb (bcuts l)) ls = true ->
    parse_lines (a :: ls) (PPara []) =
    [mk (Para (para_inlines (map drop_leading_ws (a :: ls))))].
Proof.
  intros a ls Ha Hcut Hkey Hls His.
  rewrite <- (app_nil_r (a :: ls)).
  rewrite (parse_lines_para_seed a ls [] Ha Hcut Hkey Hls His).
  rewrite app_nil_r. cbn [parse_lines].
  destruct (rev (map drop_leading_ws (a :: ls))) as [|c cur] eqn:E.
  - apply (f_equal (@rev _)) in E. rewrite rev_involutive in E.
    cbn in E. discriminate.
  - unfold remember_lines. cbn [finish]; nopos; sem_para. cbn [map].
    rewrite line_texts_rev.
    cbn [line_texts remember_line]. fold (remember_lines cur).
    unfold line_texts at 1. cbn [map snd remember_line].
    fold (line_texts (remember_lines cur)). rewrite line_texts_remember_lines.
    rewrite <- E, rev_involutive. reflexivity.
Qed.

(* The same run with a document after it.  The blank line is what ends
   the paragraph, and the parser is idle again on the other side of it,
   so the run's lines reach nothing that follows. *)
Lemma parse_lines_para_run_blank :
  forall a ls b rest,
    classify a = KText ->
    bcuts a = false ->
    keyless a = true ->
    forallb nonblank ls = true ->
    forallb (fun l => negb (bcuts l)) ls = true ->
    is_blank b = true ->
    parse_lines ((a :: ls) ++ b :: rest)%list (PPara []) =
    mk (Para (para_inlines (map drop_leading_ws (a :: ls))))
    :: parse_lines rest (PPara []).
Proof.
  intros a ls b rest Ha Hcut Hkey Hls His Hb.
  rewrite (parse_lines_para_seed a ls (b :: rest) Ha Hcut Hkey Hls His).
  destruct (rev (map drop_leading_ws (a :: ls))) as [|c cur] eqn:E.
  - apply (f_equal (@rev _)) in E. rewrite rev_involutive in E.
    cbn in E. discriminate.
  - unfold remember_lines. cbn [map].
    rewrite (parse_lines_step _ _ _ _ _
               (step_para_flush _ _ _ (classify_blank _ Hb))).
    sem_para. rewrite line_texts_rev. cbn [line_texts remember_line].
    fold (remember_lines cur). unfold line_texts at 1.
    cbn [map snd remember_line]. fold (line_texts (remember_lines cur)).
    rewrite line_texts_remember_lines.
    rewrite <- E, rev_involutive. reflexivity.
Qed.

(* A run of non-closing lines accumulates (reversed) into an open fence.
   The range is one the last line has already reached, which is what an
   opener leaves, so the run does not move it. *)
Lemma parse_lines_fence_seed :
  forall ls tail f ind range opener acc,
    touch_extent range = range ->
    forallb (fun l => negb (fence_close f l)) ls = true ->
    parse_lines (ls ++ tail)%list (PFence f ind range opener acc) =
    parse_lines tail
      (PFence f ind range opener
        (remember_lines (rev (map (drop_ws_upto ind) ls)) ++ acc)%list).
Proof.
  induction ls as [|l ls IH]; intros tail f ind range opener acc Ht H.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hl Hls].
    apply negb_true_iff in Hl.
    change ((l :: ls) ++ tail)%list with (l :: (ls ++ tail))%list.
    rewrite parse_lines_fence_content by exact Hl.
    rewrite Ht, IH by assumption.
    simpl rev. unfold remember_lines. rewrite map_app. cbn [map].
    rewrite <- app_assoc. reflexivity.
Qed.

(*
Code blocks
-----------
*)

Local Lemma parse_lines_fence_run : forall l f content rest,
  classify l = KFence f ->
  forallb (fun x => negb (fence_close f x)) content = true ->
  parse_lines (l :: content ++ rest)%list (PPara []) =
  parse_lines rest
    (PFence f (indent_of l) (open_extent l (indent_of l))
       (line_span_from l (indent_of l))
       (remember_lines (rev (map (drop_ws_upto (indent_of l)) content)))).
Proof.
  intros l f content rest Hl Hc.
  rewrite (parse_lines_fence_open _ _ _ Hl).
  rewrite parse_lines_fence_seed by (reflexivity || exact Hc).
  rewrite app_nil_r. reflexivity.
Qed.

(** CB2: a code block runs from its opener to the first line that closes
    it, and holds the lines between, each less the opener's indentation.
    `fence_close_backticks` says which lines close a backtick fence. *)
Theorem fenced_code_closed : forall l f content c rest,
  classify l = KFence f ->
  forallb (fun x => negb (fence_close f x)) content = true ->
  fence_close f c = true ->
  parse_lines (l :: content ++ c :: rest)%list (PPara []) =
  fence_block f (map (drop_ws_upto (indent_of l)) content)
  :: parse_lines rest (PPara []).
Proof.
  intros l f content c rest Hl Hc Hclose.
  rewrite (parse_lines_fence_run l f content (c :: rest) Hl Hc).
  rewrite parse_lines_fence_close by exact Hclose.
  rewrite line_texts_rev_remember_lines, rev_involutive. reflexivity.
Qed.

(* Blank lines added after the newest line of an accumulator are what
   `drop_blank_lines` takes off again. *)
Local Lemma drop_blank_lines_after : forall ws acc,
  forallb is_blank ws = true ->
  (acc = [] \/ exists x rest, acc = x :: rest /\ is_blank (snd x) = false) ->
  drop_blank_lines (remember_lines ws ++ acc)%list = acc.
Proof.
  induction ws as [|w ws IH]; intros acc Hws Hacc.
  - destruct Hacc as [->|[x [rest [-> Hx]]]];
      cbn [remember_lines map app drop_blank_lines];
      [reflexivity|rewrite Hx; reflexivity].
  - cbn [forallb] in Hws. apply andb_true_iff in Hws as [Hw Hws].
    cbn [remember_lines map app drop_blank_lines remember_line snd]. rewrite Hw.
    exact (IH acc Hws Hacc).
Qed.

(** CB2, "or the end of the document".  The blank lines the block ends
    with are not part of it. *)
Theorem fenced_code_unclosed : forall l f content ws,
  classify l = KFence f ->
  forallb (fun x => negb (fence_close f x)) (content ++ ws) = true ->
  (content = [] \/ is_blank (last content EmptyString) = false) ->
  forallb is_blank ws = true ->
  parse_lines (l :: content ++ ws) (PPara []) =
  [fence_block f (map (drop_ws_upto (indent_of l)) content)].
Proof.
  intros l f content ws Hl Hc Hlast Hws.
  rewrite <- (app_nil_r (content ++ ws)).
  rewrite (parse_lines_fence_run l f (content ++ ws) [] Hl Hc).
  cbn [parse_lines finish].
  assert (Hd : drop_blank_lines
                 (remember_lines (rev (map (drop_ws_upto (indent_of l)) (content ++ ws))))
               = remember_lines (rev (map (drop_ws_upto (indent_of l)) content))).
  { rewrite map_app, rev_app_distr. unfold remember_lines at 1. rewrite map_app.
    fold (remember_lines (rev (map (drop_ws_upto (indent_of l)) ws))).
    fold (remember_lines (rev (map (drop_ws_upto (indent_of l)) content))).
    apply drop_blank_lines_after.
    - rewrite forallb_forall in Hws |- *. intros x Hx.
      apply in_rev, in_map_iff in Hx as [y [<- Hy]].
      rewrite is_blank_drop_ws_upto. exact (Hws y Hy).
    - destruct Hlast as [->|Hlast]; [left; reflexivity|right].
      destruct content as [|c0 cs]; [discriminate Hlast|].
      destruct (@exists_last _ (c0 :: cs) ltac:(discriminate)) as [init [z Ez]].
      rewrite Ez in Hlast |- *. rewrite last_last in Hlast.
      rewrite map_app, rev_app_distr. cbn [map rev app].
      exists (remember_line (drop_ws_upto (indent_of l) z)).
      eexists. split; [reflexivity|].
      cbn [remember_line snd]. rewrite is_blank_drop_ws_upto. exact Hlast. }
  rewrite Hd, line_texts_rev_remember_lines, rev_involutive. reflexivity.
Qed.

(** RB1: with `=FORMAT` for the info string, the same block is raw
    content in that format. *)
Theorem raw_block_closed : forall l ch n fmt content c rest,
  braw_blocks = true ->
  classify l = KFence (Fence ch n (String "="%char fmt)) ->
  forallb (fun x => negb (fence_close (Fence ch n (String "="%char fmt)) x))
    content = true ->
  fence_close (Fence ch n (String "="%char fmt)) c = true ->
  parse_lines (l :: content ++ c :: rest)%list (PPara []) =
  mk (RawBlock fmt (join_nl (map (drop_ws_upto (indent_of l)) content)))
  :: parse_lines rest (PPara []).
Proof.
  intros l ch n fmt content c rest Hraw Hl Hc Hclose.
  rewrite (fenced_code_closed _ _ _ _ _ Hl Hc Hclose).
  unfold fence_block. cbn [f_info]. rewrite Hraw. reflexivity.
Qed.

(*
Heading equations
-----------------
*)

Local Lemma step_heading_cont :
  forall l lvl rng txt cur,
    bheading_continues = true ->
    classify l = KHeading lvl txt ->
    step l (PHeading lvl rng cur)
    = ([], PHeading lvl (touch_extent rng) (push_text txt cur)).
Proof.
  intros l lvl rng txt cur Hcontinues H. unfold step. cbn [step_fuel open_line].
  rewrite Hcontinues, H.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma step_heading_close :
  forall l lvl rng cur,
    classify l = KBlank ->
    step l (PHeading lvl rng cur) = ([heading_block lvl cur], PPara []).
Proof.
  intros l lvl rng cur H. unfold step. cbn [step_fuel open_line].
  destruct bheading_continues; rewrite H; reflexivity.
Qed.

Lemma parse_lines_heading_open :
  forall l rest lvl txt,
    classify l = KHeading lvl txt ->
    parse_lines (l :: rest) (PPara []) =
    parse_lines rest
      (PHeading lvl (open_extent l (indent_of l)) (push_text txt [])).
Proof.
  intros l rest lvl txt H.
  rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
Qed.

Local Lemma parse_lines_heading_cont :
  forall l rest lvl rng txt cur,
    bheading_continues = true ->
    classify l = KHeading lvl txt ->
    parse_lines (l :: rest) (PHeading lvl rng cur) =
    parse_lines rest (PHeading lvl (touch_extent rng) (push_text txt cur)).
Proof.
  intros l rest lvl rng txt cur Hcontinues H.
  rewrite (parse_lines_step _ _ _ _ _
             (step_heading_cont _ _ _ _ _ Hcontinues H)).
  reflexivity.
Qed.

Lemma parse_lines_heading_close :
  forall l rest lvl rng cur,
    classify l = KBlank ->
    parse_lines (l :: rest) (PHeading lvl rng cur) =
    heading_block lvl cur :: parse_lines rest (PPara []).
Proof.
  intros l rest lvl rng cur H.
  rewrite (parse_lines_step _ _ _ _ _ (step_heading_close _ _ _ _ H)).
  reflexivity.
Qed.

(* Ordinary text lines remain in the open heading when continuation is on.
   A line that classifies differently is deliberately outside this claim:
   lists, quotes and other block openers can end a heading. *)
Lemma parse_lines_heading_text :
  forall l rest lvl rng cur,
    bheading_continues = true ->
    classify l = KText ->
    parse_lines (l :: rest) (PHeading lvl rng cur) =
    parse_lines rest
      (PHeading lvl (touch_extent rng)
        (remember_line (drop_leading_ws l) :: cur)).
Proof.
  intros l rest lvl rng cur Hcontinues H.
  assert (Hs : step l (PHeading lvl rng cur) =
    ([], PHeading lvl (touch_extent rng)
      (remember_line (drop_leading_ws l) :: cur))).
  { unfold step. cbn [step_fuel open_line].
    rewrite H, Hcontinues. reflexivity. }
  rewrite (parse_lines_step _ _ _ _ _ Hs). reflexivity.
Qed.

Lemma parse_lines_heading_text_seed :
  forall lvl ls tail rng cur,
    bheading_continues = true ->
    touch_extent rng = rng ->
    forallb (fun l => match classify l with KText => true | _ => false end) ls = true ->
    parse_lines (ls ++ tail)%list (PHeading lvl rng cur) =
    parse_lines tail
      (PHeading lvl rng
        (remember_lines (rev (map drop_leading_ws ls)) ++ cur)%list).
Proof.
  intros lvl ls. induction ls as [|l ls IH];
    intros tail rng cur Hcontinues Hrng H.
  - reflexivity.
  - cbn [forallb] in H. apply andb_true_iff in H as [Hl Hls].
    destruct (classify l) eqn:Hclass; try discriminate.
    cbn [app]. rewrite (parse_lines_heading_text _ _ _ _ _ Hcontinues Hclass), Hrng.
    rewrite IH by assumption.
    cbn [rev map]. unfold remember_lines. rewrite map_app. cbn [map].
    rewrite <- app_assoc. reflexivity.
Qed.

Theorem heading_text_wrap_then_rest :
  forall lvl ls b rest rng cur,
    bheading_continues = true ->
    touch_extent rng = rng ->
    forallb (fun l => match classify l with KText => true | _ => false end) ls = true ->
    classify b = KBlank ->
    parse_lines (ls ++ b :: rest)%list (PHeading lvl rng cur) =
    heading_block lvl
      (remember_lines (rev (map drop_leading_ws ls)) ++ cur)%list
      :: parse_lines rest (PPara []).
Proof.
  intros lvl ls b rest rng cur Hcontinues Hrng Hls Hb.
  rewrite parse_lines_heading_text_seed by assumption.
  apply parse_lines_heading_close. exact Hb.
Qed.

(* A run of canonically-rendered heading lines accumulates (reversed,
   leading whitespace stripped) onto the open heading, exactly as
   paragraph lines do. *)
Local Lemma parse_lines_heading_seed :
  forall lvl ls tail rng cur,
    bheading_continues = true ->
    touch_extent rng = rng ->
    1 <= lvl ->
    forallb nonblank ls = true ->
    parse_lines (map (heading_line lvl) ls ++ tail)%list
                (PHeading lvl rng cur) =
    parse_lines tail
      (PHeading lvl rng
        (remember_lines (rev (map drop_leading_ws ls)) ++ cur)%list).
Proof.
  intros lvl ls. induction ls as [|a ls IH];
    intros tail rng cur Hcontinues Hrng Hlvl H.
  - reflexivity.
  - cbn [forallb] in H. apply andb_true_iff in H as [Ha Hls].
    unfold nonblank in Ha. apply negb_true_iff in Ha.
    cbn [map app].
    rewrite (parse_lines_heading_cont _ _ _ _ a _ Hcontinues
               (classify_canonical_heading lvl a Hlvl)), Hrng.
    unfold push_text. rewrite Ha.
    rewrite IH by assumption.
    cbn [rev map]. unfold remember_lines. rewrite map_app. cbn [map].
    rewrite <- app_assoc. reflexivity.
Qed.

Theorem heading_marker_wrap_then_rest :
  forall lvl ls b rest rng cur,
    bheading_continues = true ->
    touch_extent rng = rng ->
    1 <= lvl ->
    forallb nonblank ls = true ->
    classify b = KBlank ->
    parse_lines (map (heading_line lvl) ls ++ b :: rest)%list
      (PHeading lvl rng cur) =
    heading_block lvl
      (remember_lines (rev (map drop_leading_ws ls)) ++ cur)%list
      :: parse_lines rest (PPara []).
Proof.
  intros lvl ls b rest rng cur Hcontinues Hrng Hlvl Hls Hb.
  rewrite parse_lines_heading_seed by assumption.
  apply parse_lines_heading_close. exact Hb.
Qed.

(*
How a heading ends
------------------
*)

(** Whether an open heading of level `lvl` takes the line `l`: a text
    line, or a heading line of the same level. *)
Definition heading_keeps (lvl : nat) (l : string) : bool :=
  bheading_continues
  && match classify l with
     | KText => true
     | KHeading lvl' _ => Nat.eqb lvl' lvl
     | _ => false
     end.

(** What a kept line adds to the heading: its text, without the hashes. *)
Definition heading_line_text (l : string) : string :=
  match classify l with KHeading _ txt => txt | _ => l end.

Definition heading_lines (ls : list string) (cur : list stored_line)
  : list stored_line :=
  fold_left (fun cur l => push_text (heading_line_text l) cur) ls cur.

Local Lemma step_heading_keeps :
  forall l lvl rng cur,
    heading_keeps lvl l = true ->
    step l (PHeading lvl rng cur)
    = ([], PHeading lvl (touch_extent rng)
             (push_text (heading_line_text l) cur)).
Proof.
  intros l lvl rng cur H. unfold heading_keeps in H.
  apply andb_true_iff in H as [Hc H].
  unfold heading_line_text, step. cbn [step_fuel].
  destruct (classify l) eqn:E; try discriminate H; rewrite Hc.
  - rewrite H. reflexivity.
  - unfold push_text. destruct (is_blank l) eqn:Eb; [|reflexivity].
    rewrite (classify_blank l Eb) in E. discriminate E.
Qed.

Local Lemma step_heading_ends :
  forall l lvl rng cur,
    heading_keeps lvl l = false ->
    step l (PHeading lvl rng cur)
    = (heading_block lvl cur :: fst (step l (PPara [])), snd (step l (PPara []))).
Proof.
  intros l lvl rng cur H. unfold heading_keeps in H.
  unfold step. cbn [step_fuel pstate_depth].
  destruct (classify l) eqn:E; cbn [open_line open_kind close_reopen].
  all: try match goal with
           | |- close_reopen _ ?r = _ => destruct r as [bs st']
           end.
  all: cbn [close_reopen finish app fst snd]; try reflexivity.
  - destruct bheading_continues; [|reflexivity].
    cbn [andb] in H. rewrite H. reflexivity.
  - destruct bheading_continues; [discriminate H|].
    destruct (open_text (drop_leading_ws l)) as [bs st']. reflexivity.
Qed.

(** The syntax reference: "The heading text may spill over onto following
    lines, which may also be preceded by the same number of `#`
    characters (but these can also be left off).  The heading ends when a
    blank line (or the end of the document or enclosing container) is
    encountered."

    An open heading takes every line it keeps, marked or not in any mix,
    and ends at the first line `b` it does not keep, which is then read
    as if the heading had not been there.  A blank is such a line, and so
    is one that opens another block: a heading line of another level, a
    list marker, a quote, a fence.  The reference names only the blank. *)
Theorem heading_ends_at :
  forall lvl ls b rest rng cur,
    forallb (heading_keeps lvl) ls = true ->
    heading_keeps lvl b = false ->
    parse_lines (ls ++ b :: rest)%list (PHeading lvl rng cur)
    = heading_block lvl (heading_lines ls cur)
        :: parse_lines (b :: rest) (PPara []).
Proof.
  intros lvl ls. induction ls as [|l ls IH]; intros b rest rng cur Hls Hb.
  - cbn [app heading_lines fold_left].
    rewrite (parse_lines_step _ _ _ _ _ (step_heading_ends b lvl rng cur Hb)).
    cbn [app parse_lines]. destruct (step b (PPara [])); reflexivity.
  - cbn [forallb] in Hls. apply andb_true_iff in Hls as [Hl Hls]. cbn [app].
    rewrite (parse_lines_step _ _ _ _ _ (step_heading_keeps l lvl rng cur Hl)).
    apply IH; assumption.
Qed.

(** The end of the document, or of the enclosing container, whose
    contents are parsed as a document. *)
Theorem heading_ends_with_lines :
  forall lvl ls rng cur,
    forallb (heading_keeps lvl) ls = true ->
    parse_lines ls (PHeading lvl rng cur)
    = [heading_block lvl (heading_lines ls cur)].
Proof.
  intros lvl ls. induction ls as [|l ls IH]; intros rng cur Hls.
  - reflexivity.
  - cbn [forallb] in Hls. apply andb_true_iff in Hls as [Hl Hls].
    rewrite (parse_lines_step _ _ _ _ _ (step_heading_keeps l lvl rng cur Hl)).
    apply IH; assumption.
Qed.

(* A canonical single-line heading has no continuation lines to consume, so
   the same equation is available when continuation is disabled and the
   remaining rendered suffix is empty. *)
Lemma parse_lines_heading_seed_ok :
  forall lvl ls tail rng cur,
    (bheading_continues || Nat.eqb (List.length ls) 0)%bool = true ->
    touch_extent rng = rng ->
    1 <= lvl ->
    forallb nonblank ls = true ->
    parse_lines (map (heading_line lvl) ls ++ tail)%list
                (PHeading lvl rng cur) =
    parse_lines tail
      (PHeading lvl rng
        (remember_lines (rev (map drop_leading_ws ls)) ++ cur)%list).
Proof.
  intros lvl ls tail rng cur Hmode Hrng Hlvl Hlines.
  destruct bheading_continues eqn:Hcontinues.
  - apply parse_lines_heading_seed; assumption.
  - cbn in Hmode. apply Nat.eqb_eq in Hmode. destruct ls; [reflexivity|discriminate].
Qed.

(* The same through an all-whitespace pad: `classify_canonical_heading_pad`
   extracts the same pad-free `a`, and `push_text` drops what is left of
   the pad. *)
Local Lemma parse_lines_heading_seed_pad :
  forall pad, is_blank pad = true ->
  forall lvl ls tail rng cur,
    bheading_continues = true ->
    touch_extent rng = rng ->
    1 <= lvl ->
    forallb nonblank ls = true ->
    parse_lines (map (fun l => (pad ++ heading_line lvl l)%string) ls ++ tail)%list
                (PHeading lvl rng cur) =
    parse_lines tail
      (PHeading lvl rng
        (remember_lines (rev (map drop_leading_ws ls)) ++ cur)%list).
Proof.
  intros pad Hpad lvl ls. induction ls as [|a ls IH];
    intros tail rng cur Hcontinues Hrng Hlvl H.
  - reflexivity.
  - cbn [forallb] in H. apply andb_true_iff in H as [Ha Hls].
    unfold nonblank in Ha. apply negb_true_iff in Ha.
    cbn [map app].
    rewrite (parse_lines_heading_cont _ _ _ _ a _ Hcontinues
               (classify_canonical_heading_pad pad lvl a Hpad Hlvl)), Hrng.
    unfold push_text. rewrite Ha.
    rewrite IH by assumption.
    cbn [rev map]. unfold remember_lines. rewrite map_app. cbn [map].
    rewrite <- app_assoc. reflexivity.
Qed.

Local Lemma parse_lines_heading_seed_pad_ok :
  forall pad, is_blank pad = true ->
  forall lvl ls tail rng cur,
    (bheading_continues || Nat.eqb (List.length ls) 0)%bool = true ->
    touch_extent rng = rng ->
    1 <= lvl ->
    forallb nonblank ls = true ->
    parse_lines (map (fun l => (pad ++ heading_line lvl l)%string) ls ++ tail)%list
                (PHeading lvl rng cur) =
    parse_lines tail
      (PHeading lvl rng
        (remember_lines (rev (map drop_leading_ws ls)) ++ cur)%list).
Proof.
  intros pad Hpad lvl ls tail rng cur Hmode Hrng Hlvl Hlines.
  destruct bheading_continues eqn:Hcontinues.
  - apply parse_lines_heading_seed_pad; assumption.
  - cbn in Hmode. apply Nat.eqb_eq in Hmode. destruct ls; [reflexivity|discriminate].
Qed.

(*
Uniformity of block quotes
--------------------------

The payoff of routing a quote's contents back through `step`: prefixing
every line of a document with "> " parses to exactly that document,
wrapped in a quote.  Nothing about the contents is assumed, so this
holds for every construct the parser knows, nested quotes included. *)

(* The quote lemmas through an all-whitespace pad in front of every "> ";
   the unpadded forms below are the empty pad.  A quote nested in a list
   item ignores the item's indent: the pad never reaches `rest`.  A
   nested list is not like that, since its recorded column moves with the
   pad, so the list side is stated as a shift (`run_lines_pad_shift`). *)
Local Lemma consumed_quote_prefix_pad :
  forall pad l, consumed (pad ++ "> " ++ l) l = String.length pad + quote_pad.
Proof.
  intros pad l. unfold consumed, quote_pad, quote_open.
  rewrite !length_append. cbn [String.length]. lia.
Qed.

Local Lemma parse_lines_quote_cont_header_pad :
  forall pad, is_blank pad = true ->
  forall sep, classify sep = KBlank ->
  forall lines tail range header done inner,
    parse_lines (map (fun l => pad ++ "> " ++ l)%string lines ++ sep :: tail)%list
                (PQuote range header done (pad_state (String.length pad + quote_pad) inner))
    = mk (quote_block header (rev done ++ parse_lines lines inner)%list)
      :: parse_lines tail (PPara []).
Proof.
  intros pad Hpad sep Hsep. induction lines as [|l lines IH]; intros tail range header done inner.
  - cbn [map app].
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_close _ KBlank _ header _ _ _ _ Hsep eq_refl eq_refl eq_refl)).
    cbn [finish]. rewrite pad_state_finish. reflexivity.
  - cbn [map app].
    destruct (step l inner) as [bs inner'] eqn:Es.
    assert (Esh : step_at (consumed (pad ++ "> " ++ l) l) l
                    (pad_state (String.length pad + quote_pad) inner)
                  = (bs, pad_state (String.length pad + quote_pad) inner')).
    { rewrite consumed_quote_prefix_pad.
      rewrite <- (Nat.add_0_r (String.length pad + quote_pad)) at 1.
      rewrite step_at_shift, step_at_zero, Es. reflexivity. }
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ header _ _ _ _
                  (classify_canonical_quote_pad pad l Hpad) Esh)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

Local Lemma parse_lines_quote_cont_eof_header_pad :
  forall pad, is_blank pad = true ->
  forall lines range header done inner,
    parse_lines (map (fun l => pad ++ "> " ++ l)%string lines)
                (PQuote range header done (pad_state (String.length pad + quote_pad) inner))
    = [mk (quote_block header (rev done ++ parse_lines lines inner)%list)].
Proof.
  intros pad Hpad. induction lines as [|l lines IH]; intros range header done inner.
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
               (step_quote_cont _ _ _ header _ _ _ _
                  (classify_canonical_quote_pad pad l Hpad) Esh)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

Local Lemma parse_lines_quote_cont_pad :
  forall pad, is_blank pad = true ->
  forall sep, classify sep = KBlank ->
  forall lines tail range done inner,
    parse_lines (map (fun l => pad ++ "> " ++ l)%string lines ++ sep :: tail)%list
                (PQuote range None done (pad_state (String.length pad + quote_pad) inner))
    = mk (BlockQuote (rev done ++ parse_lines lines inner)%list)
      :: parse_lines tail (PPara []).
Proof.
  intros pad Hpad sep Hsep lines tail range done inner.
  exact (parse_lines_quote_cont_header_pad pad Hpad sep Hsep lines tail range None done inner).
Qed.

Local Lemma parse_lines_quote_cont_eof_pad :
  forall pad, is_blank pad = true ->
  forall lines range done inner,
    parse_lines (map (fun l => pad ++ "> " ++ l)%string lines)
                (PQuote range None done (pad_state (String.length pad + quote_pad) inner))
    = [mk (BlockQuote (rev done ++ parse_lines lines inner)%list)].
Proof.
  intros pad Hpad lines range done inner.
  exact (parse_lines_quote_cont_eof_header_pad pad Hpad lines range None done inner).
Qed.

Local Lemma parse_lines_quote_pad :
  forall pad, is_blank pad = true ->
  forall sep, classify sep = KBlank ->
  forall l lines tail,
    (quote_header l) = None ->
    parse_lines
      (map (fun x => pad ++ "> " ++ x)%string (l :: lines) ++ sep :: tail)%list
      (PPara [])
    = mk (BlockQuote (parse_lines (l :: lines) (PPara [])))
      :: parse_lines tail (PPara []).
Proof.
  intros pad Hpad sep Hsep l lines tail Hheader. cbn [map app].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote_pad pad l Hpad)
               Hheader Es)).
  cbn [app]. rewrite consumed_quote_prefix_pad.
  rewrite (parse_lines_quote_cont_pad pad Hpad sep Hsep), rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.

Theorem quote_uniformity_pad :
  forall pad, is_blank pad = true ->
  forall l lines,
    (quote_header l) = None ->
    parse_lines (map (fun x => pad ++ "> " ++ x)%string (l :: lines)) (PPara [])
    = [mk (BlockQuote (parse_lines (l :: lines) (PPara [])))].
Proof.
  intros pad Hpad l lines Hheader. cbn [map].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote_pad pad l Hpad)
               Hheader Es)).
  cbn [app]. rewrite consumed_quote_prefix_pad.
  rewrite (parse_lines_quote_cont_eof_pad pad Hpad), rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.

(* Inside an open quote, the prefixed lines drive the inner state and
   the blank line that follows closes the quote. *)
Local Lemma parse_lines_quote_cont :
  forall lines tail range done inner,
    parse_lines (map (fun l => ("> " ++ l)%string) lines ++ EmptyString :: tail)%list
                (PQuote range None done (pad_state quote_pad inner))
    = mk (BlockQuote (rev done ++ parse_lines lines inner)%list)
      :: parse_lines tail (PPara []).
Proof.
  intros lines tail range done inner.
  exact (parse_lines_quote_cont_pad EmptyString eq_refl EmptyString
           (classify_blank EmptyString eq_refl) lines tail range done inner).
Qed.

(* ...and the same when the input simply ends. *)
Local Lemma parse_lines_quote_cont_eof :
  forall lines range done inner,
    parse_lines (map (fun l => ("> " ++ l)%string) lines)
                (PQuote range None done (pad_state quote_pad inner))
    = [mk (BlockQuote (rev done ++ parse_lines lines inner)%list)].
Proof.
  intros lines range done inner.
  exact (parse_lines_quote_cont_eof_pad EmptyString eq_refl
           lines range done inner).
Qed.

Lemma parse_lines_quote :
  forall l lines tail,
    (quote_header l) = None ->
    parse_lines
      (map (fun x => ("> " ++ x)%string) (l :: lines) ++ EmptyString :: tail)%list
      (PPara [])
    = mk (BlockQuote (parse_lines (l :: lines) (PPara [])))
      :: parse_lines tail (PPara []).
Proof.
  intros l lines tail Hheader.
  exact (parse_lines_quote_pad EmptyString eq_refl EmptyString
           (classify_blank EmptyString eq_refl) l lines tail Hheader).
Qed.

(** Uniformity for block quotes: a quote's contents parse exactly as
    they would at top level.  One proof, every construct. *)
Theorem quote_uniformity :
    forall (l : string) (lines : list string),
    (* for non-empty list of lines (l :: lines) *)
    (quote_header l) = None 
    (* exclude callouts when callouts are on *)
    ->
    parse_lines (map (fun x => ("> " ++ x)%string) (l :: lines)) (PPara [])
    (* LHS: add [> ] prefix to every line, then parse the result as a document *)
    = [mk (BlockQuote (parse_lines (l :: lines) (PPara [])))].
    (* RHS: parse the lines as a document, then wrap in a BlockQuote *)
Proof.
  intros l lines Hheader.
  exact (quote_uniformity_pad EmptyString eq_refl l lines Hheader).
Qed.

Lemma parse_lines_callout :
  forall header lines tail kind fold title,
    (quote_header header) =
      Some (kind, fold, title) ->
    parse_lines
      (map quote_line (header :: lines) ++ EmptyString :: tail)%list (PPara [])
    = mk (Ext_callout kind fold (callout_title (remember_line title))
        (parse_lines lines (PPara [])))
      :: parse_lines tail (PPara []).
Proof.
  intros header lines tail kind fold title Hheader.
  cbn [map app].
  rewrite (parse_lines_step _ _ _ _ _
    (step_callout_open _ _ _ _ _ (classify_canonical_quote header) Hheader)).
  cbn [app].
  change (PQuote (open_extent (quote_line header) (indent_of (quote_line header)))
    (Some (kind, fold, remember_line title)) [] (PPara []))
    with (PQuote (open_extent (quote_line header) (indent_of (quote_line header)))
      (Some (kind, fold, remember_line title)) [] (pad_state quote_pad (PPara []))).
  exact (parse_lines_quote_cont_header_pad EmptyString eq_refl EmptyString
    (classify_blank EmptyString eq_refl) lines tail
    (open_extent (quote_line header) (indent_of (quote_line header)))
    (Some (kind, fold, remember_line title)) [] (PPara [])).
Qed.

Theorem callout_uniformity :
  forall header lines kind fold title,
    (quote_header header) =
      Some (kind, fold, title) ->
    parse_lines (map quote_line (header :: lines)) (PPara []) =
      [mk (Ext_callout kind fold (callout_title (remember_line title))
        (parse_lines lines (PPara [])))].
Proof.
  intros header lines kind fold title Hheader.
  cbn [map].
  rewrite (parse_lines_step _ _ _ _ _
    (step_callout_open _ _ _ _ _ (classify_canonical_quote header) Hheader)).
  cbn [app].
  change (PQuote (open_extent (quote_line header) (indent_of (quote_line header)))
    (Some (kind, fold, remember_line title)) [] (PPara []))
    with (PQuote (open_extent (quote_line header) (indent_of (quote_line header)))
      (Some (kind, fold, remember_line title)) [] (pad_state quote_pad (PPara []))).
  exact (parse_lines_quote_cont_eof_header_pad EmptyString eq_refl lines
    (open_extent (quote_line header) (indent_of (quote_line header)))
    (Some (kind, fold, remember_line title)) [] (PPara [])).
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

Local Lemma run_lines_app :
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

Local Lemma run_lines_continue :
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

(* How a line `x` of a quote's contents may be written: `> x`, or a bare
   `>` when `x` is empty, as in the reference's `>` between two
   paragraphs of a quote. *)
Inductive quote_spelling : string -> string -> Prop :=
  | QSpace : forall x, quote_spelling x ("> " ++ x)
  | QBare : quote_spelling "" ">".

Local Lemma parse_lines_quote_bare :
  forall lines qs range header done inner,
    Forall2 quote_spelling lines qs ->
    parse_lines qs (PQuote range header done (pad_state quote_pad inner))
    = parse_lines (map (fun x => ("> " ++ x)%string) lines)
        (PQuote range header done (pad_state quote_pad inner)).
Proof.
  intros lines qs range header done inner H. revert range header done inner.
  induction H as [|x q lines qs Hx Hrest IH]; intros range header done inner;
    [reflexivity|].
  destruct (step x inner) as [bs inner'] eqn:Es.
  assert (Esh : step_at (consumed ("" ++ "> " ++ x) x) x
                  (pad_state (String.length "" + quote_pad) inner)
                = (bs, pad_state (String.length "" + quote_pad) inner')).
  { rewrite consumed_quote_prefix_pad.
    rewrite <- (Nat.add_0_r (String.length "" + quote_pad)) at 1.
    rewrite step_at_shift, step_at_zero, Es. reflexivity. }
  pose proof (step_quote_cont _ _ range header done _ _ _
                (classify_canonical_quote_pad "" x eq_refl) Esh) as Hc.
  cbn [map].
  assert (Hq : step q (PQuote range header done (pad_state quote_pad inner))
               = step ("> " ++ x) (PQuote range header done (pad_state quote_pad inner))).
  { destruct Hx; [reflexivity|].
    apply step_quote_bare. }
  rewrite (parse_lines_step _ _ _ _ _ (eq_trans Hq Hc)),
    (parse_lines_step _ _ _ _ _ Hc).
  cbn [app]. rewrite IH. reflexivity.
Qed.

(** Uniformity for block quotes whose empty lines are written `>`.  The
    first line keeps its space: a bare `>` there opens the same quote but
    records a different source range. *)
Theorem quote_uniformity_bare :
  forall l lines qs,
    quote_header l = None ->
    Forall2 quote_spelling lines qs ->
    parse_lines (("> " ++ l)%string :: qs) (PPara [])
    = [mk (BlockQuote (parse_lines (l :: lines) (PPara [])))].
Proof.
  intros l lines qs Hheader H.
  rewrite <- (quote_uniformity l lines Hheader). cbn [map].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  pose proof (step_quote_open _ _ _ _ (classify_canonical_quote_pad "" l eq_refl)
                Hheader Es) as Ho.
  rewrite (consumed_quote_prefix_pad "") in Ho.
  rewrite !(parse_lines_step _ _ _ _ _ Ho). cbn [app].
  exact (parse_lines_quote_bare lines qs _ _ _ inner H).
Qed.

(* Inside an open quote, a line that is neither a quote line nor lazy
   closes it and is read at top level. *)
Local Lemma parse_lines_quote_cont_close :
  forall lines next tail range done inner,
    (forall r, classify next <> KQuote r) ->
    is_lazy (classify next) (snd (run_lines lines inner)) = false ->
    parse_lines (map (fun l => ("> " ++ l)%string) lines ++ next :: tail)%list
                (PQuote range None done (pad_state quote_pad inner))
    = mk (BlockQuote (rev done ++ parse_lines lines inner)%list)
      :: parse_lines (next :: tail) (PPara []).
Proof.
  induction lines as [|l lines IH]; intros next tail range done inner Hq Hlz.
  - cbn [map app run_lines snd] in Hlz |- *.
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_close_any next range None done
                  (pad_state quote_pad inner) Hq
                  ltac:(unfold is_lazy in *; rewrite Step.pad_state_lazy_ok;
                        exact Hlz))).
    destruct (step next (PPara [])) as [bs st'] eqn:Es. cbn [fst snd finish].
    rewrite pad_state_finish, (parse_lines_step _ _ _ _ _ Es). reflexivity.
  - cbn [map app].
    destruct (step l inner) as [bs inner'] eqn:Es.
    cbn [run_lines] in Hlz. rewrite Es in Hlz.
    assert (Hlz' : is_lazy (classify next) (snd (run_lines lines inner')) = false)
      by (destruct (run_lines lines inner'); exact Hlz).
    assert (Esh : step_at (consumed ("" ++ "> " ++ l) l) l
                    (pad_state (String.length "" + quote_pad) inner)
                  = (bs, pad_state (String.length "" + quote_pad) inner')).
    { rewrite consumed_quote_prefix_pad.
      rewrite <- (Nat.add_0_r (String.length "" + quote_pad)) at 1.
      rewrite step_at_shift, step_at_zero, Es. reflexivity. }
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ None _ _ _ _
                  (classify_canonical_quote_pad "" l eq_refl) Esh)).
    cbn [app]. rewrite (IH next tail _ _ _ Hq Hlz').
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

(** The same with more of the document after the quote.  The line that
    ends it is anything but a quote line or a lazy continuation of the
    quote's open paragraph; a blank line is the common case
    (`parse_lines_quote`). *)
Theorem quote_uniformity_tail :
  forall l lines next tail,
    quote_header l = None ->
    (forall r, classify next <> KQuote r) ->
    is_lazy (classify next) (snd (run_lines (l :: lines) (PPara []))) = false ->
    parse_lines (map (fun x => ("> " ++ x)%string) (l :: lines) ++ next :: tail)%list
                (PPara [])
    = mk (BlockQuote (parse_lines (l :: lines) (PPara [])))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros l lines next tail Hheader Hq Hlz. cbn [map app].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote_pad "" l eq_refl)
                Hheader Es)).
  cbn [app]. rewrite (consumed_quote_prefix_pad "").
  cbn [run_lines] in Hlz. rewrite Es in Hlz.
  rewrite (parse_lines_quote_cont_close lines next tail _ _ inner Hq
             ltac:(destruct (run_lines lines inner); exact Hlz)), rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es). reflexivity.
Qed.

(*
Uniformity of fenced divs
-------------------------

Same payoff as the quote's, and a shorter argument, because a div strips
no prefix and shifts no column: its contents are handed the line
unchanged.  What replaces the prefix machinery is the side condition.

"No content line is a closing fence" is false as a side condition,
because `div_close` strips leading whitespace before it looks.  A `:::`
indented under a list item closes the div through the list; `- a` /
`  :::` / `  b` parses one way at top level and another inside a div
(`div_indented_close_differs` below).  So the condition has to reach
every line of the contents, nested ones included.

It cannot be lexical either, because inside an open fence a `:::` line
is content, not a closer: the condition depends on the state each line
is reached in.  That makes it a run predicate of the shape `run_safe`
has.  `run_div_open` is that predicate: fold `step` over the contents
and check at each line that the div does not close there.
`div_code_fence_uniform` below is a document it accepts that a lexical
condition would have thrown away. *)

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
   and a line that closes it is consumed. *)
Local Lemma parse_lines_div_cont :
  forall len cls c content tail range opener done inner,
    run_div_open len content inner = true ->
    in_fence (snd (run_lines content inner)) = false ->
    div_close len c = true ->
    parse_lines (content ++ c :: tail)%list
                (PDiv len cls range opener done inner)
    = div_block cls (rev done ++ parse_lines content inner)%list
      :: parse_lines tail (PPara []).
Proof.
  intros len cls c content. induction content as [|l content IH];
    intros tail range opener done inner Hopen Hfence Hc.
  - cbn [run_lines snd] in Hfence. cbn [app].
    rewrite (parse_lines_step _ _ _ _ _
               (step_div_close c len cls range opener done inner Hfence Hc)).
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
               (step_div_cont l len cls range opener done inner bs inner' Hl Es)).
    cbn [app].
    rewrite (IH tail _ opener (rev bs ++ done)%list inner' Hrest
               ltac:(rewrite Er; exact Hfence) Hc).
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

(* The same contents at the end of the input: the div closes with it. *)
Local Lemma parse_lines_div_eof :
  forall len cls content range opener done inner,
    run_div_open len content inner = true ->
    parse_lines content (PDiv len cls range opener done inner)
    = [div_block cls (rev done ++ parse_lines content inner)%list].
Proof.
  intros len cls content. induction content as [|l content IH];
    intros range opener done inner Hopen; [reflexivity|].
  cbn [run_div_open] in Hopen. apply andb_true_iff in Hopen as [Hl Hrest].
  apply negb_true_iff in Hl.
  destruct (step l inner) as [bs inner'] eqn:Es. cbn [snd] in Hrest.
  rewrite (parse_lines_step _ _ _ _ _
             (step_div_cont l len cls range opener done inner bs inner' Hl Es)).
  cbn [app]. rewrite (IH _ opener (rev bs ++ done)%list inner' Hrest).
  rewrite (parse_lines_step _ _ _ _ _ Es).
  rewrite rev_app_distr, rev_involutive, <- app_assoc.
  reflexivity.
Qed.

Local Lemma parse_lines_div_open :
  forall l rest len cls,
    bdivs = true -> classify l = KDiv len cls ->
    parse_lines (l :: rest) (PPara [])
    = parse_lines rest (PDiv len cls (open_extent l (indent_of l))
                          (line_span_from l (indent_of l)) [] (PPara [])).
Proof.
  intros l rest len cls Hdivs Hl.
  assert (Hs : step l (PPara []) =
                ([], PDiv len cls (open_extent l (indent_of l))
                       (line_span_from l (indent_of l)) [] (PPara []))).
  { rewrite (step_idle l _ Hl eq_refl). cbn [open_kind]. rewrite Hdivs.
    reflexivity. }
  rewrite (parse_lines_step _ _ _ _ _ Hs). reflexivity.
Qed.

(** DV2 and DV3: a div opened by any opener (`classify_div_fences`) and
    closed by any line that closes it (`div_close_colons`) holds its
    contents parsed as a document, for contents that leave it open. *)
Theorem fenced_div_closed :
  forall l len cls content c tail,
    bdivs = true -> classify l = KDiv len cls ->
    run_div_open len content (PPara []) = true ->
    in_fence (snd (run_lines content (PPara []))) = false ->
    div_close len c = true ->
    parse_lines (l :: content ++ c :: tail)%list (PPara [])
    = div_block cls (parse_lines content (PPara []))
      :: parse_lines tail (PPara []).
Proof.
  intros l len cls content c tail Hdivs Hl Hopen Hfence Hc.
  rewrite (parse_lines_div_open _ _ _ _ Hdivs Hl).
  exact (parse_lines_div_cont _ _ _ _ _ _ _ [] _ Hopen Hfence Hc).
Qed.

(** DV2, "or with the end of the document". *)
Theorem fenced_div_unclosed :
  forall l len cls content,
    bdivs = true -> classify l = KDiv len cls ->
    run_div_open len content (PPara []) = true ->
    parse_lines (l :: content) (PPara [])
    = [div_block cls (parse_lines content (PPara []))].
Proof.
  intros l len cls content Hdivs Hl Hopen.
  rewrite (parse_lines_div_open _ _ _ _ Hdivs Hl).
  exact (parse_lines_div_eof _ _ _ _ _ [] _ Hopen).
Qed.

(** Uniformity for fenced divs: a div's contents parse exactly as they
    would at top level, for any contents that leave the div open.  The
    canonical instance of `fenced_div_closed`, with any word the opener
    reads back. *)
Theorem div_uniformity :
  forall word content,
    bdivs = true ->
    div_word_ok word = true ->
    div_content_ok content = true ->
    parse_lines (div_open_line div_fence word :: content ++ [div_fence])%list
      (PPara [])
    = [div_block word (parse_lines content (PPara []))].
Proof.
  intros word content Hdivs Hw Hok. unfold div_content_ok in Hok.
  apply andb_true_iff in Hok as [Hopen Hf]. apply negb_true_iff in Hf.
  exact (fenced_div_closed _ _ _ _ _ [] Hdivs (classify_canonical_div_open word Hw)
           Hopen Hf div_close_canonical).
Qed.

(* The same with a document after it, which is the form the roundtrip
   proof needs: the closing fence is consumed and the separator blank
   returns the parser to idle. *)
Theorem div_uniformity_tail :
  forall word content tail,
    bdivs = true ->
    div_word_ok word = true ->
    div_content_ok content = true ->
    parse_lines (div_open_line div_fence word
                   :: content ++ div_fence :: EmptyString :: tail)%list
                (PPara [])
    = div_block word (parse_lines content (PPara [])) :: parse_lines tail (PPara []).
Proof.
  intros word content tail Hdivs Hw Hok. unfold div_content_ok in Hok.
  apply andb_true_iff in Hok as [Hopen Hf]. apply negb_true_iff in Hf.
  rewrite (fenced_div_closed _ _ _ _ _ _ Hdivs (classify_canonical_div_open word Hw)
             Hopen Hf div_close_canonical).
  rewrite (parse_lines_blank_nil EmptyString tail
             (classify_blank EmptyString eq_refl)).
  reflexivity.
Qed.

Local Lemma run_lines_cons_snd :
  forall x lines st bs st',
    step x st = (bs, st') ->
    snd (run_lines (x :: lines) st) = snd (run_lines lines st').
Proof.
  intros x lines st bs st' Hs. cbn [run_lines]. rewrite Hs.
  destruct (run_lines lines st'). reflexivity.
Qed.

(* A footnote keeps a blank line or a line indented past its opener in
   its body.  The body transition is the same one top-level parsing takes;
   the footnote only collects blocks that transition commits. *)
Lemma step_foot_cont :
  forall l range ind lbl done inner bs inner',
    (is_blank l || Nat.ltb ind (indent_of l))%bool = true ->
    step l inner = (bs, inner') ->
    step l (PFoot range ind lbl done inner) =
      ([], PFoot (touch_extent range) ind lbl
            (rev bs ++ done)%list inner').
Proof.
  intros l range ind lbl done inner bs inner' Howned Hr.
  unfold step at 1. cbn [step_fuel open_line pstate_depth].
  destruct (is_blank l) eqn:Hblank.
  - rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    rewrite Hr. reflexivity.
  - cbn [orb] in Howned. unfold foot_takes.
    rewrite Nat.add_0_l, Howned, orb_true_r.
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    rewrite Hr. reflexivity.
Qed.

Lemma step_foot_close :
  forall l range ind lbl done inner bs st',
    is_blank l = false ->
    foot_takes ind 0 l inner = false ->
    is_lazy (classify l) inner = false ->
    step l (PPara []) = (bs, st') ->
    step l (PFoot range ind lbl done inner) =
      (foot_block lbl (rev done ++ finish inner)%list :: bs, st').
Proof.
  intros l range ind lbl done inner bs st' Hblank Hind Hlazy Hr.
  unfold step at 1. cbn [step_fuel open_line pstate_depth].
  rewrite Hblank, Hind, Hlazy.
  rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
  rewrite Hr. nopos. reflexivity.
Qed.

Theorem footnote_content_uniformity :
  forall lines range ind lbl done inner,
    forallb (fun l => (is_blank l || Nat.ltb ind (indent_of l))%bool)
      lines = true ->
    parse_lines lines (PFoot range ind lbl done inner) =
      [foot_block lbl (rev done ++ parse_lines lines inner)%list].
Proof.
  intros lines. induction lines as [|l lines IH];
    intros range ind lbl done inner Howned.
  - cbn [parse_lines finish]. nopos. reflexivity.
  - cbn [forallb] in Howned.
    apply andb_true_iff in Howned as [Hl Hlines].
    destruct (step l inner) as [bs inner'] eqn:Hs.
    rewrite (parse_lines_step _ _ _ _ _
      (step_foot_cont _ _ _ _ _ _ _ _ Hl Hs)).
    rewrite (parse_lines_step _ _ _ _ _ Hs).
    cbn [app]. rewrite (IH _ _ _ _ _ Hlines).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

Theorem footnote_content_uniformity_tail :
  forall lines l tail range ind lbl done inner,
    forallb (fun x => (is_blank x || Nat.ltb ind (indent_of x))%bool)
      lines = true ->
    is_blank l = false ->
    foot_takes ind 0 l (snd (run_lines lines inner)) = false ->
    is_lazy (classify l) (snd (run_lines lines inner)) = false ->
    parse_lines (lines ++ l :: tail)%list
      (PFoot range ind lbl done inner) =
      foot_block lbl (rev done ++ parse_lines lines inner)%list
        :: parse_lines (l :: tail) (PPara []).
Proof.
  intros lines. induction lines as [|x lines IH];
    intros l tail range ind lbl done inner Howned Hb Hind Hlazy.
  - cbn [app].
    destruct (step l (PPara [])) as [bs st'] eqn:Hs.
    rewrite (parse_lines_step _ _ _ _ _
      (step_foot_close _ _ _ _ _ _ _ _ Hb Hind Hlazy Hs)).
    rewrite (parse_lines_step _ _ _ _ _ Hs).
    cbn [parse_lines app]. reflexivity.
  - cbn [forallb] in Howned.
    apply andb_true_iff in Howned as [Hx Hlines].
    destruct (step x inner) as [bs inner'] eqn:Hs.
    cbn [app].
    rewrite (parse_lines_step _ _ _ _ _
      (step_foot_cont _ _ _ _ _ _ _ _ Hx Hs)).
    rewrite (parse_lines_step _ _ _ _ _ Hs).
    rewrite (run_lines_cons_snd _ _ _ _ _ Hs) in Hlazy, Hind.
    cbn [app]. rewrite (IH _ _ _ _ _ _ _ Hlines Hb Hind Hlazy).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

(** From a footnote opener through its owned lines: the body keeps the
    parser state produced by the opener's residue, while the first line
    outside the footnote is parsed again at top level. *)
Theorem footnote_open_uniformity_tail :
  forall opener lbl first lines l tail bs inner,
    bfootnotes = true ->
    classify opener = KFoot lbl first ->
    step first (PPara []) = (bs, inner) ->
    forallb (fun x =>
      (is_blank x || Nat.ltb (indent_of opener) (indent_of x))%bool)
      lines = true ->
    is_blank l = false ->
    foot_takes (indent_of opener) 0 l
      (snd (run_lines lines (pad_state (consumed opener first) inner))) = false ->
    is_lazy (classify l)
      (snd (run_lines lines (pad_state (consumed opener first) inner))) = false ->
    parse_lines (opener :: lines ++ l :: tail)%list (PPara []) =
      foot_block lbl
        (bs ++ parse_lines lines
          (pad_state (consumed opener first) inner))%list
        :: parse_lines (l :: tail) (PPara []).
Proof.
  intros opener lbl first lines l tail bs inner
    Hfoot Hclass Hfirst Hlines Hb Hind Hlazy.
  cbn [parse_lines].
  rewrite (step_foot_open opener lbl first bs inner Hclass Hfirst).
  unfold open_foot. rewrite Hfoot. cbn [fst snd app].
  rewrite (footnote_content_uniformity_tail
    lines l tail _ _ _ _ _ Hlines Hb Hind Hlazy).
  rewrite rev_involutive. reflexivity.
Qed.

(* An opener whose body state carries no column shift needs no further
   normalization: its complete body is the top-level parse of the
   residue followed by the footnote-owned lines. *)
Theorem footnote_unshifted_uniformity_tail :
  forall opener lbl first lines l tail bs inner,
    bfootnotes = true ->
    classify opener = KFoot lbl first ->
    step first (PPara []) = (bs, inner) ->
    pad_state (consumed opener first) inner = inner ->
    forallb (fun x =>
      (is_blank x || Nat.ltb (indent_of opener) (indent_of x))%bool)
      lines = true ->
    is_blank l = false ->
    foot_takes (indent_of opener) 0 l
      (snd (run_lines (first :: lines) (PPara []))) = false ->
    is_lazy (classify l) (snd (run_lines (first :: lines) (PPara []))) = false ->
    parse_lines (opener :: lines ++ l :: tail)%list (PPara []) =
      foot_block lbl (parse_lines (first :: lines) (PPara []))
        :: parse_lines (l :: tail) (PPara []).
Proof.
  intros opener lbl first lines l tail bs inner
    Hfoot Hopen Hfirst Hstable Hlines Hb Hind Hlazy.
  rewrite (run_lines_cons_snd _ _ _ _ _ Hfirst), <- Hstable in Hlazy, Hind.
  rewrite (footnote_open_uniformity_tail opener lbl first lines l tail
    bs inner Hfoot Hopen Hfirst Hlines Hb Hind Hlazy).
  rewrite Hstable.
  rewrite (parse_lines_step _ _ _ _ _ Hfirst).
  reflexivity.
Qed.

Theorem footnote_unshifted_uniformity :
  forall opener lbl first lines bs inner,
    bfootnotes = true ->
    classify opener = KFoot lbl first ->
    step first (PPara []) = (bs, inner) ->
    pad_state (consumed opener first) inner = inner ->
    forallb (fun x =>
      (is_blank x || Nat.ltb (indent_of opener) (indent_of x))%bool)
      lines = true ->
    parse_lines (opener :: lines) (PPara []) =
      [foot_block lbl (parse_lines (first :: lines) (PPara []))].
Proof.
  intros opener lbl first lines bs inner
    Hfoot Hopen Hfirst Hstable Hlines.
  cbn [parse_lines].
  rewrite (step_foot_open opener lbl first bs inner Hopen Hfirst).
  unfold open_foot. rewrite Hfoot. cbn [fst snd app].
  rewrite (footnote_content_uniformity lines _ _ _ _ _ Hlines).
  rewrite Hstable, Hfirst, rev_involutive.
  cbn [fst snd app]. reflexivity.
Qed.

(** For a text residue, padding leaves the paragraph state unchanged.
    Thus the whole footnote body has the same block parse as the residue
    followed by its owned lines at top level. *)
Theorem footnote_text_uniformity_tail :
  forall opener lbl first lines l tail,
    bfootnotes = true ->
    classify opener = KFoot lbl first ->
    classify first = KText ->
    keyless first = true ->
    forallb (fun x =>
      (is_blank x || Nat.ltb (indent_of opener) (indent_of x))%bool)
      lines = true ->
    is_blank l = false ->
    foot_takes (indent_of opener) 0 l
      (snd (run_lines (first :: lines) (PPara []))) = false ->
    is_lazy (classify l) (snd (run_lines (first :: lines) (PPara []))) = false ->
    parse_lines (opener :: lines ++ l :: tail)%list (PPara []) =
      foot_block lbl (parse_lines (first :: lines) (PPara []))
        :: parse_lines (l :: tail) (PPara []).
Proof.
  intros opener lbl first lines l tail
    Hfoot Hopen Htext Hkey Hlines Hb Hind Hlazy.
  assert (Hfirst : step first (PPara []) =
    ([], PPara [remember_line (drop_leading_ws first)])).
  { rewrite (step_idle first KText Htext eq_refl).
    apply open_text_keyless. exact Hkey. }
  exact (footnote_unshifted_uniformity_tail opener lbl first lines l tail
    [] (PPara [remember_line (drop_leading_ws first)])
    Hfoot Hopen Hfirst eq_refl Hlines Hb Hind Hlazy).
Qed.

Theorem footnote_text_uniformity :
  forall opener lbl first lines,
    bfootnotes = true ->
    classify opener = KFoot lbl first ->
    classify first = KText ->
    keyless first = true ->
    forallb (fun x =>
      (is_blank x || Nat.ltb (indent_of opener) (indent_of x))%bool)
      lines = true ->
    parse_lines (opener :: lines) (PPara []) =
      [foot_block lbl (parse_lines (first :: lines) (PPara []))].
Proof.
  intros opener lbl first lines Hfoot Hopen Htext Hkey Hlines.
  assert (Hfirst : step first (PPara []) =
    ([], PPara [remember_line (drop_leading_ws first)])).
  { rewrite (step_idle first KText Htext eq_refl).
    apply open_text_keyless. exact Hkey. }
  exact (footnote_unshifted_uniformity opener lbl first lines []
    (PPara [remember_line (drop_leading_ws first)])
    Hfoot Hopen Hfirst eq_refl Hlines).
Qed.

Theorem footnote_blank_uniformity_tail :
  forall opener lbl first lines l tail,
    bfootnotes = true ->
    classify opener = KFoot lbl first ->
    classify first = KBlank ->
    forallb (fun x =>
      (is_blank x || Nat.ltb (indent_of opener) (indent_of x))%bool)
      lines = true ->
    is_blank l = false ->
    foot_takes (indent_of opener) 0 l
      (snd (run_lines (first :: lines) (PPara []))) = false ->
    is_lazy (classify l) (snd (run_lines (first :: lines) (PPara []))) = false ->
    parse_lines (opener :: lines ++ l :: tail)%list (PPara []) =
      foot_block lbl (parse_lines (first :: lines) (PPara []))
        :: parse_lines (l :: tail) (PPara []).
Proof.
  intros opener lbl first lines l tail
    Hfoot Hopen Hblank Hlines Hb Hind Hlazy.
  assert (Hfirst : step first (PPara []) = ([], PPara [])).
  { rewrite (step_idle first KBlank Hblank eq_refl). reflexivity. }
  exact (footnote_unshifted_uniformity_tail opener lbl first lines l tail
    [] (PPara []) Hfoot Hopen Hfirst eq_refl Hlines Hb Hind Hlazy).
Qed.

Theorem footnote_blank_uniformity :
  forall opener lbl first lines,
    bfootnotes = true ->
    classify opener = KFoot lbl first ->
    classify first = KBlank ->
    forallb (fun x =>
      (is_blank x || Nat.ltb (indent_of opener) (indent_of x))%bool)
      lines = true ->
    parse_lines (opener :: lines) (PPara []) =
      [foot_block lbl (parse_lines (first :: lines) (PPara []))].
Proof.
  intros opener lbl first lines Hfoot Hopen Hblank Hlines.
  assert (Hfirst : step first (PPara []) = ([], PPara [])).
  { rewrite (step_idle first KBlank Hblank eq_refl). reflexivity. }
  exact (footnote_unshifted_uniformity opener lbl first lines
    [] (PPara []) Hfoot Hopen Hfirst eq_refl Hlines).
Qed.

(*
Lazy lines
----------
*)

(** The same for every spelling of the prefixes the containers accept
    (`spine_spelling`): after `- a`, the lines `b`, ` b` and `   b` all
    continue the item's paragraph. *)
Theorem lazy_line_spelling :
  forall pre p l post st,
    spine_spelling 0 (snd (run_lines pre st)) p ->
    lazy_ok (snd (run_lines pre st)) = true ->
    classify l = KText -> bunderline_of l = None ->
    parse_lines (pre ++ (p ++ l)%string :: post)%list st
    = parse_lines (pre ++ l :: post)%list st.
Proof.
  intros pre p l post st Hp Hlazy Htext Hu. rewrite !parse_lines_app_run.
  destruct (run_lines pre st) as [bs st'] eqn:E. cbn [snd] in *.
  cbn [parse_lines]. rewrite (step_lazy_spelling p l st' Hp Hlazy Htext Hu).
  reflexivity.
Qed.

(** Writing out a lazy line's prefixes does not change the parse.  After
    the lines `pre`, a paragraph is open, possibly inside block quotes,
    list items and footnotes.  If the next line `l` is plain text, putting
    `spine_prefix` in front of it (the `> ` and indentation those
    containers expect) gives the same blocks: `> a` / `b` parses as
    `> a` / `> b`.  The uniformity theorems above cover only documents in
    which every line has its prefix; this turns a document with lazy
    lines into one of those. *)
Theorem lazy_line_restore :
  forall pre l post st,
    lazy_ok (snd (run_lines pre st)) = true ->
    classify l = KText -> bunderline_of l = None ->
    parse_lines (pre ++ (spine_prefix 0 (snd (run_lines pre st)) ++ l)%string :: post)%list st
    = parse_lines (pre ++ l :: post)%list st.
Proof.
  intros pre l post st. apply lazy_line_spelling, spine_prefix_spelling.
Qed.

(* The containers whose paragraph lines the djot syntax reference lets
   omit the prefix: block quotes, list items and footnotes, any nesting
   of them around an open paragraph.  Written from the reference rather
   than from `lazy_ok`, so the theorem below holds the parser to it. *)
Inductive lazy_stack : pstate -> Prop :=
  | LSPara : forall c cur, lazy_stack (PPara (c :: cur))
  | LSQuote : forall range header done inner,
      lazy_stack inner -> lazy_stack (PQuote range header done inner)
  | LSList : forall ls done inner,
      lazy_stack inner -> lazy_stack (PList ls done inner)
  | LSFoot : forall range ind lbl done inner,
      lazy_stack inner -> lazy_stack (PFoot range ind lbl done inner).

Lemma lazy_stack_ok : forall st, lazy_stack st -> lazy_ok st = true.
Proof. induction 1; cbn [lazy_ok]; auto. Qed.

(** A lazy line continues the open paragraph.  When a paragraph is open
    inside block quotes, list items and footnotes (`lazy_stack st`) and
    the next line `l` is plain text, then `l` closes nothing and is added
    to that paragraph (`feed_lazy`), and `l` with `spine_prefix` in front
    gives the same result: after `> a`, both `b` and `> b` make the
    paragraph `a b`. *)
Theorem lazy_stack_line :
  forall l st,
    lazy_stack st -> classify l = KText -> bunderline_of l = None ->
    step l st = ([], feed_lazy l st) /\
    step (spine_prefix 0 st ++ l) st = step l st.
Proof.
  intros l st Hs Htext Hu. pose proof (lazy_stack_ok st Hs) as Hok.
  split; [apply step_lazy | apply step_lazy_restore]; assumption.
Qed.

(*
What a lazy line means
----------------------

The lazy-line theorems above turn a lazy line into a prefixed one, and
the uniformity theorems read a fully prefixed container.  Chained, they
say what a document with a lazy line means.  One theorem per container
the reference names, each with one lazy line `b` after a paragraph line
`a`; nesting and further lazy lines chain the same way.
*)

Theorem quote_lazy_line :
  forall a b,
    classify a = KText -> keyless a = true -> quote_header a = None ->
    classify b = KText -> bunderline_of b = None ->
    parse_lines [("> " ++ a)%string; b] (PPara [])
    = [mk (BlockQuote (parse_lines [a; b] (PPara [])))].
Proof.
  intros a b Ha Hk Hh Hb Hu.
  assert (Hstep : step ("> " ++ a) (PPara []) =
    ([], PQuote (open_extent ("> " ++ a) (indent_of ("> " ++ a))) None []
           (PPara [remember_line (drop_leading_ws a)]))).
  { rewrite (step_quote_open ("> " ++ a) a []
               (PPara [remember_line (drop_leading_ws a)])
               (classify_quote_space a) Hh
               ltac:(rewrite (step_idle a KText Ha eq_refl);
                     apply open_text_keyless; exact Hk)).
    reflexivity. }
  pose proof (lazy_line_spelling [("> " ++ a)%string] "> " b [] (PPara [])) as L.
  cbn [run_lines] in L. rewrite Hstep in L. cbn [snd app] in L.
  rewrite <- L;
    [| exact (SpQuote 0 0 _ _ _ _ _
                (SpLeaf 2 (PPara [remember_line (drop_leading_ws a)]) 0 eq_refl))
     | reflexivity | exact Hb | exact Hu].
  exact (quote_uniformity a [b] Hh).
Qed.

(* The opener is any line that opens a footnote with `a` after its colon,
   as in `footnote_text_uniformity`. *)
Theorem footnote_lazy_line :
  forall opener lbl a b,
    bfootnotes = true ->
    classify opener = KFoot lbl a ->
    classify a = KText -> keyless a = true ->
    classify b = KText -> bunderline_of b = None ->
    parse_lines [opener; b] (PPara [])
    = [foot_block lbl (parse_lines [a; b] (PPara []))].
Proof.
  intros opener lbl a b Hf Ho Ha Hk Hb Hu.
  (* the lazy line with the indentation `footnote_text_uniformity` asks *)
  set (p := blanks (S (indent_of opener))).
  assert (Ha0 : step a (PPara []) = ([], PPara [remember_line (drop_leading_ws a)])).
  { rewrite (step_idle a KText Ha eq_refl). apply open_text_keyless. exact Hk. }
  assert (Hin : Nat.ltb (indent_of opener) (indent_of (p ++ b)) = true).
  { apply Nat.ltb_lt. unfold p.
    rewrite (indent_of_ws_prefix _ _ (blanks_blank _)), blanks_length. lia. }
  pose proof (footnote_text_uniformity opener lbl a [(p ++ b)%string] Hf Ho Ha Hk
                ltac:(cbn [forallb]; rewrite Hin, orb_true_r; reflexivity)) as U.
  (* inside the note, the indentation is the paragraph's to ignore *)
  pose proof (lazy_line_spelling [a] p b [] (PPara [])) as L1.
  cbn [run_lines] in L1. rewrite Ha0 in L1. cbn [snd app] in L1.
  rewrite L1 in U; [| apply SpLeaf; reflexivity | reflexivity | exact Hb | exact Hu].
  (* and outside it, the lazy line is the indented one *)
  rewrite <- U. symmetry.
  pose proof (lazy_line_spelling [opener] p b [] (PPara [])) as L2.
  cbn [run_lines app] in L2.
  rewrite (step_foot_open opener lbl a [] _ Ho Ha0) in L2.
  unfold open_foot in L2. rewrite Hf in L2. cbn [snd rev] in L2.
  apply L2; [| reflexivity | exact Hb | exact Hu].
  unfold p. rewrite <- (append_empty_r (blanks (S (indent_of opener)))).
  change EmptyString with (blanks 0).
  apply SpFoot; [lia | cbn [pad_state]; apply SpLeaf; reflexivity].
Qed.

(*
Block attributes
----------------
*)

(* Can a state carry pending attributes down to the block that will
   claim them?  Three cannot: the idle state hands a blank line back as
   nothing at all, and `PAttr` and `PPend` are the two states that read
   the pending set themselves rather than passing it on. *)
Local Definition pend_carriable (st : pstate) : bool :=
  match st with
  | PPara [] | PAttr _ _ _ _ _ _ | PPend _ _ _ => false
  | _ => true
  end.

(* The same question of a state and the line about to reach it.  An idle
   state is carriable for every line but the two `PPend` answers itself:
   a blank drops the pending set and a spec merges into it. *)
Definition pend_ready (st : pstate) (l : string) : bool :=
  match st with
  | PPara [] => match classify l with KBlank | KAttr _ => false | _ => true end
  | PAttr _ _ _ _ _ _ | PPend _ _ _ => false
  | _ => true
  end.

Local Lemma pend_carriable_ready :
  forall st l, pend_carriable st = true -> pend_ready st l = true.
Proof.
  intros [cur| | | | | | | | | | | |] l H; try exact H;
    destruct cur; [discriminate|reflexivity].
Qed.

(* On a ready state the wrapper is transparent: the line goes down
   unchanged and `pend_result` decides what to do with what comes back. *)
Local Lemma step_pend_pass :
  forall l pend specs st, pend_ready st l = true ->
  step l (PPend pend specs st) = pend_result pend specs (step l st).
Proof.
  intros l pend specs st H. unfold step at 1. cbn [step_fuel pstate_depth].
  rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
  destruct st as [cur| | | | | | | | | | | |]; cbn [pend_ready] in H;
    try discriminate H;
    try (destruct (classify l); reflexivity).
  destruct cur as [|c cur'];
    [ destruct (classify l); try discriminate H; reflexivity
    | destruct (classify l); cbn [is_idle]; reflexivity ].
Qed.

(* What a line opens is carriable, save for the two kinds `pend_ready`
   excludes: a blank opens nothing and a spec opens the state that reads
   the pending set. *)
Local Lemma open_line_carriable :
  forall descend ind l k,
    match k with KBlank | KAttr _ => false | _ => true end = true ->
    fst (open_line descend ind l k) = [] ->
    pend_carriable (snd (open_line descend ind l k)) = true.
Proof.
  intros descend ind l k Hk Hempty. destruct k; try discriminate Hk;
    cbn [open_line open_kind] in Hempty |- *;
    unfold open_quote, open_list, open_foot, open_ref, open_fence,
      open_text in *;
    repeat (match goal with
            | |- context [match ?x with _ => _ end] => destruct x
            end);
    cbn [fst snd pend_carriable] in Hempty |- *;
    try reflexivity; try discriminate.
Qed.

(* The step that keeps the wrapper alive keeps it carriable: a state that
   emits nothing has not yet handed the pending set anywhere, and what it
   became can still carry it.  Every close emits, so the cases that would
   lose the set are the ones the hypothesis rules out. *)
Local Lemma step_empty_carriable :
  forall l st, pend_ready st l = true -> fst (step l st) = [] ->
  pend_carriable (snd (step l st)) = true.
Proof.
  intros l st Hready Hempty. unfold step in *.
  destruct st as [cur|lvl cur|f fnd crng cop acc|qrng done inner|dlen dcls drng dop ddone dinner
                 |ls ldone linner|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
                 |frng find flbl fdone finner|trng trows tcap|ppend pspecs pinner|krng klbl ksrc kinner];
    cbn [pend_ready] in Hready; try discriminate Hready;
    cbn [step_fuel] in Hempty |- *;
    unfold close_reopen, open_quote, open_list, open_foot, open_ref,
           open_fence, open_attr, open_text, key_result in *;
    repeat (match goal with
            | |- context [match ?x with _ => _ end] => destruct x eqn:?
            end);
    cbn [fst snd pend_carriable finish app open_line open_kind]
      in Hempty |- *;
    try reflexivity; try discriminate.
  apply open_line_carriable; [exact Hready | exact Hempty].
Qed.

(* Pending attributes are invisible to the fold except at its head: the
   run under the wrapper is the run without it, decorated.  The side
   condition is on the first line only, because after it the wrapper
   either is gone or sits on a carriable state. *)
Local Lemma parse_lines_pend :
  forall ls pend specs st,
    match ls with [] => True | l :: _ => pend_ready st l = true end ->
    parse_lines ls (PPend pend specs st) = decorate_head pend (parse_lines ls st).
Proof.
  induction ls as [|l rest IH]; intros pend specs st H; [reflexivity|].
  cbn [parse_lines]. rewrite (step_pend_pass l pend specs st H).
  destruct (step l st) as [bs st'] eqn:Es. cbn [pend_result]; nopos.
  destruct bs as [|b bs'].
  - cbn [app]. apply IH.
    destruct rest as [|l2 rest']; [exact I|].
    apply pend_carriable_ready.
    pose proof (step_empty_carriable l st H) as Hc.
    rewrite Es in Hc. cbn [fst snd] in Hc. exact (Hc eq_refl).
  - cbn [app]. rewrite decorate_head_cons_app. reflexivity.
Qed.

(* A finished spec refuses the line and resolves to the pending set over
   an idle state, on the same line. *)
Local Lemma step_attr_done :
  forall l pend specs range ind ap slices, ap_done ap = true ->
  step l (PAttr pend specs range ind ap slices)
  = step l (PPend (Attr.merge (ap_attrs ap) pend)
              (specs ++ [extent_span range])%list (PPara [])).
Proof.
  intros l pend specs range ind ap slices H. unfold step at 1.
  cbn [step_fuel pstate_depth]. rewrite H.
  rewrite step_fuel_enough by (cbn [pstate_depth]; lia). reflexivity.
Qed.

Local Lemma parse_lines_attr_done :
  forall ls pend specs range ind ap slices, ap_done ap = true ->
  parse_lines ls (PAttr pend specs range ind ap slices)
  = parse_lines ls (PPend (Attr.merge (ap_attrs ap) pend)
                      (specs ++ [extent_span range])%list (PPara [])).
Proof.
  intros [|l rest] pend specs range ind ap slices H;
    [cbn [parse_lines finish decorate_head]; rewrite H; reflexivity|].
  cbn [parse_lines].
  rewrite (step_attr_done l pend specs range ind ap slices H). reflexivity.
Qed.

(* A finished spec followed by another spec line: the pending set takes
   the first spec's attributes, and the second spec opens over it. *)
Local Lemma step_attr_merge :
  forall l ap' pend specs range ind ap slices,
    battrs = true -> ap_done ap = true -> classify l = KAttr ap' ->
    step l (PAttr pend specs range ind ap slices)
    = ([], PAttr (Attr.merge (ap_attrs ap) pend) (specs ++ [extent_span range])%list
             (open_extent l (indent_of l)) (indent_of l) ap'
             [remember_line (drop_leading_ws l)]).
Proof.
  intros l ap' pend specs range ind ap slices Hattrs Hdone Hl.
  rewrite step_attr_done by exact Hdone.
  unfold step. cbn [step_fuel pstate_depth]. rewrite Hl. cbn [is_idle].
  unfold open_attr. rewrite Hattrs. reflexivity.
Qed.

(* A line holding a complete spec and nothing else. *)
Definition attr_line (l : string) (ap : aparser) : Prop :=
  classify l = KAttr ap /\ ap_done ap = true.

Local Lemma parse_lines_attr_run :
  forall lines aps ls pend specs range ind ap slices,
    battrs = true -> ap_done ap = true ->
    Forall2 attr_line lines aps ->
    match ls with [] => True | l :: _ => pend_ready (PPara []) l = true end ->
    parse_lines (lines ++ ls)%list (PAttr pend specs range ind ap slices)
    = decorate_head
        (fold_left (fun acc a => Attr.merge (ap_attrs a) acc) aps
           (Attr.merge (ap_attrs ap) pend))
        (parse_lines ls (PPara [])).
Proof.
  intros lines aps ls pend specs range ind ap slices Hattrs Hdone H.
  revert pend specs range ind ap slices Hdone.
  induction H as [|l a lines aps [Hl Ha] Hrest IH];
    intros pend specs range ind ap slices Hdone Hready.
  - cbn [app fold_left].
    rewrite (parse_lines_attr_done _ _ _ _ _ _ _ Hdone).
    apply parse_lines_pend, Hready.
  - cbn [app fold_left].
    rewrite (parse_lines_step _ _ _ _ _
               (step_attr_merge l a pend specs range ind ap slices Hattrs Hdone Hl)).
    cbn [app]. apply IH; assumption.
Qed.

(** BA3: a run of complete specs, one per line, puts their attributes on
    the block after them, merged in order (`Attr.merge`: classes
    accumulate, a later value for a key replaces an earlier one).  The
    side condition is the one line the run can still claim for itself: a
    blank drops it, and a further spec would extend it. *)
Theorem attr_accumulate :
  forall l ap lines aps ls,
    battrs = true -> attr_line l ap -> Forall2 attr_line lines aps ->
    match ls with [] => True | l2 :: _ => pend_ready (PPara []) l2 = true end ->
    parse_lines (l :: lines ++ ls)%list (PPara [])
    = decorate_head
        (fold_left (fun acc a => Attr.merge (ap_attrs a) acc) aps
           (Attr.merge (ap_attrs ap) []))
        (parse_lines ls (PPara [])).
Proof.
  intros l ap lines aps ls Hattrs [Hcl Hdone] H Hready.
  cbn [parse_lines]. rewrite (step_attr_open l ap Hcl).
  unfold open_attr. rewrite Hattrs. cbn [fst snd app].
  exact (parse_lines_attr_run _ _ _ _ _ _ _ _ _ Hattrs Hdone H Hready).
Qed.

(** Uniformity for a block attribute line: a document preceded by a
    complete spec parses as that document with the spec's attributes on
    its first block.  The one-spec case of `attr_accumulate`. *)
Theorem attr_uniformity :
  forall l ap ls,
    battrs = true -> classify l = KAttr ap -> ap_done ap = true ->
    match ls with [] => True | l2 :: _ => pend_ready (PPara []) l2 = true end ->
    parse_lines (l :: ls) (PPara [])
    = decorate_head (Attr.merge (ap_attrs ap) []) (parse_lines ls (PPara [])).
Proof.
  intros l ap ls Hattrs Hcl Hdone Hready.
  exact (attr_accumulate l ap [] [] ls Hattrs (conj Hcl Hdone) (Forall2_nil _) Hready).
Qed.

(* An unfinished spec takes a line indented past its opener, and stays
   open while the line leaves it neither done nor failed. *)
Local Lemma step_attr_cont :
  forall l pend specs range ind ap slices,
    ap_done ap = false -> ind < indent_of l -> ap_failed (attr_feed l ap) = false ->
    step l (PAttr pend specs range ind ap slices)
    = ([], PAttr pend specs (touch_extent range) ind (attr_feed l ap)
             (push_text l slices)).
Proof.
  intros l pend specs range ind ap slices Hd Hi Hf. unfold step.
  cbn [step_fuel]. rewrite Hd. cbn [Nat.add].
  replace (Nat.ltb ind (indent_of l)) with true by (symmetry; apply Nat.ltb_lt, Hi).
  rewrite Hf. reflexivity.
Qed.

Local Lemma parse_lines_attr_cont :
  forall ls2 ls pend specs range ind ap slices,
    spec_runs ap ls2 = true -> Forall (fun l => ind < indent_of l) ls2 ->
    match ls with [] => True | l :: _ => pend_ready (PPara []) l = true end ->
    parse_lines (ls2 ++ ls)%list (PAttr pend specs range ind ap slices)
    = decorate_head (Attr.merge (ap_attrs (feed_lines ls2 ap)) pend)
        (parse_lines ls (PPara [])).
Proof.
  induction ls2 as [|l ls2 IH]; intros ls pend specs range ind ap slices Hr Hi Hready.
  - cbn [spec_runs] in Hr. cbn [app feed_lines fold_left].
    rewrite (parse_lines_attr_done _ _ _ _ _ _ _ Hr).
    apply parse_lines_pend, Hready.
  - cbn [spec_runs] in Hr. apply andb_true_iff in Hr as [Hr Hrest].
    apply andb_true_iff in Hr as [Hd Hf]. apply negb_true_iff in Hd, Hf.
    inversion Hi as [|? ? Hl Hi']; subst.
    cbn [app]. rewrite (parse_lines_step _ _ _ _ _
                          (step_attr_cont l pend specs range ind ap slices Hd Hl Hf)).
    cbn [app]. rewrite (IH ls pend specs _ ind _ _ Hrest Hi' Hready). reflexivity.
Qed.

(* A spec's lines joined onto its first, a space for each line break. *)
Definition attr_join (l : string) (ls : list string) : string := l ++ join_tail ls.

(** BA2: a spec that does not fit on one line continues on lines
    indented past its opener, and parses as the same spec written on one
    line.  Each continuation line has content (`blank_to_eol` is the
    machine's own blank test); a blank one would let a spec that closed
    on the line before it drop its attributes. *)
Theorem attr_continuation :
  forall l1 ap1 ls2 apJ ls,
    battrs = true -> classify l1 = KAttr ap1 ->
    Forall (fun l => indent_of l1 < indent_of l /\
                     blank_to_eol (drop_leading_ws l) = false) ls2 ->
    attr_line (attr_join l1 ls2) apJ ->
    match ls with [] => True | l :: _ => pend_ready (PPara []) l = true end ->
    parse_lines (l1 :: ls2 ++ ls)%list (PPara [])
    = parse_lines (attr_join l1 ls2 :: ls) (PPara []).
Proof.
  intros l1 ap1 ls2 apJ ls Hattrs H1 Hls [HJ HdJ] Hready.
  destruct (attr_open_inv l1 ap1 (classify_attr_open l1 ap1 H1))
    as (b1 & r1 & Ed1 & Ef1 & Hf1 & _).
  destruct (attr_open_inv _ apJ (classify_attr_open _ apJ HJ))
    as (bJ & rJ & EdJ & EfJ & _ & HbJ).
  unfold attr_join in EdJ.
  rewrite drop_leading_ws_app_nonblank, Ed1 in EdJ by (rewrite Ed1; discriminate).
  cbn [append] in EdJ. injection EdJ as <-.
  destruct (joined_spec_runs b1 ls2 ap1 r1 apJ rJ
              (Forall_impl _ (fun l H => proj2 H) Hls) Ef1 Hf1 EfJ HdJ (HbJ HdJ))
    as [Hruns Hattrs'].
  rewrite (attr_uniformity _ apJ ls Hattrs HJ HdJ Hready).
  cbn [parse_lines]. rewrite (step_attr_open l1 ap1 H1).
  unfold open_attr. rewrite Hattrs. cbn [fst snd app].
  rewrite (parse_lines_attr_cont ls2 ls [] [] _ _ ap1 _ Hruns
             (Forall_impl _ (fun l H => proj1 H) Hls) Hready).
  rewrite Hattrs'. reflexivity.
Qed.

(** BA2, the "must": a line not indented past the opener ends an
    unfinished spec, which becomes a paragraph of its lines, read with
    attributes off. *)
Theorem attr_unindented :
  forall l1 ap l2,
    battrs = true -> classify l1 = KAttr ap -> ap_done ap = false ->
    is_blank l2 = false -> indent_of l2 <= indent_of l1 ->
    bunderline_of l2 = None -> binterrupt (classify l2) = false ->
    parse_lines [l1; l2] (PPara [])
    = [mk (Para (para_inlines_off 1 [drop_leading_ws l1; drop_leading_ws l2]))].
Proof.
  intros l1 ap l2 Hattrs H1 Hd Hb Hi Hu Hint.
  cbn [parse_lines]. rewrite (step_attr_open l1 ap H1).
  unfold open_attr. rewrite Hattrs. cbn [fst snd app].
  unfold step at 1. cbn [step_fuel]. rewrite Hd. cbn [Nat.add].
  replace (Nat.ltb (indent_of l1) (indent_of l2)) with false
    by (symmetry; apply Nat.ltb_ge, Hi).
  rewrite Hb, step_fuel_enough by (cbn [pstate_depth para_recover]; lia).
  unfold para_recover. cbn [List.length Nat.add].
  assert (Hs : step l2 (PParaOff 1 [remember_line (drop_leading_ws l1)])
               = ([], PParaOff 1 [remember_line (drop_leading_ws l2);
                                  remember_line (drop_leading_ws l1)])).
  { unfold step. cbn [step_fuel]. rewrite Hu.
    destruct (classify l2) eqn:Ek;
      try (rewrite (classify_kblank_blank l2 Ek) in Hb; discriminate);
      cbn [binterrupt] in Hint |- *; rewrite ?Hint; reflexivity. }
  rewrite Hs. cbn [pend_result app parse_lines finish]. nopos. sem_para.
  reflexivity.
Qed.

(* A key passes every line that pending attributes can pass.  Reusing
   that invariant lets a completed child prefix admit any suffix. *)
Local Lemma pend_ready_key_pass :
  forall st l, pend_ready st l = true ->
    (is_blank l && is_idle st)%bool = false.
Proof.
  intros [cur| | | | | | | | | | | |] l H;
    cbn [is_idle]; try apply andb_false_r.
  destruct cur; [|apply andb_false_r]. rewrite andb_true_r.
  destruct (is_blank l) eqn:E; [|reflexivity].
  cbn [pend_ready] in H. rewrite (classify_blank l E) in H. discriminate.
Qed.

(* Pending attributes around a live child are safe too: the key wraps
   the attributed node after the pending wrapper has decorated it. *)
Local Definition key_carriable (st : pstate) : bool :=
  match st with
  | PPend _ _ inner => pend_carriable inner
  | _ => pend_carriable st
  end.

Local Lemma key_carriable_pass :
  forall st l, key_carriable st = true ->
    (is_blank l && is_idle st)%bool = false.
Proof.
  intros st l H. destruct st; try apply andb_false_r.
  apply pend_ready_key_pass, pend_carriable_ready, H.
Qed.

Local Lemma step_empty_key_carriable :
  forall l st, key_carriable st = true -> fst (step l st) = [] ->
    key_carriable (snd (step l st)) = true.
Proof.
  intros l st H Hempty.
  assert (Hp : forall st, pend_carriable st = true -> key_carriable st = true).
  { intros st0 H0. destruct st0; try exact H0. discriminate H0. }
  destruct st as [cur|lvl cur|f fnd crng cop acc|qrng done inner|dlen dcls drng dop ddone dinner
                 |ls ldone linner|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
                 |frng find flbl fdone finner|trng trows tcap|ppend pspecs pinner|krng klbl ksrc kinner];
    try (apply Hp, (step_empty_carriable l _ (pend_carriable_ready _ l H)), Hempty).
  cbn [key_carriable] in H.
  pose proof (pend_carriable_ready pinner l H) as Hr.
  rewrite (step_pend_pass l ppend pspecs pinner Hr) in Hempty |- *.
  destruct (step l pinner) as [bs st'] eqn:E. destruct bs as [|b bs].
  - cbn [pend_result snd key_carriable]; nopos.
    pose proof (step_empty_carriable l pinner Hr) as Hc.
    rewrite E in Hc. exact (Hc eq_refl).
  - destruct b as [p a x]. destruct x; discriminate Hempty.
Qed.

Local Lemma parse_lines_key_carriable :
  forall ls range lbl src st, key_carriable st = true ->
    parse_lines ls (PKey range lbl src st) = key_close (extent_start range) lbl src (parse_lines ls st).
Proof.
  induction ls as [|l rest IH]; intros range lbl src st H; [reflexivity|].
  cbn [parse_lines].
  rewrite (step_key_pass l range lbl src st (key_carriable_pass st l H)).
  destruct (step l st) as [bs st'] eqn:E. cbn [key_result].
  destruct bs as [|b bs].
  - cbn [app]. apply (IH (touch_extent range)).
    pose proof (step_empty_key_carriable l st H) as Hc.
    rewrite E in Hc. exact (Hc eq_refl).
  - reflexivity.
Qed.

(* Until the first emission, no blank may retract the key.  If the
   prefix emits nothing, its final state must carry the wrapper through
   any suffix.  In particular, a complete attribute line alone fails,
   while that line followed by its child can pass. *)
Fixpoint key_content_ok (ls : list string) (st : pstate) : bool :=
  match ls with
  | [] => key_carriable st
  | l :: rest =>
      negb (is_blank l && is_idle st) &&
      let '(bs, st') := step l st in
      match bs with [] => key_content_ok rest st' | _ => true end
  end.

Lemma parse_lines_key_content :
  forall ls tail range lbl src st, key_content_ok ls st = true ->
    parse_lines (ls ++ tail) (PKey range lbl src st)
    = key_close (extent_start range) lbl src (parse_lines (ls ++ tail) st).
Proof.
  induction ls as [|l rest IH]; intros tail range lbl src st H.
  - apply parse_lines_key_carriable, H.
  - cbn [key_content_ok] in H. apply andb_true_iff in H as [Hr H].
    apply negb_true_iff in Hr. cbn [app parse_lines].
    rewrite (step_key_pass l range lbl src st Hr).
    destruct (step l st) as [bs st'] eqn:E. cbn [key_result] in *.
    destruct bs as [|b bs]; [cbn [app]; apply (IH _ (touch_extent range)), H|reflexivity].
Qed.

End WithTable.

(* The div boundary, pinned at djot's table.  The side condition cannot
   be "no top-level content line closes the div": here the closing line
   is a list-item continuation, and the div takes it anyway.  djot.js
   agrees with the left-hand side. *)
Example div_indented_close_differs :
  let content := ["- a"; "  :::"; "  b"]%list in
  parse_lines (div_fence :: content ++ [div_fence])%list (PPara [])
  <> [mk (Div EmptyString (parse_lines content (PPara [])))].
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
  = [mk (Div EmptyString (parse_lines content (PPara [])))].
Proof. reflexivity. Qed.

Example div_code_fence_accepted :
  run_div_open 3 ["```"; ":::"; "```"]%list (PPara []) = true.
Proof. reflexivity. Qed.

(* A fence still open at the end swallows the closer, which is what the
   `in_fence` hypothesis rules out. *)
Example div_unclosed_fence_differs :
  let content := ["```"]%list in
  parse_lines (div_fence :: content ++ [div_fence])%list (PPara [])
  <> [mk (Div EmptyString (parse_lines content (PPara [])))].
Proof. vm_compute. discriminate. Qed.

(*
Prefix determinism
------------------

The spec's block-level promise: "blocks can be parsed line by line ...
the contribution a line makes to block-level structure never depends on
a future line."  `Line.v` gives each line its kind; these say the fold
over those kinds commits as it goes.

`parse_lines` is a fold, so the property holds by construction, and the
three statements below are one rewrite each off `parse_lines_app_run`.
They state what the construction guarantees, so a reader need not
reconstruct it.

Stated at the line level, which is where the parser is incremental.
Lifting to `parse_doc` would need `split_lines` to distribute over
concatenation, and it does so only when the prefix ends at a newline:
`split_lines "a" ++ split_lines "b"` is `["a"; "b"]` while
`split_lines "ab"` is `["ab"]`.

A pipe table's separator turns the row before it into a header, but
that happens inside the open table state (`Step.table_fold`) before
anything is emitted, so the statements are over full parse results
rather than tree shape.
*)

(* Back into the family: the determinism theorems below are about any
   admissible table, like the fold equations above them. *)
Section WithTableDet.
Context {T : dtable}.
Context {K : bconfig}.

 (** What a line prefix has already emitted.  A fold over the prefix, so
    "computable line by line" is definitional. *)
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

(*
Replacing a span of lines
-------------------------

An editor holding source text splits a document as `pre ++ mid ++ post`
and replaces `mid`.  The three theorems above are what says it need not
look at `pre` or `post` again, and `parse_span` puts them in the form
that says it: three summands, one per region.
*)

(** The parse of a three-way split, region by region.  `pre` contributes
    `committed pre st` and a state; `mid` contributes `committed mid` from
    that state and a state of its own; `post` is parsed from the second.
    Every dependence between regions is one `pstate`. *)
Lemma parse_span :
  forall pre mid post st,
    parse_lines (pre ++ mid ++ post)%list st
    = (committed pre st
       ++ committed mid (snd (run_lines pre st))
       ++ parse_lines post (snd (run_lines mid (snd (run_lines pre st)))))%list.
Proof.
  intros pre mid post st. rewrite prefix_determinism, prefix_determinism.
  reflexivity.
Qed.

(** Reparsing only the replacement.  If the new lines leave the parser in
    the state the old ones did, the edited document's parse is the old
    first summand, the new middle, and the old third summand -- the two
    conclusions share `parse_lines post ...` as a subterm, so `post` is
    not merely equal after the edit, it is never reached.

    The hypothesis is the whole cost of the optimization, and it is
    decidable by running `new` from the saved state and comparing.  When
    it fails the theorem says nothing: parsing has to continue into `post`
    until the two states agree again, and nothing here promises they ever
    do. *)
Theorem reparse_only_new :
  forall pre old new post st,
    snd (run_lines new (snd (run_lines pre st)))
      = snd (run_lines old (snd (run_lines pre st))) ->
    parse_lines (pre ++ old ++ post)%list st
      = (committed pre st
         ++ committed old (snd (run_lines pre st))
         ++ parse_lines post (snd (run_lines old (snd (run_lines pre st)))))%list
    /\ parse_lines (pre ++ new ++ post)%list st
      = (committed pre st
         ++ committed new (snd (run_lines pre st))
         ++ parse_lines post (snd (run_lines old (snd (run_lines pre st)))))%list.
Proof.
  intros pre old new post st H. split; [apply parse_span|].
  rewrite parse_span, H. reflexivity.
Qed.

(** The check an implementation actually runs.  A replaced span that both
    starts and ends at a block boundary leaves the parser idle, and `PPara
    []` is a closed term, so the hypothesis above is two comparisons
    against a constant rather than an equality between two runs. *)
Corollary reparse_only_new_idle :
  forall pre old new post st,
    snd (run_lines new (snd (run_lines pre st))) = PPara [] ->
    snd (run_lines old (snd (run_lines pre st))) = PPara [] ->
    parse_lines (pre ++ new ++ post)%list st
    = (committed pre st
       ++ committed new (snd (run_lines pre st))
       ++ parse_lines post (PPara []))%list.
Proof.
  intros pre old new post st Hnew Hold.
  destruct (reparse_only_new pre old new post st
              ltac:(rewrite Hnew, Hold; reflexivity)) as [_ Hedit].
  rewrite Hedit, Hold. reflexivity.
Qed.

Local Lemma app_cons_app :
  forall {A : Type} (xs : list A) x ys tail,
    ((xs ++ (x :: ys)) ++ tail)%list =
    (xs ++ (x :: (ys ++ tail)))%list.
Proof.
  intros A xs x ys tail. induction xs as [|a xs IH];
    [reflexivity|cbn; rewrite IH; reflexivity].
Qed.

End WithTableDet.

(* Why the state hypothesis of `reparse_only_new` is not decoration.  Both
   replacements are one line and both are paragraphs at top level, but the
   second opens a code fence, so it leaves a state the first does not and
   the line after the edit stops being a paragraph of its own.  An
   implementation that reused the tail here would be wrong. *)
Example reparse_state_matters :
  let pre := ["a"; ""]%list in
  let post := ["c"]%list in
  parse_lines (pre ++ ["b"] ++ post)%list (PPara [])
  <> parse_lines (pre ++ ["```"] ++ post)%list (PPara []).
Proof. vm_compute. discriminate. Qed.

Example reparse_state_matters_states :
  snd (run_lines ["```"]%list (PPara [])) <> snd (run_lines ["b"]%list (PPara [])).
Proof. vm_compute. discriminate. Qed.
