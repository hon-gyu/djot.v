(* Roundtrip for the paragraph fragment:

     parse_doc (render_djot (doc_of_paras lss)) = doc_of_paras lss

   for canonical paragraph line-lists (nonblank, newline-free lines; last
   line of each paragraph carries no trailing whitespace).  This is the
   Phase 1 roundtrip theorem in miniature; it grows with the parser. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Ast Parser Render Wf.
Import ListNotations.

Local Open Scope string_scope.

(*
String append and reverse
=========================
*)

Lemma append_empty_r : forall s, s ++ "" = s.
Proof.
  induction s as [|c s IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma append_assoc : forall a b c, (a ++ b) ++ c = a ++ (b ++ c).
Proof.
  induction a as [|x a IH]; intros; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma rev_aux_app :
  forall s acc, rev_string_aux s acc = rev_string s ++ acc.
Proof.
  induction s as [|c s IH]; intros acc; simpl.
  - reflexivity.
  - rewrite IH. unfold rev_string. simpl. rewrite (IH (String c "")).
    rewrite append_assoc. reflexivity.
Qed.

Lemma rev_string_cons :
  forall c s, rev_string (String c s) = rev_string s ++ String c "".
Proof.
  intros c s. unfold rev_string. simpl. apply rev_aux_app.
Qed.

Lemma rev_string_app :
  forall a b, rev_string (a ++ b) = rev_string b ++ rev_string a.
Proof.
  induction a as [|c a IH]; intros b; simpl.
  - rewrite append_empty_r. reflexivity.
  - rewrite !rev_string_cons, IH, append_assoc. reflexivity.
Qed.

Lemma rev_string_involutive : forall s, rev_string (rev_string s) = s.
Proof.
  induction s as [|c s IH].
  - reflexivity.
  - rewrite rev_string_cons, rev_string_app, IH. reflexivity.
Qed.

(*
Splitting rendered lines
========================
*)

Lemma split_aux_no_nl :
  forall x cur, no_nl x = true ->
  split_lines_aux x cur =
  match rev_string_aux x cur with
  | EmptyString => []
  | String _ _ => [rev_string (rev_string_aux x cur)]
  end.
Proof.
  induction x as [|c x IH]; intros cur H; simpl.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hc Hx].
    apply negb_true_iff in Hc. rewrite Hc.
    apply IH. exact Hx.
Qed.

Lemma split_lines_single :
  forall x, no_nl x = true -> x <> EmptyString -> split_lines x = [x].
Proof.
  intros x H Hne. unfold split_lines.
  rewrite (split_aux_no_nl x EmptyString H).
  rewrite rev_aux_app, append_empty_r.
  destruct (rev_string x) eqn:E.
  - exfalso. apply Hne.
    apply (f_equal String.length) in E. rewrite rev_length in E.
    destruct x; [reflexivity | discriminate].
  - rewrite <- E, rev_string_involutive. reflexivity.
Qed.

Lemma split_lines_line :
  forall x r, no_nl x = true ->
  split_lines (x ++ String "010"%char r) = x :: split_lines r.
Proof.
  intros x r H. unfold split_lines.
  (* aux with a general accumulator *)
  assert (Haux : forall x cur, no_nl x = true ->
    split_lines_aux (x ++ String "010"%char r) cur =
    rev_string (rev_string_aux x cur) :: split_lines_aux r EmptyString).
  { induction x0 as [|c x0 IH]; intros cur Hx; simpl.
    - reflexivity.
    - simpl in Hx. apply andb_true_iff in Hx as [Hc Hx].
      apply negb_true_iff in Hc. rewrite Hc.
      apply IH. exact Hx. }
  rewrite (Haux x EmptyString H).
  rewrite rev_aux_app, append_empty_r, rev_string_involutive.
  reflexivity.
Qed.

Lemma split_lines_cons_nl :
  forall r, split_lines (String "010"%char r) = EmptyString :: split_lines r.
Proof. reflexivity. Qed.

(*
Rendered paragraphs split back into their lines
===============================================
*)

Lemma line_ok_no_nl : forall l, line_ok l = true -> no_nl l = true.
Proof.
  intros l H. unfold line_ok in H. apply andb_true_iff in H as [_ H]. exact H.
Qed.

Lemma line_ok_nonblank : forall l, line_ok l = true -> is_blank l = false.
Proof.
  intros l H. unfold line_ok in H. apply andb_true_iff in H as [H _].
  apply negb_true_iff in H. exact H.
Qed.

Lemma line_ok_nonempty : forall l, line_ok l = true -> l <> EmptyString.
Proof.
  intros l H E. subst. discriminate (line_ok_nonblank _ H).
Qed.

Lemma split_join_last :
  forall a ls, forallb line_ok (a :: ls) = true ->
  split_lines (String.concat nl (a :: ls)) = a :: ls.
Proof.
  intros a ls. revert a.
  induction ls as [|b ls IH]; intros a H; simpl in H;
    apply andb_true_iff in H as [Ha Hrest].
  - simpl. apply split_lines_single.
    + apply line_ok_no_nl; exact Ha.
    + apply line_ok_nonempty; exact Ha.
  - change (String.concat nl (a :: b :: ls))
      with (a ++ nl ++ String.concat nl (b :: ls)).
    change (a ++ nl ++ String.concat nl (b :: ls))
      with (a ++ String "010"%char (String.concat nl (b :: ls))).
    rewrite split_lines_line by (apply line_ok_no_nl; exact Ha).
    f_equal. apply IH. exact Hrest.
Qed.

Lemma split_join_para :
  forall a ls r, forallb line_ok (a :: ls) = true ->
  split_lines (String.concat nl (a :: ls) ++ String "010"%char r) =
  ((a :: ls) ++ split_lines r)%list.
Proof.
  intros a ls. revert a.
  induction ls as [|b ls IH]; intros a r H; simpl in H;
    apply andb_true_iff in H as [Ha Hrest].
  - simpl. apply split_lines_line. apply line_ok_no_nl; exact Ha.
  - change (String.concat nl (a :: b :: ls))
      with (a ++ nl ++ String.concat nl (b :: ls)).
    change (a ++ nl ++ String.concat nl (b :: ls))
      with (a ++ String "010"%char (String.concat nl (b :: ls))).
    rewrite append_assoc. simpl.
    rewrite split_lines_line by (apply line_ok_no_nl; exact Ha).
    simpl. f_equal. apply IH. exact Hrest.
Qed.

(*
Whole documents: split, with blank separator lines
==================================================
*)

Fixpoint sep_lines (lss : list (list string)) : list string :=
  match lss with
  | [] => []
  | [ls] => ls
  | ls :: rest => (ls ++ EmptyString :: sep_lines rest)%list
  end.

Lemma para_ok_lines : forall ls, para_ok ls = true -> forallb line_ok ls = true.
Proof.
  intros ls H. destruct ls; [discriminate|].
  unfold para_ok in H. apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma split_render :
  forall lss, forallb para_ok lss = true ->
  split_lines (render_paras lss) = sep_lines lss.
Proof.
  induction lss as [|ls rest IH]; intros H; simpl in H.
  - reflexivity.
  - apply andb_true_iff in H as [Hls Hrest].
    destruct ls as [|a ls']; [discriminate|].
    apply para_ok_lines in Hls.
    destruct rest as [|ls2 rest'].
    + simpl. apply split_join_last. exact Hls.
    + change (render_paras ((a :: ls') :: ls2 :: rest'))
        with (String.concat nl (a :: ls')
              ++ (nl ++ nl) ++ render_paras (ls2 :: rest')).
      change ((nl ++ nl) ++ render_paras (ls2 :: rest'))
        with (String "010"%char
                (String "010"%char (render_paras (ls2 :: rest')))).
      rewrite split_join_para by exact Hls.
      rewrite split_lines_cons_nl.
      rewrite IH by exact Hrest.
      reflexivity.
Qed.

(*
Grouping the split lines back into paragraphs
=============================================
*)

Lemma group_paras_seed :
  forall ls tail cur,
    forallb nonblank ls = true ->
    group_paras ((ls ++ tail)%list) cur = group_paras tail ((rev ls ++ cur)%list).
Proof.
  induction ls as [|l ls IH]; intros tail cur H; simpl in H |- *.
  - reflexivity.
  - apply andb_true_iff in H as [Hl Hls].
    unfold nonblank in Hl. apply negb_true_iff in Hl.
    rewrite Hl. rewrite IH by exact Hls.
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma group_paras_nil_cons :
  forall c cur',
    group_paras [] (c :: cur') = [mk (Para (para_inlines (rev (c :: cur'))))].
Proof. reflexivity. Qed.

Lemma group_paras_blank_cons :
  forall l rest c cur',
    is_blank l = true ->
    group_paras (l :: rest) (c :: cur') =
    mk (Para (para_inlines (rev (c :: cur')))) :: group_paras rest [].
Proof.
  intros l rest c cur' H. cbn [group_paras]. rewrite H. reflexivity.
Qed.

Lemma forallb_line_ok_nonblank :
  forall ls, forallb line_ok ls = true -> forallb nonblank ls = true.
Proof.
  induction ls as [|l ls IH]; intros H; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H as [Hl Hls].
    unfold nonblank. rewrite (line_ok_nonblank _ Hl). simpl.
    apply IH. exact Hls.
Qed.

Lemma rev_cons_shape :
  forall {A : Type} (a : A) (ls : list A),
  exists c cur', rev (a :: ls) = c :: cur'.
Proof.
  intros A a ls.
  destruct (rev (a :: ls)) as [|c cur'] eqn:E.
  - exfalso. apply (f_equal (@length A)) in E.
    rewrite length_rev in E. discriminate.
  - eauto.
Qed.

Lemma group_sep :
  forall lss, forallb para_ok lss = true ->
  group_paras (sep_lines lss) [] =
  map (fun ls => mk (Para (para_inlines ls))) lss.
Proof.
  induction lss as [|ls rest IH]; intros H; simpl in H.
  - reflexivity.
  - apply andb_true_iff in H as [Hls Hrest].
    destruct ls as [|a ls']; [discriminate|].
    pose proof (para_ok_lines _ Hls) as Hlok.
    pose proof (forallb_line_ok_nonblank _ Hlok) as Hnb.
    destruct (rev_cons_shape a ls') as [c [cur' Erev]].
    destruct rest as [|ls2 rest'].
    + cbn [sep_lines].
      rewrite <- (app_nil_r (a :: ls')) at 1.
      rewrite group_paras_seed by exact Hnb.
      rewrite app_nil_r, Erev, group_paras_nil_cons.
      rewrite <- Erev, rev_involutive. reflexivity.
    + cbn [sep_lines map].
      rewrite group_paras_seed by exact Hnb.
      rewrite app_nil_r, Erev.
      rewrite group_paras_blank_cons by reflexivity.
      rewrite <- Erev, rev_involutive.
      f_equal. apply IH. exact Hrest.
Qed.

(*
The renderer emits exactly the canonical lines
==============================================
*)

Lemma inline_lines_para :
  forall ls, para_ok ls = true ->
  inline_lines (para_inlines ls) EmptyString = ls.
Proof.
  induction ls as [|x rest IH]; intros H; [discriminate|].
  destruct rest as [|y rest'].
  - (* singleton: parser strips the (only) line; canonicality says the
       strip is the identity *)
    unfold para_ok in H. apply andb_true_iff in H as [_ Hlast].
    apply String.eqb_eq in Hlast. simpl in Hlast.
    rewrite para_inlines_one. simpl.
    rewrite Hlast. reflexivity.
  - rewrite para_inlines_cons2. simpl.
    f_equal.
    apply IH.
    unfold para_ok in H |- *.
    apply andb_true_iff in H as [Hlines Hlast].
    apply andb_true_iff; split.
    + simpl in Hlines. apply andb_true_iff in Hlines as [_ Hl]. exact Hl.
    + replace (last (y :: rest') EmptyString)
        with (last (x :: y :: rest') EmptyString) by reflexivity.
      exact Hlast.
Qed.

Lemma render_djot_paras :
  forall lss, forallb para_ok lss = true ->
  render_djot (doc_of_paras lss) = render_paras lss.
Proof.
  intros lss H.
  unfold render_djot, doc_of_paras, render_paras. simpl.
  f_equal.
  rewrite map_map. simpl.
  induction lss as [|ls rest IH]; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H as [Hls Hrest].
    rewrite (inline_lines_para _ Hls).
    f_equal. apply IH. exact Hrest.
Qed.

(*
The theorem
===========
*)

Theorem roundtrip_paragraphs :
  forall lss, forallb para_ok lss = true ->
  parse_doc (render_djot (doc_of_paras lss)) = doc_of_paras lss.
Proof.
  intros lss H.
  rewrite render_djot_paras by exact H.
  unfold parse_doc, doc_of_paras.
  f_equal.
  change (render_paras lss) with (render_paras lss).
  rewrite (split_render lss H).
  apply group_sep. exact H.
Qed.
