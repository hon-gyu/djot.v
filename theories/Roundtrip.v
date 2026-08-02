(* Roundtrip:  parse_doc (render_djot (doc_of_cblocks cbs)) = doc_of_cblocks cbs
   for canonical blocks (Render.v).  Exact equality — canonicality is in
   the cb_ok hypothesis, so no quotient is needed.

   Proof shape, per block: rendering emits lines; split_lines recovers
   them exactly (Strings.v split/join inversion); the parser folds them
   back via its equation lemmas (Parser.v).  Extending to a new construct
   touches the three case analyses marked below and nothing else. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Line Ast Parser Render Wf.
Import ListNotations.

Local Open Scope string_scope.

(*
Splitting a rendered document
=============================
*)

Fixpoint sep_lines (lss : list (list string)) : list string :=
  match lss with
  | [] => []
  | [ls] => ls
  | ls :: rest => (ls ++ EmptyString :: sep_lines rest)%list
  end.

Definition lines_ok (ls : list string) : bool :=
  nonempty ls && forallb line_ok ls.

Lemma split_render :
  forall lss, forallb lines_ok lss = true ->
  split_lines (render_paras lss) = sep_lines lss.
Proof.
  induction lss as [|ls rest IH]; intros H; simpl in H.
  - reflexivity.
  - apply andb_true_iff in H as [Hls Hrest].
    unfold lines_ok in Hls. apply andb_true_iff in Hls as [Hne Hlok].
    destruct ls as [|a ls']; [discriminate|].
    destruct rest as [|ls2 rest'].
    + simpl. apply split_join_last. exact Hlok.
    + change (render_paras ((a :: ls') :: ls2 :: rest'))
        with (String.concat nl (a :: ls')
              ++ (nl ++ nl) ++ render_paras (ls2 :: rest')).
      change ((nl ++ nl) ++ render_paras (ls2 :: rest'))
        with (String "010"%char
                (String "010"%char (render_paras (ls2 :: rest')))).
      rewrite split_join_line by exact Hlok.
      rewrite split_lines_cons_nl.
      rewrite IH by exact Hrest.
      reflexivity.
Qed.

(*
Facts about canonical blocks
============================
*)

Lemma forallb_line_ok_nonblank :
  forall ls, forallb line_ok ls = true -> forallb nonblank ls = true.
Proof.
  induction ls as [|l ls IH]; intros H; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H as [Hl Hls].
    unfold nonblank. rewrite (line_ok_nonblank _ Hl). simpl.
    apply IH. exact Hls.
Qed.

Lemma para_ok_parts :
  forall a ls, para_ok (a :: ls) = true ->
  classify a = KText
  /\ forallb line_ok (a :: ls) = true
  /\ strip_trailing_ws (last (a :: ls) EmptyString) = last (a :: ls) EmptyString.
Proof.
  intros a ls H. unfold para_ok in H.
  apply andb_true_iff in H as [H Hlast].
  apply andb_true_iff in H as [Htext Hlok].
  repeat split.
  - apply is_text_classify. exact Htext.
  - exact Hlok.
  - apply String.eqb_eq. exact Hlast.
Qed.

Lemma cb_ok_lines_ok :
  forall cb, cb_ok cb = true -> lines_ok (cb_lines cb) = true.
Proof.
  intros cb H. destruct cb as [ls|].
  - destruct ls as [|a ls']; [discriminate|].
    apply para_ok_parts in H as (_ & Hlok & _).
    unfold lines_ok. simpl cb_lines. rewrite Hlok. reflexivity.
  - reflexivity.
Qed.

Lemma forallb_cb_lines_ok :
  forall cbs, forallb cb_ok cbs = true ->
  forallb lines_ok (map cb_lines cbs) = true.
Proof.
  induction cbs as [|cb cbs IH]; intros H; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H as [Hcb Hcbs].
    rewrite (cb_ok_lines_ok _ Hcb). simpl.
    apply IH. exact Hcbs.
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

(*
Parsing the separated lines
===========================

Case analysis over the head cblock — extend here for new constructs.
*)

Lemma parse_sep :
  forall cbs, forallb cb_ok cbs = true ->
  parse_lines (sep_lines (map cb_lines cbs)) [] = map cb_ast cbs.
Proof.
  induction cbs as [|cb rest IH]; intros H; simpl in H; [reflexivity|].
  apply andb_true_iff in H as [Hcb Hrest].
  destruct cb as [ls|].
  - (* paragraph *)
    destruct ls as [|a ls']; [discriminate|].
    apply para_ok_parts in Hcb as (Htext & Hlok & _).
    pose proof (forallb_line_ok_nonblank _ Hlok) as Hnb.
    simpl in Hnb. apply andb_true_iff in Hnb as [_ Hnb'].
    destruct (rev_cons_shape a ls') as [c [cur' Erev]].
    destruct rest as [|cb2 rest'].
    + cbn [map sep_lines cb_lines].
      rewrite <- (app_nil_r (a :: ls')) at 1.
      rewrite parse_lines_para_seed by assumption.
      rewrite Erev, parse_lines_nil_cons, <- Erev, rev_involutive.
      reflexivity.
    + cbn [map sep_lines cb_lines].
      rewrite parse_lines_para_seed by assumption.
      rewrite Erev, parse_lines_blank_cons by reflexivity.
      rewrite <- Erev, rev_involutive.
      cbn [map cb_ast]. f_equal.
      apply IH. exact Hrest.
  - (* thematic break *)
    destruct rest as [|cb2 rest'].
    + reflexivity.
    + cbn [map sep_lines cb_lines app].
      rewrite parse_lines_thematic_nil by apply classify_canonical_thematic.
      rewrite parse_lines_blank_nil by reflexivity.
      cbn [map cb_ast]. f_equal.
      apply IH. exact Hrest.
Qed.

(*
The renderer emits exactly the canonical lines
==============================================
*)

Lemma inline_lines_para :
  forall ls,
    ls <> [] ->
    forallb line_ok ls = true ->
    strip_trailing_ws (last ls EmptyString) = last ls EmptyString ->
    inline_lines (para_inlines ls) EmptyString = ls.
Proof.
  induction ls as [|x rest IH]; intros Hne Hlok Hlast; [congruence|].
  destruct rest as [|y rest'].
  - (* singleton: parser strips the (only) line; canonicality says the
       strip is the identity *)
    simpl in Hlast.
    rewrite para_inlines_one. simpl.
    rewrite Hlast. reflexivity.
  - rewrite para_inlines_cons2. simpl.
    f_equal.
    simpl in Hlok. apply andb_true_iff in Hlok as [_ Hlok].
    apply IH; [discriminate | exact Hlok |].
    replace (last (y :: rest') EmptyString)
      with (last (x :: y :: rest') EmptyString) by reflexivity.
    exact Hlast.
Qed.

Lemma render_djot_cblocks :
  forall cbs, forallb cb_ok cbs = true ->
  render_djot (doc_of_cblocks cbs) = render_paras (map cb_lines cbs).
Proof.
  intros cbs H.
  unfold render_djot, doc_of_cblocks, render_paras. simpl.
  f_equal. rewrite !map_map.
  induction cbs as [|cb rest IH]; simpl in *; [reflexivity|].
  apply andb_true_iff in H as [Hcb Hrest].
  f_equal; [| apply IH; exact Hrest].
  destruct cb as [ls|]; [| reflexivity].
  destruct ls as [|a ls']; [discriminate|].
  apply para_ok_parts in Hcb as (_ & Hlok & Hlast).
  cbn [cb_ast cb_lines node_contents mk render_block_djot].
  rewrite inline_lines_para by (assumption || discriminate).
  reflexivity.
Qed.

(*
The theorem
===========
*)

Theorem roundtrip_blocks :
  forall cbs, forallb cb_ok cbs = true ->
  parse_doc (render_djot (doc_of_cblocks cbs)) = doc_of_cblocks cbs.
Proof.
  intros cbs H.
  rewrite render_djot_cblocks by exact H.
  unfold parse_doc, doc_of_cblocks.
  f_equal.
  rewrite split_render by (apply forallb_cb_lines_ok; exact H).
  apply parse_sep. exact H.
Qed.
