(* Roundtrip:  parse_doc (render_djot (doc_of_cblocks cbs)) = doc_of_cblocks cbs
   for canonical blocks (Render.v).  Exact equality — canonicality is in
   the cb_ok hypothesis, so no quotient is needed.

   Proof shape, per block: rendering emits lines; split_lines recovers
   them exactly (Strings.v split/join inversion); the parser folds them
   back via its equation lemmas (Parser.v).  Extending to a new construct
   touches the three case analyses marked below and nothing else. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Line Ast Parser Render.
Import ListNotations.

Local Open Scope string_scope.

(*
Splitting a rendered document
=============================
*)

(* Flatten per-block line lists into one line list, with a single blank
   line between blocks (and none at either end).  This is exactly what
   split_lines returns for a rendered document. *)
Fixpoint sep_lines (lss : list (list string)) : list string :=
  match lss with
  | [] => []
  | [ls] => ls
  | ls :: rest => (ls ++ EmptyString :: sep_lines rest)%list
  end.

(* What the split/join inversion needs of each block's lines: newline-free
   throughout, and a nonempty final line (split_lines drops a trailing
   empty line).  Interior lines may be blank — code content is verbatim. *)
Definition lines_ok (ls : list string) : bool :=
  nonempty ls
  && forallb no_nl ls
  && nonempty_str (last ls EmptyString).

Lemma nonempty_str_neq :
  forall s, nonempty_str s = true -> s <> EmptyString.
Proof. destruct s; [discriminate | congruence]. Qed.

(* Half one of the roundtrip: rendering then splitting recovers the
   per-block lines, laid out by sep_lines. *)
Lemma split_render :
  forall lss, forallb lines_ok lss = true ->
  split_lines (render_paras lss) = sep_lines lss.
Proof.
  induction lss as [|ls rest IH]; intros H; simpl in H.
  - reflexivity.
  - apply andb_true_iff in H as [Hls Hrest].
    unfold lines_ok in Hls.
    apply andb_true_iff in Hls as [Hls Hlast].
    apply andb_true_iff in Hls as [Hne Hnl].
    destruct ls as [|a ls']; [discriminate|].
    destruct rest as [|ls2 rest'].
    + simpl. apply split_join_last;
        [exact Hnl | apply nonempty_str_neq; exact Hlast].
    + change (render_paras ((a :: ls') :: ls2 :: rest'))
        with (String.concat nl (a :: ls')
              ++ (nl ++ nl) ++ render_paras (ls2 :: rest')).
      change ((nl ++ nl) ++ render_paras (ls2 :: rest'))
        with (String "010"%char
                (String "010"%char (render_paras (ls2 :: rest')))).
      rewrite split_join_line by exact Hnl.
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

Lemma forallb_weaken :
  forall {A : Type} (f g : A -> bool),
    (forall x, f x = true -> g x = true) ->
    forall l, forallb f l = true -> forallb g l = true.
Proof.
  intros A f g Hfg.
  induction l as [|x l IH]; intros H; simpl in *; [reflexivity|].
  apply andb_true_iff in H as [Hx Hl].
  rewrite (Hfg _ Hx). simpl. apply IH. exact Hl.
Qed.

Lemma info_no_nl :
  forall info, all_info_chars info = true -> no_nl info = true.
Proof.
  induction info as [|c info IH]; intros H; simpl in *; [reflexivity|].
  apply andb_true_iff in H as [Hc Hinfo].
  apply info_char_parts in Hc as (_ & _ & Hn).
  rewrite Hn. simpl. apply IH. exact Hinfo.
Qed.

Lemma code_ok_parts :
  forall info content, code_ok info content = true ->
  all_info_chars info = true
  /\ forallb no_nl content = true
  /\ forallb (fun l => negb (fence_close (Fence "`"%char 3 info) l)) content
     = true.
Proof.
  intros info content H. unfold code_ok in H.
  apply andb_true_iff in H as [Hinfo Hcontent].
  repeat split; [exact Hinfo | ..].
  - refine (forallb_weaken _ _ _ _ Hcontent).
    intros l Hl. apply andb_true_iff in Hl as [Hl _]. exact Hl.
  - refine (forallb_weaken _ _ _ _ Hcontent).
    intros l Hl. apply andb_true_iff in Hl as [_ Hl]. exact Hl.
Qed.

Lemma last_cons_app :
  forall {A : Type} (a : A) (l : list A) (x d : A),
    last (a :: l ++ [x])%list d = x.
Proof.
  intros A a l x d.
  change (a :: l ++ [x])%list with ((a :: l) ++ [x])%list.
  apply last_app_singleton.
Qed.

(* cb_ok is stated per construct; lines_ok is what split_render needs.
   This is the bridge between them. *)
Lemma cb_ok_lines_ok :
  forall cb, cb_ok cb = true -> lines_ok (cb_lines cb) = true.
Proof.
  intros cb H. destruct cb as [ls| |info content].
  - (* paragraph: line_ok everywhere implies the split conditions *)
    destruct ls as [|a ls']; [discriminate|].
    apply para_ok_parts in H as (_ & Hlok & _).
    unfold lines_ok. simpl cb_lines.
    rewrite (forallb_weaken _ _ line_ok_no_nl _ Hlok).
    pose proof (forallb_last _ _ _ Hlok) as Hl.
    apply line_ok_nonblank, nonblank_nonempty in Hl.
    rewrite Hl. reflexivity.
  - reflexivity.
  - (* code block: open/content/close all newline-free; close is last *)
    apply code_ok_parts in H as (Hinfo & Hnl & _).
    unfold lines_ok. cbn [cb_lines].
    apply andb_true_iff. split; [apply andb_true_iff; split|].
    + reflexivity.
    + cbn [forallb].
      unfold code_open. rewrite no_nl_append, (info_no_nl _ Hinfo).
      simpl. rewrite forallb_app, Hnl. reflexivity.
    + rewrite last_cons_app. reflexivity.
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

(* Half two: the parser folds those lines back into the intended blocks.
   Each case feeds the block's lines with a seed lemma, then closes it
   on the following blank line (or on end of input). *)
Lemma parse_sep :
  forall cbs, forallb cb_ok cbs = true ->
  parse_lines (sep_lines (map cb_lines cbs)) (PPara []) = map cb_ast cbs.
Proof.
  induction cbs as [|cb rest IH]; intros H; simpl in H; [reflexivity|].
  apply andb_true_iff in H as [Hcb Hrest].
  destruct cb as [ls| |info content].
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
  - (* code block *)
    apply code_ok_parts in Hcb as (Hinfo & _ & Hnc).
    destruct rest as [|cb2 rest'].
    + cbn [map sep_lines cb_lines].
      rewrite (parse_lines_fence_open _ _ _
                 (classify_backtick_fence info Hinfo)).
      rewrite parse_lines_fence_seed by exact Hnc.
      rewrite app_nil_r.
      rewrite parse_lines_fence_close by apply fence_close_canonical.
      rewrite rev_involutive.
      reflexivity.
    + cbn [map sep_lines cb_lines app].
      rewrite (parse_lines_fence_open _ _ _
                 (classify_backtick_fence info Hinfo)).
      rewrite <- app_assoc.
      rewrite parse_lines_fence_seed by exact Hnc.
      rewrite app_nil_r. cbn [app].
      rewrite parse_lines_fence_close by apply fence_close_canonical.
      rewrite rev_involutive.
      rewrite parse_lines_blank_nil by reflexivity.
      cbn [map cb_ast]. f_equal.
      apply IH. exact Hrest.
Qed.

(*
The renderer emits exactly the canonical lines
==============================================
*)

(* inline_lines inverts para_inlines on canonical input. *)
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

(* The rendered fence: open line, newline, content lines each with their
   newline, close line. *)
Lemma render_fence_line :
  forall open content,
    (open ++ nl ++ join_nl content ++ code_close)%string =
    String.concat nl (open :: content ++ [code_close])%list.
Proof.
  intros open content.
  rewrite concat_cons_ne by (destruct content; discriminate).
  rewrite <- join_nl_last. reflexivity.
Qed.

(* fence_block inverts to the canonical fence rendering, whether the info
   string makes it a code block or (starting with '=') a raw block.  The
   256-way destruct reduces the character match in fence_block; each
   branch closes by conversion because the fence prefix is a literal. *)
Lemma render_fence_block :
  forall info content,
    render_block_djot
      (node_contents (fence_block (Fence "`"%char 3 info) content)) =
    (code_open info ++ nl ++ join_nl content ++ code_close)%string.
Proof.
  intros info content. unfold fence_block. cbn [f_info].
  destruct info as [|c info']; [reflexivity|].
  destruct c as [[|] [|] [|] [|] [|] [|] [|] [|]]; reflexivity.
Qed.

(* Rendering a canonical document is the same as joining its cb_lines —
   this is what lets split_render/parse_sep take over. *)
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
  destruct cb as [ls| |info content].
  - destruct ls as [|a ls']; [discriminate|].
    apply para_ok_parts in Hcb as (_ & Hlok & Hlast).
    cbn [cb_ast cb_lines node_contents mk render_block_djot].
    rewrite inline_lines_para by (assumption || discriminate).
    reflexivity.
  - reflexivity.
  - cbn [cb_ast cb_lines].
    rewrite render_fence_block.
    apply render_fence_line.
Qed.

(*
The theorem
===========
*)

(** Render then parse is the identity on canonical blocks. *)
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
