(* Roundtrip:  parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs
   for canonical blocks (Render.v).  Exact equality — canonicality is in
   the cb_ok hypothesis, so no quotient is needed.

   Proof shape, per block: rendering emits lines; split_lines recovers
   them exactly (Strings.v split/join inversion); the parser folds them
   back via its equation lemmas (Parser.v).  Extending to a new construct
   touches the three case analyses marked below and nothing else. *)

From Stdlib Require Import String Ascii List Bool PeanoNat.
From DjotV Require Import Strings Line Ast Parser Document Render.
Import ListNotations.

Local Open Scope string_scope.

(*
Splitting a rendered document
=============================
*)

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

Lemma lines_ok_parts :
  forall ls, lines_ok ls = true ->
  ls <> [] /\ forallb no_nl ls = true /\ last ls EmptyString <> EmptyString.
Proof.
  intros ls H. unfold lines_ok in H.
  apply andb_true_iff in H as [H Hlast].
  apply andb_true_iff in H as [Hne Hnl].
  repeat split; [| exact Hnl | apply nonempty_str_neq; exact Hlast].
  destruct ls; [discriminate | congruence].
Qed.

(*
sep_lines is itself a well-formed line list
-------------------------------------------

Which is what lets a block quote's contents be laid out by exactly the
same function as a document's, and inverted by the same lemma. *)

Lemma sep_lines_nonempty :
  forall ls rest, lines_ok ls = true -> sep_lines (ls :: rest) <> [].
Proof.
  intros ls rest H. apply lines_ok_parts in H as (Hne & _ & _).
  destruct rest as [|ls2 rest'].
  - exact Hne.
  - cbn [sep_lines]. destruct ls; [congruence | discriminate].
Qed.

Lemma sep_lines_no_nl :
  forall lss,
    forallb lines_ok lss = true -> forallb no_nl (sep_lines lss) = true.
Proof.
  induction lss as [|ls rest IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hls Hrest].
  apply lines_ok_parts in Hls as (_ & Hnl & _).
  destruct rest as [|ls2 rest']; [exact Hnl|].
  cbn [sep_lines]. rewrite forallb_app, Hnl.
  cbn [forallb no_nl andb]. apply IH. exact Hrest.
Qed.

Lemma sep_lines_last :
  forall ls rest,
    forallb lines_ok (ls :: rest) = true ->
    last (sep_lines (ls :: rest)) EmptyString <> EmptyString.
Proof.
  intros ls rest. revert ls.
  induction rest as [|ls2 rest' IH]; intros ls H;
    cbn [forallb] in H; apply andb_true_iff in H as [Hls Hrest].
  - apply lines_ok_parts in Hls as (_ & _ & Hlast). exact Hlast.
  - cbn [sep_lines].
    rewrite last_app_nonnil by discriminate.
    rewrite last_cons_nonnil
      by (apply sep_lines_nonempty;
          cbn [forallb] in Hrest; apply andb_true_iff in Hrest as [H2 _];
          exact H2).
    apply IH. exact Hrest.
Qed.

(* Half one of the roundtrip: rendering then splitting recovers the
   per-block lines, laid out by sep_lines. *)
Lemma split_render :
  forall lss, forallb lines_ok lss = true ->
  split_lines (String.concat nl (sep_lines lss)) = sep_lines lss.
Proof.
  intros lss H. destruct lss as [|ls rest]; [reflexivity|].
  pose proof H as H0. cbn [forallb] in H0.
  apply andb_true_iff in H0 as [Hls _].
  pose proof (sep_lines_no_nl _ H) as Hnl.
  pose proof (sep_lines_last _ _ H) as Hlast.
  destruct (sep_lines (ls :: rest)) as [|a ls'] eqn:E.
  - exfalso. apply (sep_lines_nonempty ls rest Hls). exact E.
  - apply split_join_last; assumption.
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

(* Canonical lines are already flush left, so stripping leading
   whitespace off each one is the identity — the fact that lets the
   parser's now-stripping continuation rule reproduce a canonical
   cblock's lines unchanged. *)
Lemma forallb_line_ok_map_drop_leading_ws :
  forall ls, forallb line_ok ls = true -> map drop_leading_ws ls = ls.
Proof.
  induction ls as [|l ls IH]; intros H; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H as [Hl Hls].
    rewrite (line_ok_no_leading_ws _ Hl), (IH Hls). reflexivity.
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

(* Marker-prefixed lines: every construct whose rendering puts a fixed
   marker in front of each line (quotes, headings) needs exactly this —
   newline-freedom survives, and the last line is nonempty because the
   marker is. *)
Lemma no_nl_quote_line :
  forall l, no_nl (quote_line l) = no_nl l.
Proof.
  intros l. unfold quote_line, quote_open.
  rewrite no_nl_append. reflexivity.
Qed.

Lemma lines_ok_map :
  forall (f : string -> string) ls,
    (forall l, no_nl l = true -> no_nl (f l) = true) ->
    (forall l, f l <> EmptyString) ->
    ls <> [] -> forallb no_nl ls = true ->
    lines_ok (map f ls) = true.
Proof.
  intros f ls Hnlf Hnef Hne Hnl. unfold lines_ok.
  apply andb_true_iff. split; [apply andb_true_iff; split|].
  - destruct ls; [congruence | reflexivity].
  - clear Hne. induction ls as [|l ls IH]; [reflexivity|].
    cbn [forallb] in Hnl. apply andb_true_iff in Hnl as [Hl Hls].
    cbn [map forallb]. rewrite (Hnlf _ Hl). cbn [andb].
    apply IH. exact Hls.
  - rewrite (last_default (map f ls) EmptyString (f EmptyString))
      by (destruct ls; [congruence | discriminate]).
    rewrite (last_map f ls EmptyString Hne).
    apply nonempty_str_intro, Hnef.
Qed.

Lemma lines_ok_quote :
  forall ls, ls <> [] -> forallb no_nl ls = true ->
  lines_ok (map quote_line ls) = true.
Proof.
  intros ls Hne Hnl. apply lines_ok_map; try assumption.
  - intros l Hl. rewrite no_nl_quote_line. exact Hl.
  - intros l. unfold quote_line, quote_open. discriminate.
Qed.

Lemma heading_ok_parts :
  forall lvl ls, heading_ok lvl ls = true ->
  1 <= lvl /\ ls <> [] /\ forallb line_ok ls = true
  /\ strip_trailing_ws (last ls EmptyString) = last ls EmptyString.
Proof.
  intros lvl ls H. unfold heading_ok in H.
  apply andb_true_iff in H as [H Hlast].
  apply andb_true_iff in H as [H Hlok].
  apply andb_true_iff in H as [Hlvl Hne].
  repeat split.
  - apply Nat.leb_le. exact Hlvl.
  - destruct ls; [discriminate | congruence].
  - exact Hlok.
  - apply String.eqb_eq. exact Hlast.
Qed.

(* cb_ok is stated per construct; lines_ok is what split_render needs.
   This is the bridge between them.  The quote case needs the same fact
   about its contents' layout, hence the two-predicate induction. *)
Lemma cb_ok_lines_ok :
  forall cb, cb_ok cb = true -> lines_ok (cb_lines cb) = true.
Proof.
  refine (cblock_ind2
            (fun cb => cb_ok cb = true -> lines_ok (cb_lines cb) = true)
            (fun cbs => forallb cb_ok cbs = true ->
                        forallb lines_ok (map cb_lines cbs) = true)
            _ _ _ _ _ _ _).
  - (* paragraph: line_ok everywhere implies the split conditions *)
    intros ls H.
    destruct ls as [|a ls']; [discriminate|].
    apply para_ok_parts in H as (_ & Hlok & _).
    unfold lines_ok. simpl cb_lines.
    rewrite (forallb_weaken _ _ line_ok_no_nl _ Hlok).
    pose proof (forallb_last _ _ _ Hlok) as Hl.
    apply line_ok_nonblank, nonblank_nonempty in Hl.
    rewrite Hl. reflexivity.
  - reflexivity.
  - (* code block: open/content/close all newline-free; close is last *)
    intros info content H.
    apply code_ok_parts in H as (Hinfo & Hnl & _).
    unfold lines_ok. cbn [cb_lines].
    apply andb_true_iff. split; [apply andb_true_iff; split|].
    + reflexivity.
    + cbn [forallb].
      unfold code_open. rewrite no_nl_append, (info_no_nl _ Hinfo).
      simpl. rewrite forallb_app, Hnl. reflexivity.
    + rewrite last_cons_app. reflexivity.
  - (* heading: every rendered line carries the hashes, so the last one
       is nonempty whatever the text is *)
    intros lvl ls H.
    change (cb_ok (CHeading lvl ls)) with (heading_ok lvl ls) in H.
    apply heading_ok_parts in H as (Hlvl & Hne & Hlok & _).
    cbn [cb_lines]. apply lines_ok_map.
    + intros l Hl. rewrite heading_line_no_nl. exact Hl.
    + intros l. apply heading_line_nonempty. exact Hlvl.
    + exact Hne.
    + exact (forallb_weaken _ _ line_ok_no_nl _ Hlok).
  - (* quote: its contents lay out exactly as a document's would *)
    intros inner IH H.
    rewrite cb_ok_quote in H. apply andb_true_iff in H as [Hne Hok].
    rewrite cb_lines_quote.
    apply lines_ok_quote.
    + destruct inner as [|c rest]; [discriminate|].
      apply sep_lines_nonempty.
      cbn [map forallb] in IH |- *.
      specialize (IH Hok). apply andb_true_iff in IH as [Hc _]. exact Hc.
    + apply sep_lines_no_nl. apply IH. exact Hok.
  - reflexivity.
  - intros c rest Hc Hrest H.
    cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
    cbn [map forallb]. rewrite (Hc H1). cbn [andb]. apply Hrest. exact H2.
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

(* Half two, per block: feeding a canonical block's lines re-emits it and
   returns the parser to idle, whether a blank line follows (the
   in-document case) or the input ends.  Proved for a block and a list of
   blocks together, because a quote's contents are the latter. *)
Lemma parse_cblock :
  forall cb,
    (forall tail, cb_ok cb = true ->
       parse_lines (cb_lines cb ++ EmptyString :: tail)%list (PPara [])
       = cb_ast cb :: parse_lines tail (PPara []))
    /\ (cb_ok cb = true ->
        parse_lines (cb_lines cb) (PPara []) = [cb_ast cb]).
Proof.
  refine (cblock_ind2 _
            (fun cbs => forallb cb_ok cbs = true ->
                        parse_lines (sep_lines (map cb_lines cbs)) (PPara [])
                        = map cb_ast cbs)
            _ _ _ _ _ _ _).
  - (* paragraph *)
    intros ls. split; [intros tail H | intros H];
      change (cb_ok (CPara ls)) with (para_ok ls) in H;
      destruct ls as [|a ls']; try discriminate;
      apply para_ok_parts in H as (Htext & Hlok & _);
      pose proof (forallb_line_ok_nonblank _ Hlok) as Hnb;
      cbn [forallb] in Hnb; apply andb_true_iff in Hnb as [_ Hnb'];
      destruct (rev_cons_shape a ls') as [c [cur' Erev]];
      cbn [cb_lines].
    + rewrite parse_lines_para_seed by assumption.
      rewrite (forallb_line_ok_map_drop_leading_ws _ Hlok).
      rewrite Erev, parse_lines_blank_cons by reflexivity.
      rewrite <- Erev, rev_involutive. reflexivity.
    + rewrite <- (app_nil_r (a :: ls')) at 1.
      rewrite parse_lines_para_seed by assumption.
      rewrite (forallb_line_ok_map_drop_leading_ws _ Hlok).
      rewrite Erev, parse_lines_nil_cons, <- Erev, rev_involutive.
      reflexivity.
  - (* thematic break *)
    split; intros; cbn [cb_lines app].
    + rewrite parse_lines_thematic_nil by apply classify_canonical_thematic.
      rewrite parse_lines_blank_nil by reflexivity. reflexivity.
    + rewrite parse_lines_thematic_nil by apply classify_canonical_thematic.
      reflexivity.
  - (* code block *)
    intros info content. split; [intros tail H | intros H];
      change (cb_ok (CCode info content)) with (code_ok info content) in H;
      apply code_ok_parts in H as (Hinfo & _ & Hnc); cbn [cb_lines app].
    + rewrite (parse_lines_fence_open _ _ _
                 (classify_backtick_fence info Hinfo)).
      rewrite <- app_assoc.
      rewrite parse_lines_fence_seed by exact Hnc.
      rewrite app_nil_r. cbn [app].
      rewrite parse_lines_fence_close by apply fence_close_canonical.
      rewrite rev_involutive.
      rewrite parse_lines_blank_nil by reflexivity. reflexivity.
    + rewrite (parse_lines_fence_open _ _ _
                 (classify_backtick_fence info Hinfo)).
      rewrite parse_lines_fence_seed by exact Hnc.
      rewrite app_nil_r.
      rewrite parse_lines_fence_close by apply fence_close_canonical.
      rewrite rev_involutive. reflexivity.
  - (* heading: open on the first line, accumulate the rest, close on the
       blank line or at end of input.  No first-line classification
       condition — the hashes make every rendered line a heading line. *)
    intros lvl ls. split; [intros tail H | intros H];
      change (cb_ok (CHeading lvl ls)) with (heading_ok lvl ls) in H;
      apply heading_ok_parts in H as (Hlvl & Hne & Hlok & _);
      destruct ls as [|a ls']; [congruence| |congruence|];
      pose proof (forallb_line_ok_nonblank _ Hlok) as Hnb;
      cbn [forallb] in Hnb; apply andb_true_iff in Hnb as [Hna Hnb'];
      unfold nonblank in Hna; apply negb_true_iff in Hna;
      cbn [forallb] in Hlok; apply andb_true_iff in Hlok as [Hlok_a Hlok_ls'];
      cbn [cb_lines cb_ast map app];
      rewrite (parse_lines_heading_open _ _ _ a
                 (classify_canonical_heading lvl a Hlvl));
      replace (push_text a []) with [a]
        by (unfold push_text; rewrite Hna;
            rewrite (line_ok_no_leading_ws _ Hlok_a); reflexivity).
    + rewrite parse_lines_heading_seed by assumption.
      rewrite (forallb_line_ok_map_drop_leading_ws _ Hlok_ls').
      rewrite parse_lines_heading_close by reflexivity.
      unfold heading_block. rewrite rev_app_distr, rev_involutive.
      reflexivity.
    + rewrite <- (app_nil_r (map (heading_line lvl) ls')).
      rewrite parse_lines_heading_seed by assumption.
      rewrite (forallb_line_ok_map_drop_leading_ws _ Hlok_ls').
      rewrite parse_lines_nil. cbn [finish].
      unfold heading_block. rewrite rev_app_distr, rev_involutive.
      reflexivity.
  - (* quote: the contents parse at top level, then get wrapped *)
    intros inner IH.
    assert (Hsplit : cb_ok (CQuote inner) = true ->
                     exists l L, sep_lines (map cb_lines inner) = l :: L
                                 /\ forallb cb_ok inner = true).
    { intros H. rewrite cb_ok_quote in H.
      apply andb_true_iff in H as [Hne Hok].
      destruct inner as [|c rest]; [discriminate|].
      assert (Hc : lines_ok (cb_lines c) = true).
      { apply cb_ok_lines_ok. cbn [forallb] in Hok.
        apply andb_true_iff in Hok as [H1 _]. exact H1. }
      destruct (sep_lines (map cb_lines (c :: rest))) as [|l L] eqn:E.
      - exfalso. apply (sep_lines_nonempty (cb_lines c) (map cb_lines rest) Hc).
        exact E.
      - eauto. }
    split; [intros tail H | intros H];
      destruct (Hsplit H) as [l [L [E Hok]]];
      rewrite cb_lines_quote, cb_ast_quote, E;
      unfold quote_line, quote_open.
    + rewrite parse_lines_quote, <- E, (IH Hok). reflexivity.
    + rewrite quote_uniformity, <- E, (IH Hok). reflexivity.
  - (* the list side: nothing to parse *)
    reflexivity.
  - (* the list side: one block, then the rest after a blank line *)
    intros c rest [Hc1 Hc2] Hrest H.
    cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
    destruct rest as [|c2 rest'].
    + cbn [map sep_lines]. rewrite (Hc2 H1). reflexivity.
    + cbn [map sep_lines]. rewrite (Hc1 _ H1).
      cbn [map cb_ast]. f_equal. apply Hrest. exact H2.
Qed.

(* Half two: the parser folds a document's lines back into its blocks. *)
Lemma parse_sep :
  forall cbs, forallb cb_ok cbs = true ->
  parse_lines (sep_lines (map cb_lines cbs)) (PPara []) = map cb_ast cbs.
Proof.
  induction cbs as [|cb rest IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hcb Hrest].
  destruct (parse_cblock cb) as [Hc1 Hc2].
  destruct rest as [|cb2 rest'].
  - cbn [map sep_lines]. rewrite (Hc2 Hcb). reflexivity.
  - cbn [map sep_lines]. rewrite (Hc1 _ Hcb).
    cbn [map cb_ast]. f_equal. apply IH. exact Hrest.
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

(* fence_block renders back to the canonical fence lines, whether the
   info string makes it a code block or (starting with '=') a raw block.
   The 256-way destruct reduces the character match in fence_block. *)
Lemma render_fence_block :
  forall info content,
    forallb no_nl content = true ->
    render_block_lines
      (node_contents (fence_block (Fence "`"%char 3 info) content)) =
    (code_open info :: content ++ [code_close])%list.
Proof.
  intros info content H. unfold fence_block. cbn [f_info].
  destruct info as [|c info'].
  - cbn [render_block_lines node_contents mk].
    rewrite split_join_nl by exact H. reflexivity.
  - destruct c as [[|] [|] [|] [|] [|] [|] [|] [|]];
      cbn [render_block_lines node_contents mk];
      rewrite split_join_nl by exact H; reflexivity.
Qed.

(* The renderer emits exactly a cblock's canonical lines.  Same
   two-predicate induction as cb_ok_lines_ok, for the same reason. *)
Lemma render_cb_lines :
  forall cb, cb_ok cb = true ->
  render_block_lines (node_contents (cb_ast cb)) = cb_lines cb.
Proof.
  refine (cblock_ind2
            (fun cb => cb_ok cb = true ->
                       render_block_lines (node_contents (cb_ast cb))
                       = cb_lines cb)
            (fun cbs => forallb cb_ok cbs = true ->
                        render_blocks_lines (map cb_ast cbs)
                        = map cb_lines cbs)
            _ _ _ _ _ _ _).
  - (* paragraph: inline_lines inverts para_inlines *)
    intros ls H. change (cb_ok (CPara ls)) with (para_ok ls) in H.
    destruct ls as [|a ls']; [discriminate|].
    apply para_ok_parts in H as (_ & Hlok & Hlast).
    cbn [cb_ast cb_lines node_contents mk render_block_lines].
    rewrite inline_lines_para by (assumption || discriminate).
    reflexivity.
  - reflexivity.
  - (* code block *)
    intros info content H.
    change (cb_ok (CCode info content)) with (code_ok info content) in H.
    apply code_ok_parts in H as (_ & Hnl & _).
    cbn [cb_lines]. apply render_fence_block. exact Hnl.
  - (* heading: the same inline inversion as a paragraph, prefixed *)
    intros lvl ls H.
    change (cb_ok (CHeading lvl ls)) with (heading_ok lvl ls) in H.
    apply heading_ok_parts in H as (_ & Hne & Hlok & Hlast).
    cbn [cb_ast cb_lines node_contents mk render_block_lines].
    rewrite inline_lines_para by assumption.
    reflexivity.
  - (* quote: prefix the contents' layout *)
    intros inner IH H.
    rewrite cb_ok_quote in H. apply andb_true_iff in H as [_ Hok].
    rewrite cb_ast_quote. cbn [node_contents mk].
    rewrite render_block_quote, (IH Hok), cb_lines_quote.
    reflexivity.
  - reflexivity.
  - intros c rest Hc Hrest H.
    cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
    unfold render_blocks_lines in *. cbn [map].
    rewrite (Hc H1), (Hrest H2). reflexivity.
Qed.

(* Rendering a canonical document is the same as joining its cb_lines —
   this is what lets split_render/parse_sep take over. *)
Lemma render_djot_cblocks :
  forall cbs, forallb cb_ok cbs = true ->
  render_djot (blocks_of_cblocks cbs)
  = String.concat nl (sep_lines (map cb_lines cbs)).
Proof.
  intros cbs H. unfold render_djot, blocks_of_cblocks. cbn [doc_blocks].
  f_equal. f_equal.
  induction cbs as [|cb rest IH]; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hcb Hrest].
  unfold render_blocks_lines in *. cbn [map].
  rewrite (render_cb_lines _ Hcb), (IH Hrest). reflexivity.
Qed.

(*
The theorem
===========
*)

(** Render then parse is the identity on canonical blocks. *)
Theorem roundtrip_blocks :
  forall cbs, forallb cb_ok cbs = true ->
  parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof.
  intros cbs H.
  rewrite render_djot_cblocks by exact H.
  unfold parse_blocks, blocks_of_cblocks.
  f_equal.
  rewrite split_render by (apply forallb_cb_lines_ok; exact H).
  apply parse_sep. exact H.
Qed.

(*
Worked examples
===============

The theorem quantifies over cb_ok cblocks; these check that quotes are
really in that set, and that the rendering is the one a human would
write. *)

Definition quote_example : list cblock :=
  [ CQuote [CPara ["a"]; CThematic]; CPara ["after"] ].

Example quote_example_ok : forallb cb_ok quote_example = true.
Proof. reflexivity. Qed.

(* Spelled with explicit nl rather than a multi-line literal: the blank
   line inside the quote renders as "> ", prefix and all, and a literal
   would hide that trailing space. *)
Example quote_example_render :
  render_djot (blocks_of_cblocks quote_example)
  = ("> a" ++ nl ++ "> " ++ nl ++ "> * * * *" ++ nl ++ nl ++ "after")%string.
Proof. reflexivity. Qed.

Example quote_example_roundtrip :
  parse_blocks (render_djot (blocks_of_cblocks quote_example))
  = blocks_of_cblocks quote_example.
Proof. apply roundtrip_blocks. reflexivity. Qed.

(* A multi-line heading renders with the hashes repeated on every line,
   which is what makes it reparse as a continuation of itself. *)
Example heading_example_roundtrip :
  let cbs := [CHeading 2 ["a"; "b"]; CPara ["p"]] in
  render_djot (blocks_of_cblocks cbs)
    = ("## a" ++ nl ++ "## b" ++ nl ++ nl ++ "p")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* Headings nest inside quotes with no extra machinery. *)
Example heading_in_quote_roundtrip :
  let cbs := [CQuote [CHeading 1 ["h"]; CPara ["t"]]] in
  render_djot (blocks_of_cblocks cbs)
    = ("> # h" ++ nl ++ "> " ++ nl ++ "> t")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* Nesting roundtrips too, with no extra hypotheses. *)
Example nested_quote_roundtrip :
  let cbs := [CQuote [CQuote [CPara ["deep"]]]] in
  render_djot (blocks_of_cblocks cbs) = "> > deep"
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(*
Above the block layer
=====================

roundtrip_blocks is about `parse_blocks`, the line fold.  The parser's
actual entry point is `Document.parse_doc`, which runs the
whole-document pass on top — so the theorem only reaches the entry point
once the pass is shown to add nothing that erasure cannot take back
(Document.pass_erase).  The canonical fragment is exactly the kind of
input that theorem wants: cb_ast builds bare `mk` nodes, so no heading
carries an explicit id, and it builds no sections.
*)

Lemma cb_ast_pristine : forall cb, pristine_node (cb_ast cb) = true.
Proof.
  intros cb.
  induction cb using cblock_ind2 with
    (Q := fun cbs => pristine (map cb_ast cbs) = true);
    try reflexivity.
  - (* CCode: raw or code block, depending on the info string *)
    unfold cb_ast, fence_block. cbn [f_info].
    destruct info as [|c info']; [reflexivity|].
    (* the "=FORMAT" test is a match on the leading byte; both arms build
       a bare mk node, so all 256 close alike *)
    destruct c as [[][][][][][][][]]; reflexivity.
  - (* CQuote *)
    rewrite cb_ast_quote. cbn [pristine_node mk].
    rewrite pristine_quote. exact IHcb.
  - (* c :: rest *)
    cbn [map]. rewrite pristine_cons_node, IHcb, IHcb0. reflexivity.
Qed.

Lemma blocks_of_cblocks_pristine :
  forall cbs, pristine (blocks_of_cblocks cbs) = true.
Proof.
  induction cbs as [|cb rest IH]; [reflexivity|].
  unfold blocks_of_cblocks in *. cbn [map].
  rewrite pristine_cons_node, cb_ast_pristine, IH. reflexivity.
Qed.

(** The roundtrip at the parser's entry point: render, parse, undo the
    whole-document pass, and you are back where you started. *)
Theorem roundtrip_doc :
  forall cbs, forallb cb_ok cbs = true ->
  undo_pass (doc_blocks (parse_doc (render_djot (blocks_of_cblocks cbs))))
  = blocks_of_cblocks cbs.
Proof.
  intros cbs H. unfold parse_doc.
  rewrite (roundtrip_blocks _ H).
  apply pass_erase, blocks_of_cblocks_pristine.
Qed.

(* The sections and identifiers the pass adds are exactly what the
   erasure above takes back out. *)
Example heading_roundtrip_doc :
  let cbs := [CHeading 1 ["h"]; CPara ["p"]] in
  doc_blocks (parse_doc (render_djot (blocks_of_cblocks cbs)))
  = [ Node NoPos [("id", "h")]
        (Section [ mk (Heading 1 [mk (Str "h")]); mk (Para [mk (Str "p")]) ]) ]
  /\ undo_pass (doc_blocks (parse_doc (render_djot (blocks_of_cblocks cbs))))
     = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_doc; reflexivity]. Qed.
