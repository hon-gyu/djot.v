(* ai-disclosure: ai-generated *)

(* Roundtrip:  parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs
   for canonical blocks (Render.v).  Exact equality — canonicality is in
   the cb_ok hypothesis, so no quotient is needed.

   Proof shape, per block: rendering emits lines; split_lines recovers
   them exactly (Strings.v split/join inversion); the parser folds them
   back via its equation lemmas (Parser.v).  Extending to a new construct
   touches the three case analyses marked below and nothing else.

   Sections, in dependency order:

     Splitting a rendered document            line shape of a rendering
     Facts about canonical blocks             cb_ok's consequences
     Parsing the separated lines, under a pad blocks inside a list item
     Canonical lists                          the CList case, seven layers
     Blocks and block sequences               parse_cblock, parse_sep
     The renderer emits exactly the canonical lines
     The theorem                              roundtrip_blocks
     Worked examples                          regression witnesses
     Above the block layer                    roundtrip_doc

   Lists take two thirds of the file.  A list is the one construct whose
   parse cannot be stated block-at-a-time, so its section builds its own
   vocabulary (`run_lines`, `scan_list_content`) before reaching the two
   lemmas the block layer consumes: `parse_canonical_list_end` and
   `parse_canonical_list_then_nonlist`. *)

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

(*
list_lines is itself a well-formed line list
---------------------------------------------

list_lines Loose is sep_lines under a different name (same unconditional
blank separator); list_lines Tight is plain concatenation, so its three
facts drop the "blank cons" step sep_lines needs. *)

Lemma list_lines_loose_eq : forall lss, list_lines Loose lss = sep_lines lss.
Proof.
  induction lss as [|ls rest IH]; [reflexivity|].
  destruct rest as [|ls2 rest']; [reflexivity|].
  change (list_lines Loose (ls :: ls2 :: rest'))
    with (ls ++ EmptyString :: list_lines Loose (ls2 :: rest'))%list.
  change (sep_lines (ls :: ls2 :: rest'))
    with (ls ++ EmptyString :: sep_lines (ls2 :: rest'))%list.
  rewrite IH. reflexivity.
Qed.

Lemma list_lines_tight_nonempty :
  forall ls rest, lines_ok ls = true -> list_lines Tight (ls :: rest) <> [].
Proof.
  intros ls rest H. apply lines_ok_parts in H as (Hne & _ & _).
  destruct rest as [|ls2 rest'].
  - exact Hne.
  - cbn [list_lines]. destruct ls; [congruence | discriminate].
Qed.

Lemma list_lines_tight_no_nl :
  forall lss,
    forallb lines_ok lss = true -> forallb no_nl (list_lines Tight lss) = true.
Proof.
  induction lss as [|ls rest IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hls Hrest].
  apply lines_ok_parts in Hls as (_ & Hnl & _).
  destruct rest as [|ls2 rest']; [exact Hnl|].
  cbn [list_lines]. rewrite forallb_app, Hnl. cbn [andb]. apply IH. exact Hrest.
Qed.

Lemma list_lines_tight_last :
  forall ls rest,
    forallb lines_ok (ls :: rest) = true ->
    last (list_lines Tight (ls :: rest)) EmptyString <> EmptyString.
Proof.
  intros ls rest. revert ls.
  induction rest as [|ls2 rest' IH]; intros ls H;
    cbn [forallb] in H; apply andb_true_iff in H as [Hls Hrest].
  - apply lines_ok_parts in Hls as (_ & _ & Hlast). exact Hlast.
  - cbn [list_lines].
    pose proof Hrest as Hrest0. cbn [forallb] in Hrest0.
    apply andb_true_iff in Hrest0 as [Hls2 _].
    rewrite last_app_nonnil by exact (list_lines_tight_nonempty ls2 rest' Hls2).
    apply IH. exact Hrest.
Qed.

(* Either spacing: nonempty items with lines_ok lines produce lines_ok
   output.  The single lemma cb_ok_lines_ok's CList case needs. *)
Lemma list_lines_ok :
  forall sp lss, lss <> [] -> forallb lines_ok lss = true ->
  lines_ok (list_lines sp lss) = true.
Proof.
  intros sp lss Hne Hok. destruct lss as [|ls rest]; [congruence|].
  pose proof Hok as Hok0. cbn [forallb] in Hok0.
  apply andb_true_iff in Hok0 as [Hls _].
  destruct sp.
  - unfold lines_ok. apply andb_true_iff. split; [apply andb_true_iff; split|].
    + destruct (list_lines Tight (ls :: rest)) eqn:E; [|reflexivity].
      exfalso. apply (list_lines_tight_nonempty ls rest Hls). exact E.
    + apply list_lines_tight_no_nl. exact Hok.
    + apply nonempty_str_intro, (list_lines_tight_last ls rest Hok).
  - rewrite list_lines_loose_eq. unfold lines_ok.
    apply andb_true_iff. split; [apply andb_true_iff; split|].
    + destruct (sep_lines (ls :: rest)) eqn:E; [|reflexivity].
      exfalso. apply (sep_lines_nonempty ls rest Hls). exact E.
    + apply sep_lines_no_nl. exact Hok.
    + apply nonempty_str_intro, (sep_lines_last ls rest Hok).
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

(* Pushing an all-whitespace pad through a mapped nonblank/drop_leading_ws
   check — the two facts parse_cblock_pad's paragraph case needs to reuse
   parse_lines_para_seed (already generic over its lines) with padded
   arguments. *)
Lemma forallb_nonblank_map_pad :
  forall pad ls, is_blank pad = true -> forallb nonblank ls = true ->
  forallb nonblank (map (fun l => pad ++ l) ls) = true.
Proof.
  intros pad ls Hpad. induction ls as [|l ls IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hl Hls].
  cbn [map forallb]. unfold nonblank in Hl |- *.
  rewrite is_blank_ws_prefix by exact Hpad. rewrite Hl. cbn [andb]. apply IH, Hls.
Qed.

Lemma map_drop_leading_ws_map_pad :
  forall pad ls, is_blank pad = true ->
  map drop_leading_ws (map (fun l => pad ++ l) ls) = map drop_leading_ws ls.
Proof.
  intros pad ls Hpad. rewrite map_map.
  apply map_ext. intros a. apply drop_leading_ws_ws_prefix, Hpad.
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

Lemma forallb_no_nl_map_append :
  forall p ls, no_nl p = true -> forallb no_nl ls = true ->
  forallb no_nl (map (fun x => p ++ x) ls) = true.
Proof.
  intros p ls Hp. induction ls as [|l ls IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hl Hls].
  cbn [map forallb]. rewrite no_nl_append, Hp, Hl. cbn [andb]. apply IH, Hls.
Qed.

(* A list item's rendering: marker on the first line, plain indent on
   the rest — two prefixes instead of quote_line's one, so this isn't
   quite lines_ok_map, but the same shape otherwise. *)
Lemma lines_ok_indent :
  forall p1 p2 ls,
    no_nl p1 = true -> no_nl p2 = true -> p1 <> EmptyString -> p2 <> EmptyString ->
    ls <> [] -> forallb no_nl ls = true ->
    lines_ok (indent_lines p1 p2 ls) = true.
Proof.
  intros p1 p2 ls Hn1 Hn2 He1 He2 Hne Hnl.
  destruct ls as [|l rest]; [congruence|].
  cbn [forallb] in Hnl. apply andb_true_iff in Hnl as [Hl Hrest].
  unfold lines_ok. apply andb_true_iff. split; [apply andb_true_iff; split|].
  - cbn [indent_lines]. reflexivity.
  - cbn [indent_lines forallb]. rewrite no_nl_append, Hn1, Hl. cbn [andb].
    apply forallb_no_nl_map_append; assumption.
  - cbn [indent_lines]. destruct rest as [|r rest'].
    + apply nonempty_str_intro. destruct p1 as [|c s].
      * exfalso. apply He1. reflexivity.
      * discriminate.
    + rewrite (last_cons_nonnil (p1 ++ l) (map (fun x => p2 ++ x) (r :: rest'))
                 EmptyString) by (cbn [map]; discriminate).
      rewrite (last_default (map (fun x => p2 ++ x) (r :: rest')) EmptyString
                 (p2 ++ EmptyString)) by (cbn [map]; discriminate).
      rewrite (last_map (fun x => p2 ++ x) (r :: rest') EmptyString) by discriminate.
      apply nonempty_str_intro. destruct p2 as [|c s].
      * exfalso. apply He2. reflexivity.
      * discriminate.
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
            (Forall (fun cbs => forallb cb_ok cbs = true ->
                                 forallb lines_ok (map cb_lines cbs) = true))
            _ _ _ _ _ _ _ _ (Forall_nil _) (fun item items Hi Hr => Forall_cons _ Hi Hr)).
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
    rewrite cb_ok_quote in H. apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [Hne Hok].
    rewrite cb_lines_quote.
    apply lines_ok_quote.
    + destruct inner as [|c rest]; [discriminate|].
      apply sep_lines_nonempty.
      cbn [map forallb] in IH |- *.
      specialize (IH Hok). apply andb_true_iff in IH as [Hc _]. exact Hc.
    + apply sep_lines_no_nl. apply IH. exact Hok.
  - (* list: each item lays out as a document would, then gets its
       marker/indent prefix; list_lines_ok closes the spacing. *)
    intros sp items IH H.
    rewrite cb_ok_list in H.
    apply andb_true_iff in H as [H Hspacing].
    apply andb_true_iff in H as [H Hsafe].
    apply andb_true_iff in H as [H Hmarker].
    apply andb_true_iff in H as [Hne Hitems].
    rewrite cb_lines_list. apply list_lines_ok.
    + destruct items as [|it items']; discriminate.
    + clear Hne Hspacing Hmarker Hsafe. revert Hitems.
      induction IH as [|it items' HQ IHrest IHind]; intros Hitems; [reflexivity|].
      cbn [forallb] in Hitems. apply andb_true_iff in Hitems as [Hit Hitems'].
      apply andb_true_iff in Hit as [Hitne Hitok].
      pose proof (HQ Hitok) as Hlok_it.
      cbn [map forallb].
      rewrite (lines_ok_indent bullet_open bullet_cont).
      * cbn [andb]. apply IHind. exact Hitems'.
      * reflexivity.
      * reflexivity.
      * discriminate.
      * discriminate.
      * destruct it as [|c rest]; [discriminate|].
        apply sep_lines_nonempty.
        cbn [map forallb] in Hlok_it |- *.
        apply andb_true_iff in Hlok_it as [Hc _]. exact Hc.
      * apply sep_lines_no_nl. exact Hlok_it.
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
Parsing the separated lines, under a pad
========================================

Case analysis over the head cblock — extend here, and in `parse_cblock`
below, for new constructs.  This half handles a block sitting inside a
list item, where every line carries the item's continuation whitespace;
the unpadded case is `parse_cblock`, after the list machinery.
*)

(* parse_cblock, generalized by a whitespace pad in front of every line —
   what a list item's content needs, since bullet_cont ("  ") sits in
   front of every line but the item's first.  Restricted to
   list_content_safe cblocks: CCode and CList are exactly the two
   constructs that don't tolerate an arbitrary ambient pad (Render.v's
   list_content_safe explains why), so their cases are vacuous here —
   cb_ok never lets a list item reach either.

   `pad` sits *inside* P/Q, not fixed once up front: a CQuote's own
   content is reparsed at pad = EmptyString regardless of what pad wraps
   the quote itself (a quote strips its own prefix exactly, absorbing
   any ambient pad — Line.classify_canonical_quote_pad), so the
   induction hypothesis needs to be instantiable at a *different* pad
   than the one this case was called with. *)
Lemma parse_cblock_pad :
  forall cb,
    list_content_safe cb = true ->
    forall pad, is_blank pad = true ->
    (forall sep tail, classify sep = KBlank -> cb_ok cb = true ->
       parse_lines (map (fun l => (pad ++ l)%string) (cb_lines cb) ++ sep :: tail)%list
                   (PPara [])
       = cb_ast cb :: parse_lines tail (PPara []))
    /\ (cb_ok cb = true ->
        parse_lines (map (fun l => (pad ++ l)%string) (cb_lines cb)) (PPara []) = [cb_ast cb]).
Proof.
  refine (cblock_ind2
            (fun cb =>
               list_content_safe cb = true ->
               forall pad, is_blank pad = true ->
               (forall sep tail, classify sep = KBlank -> cb_ok cb = true ->
                  parse_lines (map (fun l => (pad ++ l)%string) (cb_lines cb) ++ sep :: tail)%list
                              (PPara [])
                  = cb_ast cb :: parse_lines tail (PPara []))
               /\ (cb_ok cb = true ->
                   parse_lines (map (fun l => (pad ++ l)%string) (cb_lines cb)) (PPara []) = [cb_ast cb]))
            (fun cbs =>
               forallb list_content_safe cbs = true ->
               forall pad, is_blank pad = true ->
               forallb cb_ok cbs = true ->
               parse_lines (map (fun l => (pad ++ l)%string) (sep_lines (map cb_lines cbs))) (PPara [])
               = map cb_ast cbs)
            (fun _ => True)
            _ _ _ _ _ _ _ _ I (fun _ _ _ _ => I)).
  - (* paragraph *)
    intros ls Hsafe pad Hpad. split; [intros sep tail Hsep H | intros H];
      change (cb_ok (CPara ls)) with (para_ok ls) in H;
      destruct ls as [|a ls']; try discriminate;
      apply para_ok_parts in H as (Htext & Hlok & _);
      pose proof (forallb_line_ok_nonblank _ Hlok) as Hnb;
      cbn [forallb] in Hnb; apply andb_true_iff in Hnb as [_ Hnb'];
      pose proof (forallb_nonblank_map_pad pad ls' Hpad Hnb') as Hnb'pad;
      assert (Hcls : classify (pad ++ a) = KText)
        by (rewrite classify_ws_prefix by exact Hpad; exact Htext);
      cbn [cb_lines map].
    + rewrite (parse_lines_para_seed (pad ++ a) (map (fun l => (pad ++ l)%string) ls')
                 (sep :: tail) Hcls Hnb'pad).
      change ((pad ++ a)%string :: map (fun l => (pad ++ l)%string) ls')
        with (map (fun l => (pad ++ l)%string) (a :: ls')).
      rewrite (map_drop_leading_ws_map_pad pad (a :: ls') Hpad).
      rewrite (forallb_line_ok_map_drop_leading_ws _ Hlok).
      destruct (rev_cons_shape a ls') as [c0 [cur0 Erev0]].
      rewrite Erev0, (parse_lines_blank_cons sep tail c0 cur0 Hsep).
      rewrite <- Erev0, rev_involutive. reflexivity.
    + rewrite <- (app_nil_r ((pad ++ a)%string :: map (fun l => (pad ++ l)%string) ls')) at 1.
      rewrite (parse_lines_para_seed (pad ++ a) (map (fun l => (pad ++ l)%string) ls') []
                 Hcls Hnb'pad).
      change ((pad ++ a)%string :: map (fun l => (pad ++ l)%string) ls')
        with (map (fun l => (pad ++ l)%string) (a :: ls')).
      rewrite (map_drop_leading_ws_map_pad pad (a :: ls') Hpad).
      rewrite (forallb_line_ok_map_drop_leading_ws _ Hlok).
      destruct (rev_cons_shape a ls') as [c0 [cur0 Erev0]].
      rewrite Erev0, parse_lines_nil_cons, <- Erev0, rev_involutive.
      reflexivity.
  - (* thematic break *)
    intros Hsafe pad Hpad. split; [intros sep tail Hsep H | intros H];
      cbn [cb_lines app map].
    + rewrite (parse_lines_thematic_nil (pad ++ thematic_line))
        by (rewrite classify_ws_prefix by exact Hpad; apply classify_canonical_thematic).
      rewrite (parse_lines_blank_nil sep tail Hsep). reflexivity.
    + rewrite (parse_lines_thematic_nil (pad ++ thematic_line))
        by (rewrite classify_ws_prefix by exact Hpad; apply classify_canonical_thematic).
      reflexivity.
  - (* code block: excluded by list_content_safe *)
    intros info content Hsafe. discriminate Hsafe.
  - (* heading *)
    intros lvl ls Hsafe pad Hpad. split; [intros sep tail Hsep H | intros H];
      change (cb_ok (CHeading lvl ls)) with (heading_ok lvl ls) in H;
      apply heading_ok_parts in H as (Hlvl & Hne & Hlok & _);
      destruct ls as [|a ls']; [congruence| |congruence|];
      pose proof (forallb_line_ok_nonblank _ Hlok) as Hnb;
      cbn [forallb] in Hnb; apply andb_true_iff in Hnb as [Hna Hnb'];
      unfold nonblank in Hna; apply negb_true_iff in Hna;
      cbn [forallb] in Hlok; apply andb_true_iff in Hlok as [Hlok_a Hlok_ls'];
      cbn [cb_lines cb_ast map app];
      rewrite (parse_lines_heading_open _ _ _ a
                 (classify_canonical_heading_pad pad lvl a Hpad Hlvl));
      replace (push_text a []) with [a]
        by (unfold push_text; rewrite Hna;
            rewrite (line_ok_no_leading_ws _ Hlok_a); reflexivity).
    + rewrite map_map.
      rewrite (parse_lines_heading_seed_pad pad Hpad lvl ls' (sep :: tail) [a] Hlvl Hnb').
      rewrite (forallb_line_ok_map_drop_leading_ws _ Hlok_ls').
      rewrite (parse_lines_heading_close sep tail lvl (rev ls' ++ [a]) Hsep).
      unfold heading_block. rewrite rev_app_distr, rev_involutive.
      reflexivity.
    + rewrite map_map.
      rewrite <- (app_nil_r (map (fun l => (pad ++ heading_line lvl l)%string) ls')).
      rewrite (parse_lines_heading_seed_pad pad Hpad lvl ls' [] [a] Hlvl Hnb').
      rewrite (forallb_line_ok_map_drop_leading_ws _ Hlok_ls').
      rewrite parse_lines_nil. cbn [finish].
      unfold heading_block. rewrite rev_app_distr, rev_involutive.
      reflexivity.
  - (* quote: its own content is reparsed pad-free, regardless of the
       pad wrapping the quote itself — quote_prefix absorbs it exactly *)
    intros inner IH Hsafe pad Hpad.
    cbn [list_content_safe] in Hsafe.
    assert (Hsplit : cb_ok (CQuote inner) = true ->
                     exists l L, sep_lines (map cb_lines inner) = l :: L
                                 /\ forallb cb_ok inner = true).
    { intros H. rewrite cb_ok_quote in H.
      apply andb_true_iff in H as [H _].
      apply andb_true_iff in H as [Hne Hok].
      destruct inner as [|c rest]; [discriminate|].
      assert (Hc : lines_ok (cb_lines c) = true).
      { apply cb_ok_lines_ok. cbn [forallb] in Hok.
        apply andb_true_iff in Hok as [H1 _]. exact H1. }
      destruct (sep_lines (map cb_lines (c :: rest))) as [|l L] eqn:E.
      - exfalso. apply (sep_lines_nonempty (cb_lines c) (map cb_lines rest) Hc).
        exact E.
      - eauto. }
    split; [intros sep tail Hsep H | intros H];
      destruct (Hsplit H) as [l [L [E Hok]]];
      rewrite cb_lines_quote, cb_ast_quote, map_map;
      unfold quote_line, quote_open; rewrite E;
      pose proof (IH Hsafe EmptyString eq_refl Hok) as IHinner;
      rewrite E in IHinner;
      rewrite (map_ext (fun l0 => (EmptyString ++ l0)%string) (fun l0 => l0)
                 (fun x => eq_refl) (l :: L)), map_id in IHinner.
    + rewrite (parse_lines_quote_pad pad Hpad sep Hsep l L tail).
      rewrite IHinner. reflexivity.
    + rewrite (quote_uniformity_pad pad Hpad l L).
      rewrite IHinner. reflexivity.
  - (* CList: excluded by list_content_safe *)
    intros sp items _ Hsafe. discriminate Hsafe.
  - (* the list side: nothing to parse *)
    intros _ pad _ _. reflexivity.
  - (* the list side: one block, then the rest after a blank line *)
    intros c rest Hc Hrest Hsafe pad Hpad H.
    cbn [forallb] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe1 Hsafe2].
    cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
    destruct rest as [|c2 rest'].
    + cbn [map sep_lines]. destruct (Hc Hsafe1 pad Hpad) as [_ Hc2].
      rewrite (Hc2 H1). reflexivity.
    + cbn [map sep_lines].
      destruct (Hc Hsafe1 pad Hpad) as [Hc1 _].
      rewrite map_app, map_cons, append_empty_r.
      rewrite (Hc1 pad _ (classify_blank pad Hpad) H1).
      cbn [map cb_ast]. f_equal. apply Hrest; assumption.
Qed.


(*
Canonical lists
===============

Everything from here to `parse_cblock` serves the CList case, which is the
only construct whose rendering the parser cannot absorb one block at a
time: a list's lines open a container that stays open across items, and
whether the result is Tight or Loose is decided by blank lines scattered
through the whole run.  So the proof cannot go through `parse_lines`,
which finishes at end of input and discards the state.  It threads
`run_lines` instead, and tracks the open `list_state` explicitly.

The layers below, in dependency order:

  1. `run_lines`             — step a prefix, keep the residual state
  2. `scan_list_content`     — the same run, projected to the list state
  3. state algebra           — how that projection composes
  4. canonical item          — one cb_ok item's lines drive both of the above
  5. sibling transitions     — item to item, tight and loose
  6. tail induction          — a run of siblings, tight and loose
  7. closing                 — the list ends at a blank line plus a non-list

Tight and loose are proved as separate lemma pairs throughout, not by a
shared lemma over a flag: the tight case must additionally rule out
`item_forces_loose`, and the loose case renders a different line shape
(`canonical_loose_tail_lines`).  The pairs are near-identical in tactic
text; see the note in the section on the tail induction.
*)


(*
Item content under the continuation pad
---------------------------------------

A canonical item renders as `- ` on its first line and `bullet_cont` on
every later one.  The parser sees those padded lines; the item's own
blocks must parse as if unpadded.  `list_content_safe` (Render.v) is what
makes that true, by excluding the two constructs a pad would change:
CCode, whose content is verbatim, and a nested CList, whose marker the pad
would re-indent.  These lemmas discharge the pad, and expose the shape of
an item's first line, which decides whether the parser opens a new item or
continues the current one.
*)

(* A continuation pad changes nothing inside a flat item.  The column
   offset makes the general claim false -- a list opened on the padded
   line records its column two further right -- but a list item whose
   content is list_content_safe never opens one, and then there is no
   column to shift.  Parser.step_pad_flat is that argument; the two
   no_columns side conditions are what list_content_safe buys. *)
Lemma step_idle_bullet_cont :
  forall l st,
    pad_safe st = true -> no_columns st = true ->
    no_columns (snd (step l st)) = true ->
    step (bullet_cont ++ l) st = step l st.
Proof.
  intros l st Hsafe Hst Hafter.
  exact (step_pad_flat bullet_cont l st bullet_cont_blank Hsafe Hst Hafter).
Qed.



Lemma run_lines_first_unpadded :
  forall a rest,
    (forall m item, classify a <> KList m item) ->
    no_columns (snd (step a (PPara []))) = true ->
    run_lines (a :: map (fun l => (bullet_cont ++ l)%string) rest) (PPara [])
    = run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest)) (PPara []).
Proof.
  intros a rest Hnot Hcols. cbn [map run_lines].
  rewrite (step_idle_bullet_cont a (PPara []) eq_refl eq_refl Hcols).
  reflexivity.
Qed.

Lemma safe_cblock_first :
  forall cb,
    list_content_safe cb = true -> cb_ok cb = true ->
    exists a rest,
      cb_lines cb = a :: rest /\
      forall m item, classify a <> KList m item.
Proof.
  intros cb Hsafe Hok.
  pose proof (cb_ok_lines_ok cb Hok) as Hlines.
  apply lines_ok_parts in Hlines as (Hne & _ & _).
  destruct cb as [ls| |info content|lvl ls|inner|sp items].
  - destruct ls as [|a rest].
    + exfalso. apply Hne. reflexivity.
    +
    exists a, rest. split; [reflexivity|].
    change (cb_ok (CPara (a :: rest))) with (para_ok (a :: rest)) in Hok.
    apply para_ok_parts in Hok as [Ha _].
    intros m item E. rewrite Ha in E. discriminate.
  - exists thematic_line, []. split; [reflexivity|].
    intros m item E. unfold thematic_line in E.
    rewrite classify_canonical_thematic in E. discriminate.
  - discriminate Hsafe.
  - change (cb_ok (CHeading lvl ls)) with (heading_ok lvl ls) in Hok.
    apply heading_ok_parts in Hok as [Hlvl [Hls _]].
    destruct ls as [|a rest].
    + exfalso. apply Hls. reflexivity.
    +
    exists (heading_line lvl a), (map (heading_line lvl) rest).
    split; [reflexivity|]. intros m item E.
    rewrite (classify_canonical_heading lvl a Hlvl) in E. discriminate.
  - rewrite cb_lines_quote.
    destruct (sep_lines (map cb_lines inner)) as [|l rest] eqn:Esep.
    + exfalso. apply Hne. rewrite cb_lines_quote, Esep. reflexivity.
    + exists (quote_line l), (map quote_line rest). split; [reflexivity|].
      intros m item E. rewrite classify_canonical_quote in E. discriminate.
  - discriminate Hsafe.
Qed.

(* Stronger than safe_cblock_first, and the quote case is why it needs an
   induction rather than a case split: a quote's *own* first line never
   classifies as a list marker, but the state it opens contains whatever
   the quote's contents opened.  list_content_safe rules out a CList
   anywhere inside, so no column is ever recorded, and the continuation
   pad stays invisible (Parser.step_pad_flat). *)
Lemma safe_cblock_no_columns :
  forall cb,
    list_content_safe cb = true -> cb_ok cb = true ->
    forall a rest, cb_lines cb = a :: rest ->
    no_columns (snd (step a (PPara []))) = true.
Proof.
  refine (cblock_ind2
            (fun cb => list_content_safe cb = true -> cb_ok cb = true ->
                       forall a rest, cb_lines cb = a :: rest ->
                       no_columns (snd (step a (PPara []))) = true)
            (fun cbs => forallb list_content_safe cbs = true ->
                        forallb cb_ok cbs = true ->
                        forall a rest, sep_lines (map cb_lines cbs) = a :: rest ->
                        no_columns (snd (step a (PPara []))) = true)
            (fun _ => True)
            _ _ _ _ _ _ _ _ I (fun _ _ _ _ => I)).
  - (* paragraph: a text line opens a paragraph *)
    intros ls Hsafe Hok a rest Hl.
    destruct ls as [|x xs]; [discriminate Hl|].
    cbn [cb_lines] in Hl. injection Hl as <- <-.
    change (cb_ok (CPara (x :: xs))) with (para_ok (x :: xs)) in Hok.
    apply para_ok_parts in Hok as [Ha _].
    rewrite (step_idle x KText Ha eq_refl). reflexivity.
  - (* thematic break *)
    intros Hsafe Hok a rest Hl. cbn [cb_lines] in Hl. injection Hl as <- <-.
    rewrite (step_idle thematic_line KThematic classify_canonical_thematic
               eq_refl). reflexivity.
  - intros info content Hsafe. discriminate Hsafe.
  - (* heading *)
    intros lvl ls Hsafe Hok a rest Hl.
    change (cb_ok (CHeading lvl ls)) with (heading_ok lvl ls) in Hok.
    apply heading_ok_parts in Hok as [Hlvl [Hls _]].
    destruct ls as [|x xs]; [congruence|].
    cbn [cb_lines map] in Hl. injection Hl as <- <-.
    rewrite (step_idle _ (KHeading lvl x)
               (classify_canonical_heading lvl x Hlvl) eq_refl).
    reflexivity.
  - (* quote: the pad the prefix eats cannot introduce a column *)
    intros inner IH Hsafe Hok a rest Hl.
    rewrite list_content_safe_quote in Hsafe.
    rewrite cb_ok_quote in Hok.
    apply andb_true_iff in Hok as [Hok _].
    apply andb_true_iff in Hok as [_ Hokinner].
    rewrite cb_lines_quote in Hl.
    destruct (sep_lines (map cb_lines inner)) as [|l L] eqn:Esep;
      [discriminate Hl|].
    cbn [map] in Hl. injection Hl as <- <-.
    destruct (step l (PPara [])) as [bs inner'] eqn:Es.
    unfold quote_line, quote_open.
    rewrite (step_quote_open _ l bs inner' (classify_canonical_quote l) Es).
    cbn [snd no_columns]. rewrite no_columns_pad_state.
    pose proof (IH Hsafe Hokinner l L eq_refl) as Hin.
    rewrite Es in Hin. cbn [snd] in Hin. exact Hin.
  - intros sp items _ Hsafe. discriminate Hsafe.
  - (* the empty content list has no first line *)
    intros _ _ a rest Hl. cbn [map sep_lines] in Hl. discriminate Hl.
  - (* a content list's first line is its first block's first line *)
    intros c rest IHc IHrest Hsafe Hok a l Hl.
    cbn [forallb] in Hsafe, Hok.
    apply andb_true_iff in Hsafe as [Hsafec Hsaferest].
    apply andb_true_iff in Hok as [Hokc Hokrest].
    pose proof (cb_ok_lines_ok c Hokc) as Hvalid.
    apply lines_ok_parts in Hvalid as [Hne _].
    destruct (cb_lines c) as [|x xs] eqn:Ec; [exfalso; apply Hne; reflexivity|].
    destruct rest as [|c2 rest'].
    + cbn [map sep_lines] in Hl. rewrite Ec in Hl. injection Hl as <- <-.
      exact (IHc Hsafec Hokc x xs eq_refl).
    + cbn [map sep_lines] in Hl. rewrite Ec in Hl.
      cbn [app] in Hl. injection Hl as <- <-.
      exact (IHc Hsafec Hokc x xs eq_refl).
Qed.

Lemma nonlist_cblock_first :
  forall cb,
    is_clist cb = false -> cb_ok cb = true ->
    exists a rest,
      cb_lines cb = a :: rest /\
      forall m item, classify a <> KList m item.
Proof.
  intros cb Hnonlist Hok.
  pose proof (cb_ok_lines_ok cb Hok) as Hlines.
  apply lines_ok_parts in Hlines as (Hne & _ & _).
  destruct cb as [ls| |info content|lvl ls|inner|sp items].
  - destruct ls as [|a rest].
    + exfalso. apply Hne. reflexivity.
    + exists a, rest. split; [reflexivity|].
      change (cb_ok (CPara (a :: rest))) with (para_ok (a :: rest)) in Hok.
      apply para_ok_parts in Hok as [Ha _].
      intros m item E. rewrite Ha in E. discriminate.
  - exists thematic_line, []. split; [reflexivity|].
    intros m item E. unfold thematic_line in E.
    rewrite classify_canonical_thematic in E. discriminate.
  - exists (code_open info), (content ++ [code_close])%list.
    split; [reflexivity|]. intros m item E.
    change (cb_ok (CCode info content)) with (code_ok info content) in Hok.
    apply code_ok_parts in Hok as [Hinfo _].
    unfold code_open in E.
    rewrite (classify_backtick_fence info Hinfo) in E. discriminate.
  - change (cb_ok (CHeading lvl ls)) with (heading_ok lvl ls) in Hok.
    apply heading_ok_parts in Hok as [Hlvl [Hls _]].
    destruct ls as [|a rest].
    + exfalso. apply Hls. reflexivity.
    + exists (heading_line lvl a), (map (heading_line lvl) rest).
      split; [reflexivity|]. intros m item E.
      rewrite (classify_canonical_heading lvl a Hlvl) in E. discriminate.
  - rewrite cb_lines_quote.
    destruct (sep_lines (map cb_lines inner)) as [|l rest] eqn:Esep.
    + exfalso. apply Hne. rewrite cb_lines_quote, Esep. reflexivity.
    + exists (quote_line l), (map quote_line rest). split; [reflexivity|].
      intros m item E. rewrite classify_canonical_quote in E. discriminate.
  - discriminate Hnonlist.
Qed.

Lemma parse_safe_cblocks_pad :
  forall cbs,
    forallb list_content_safe cbs = true ->
    forall pad, is_blank pad = true ->
    forallb cb_ok cbs = true ->
    parse_lines (map (fun l => (pad ++ l)%string)
                   (sep_lines (map cb_lines cbs))) (PPara [])
    = map cb_ast cbs.
Proof.
  induction cbs as [|c rest IH]; intros Hsafe pad Hpad Hok; [reflexivity|].
  cbn [forallb] in Hsafe, Hok.
  apply andb_true_iff in Hsafe as [Hsafec Hsaferest].
  apply andb_true_iff in Hok as [Hokc Hokrest].
  destruct rest as [|c2 rest'].
  - cbn [map sep_lines].
    destruct (parse_cblock_pad c Hsafec pad Hpad) as [_ Hparse].
    rewrite (Hparse Hokc). reflexivity.
  - cbn [map sep_lines]. rewrite map_app. cbn [map]. rewrite append_empty_r.
    destruct (parse_cblock_pad c Hsafec pad Hpad) as [Hparse _].
    rewrite (Hparse pad _ (classify_blank pad Hpad) Hokc).
    cbn [map]. f_equal. apply IH; assumption.
Qed.

Lemma run_first_list_item :
  forall a rest bs inner',
    (forall m item, classify a <> KList m item) ->
    no_columns (snd (step a (PPara []))) = true ->
    is_thematic (bullet_open ++ a) = false ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, inner') ->
    run_lines (indent_lines bullet_open bullet_cont (a :: rest)) (PPara [])
    = ([], PList
             (scan_list_content (LSt 0 "-"%char false false []) rest)
             (rev bs) inner').
Proof.
  intros a rest bs inner' Hnot Hcols Hmarker Hrun.
  pose proof (run_lines_first_unpadded a rest Hnot Hcols) as Hsame.
  rewrite Hrun in Hsame.
  cbn [map run_lines indent_lines] in Hsame |- *.
  destruct (step a (PPara [])) as [head inner] eqn:Hstep.
  destruct (run_lines (map (fun l => bullet_cont ++ l) rest) inner)
    as [more final] eqn:Hmore.
  inversion Hsame; subst bs inner'.
  assert (Hopen : step (bullet_open ++ a) (PPara []) =
                    ([], PList (LSt 0 "-"%char false false []) (rev head) inner)).
  { rewrite (step_list_open (bullet_open ++ a) "-"%char a head inner
               (classify_bullet_open a Hmarker) Hstep).
    rewrite indent_of_bullet_open.
    (* the marker eats two columns, but a flat item records none *)
    cbn [snd] in Hcols.
    rewrite (pad_state_no_columns _ inner Hcols). reflexivity. }
  rewrite Hopen. cbn [app].
  rewrite (run_lines_list_cont rest (LSt 0 "-"%char false false [])
             (rev head) inner more final) by (reflexivity || exact Hmore).
  rewrite rev_app_distr. reflexivity.
Qed.

Lemma classify_not_blank_nonblank :
  forall l, classify l <> KBlank -> nonblank l = true.
Proof.
  intros l H. unfold nonblank. apply negb_true_iff.
  destruct (is_blank l) eqn:Hblank; [|reflexivity].
  exfalso. apply H. apply classify_blank. exact Hblank.
Qed.

(*
State algebra of scan_list_content
----------------------------------

How the projection composes, and what each field of `list_state` does or
does not depend on.  The recurring shape: `ind`, `marker` and `items` are
invariant under content lines, `loose` is monotone (once set it stays
set), and `blanks` is decided by the last line alone.  Everything above
uses these to avoid re-inducting over `scan_list_content`.
*)

Lemma scan_list_content_nonblank :
  forall lines ind marker loose items,
    forallb nonblank lines = true ->
    scan_list_content (LSt ind marker loose false items) lines
    = LSt ind marker loose false items.
Proof.
  induction lines as [|l lines IH]; intros ind marker loose items H;
    [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hl Hrest].
  cbn [scan_list_content].
  destruct (classify l) as [| |f|q|lvl txt|m rest|] eqn:Hclass.
  - apply classify_kblank_blank in Hclass. unfold nonblank in Hl.
    rewrite Hclass in Hl. discriminate.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
Qed.

Lemma safe_cb_lines_nonblank :
  forall cb,
    list_content_safe cb = true -> cb_ok cb = true ->
    forallb nonblank (cb_lines cb) = true.
Proof.
  intros cb Hsafe Hok.
  destruct cb as [ls| |info content|lvl ls|inner|sp items].
  - change (cb_ok (CPara ls)) with (para_ok ls) in Hok.
    destruct ls as [|a rest]; [discriminate|].
    apply para_ok_parts in Hok as [_ [Hlines _]].
    apply forallb_line_ok_nonblank. exact Hlines.
  - cbn [cb_lines forallb].
    rewrite (classify_not_blank_nonblank thematic_line).
    + reflexivity.
    + intros E. unfold thematic_line in E.
      rewrite classify_canonical_thematic in E. discriminate.
  - discriminate Hsafe.
  - change (cb_ok (CHeading lvl ls)) with (heading_ok lvl ls) in Hok.
    apply heading_ok_parts in Hok as [Hlvl [_ [Hlines _]]].
    clear Hsafe. induction ls as [|l ls IH]; [reflexivity|].
    cbn [forallb] in Hlines. apply andb_true_iff in Hlines as [_ Hrest].
    cbn [cb_lines map forallb].
    rewrite (classify_not_blank_nonblank (heading_line lvl l)).
    + apply IH. exact Hrest.
    + intros E. rewrite (classify_canonical_heading lvl l Hlvl) in E.
      discriminate.
  - rewrite cb_lines_quote. clear Hsafe.
    induction (sep_lines (map cb_lines inner)) as [|l lines IH]; [reflexivity|].
    cbn [map forallb].
    rewrite (classify_not_blank_nonblank (quote_line l)).
    + exact IH.
    + intros E. rewrite classify_canonical_quote in E. discriminate.
  - discriminate Hsafe.
Qed.

Lemma scan_list_content_loose :
  forall lines ind marker blanks items,
    ls_loose (scan_list_content (LSt ind marker true blanks items) lines) = true.
Proof.
  induction lines as [|l lines IH]; intros ind marker blanks items;
    [reflexivity|].
  cbn [scan_list_content]. destruct (classify l); apply IH.
Qed.

Lemma scan_list_content_app :
  forall xs ys ls,
    scan_list_content ls (xs ++ ys)%list =
    scan_list_content (scan_list_content ls xs) ys.
Proof.
  induction xs as [|x xs IH]; intros ys ls; [reflexivity|].
  cbn [app]. destruct (classify x) eqn:Hclass;
    cbn [scan_list_content]; apply IH.
Qed.

Lemma scan_list_content_fields :
  forall lines ls,
    ls_indent (scan_list_content ls lines) = ls_indent ls /\
    ls_marker (scan_list_content ls lines) = ls_marker ls /\
    ls_items (scan_list_content ls lines) = ls_items ls.
Proof.
  intros lines ls. split.
  - revert ls. induction lines as [|l lines IH]; intros ls; [reflexivity|].
    cbn [scan_list_content]. destruct (classify l);
      rewrite IH; destruct ls; reflexivity.
  - split.
    + revert ls. induction lines as [|l lines IH]; intros ls; [reflexivity|].
      cbn [scan_list_content]. destruct (classify l);
        rewrite IH; destruct ls; reflexivity.
    + revert ls. induction lines as [|l lines IH]; intros ls; [reflexivity|].
      cbn [scan_list_content]. destruct (classify l);
        rewrite IH; destruct ls; reflexivity.
Qed.

Lemma scan_list_content_loose_ext :
  forall lines ind marker loose blanks done,
    ls_loose (scan_list_content (LSt ind marker loose blanks done) lines) =
    ls_loose (scan_list_content (LSt 0 "-"%char loose blanks []) lines).
Proof.
  induction lines as [|l lines IH]; intros ind marker loose blanks done;
    [reflexivity|].
  cbn [scan_list_content]. destruct (classify l);
    cbn [list_blank list_content]; apply IH.
Qed.

Lemma scan_list_content_blanks_last :
  forall lines ls,
    lines <> [] -> nonblank (last lines EmptyString) = true ->
    ls_blanks (scan_list_content ls lines) = false.
Proof.
  induction lines as [|l lines IH]; intros ls Hne Hlast; [congruence|].
  destruct lines as [|l2 lines'].
  - cbn [last scan_list_content] in Hlast |- *.
    destruct (classify l) as [| |f|q|lvl txt|m item|] eqn:Hclass;
      cbn [list_blank list_content].
    all: try (apply classify_kblank_blank in Hclass; unfold nonblank in Hlast;
              rewrite Hclass in Hlast; discriminate).
    all: destruct ls; reflexivity.
  - cbn [last] in Hlast.
    change (ls_blanks
      (scan_list_content
        (match classify l with
         | KBlank => list_blank ls
         | k => list_content ls k
         end) (l2 :: lines')) = false).
    apply IH; [discriminate|exact Hlast].
Qed.

Lemma forallb_nonblank_last :
  forall lines,
    lines <> [] -> forallb nonblank lines = true ->
    nonblank (last lines EmptyString) = true.
Proof.
  induction lines as [|l lines IH]; intros Hne Hall; [congruence|].
  cbn [forallb] in Hall. apply andb_true_iff in Hall as [Hl Hrest].
  destruct lines as [|l2 lines']; [exact Hl|].
  apply IH; [discriminate|exact Hrest].
Qed.

Lemma safe_item_last_nonblank :
  forall item,
    item <> [] ->
    forallb list_content_safe item = true -> forallb cb_ok item = true ->
    nonblank (last (sep_lines (map cb_lines item)) EmptyString) = true.
Proof.
  induction item as [|c rest IH]; intros Hne Hsafe Hok; [congruence|].
  cbn [forallb] in Hsafe, Hok.
  apply andb_true_iff in Hsafe as [Hsafec Hsaferest].
  apply andb_true_iff in Hok as [Hokc Hokrest].
  pose proof (safe_cb_lines_nonblank c Hsafec Hokc) as Hcnb.
  pose proof (cb_ok_lines_ok c Hokc) as Hclines.
  apply lines_ok_parts in Hclines as [Hcne _].
  destruct rest as [|c2 rest'].
  - cbn [map sep_lines]. apply forallb_nonblank_last; assumption.
  - change (nonblank
      (last (cb_lines c ++ EmptyString :: sep_lines (map cb_lines (c2 :: rest')))%list
        EmptyString) = true).
    assert (Htail : sep_lines (map cb_lines (c2 :: rest')) <> []).
    { apply sep_lines_nonempty. apply cb_ok_lines_ok.
      cbn [forallb] in Hokrest.
      apply andb_true_iff in Hokrest as [Hokc2 _]. exact Hokc2. }
    rewrite last_app_nonnil by discriminate.
    destruct (sep_lines (map cb_lines (c2 :: rest'))) as [|x xs] eqn:E;
      [congruence|].
    change (nonblank (last (x :: xs) EmptyString) = true).
    apply IH; [discriminate|exact Hsaferest|exact Hokrest].
Qed.

Lemma scan_list_content_after_blank :
  forall b rest ind marker items,
    classify b <> KBlank ->
    (forall m item, classify b <> KList m item) ->
    ls_loose
      (scan_list_content (list_blank (LSt ind marker false false items))
         (b :: rest)) = true.
Proof.
  intros b rest ind marker items Hblank Hlist.
  cbn [scan_list_content].
  destruct (classify b) as [| |f|q|lvl txt|m item|] eqn:Hclass.
  - exfalso. apply Hblank. reflexivity.
  - apply scan_list_content_loose.
  - apply scan_list_content_loose.
  - apply scan_list_content_loose.
  - apply scan_list_content_loose.
  - exfalso. apply (Hlist m item). reflexivity.
  - apply scan_list_content_loose.
Qed.

(*
One canonical item
------------------

The first place the render side and the parser side meet.  Render.v
decides looseness syntactically, per item, with `item_forces_loose` (an
item forces Loose when it holds more than one block, so its rendering
contains a blank line).  `scan_item_forces_loose` proves the parser agrees:
scanning that item's lines sets `ls_loose` exactly when the predicate
holds.  The rest of the section packages a cb_ok item as a run — its
lines, the blocks it emits, the state it leaves behind.
*)

Lemma scan_item_forces_loose :
  forall item a rest,
    forallb list_content_safe item = true ->
    forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    ls_loose
      (scan_list_content (LSt 0 "-"%char false false []) rest)
    = item_forces_loose item.
Proof.
  intros item a rest Hsafe Hok Hlines.
  unfold item_forces_loose. rewrite Hlines, scan_loose_eq.
  cbn [ls_loose ls_blanks].
  destruct item as [|c item']; [discriminate Hlines|].
  cbn [forallb] in Hsafe, Hok.
  apply andb_true_iff in Hsafe as [Hsafec _].
  apply andb_true_iff in Hok as [Hokc _].
  pose proof (safe_cb_lines_nonblank c Hsafec Hokc) as Hnonblank.
  destruct (cb_lines c) as [|first more] eqn:Hc.
  { pose proof (cb_ok_lines_ok c Hokc) as Hvalid.
    apply lines_ok_parts in Hvalid as [Hne _]. congruence. }
  cbn [forallb] in Hnonblank. apply andb_true_iff in Hnonblank as [Hfirst _].
  assert (Ha : nonblank a = true).
  { destruct item'; cbn [map sep_lines] in Hlines; rewrite Hc in Hlines;
      injection Hlines as <- _; exact Hfirst. }
  symmetry. apply lines_loose_cons_nonblank.
  intros E. apply classify_kblank_blank in E.
  unfold nonblank in Ha. rewrite E in Ha. discriminate.
Qed.

Lemma scan_canonical_item_state :
  forall item a rest ind marker done,
    forallb list_content_safe item = true ->
    forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    scan_list_content (LSt ind marker false false done) rest
    = LSt ind marker (item_forces_loose item) false done.
Proof.
  intros item a rest ind marker done Hsafe Hok Hlines.
  pose proof (scan_item_forces_loose item a rest Hsafe Hok Hlines) as Hloose.
  rewrite <- (scan_list_content_loose_ext rest ind marker false false done)
    in Hloose.
  pose proof (scan_list_content_fields rest
    (LSt ind marker false false done)) as [Hind [Hmarker Hitems]].
  assert (Hblank : ls_blanks
    (scan_list_content (LSt ind marker false false done) rest) = false).
  { destruct rest as [|r rest']; [reflexivity|].
    apply scan_list_content_blanks_last; [discriminate|].
    assert (Hlast := safe_item_last_nonblank item).
    destruct item as [|c item']; [discriminate Hlines|].
    specialize (Hlast ltac:(discriminate) Hsafe Hok).
    rewrite Hlines in Hlast. exact Hlast. }
  destruct (scan_list_content (LSt ind marker false false done)) eqn:E.
  cbn in Hind, Hmarker, Hitems, Hblank, Hloose |- *.
  subst. reflexivity.
Qed.

Lemma scan_canonical_item_state_loose :
  forall item a rest ind marker done,
    forallb list_content_safe item = true ->
    forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    scan_list_content (LSt ind marker true false done) rest
    = LSt ind marker true false done.
Proof.
  intros item a rest ind marker done Hsafe Hok Hlines.
  pose proof (scan_list_content_loose rest ind marker false done) as Hloose.
  pose proof (scan_list_content_fields rest
    (LSt ind marker true false done)) as [Hind [Hmarker Hitems]].
  assert (Hblank : ls_blanks
    (scan_list_content (LSt ind marker true false done) rest) = false).
  { destruct rest as [|r rest']; [reflexivity|].
    apply scan_list_content_blanks_last; [discriminate|].
    pose proof (safe_item_last_nonblank item) as Hlast.
    destruct item as [|c item']; [discriminate Hlines|].
    specialize (Hlast ltac:(discriminate) Hsafe Hok).
    rewrite Hlines in Hlast. exact Hlast. }
  destruct (scan_list_content (LSt ind marker true false done)) eqn:E.
  cbn in Hind, Hmarker, Hitems, Hblank, Hloose |- *.
  subst. reflexivity.
Qed.

Lemma canonical_item_run_exists :
  forall item,
    item <> [] -> forallb cb_ok item = true ->
    exists a rest bs st,
      sep_lines (map cb_lines item) = a :: rest /\
      run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
        (PPara []) = (bs, st).
Proof.
  intros item Hne Hok.
  destruct item as [|c item']; [congruence|].
  assert (Hc : lines_ok (cb_lines c) = true).
  { apply cb_ok_lines_ok. cbn [forallb] in Hok.
    apply andb_true_iff in Hok as [Hc _]. exact Hc. }
  destruct (sep_lines (map cb_lines (c :: item'))) as [|a rest] eqn:E.
  - exfalso. apply (sep_lines_nonempty (cb_lines c) (map cb_lines item') Hc).
    exact E.
  - destruct (run_lines
      (map (fun l => (bullet_cont ++ l)%string) (a :: rest)) (PPara []))
      as [bs st] eqn:Hrun.
    exists a, rest, bs, st. auto.
Qed.

Lemma canonical_item_first_nonblank :
  forall item a rest,
    forallb list_content_safe item = true -> forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest -> nonblank a = true.
Proof.
  intros item a rest Hsafe Hok Hlines.
  destruct item as [|c item']; [discriminate Hlines|].
  cbn [forallb] in Hsafe, Hok.
  apply andb_true_iff in Hsafe as [Hsafec _].
  apply andb_true_iff in Hok as [Hokc _].
  pose proof (safe_cb_lines_nonblank c Hsafec Hokc) as Hnb.
  destruct (cb_lines c) as [|first more] eqn:Hfirst.
  { pose proof (cb_ok_lines_ok c Hokc) as Hvalid.
    apply lines_ok_parts in Hvalid as [Hne _]. congruence. }
  cbn [map sep_lines] in Hlines.
  destruct item' as [|c2 item'']; rewrite Hfirst in Hlines;
    injection Hlines as <- <-;
    cbn [forallb] in Hnb; apply andb_true_iff in Hnb as [H _]; exact H.
Qed.

Lemma run_canonical_item :
  forall item a rest bs st,
    forallb list_content_safe item = true ->
    forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, st) ->
    (bs ++ finish st)%list = map cb_ast item.
Proof.
  intros item a rest bs st Hsafe Hok Hlines Hrun.
  pose proof (parse_lines_run _ _ _ _ Hrun) as Hparsed.
  pose proof
    (parse_safe_cblocks_pad item Hsafe bullet_cont bullet_cont_blank Hok)
    as Hcanonical.
  rewrite Hlines in Hcanonical. rewrite Hparsed in Hcanonical.
  exact Hcanonical.
Qed.

Lemma parse_safe_cblocks_pad_sep :
  forall item,
    forallb list_content_safe item = true ->
    forall pad, is_blank pad = true ->
    forall sep tail, classify sep = KBlank ->
    forallb cb_ok item = true ->
    parse_lines
      (map (fun l => (pad ++ l)%string) (sep_lines (map cb_lines item))
       ++ sep :: tail)%list (PPara [])
    = (map cb_ast item ++ parse_lines tail (PPara []))%list.
Proof.
  induction item as [|c rest IH]; intros Hsafe pad Hpad sep tail Hsep Hok.
  - cbn [map sep_lines app]. apply parse_lines_blank_nil. exact Hsep.
  - cbn [forallb] in Hsafe, Hok.
    apply andb_true_iff in Hsafe as [Hsafec Hsaferest].
    apply andb_true_iff in Hok as [Hokc Hokrest].
    destruct rest as [|c2 rest'].
    + cbn [map sep_lines].
      destruct (parse_cblock_pad c Hsafec pad Hpad) as [Hparse _].
      rewrite (Hparse sep tail Hsep Hokc). reflexivity.
    + cbn [map sep_lines]. rewrite map_app. cbn [map]. rewrite append_empty_r.
      rewrite app_cons_app.
      destruct (parse_cblock_pad c Hsafec pad Hpad) as [Hparse _].
      rewrite (Hparse pad _ (classify_blank pad Hpad) Hokc).
      change (cb_ast c ::
                parse_lines
                  (map (fun l => (pad ++ l)%string)
                     (sep_lines (map cb_lines (c2 :: rest')))
                   ++ sep :: tail)%list (PPara [])
              = (cb_ast c :: cb_ast c2 :: map cb_ast rest'
                 ++ parse_lines tail (PPara []))%list).
      rewrite (IH Hsaferest pad Hpad sep tail Hsep Hokrest).
      reflexivity.
Qed.

Lemma run_canonical_item_blank :
  forall item a rest bs st sep,
    forallb list_content_safe item = true ->
    forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, st) ->
    classify sep = KBlank ->
    exists more st',
      step sep st = (more, st') /\
      (bs ++ more ++ finish st')%list = map cb_ast item.
Proof.
  intros item a rest bs st sep Hsafe Hok Hlines Hrun Hsep.
  destruct (step sep st) as [more st'] eqn:Hstep.
  exists more, st'. split; [reflexivity|].
  pose proof
    (parse_safe_cblocks_pad_sep item Hsafe bullet_cont bullet_cont_blank
       sep [] Hsep Hok) as Hparsed.
  rewrite Hlines in Hparsed.
  rewrite (parse_lines_app_run
             (map (fun l => bullet_cont ++ l) (a :: rest)) [sep]
             (PPara [])) in Hparsed.
  rewrite Hrun in Hparsed. cbn [parse_lines run_lines] in Hparsed.
  rewrite Hstep in Hparsed. cbn [app] in Hparsed.
  rewrite app_nil_r in Hparsed. exact Hparsed.
Qed.

(*
Item-to-item transitions
------------------------

A sibling marker arrives while an item is open: the parser closes the
current item into `ls_items` and opens the next at the same indent and
marker.  Four lemmas, two axes.  `_tight`/`_loose` differ in the incoming
`ls_loose` flag and so in the AST the transition accumulates;
`_canonical_` versions specialize the generic ones to an item that is
cb_ok, discharging the side conditions from `cb_ok` rather than assuming
them.
*)

Lemma run_list_sibling_tight :
  forall item a rest bs st ls next head inner,
    forallb list_content_safe item = true ->
    forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, st) ->
    ls_indent ls = 0 -> ls_marker ls = "-"%char ->
    is_thematic (bullet_open ++ next) = false ->
    step next (PPara []) = (head, inner) ->
    no_columns inner = true ->
    run_lines [bullet_open ++ next] (PList ls (rev bs) st)
    = ([], PList (list_next ls (map cb_ast item) next) (rev head) inner).
Proof.
  intros item a rest bs st ls next head inner Hsafe Hok Hlines Hrun
    Hind Hmarker Htheme Hnext Hcols.
  pose proof (run_canonical_item item a rest bs st Hsafe Hok Hlines Hrun)
    as Hitem.
  cbn [run_lines].
  rewrite (step_list_sibling (bullet_open ++ next) "-"%char next ls
             (rev bs) st head inner).
  2: apply classify_bullet_open; exact Htheme.
  2: rewrite Hmarker; reflexivity.
  2: rewrite Hind, indent_of_bullet_open; reflexivity.
  2: exact Hnext.
  rewrite (pad_state_no_columns _ inner Hcols).
  cbn [run_lines app]. rewrite rev_involutive, Hitem. reflexivity.
Qed.

Lemma run_list_sibling_loose :
  forall item a rest bs st ls next head inner,
    forallb list_content_safe item = true ->
    forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, st) ->
    ls_indent ls = 0 -> ls_marker ls = "-"%char ->
    is_thematic (bullet_open ++ next) = false ->
    step next (PPara []) = (head, inner) ->
    no_columns inner = true ->
    run_lines [EmptyString; bullet_open ++ next] (PList ls (rev bs) st)
    = ([], PList
             (list_next (list_blank ls) (map cb_ast item) next)
             (rev head) inner).
Proof.
  intros item a rest bs st ls next head inner Hsafe Hok Hlines Hrun
    Hind Hmarker Htheme Hnext Hcols.
  destruct (run_canonical_item_blank item a rest bs st EmptyString
              Hsafe Hok Hlines Hrun (classify_blank EmptyString eq_refl))
    as [more [st' [Hblank Hitem]]].
  cbn [run_lines].
  rewrite (step_list_blank EmptyString ls (rev bs) st more st'
             (classify_blank EmptyString eq_refl) Hblank).
  assert (Hm : Ascii.eqb "-"%char (ls_marker (list_blank ls)) = true).
  { change (Ascii.eqb "-"%char (ls_marker ls) = true).
    rewrite Hmarker. reflexivity. }
  assert (Hi : Nat.ltb (ls_indent (list_blank ls))
                 (indent_of (bullet_open ++ next)) = false).
  { change (Nat.ltb (ls_indent ls) (indent_of (bullet_open ++ next)) = false).
    rewrite Hind, indent_of_bullet_open. reflexivity. }
  rewrite (step_list_sibling (bullet_open ++ next) "-"%char next
             (list_blank ls) (rev more ++ rev bs)%list st' head inner
             (classify_bullet_open next Htheme) Hm Hi Hnext).
  rewrite (pad_state_no_columns _ inner Hcols).
  cbn [run_lines app].
  rewrite rev_app_distr, !rev_involutive, <- app_assoc, Hitem. reflexivity.
Qed.

Lemma run_first_canonical_item :
  forall item a rest bs st,
    forallb list_content_safe item = true ->
    forallb cb_ok item = true ->
    item_marker_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, st) ->
    run_lines (indent_lines bullet_open bullet_cont (a :: rest)) (PPara [])
    = ([], PList
             (scan_list_content (LSt 0 "-"%char false false []) rest)
             (rev bs) st).
Proof.
  intros item a rest bs st Hsafe Hok Hmarker Hlines Hrun.
  destruct item as [|c item']; [discriminate Hlines|].
  cbn [forallb] in Hsafe, Hok.
  apply andb_true_iff in Hsafe as [Hsafec _].
  apply andb_true_iff in Hok as [Hokc _].
  destruct (safe_cblock_first c Hsafec Hokc)
    as [first [cmore [Hfirst Hnotlist]]].
  pose proof (safe_cblock_no_columns c Hsafec Hokc first cmore Hfirst) as Hcols.
  unfold item_marker_ok, item_first_line in Hmarker.
  rewrite Hfirst in Hmarker.
  apply negb_true_iff in Hmarker.
  cbn [map sep_lines] in Hlines.
  destruct item' as [|c2 item'']; rewrite Hfirst in Hlines;
    injection Hlines as <- <-;
    eapply run_first_list_item; eassumption.
Qed.

Lemma run_list_sibling_canonical_tight :
  forall item a rest bs st next na nr nbs nst ls,
    forallb list_content_safe item = true ->
    forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, st) ->
    forallb list_content_safe next = true ->
    forallb cb_ok next = true ->
    item_marker_ok next = true ->
    sep_lines (map cb_lines next) = na :: nr ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (na :: nr))
      (PPara []) = (nbs, nst) ->
    ls_indent ls = 0 -> ls_marker ls = "-"%char ->
    run_lines (indent_lines bullet_open bullet_cont (na :: nr))
      (PList ls (rev bs) st)
    = ([], PList
             (scan_list_content
                (list_next ls (map cb_ast item) na) nr)
             (rev nbs) nst).
Proof.
  intros item a rest bs st next na nr nbs nst ls
    Hsafe Hok Hlines Hrun Hsafen Hokn Hmarker Hnext Hnrun Hind Hmark.
  destruct next as [|c next']; [discriminate Hnext|].
  cbn [forallb] in Hsafen, Hokn.
  apply andb_true_iff in Hsafen as [Hsafec _].
  apply andb_true_iff in Hokn as [Hokc _].
  destruct (safe_cblock_first c Hsafec Hokc)
    as [first [more [Hfirst Hnotlist]]].
  unfold item_marker_ok, item_first_line in Hmarker.
  rewrite Hfirst in Hmarker. apply negb_true_iff in Hmarker.
  cbn [map sep_lines] in Hnext.
  destruct next' as [|c2 next'']; rewrite Hfirst in Hnext;
    injection Hnext as Hna Hnr; subst na.
  all: pose proof (safe_cblock_no_columns c Hsafec Hokc first more Hfirst)
         as Hcols;
       pose proof (run_lines_first_unpadded first nr Hnotlist Hcols) as Hsame;
       rewrite Hnrun in Hsame;
       cbn [map run_lines indent_lines] in Hsame |- *;
       destruct (step first (PPara [])) as [head inner] eqn:Hhead;
       destruct (run_lines (map (fun l => bullet_cont ++ l) nr) inner)
         as [more' final] eqn:Hmore;
       inversion Hsame; subst nbs nst;
       pose proof
         (run_list_sibling_tight item a rest bs st ls first head inner
            Hsafe Hok Hlines Hrun Hind Hmark Hmarker Hhead
            ltac:(cbn [snd] in Hcols; exact Hcols)) as Hsibling;
       pose proof
         (run_lines_list_cont nr (list_next ls (map cb_ast item) first)
            (rev head) inner more' final) as Hcont;
       specialize (Hcont ltac:(unfold list_next; destruct (is_blank first);
                               exact Hind) Hmore);
       pose proof
         (run_lines_continue [(bullet_open ++ first)%string]
            (map (fun l => (bullet_cont ++ l)%string) nr)
            (PList ls (rev bs) st) []
            (PList (list_next ls (map cb_ast item) first) (rev head) inner)
            []
            (PList (scan_list_content
                       (list_next ls (map cb_ast item) first) nr)
               (rev more' ++ rev head)%list final)
            Hsibling Hcont) as Hall;
       rewrite rev_app_distr. cbn [app] in Hall. exact Hall.
  Unshelve. all: assumption.
Qed.

Lemma run_list_sibling_canonical_loose :
  forall item a rest bs st next na nr nbs nst ls,
    forallb list_content_safe item = true ->
    forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, st) ->
    forallb list_content_safe next = true ->
    forallb cb_ok next = true ->
    item_marker_ok next = true ->
    sep_lines (map cb_lines next) = na :: nr ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (na :: nr))
      (PPara []) = (nbs, nst) ->
    ls_indent ls = 0 -> ls_marker ls = "-"%char ->
    run_lines (EmptyString :: indent_lines bullet_open bullet_cont (na :: nr))
      (PList ls (rev bs) st)
    = ([], PList
             (scan_list_content
                (list_next (list_blank ls) (map cb_ast item) na) nr)
             (rev nbs) nst).
Proof.
  intros item a rest bs st next na nr nbs nst ls
    Hsafe Hok Hlines Hrun Hsafen Hokn Hmarker Hnext Hnrun Hind Hmark.
  destruct next as [|c next']; [discriminate Hnext|].
  cbn [forallb] in Hsafen, Hokn.
  apply andb_true_iff in Hsafen as [Hsafec _].
  apply andb_true_iff in Hokn as [Hokc _].
  destruct (safe_cblock_first c Hsafec Hokc)
    as [first [cmore [Hfirst Hnotlist]]].
  unfold item_marker_ok, item_first_line in Hmarker.
  rewrite Hfirst in Hmarker. apply negb_true_iff in Hmarker.
  cbn [map sep_lines] in Hnext.
  destruct next' as [|c2 next'']; rewrite Hfirst in Hnext;
    injection Hnext as Hna Hnr; subst na.
  all: pose proof (safe_cblock_no_columns c Hsafec Hokc first cmore Hfirst)
         as Hcols;
       pose proof (run_lines_first_unpadded first nr Hnotlist Hcols) as Hsame;
       rewrite Hnrun in Hsame;
       cbn [map run_lines indent_lines] in Hsame |- *;
       destruct (step first (PPara [])) as [head inner] eqn:Hhead;
       destruct (run_lines (map (fun l => bullet_cont ++ l) nr) inner)
         as [more' final] eqn:Hmore;
       inversion Hsame; subst nbs nst;
       pose proof
         (run_list_sibling_loose item a rest bs st ls first head inner
            Hsafe Hok Hlines Hrun Hind Hmark Hmarker Hhead
            ltac:(cbn [snd] in Hcols; exact Hcols)) as Hsibling;
       pose proof
         (run_lines_list_cont nr
            (list_next (list_blank ls) (map cb_ast item) first)
            (rev head) inner more' final) as Hcont;
       specialize (Hcont ltac:(unfold list_next, list_blank;
                               destruct (is_blank first); exact Hind) Hmore);
       pose proof
         (run_lines_continue [EmptyString; (bullet_open ++ first)%string]
            (map (fun l => (bullet_cont ++ l)%string) nr)
            (PList ls (rev bs) st) []
            (PList (list_next (list_blank ls) (map cb_ast item) first)
               (rev head) inner)
            []
            (PList (scan_list_content
                       (list_next (list_blank ls) (map cb_ast item) first) nr)
               (rev more' ++ rev head)%list final)
            Hsibling Hcont) as Hall;
       rewrite rev_app_distr. cbn [app] in Hall. exact Hall.
  Unshelve. all: assumption.
Qed.

(*
The run of siblings
-------------------

Induction over the remaining items, tight and loose, in two forms:
`parse_canonical_list_tail_*` for a list that ends the input, and
`run_canonical_list_tail_*` for one that has to hand a state back to the
caller.  Both consume `canonical_item_lines` per item; the separator
between them is the only difference between the flavors, so the loose case
gets its own line function (`canonical_loose_tail_lines`).

The tight and loose proofs are near-identical tactic text and are the most
obvious duplication in the file.  Collapsing them wants a record holding
the flavor's line function, its `ls_loose` value, and its per-item side
condition (`item_forces_loose = false` in the tight case, nothing in the
loose one) — not a bare boolean, which would leave the side condition
dangling.  Not worth doing until the state invariants below have settled
names.
*)

Definition canonical_item_lines (item : list cblock) : list string :=
  indent_lines bullet_open bullet_cont (sep_lines (map cb_lines item)).

Definition canonical_item_ast (item : list cblock) : blocks := map cb_ast item.

Lemma parse_canonical_list_tail_tight :
  forall remaining completed item a rest bs st,
    forallb (fun it => nonempty it && forallb cb_ok it)%bool remaining = true ->
    forallb item_marker_ok remaining = true ->
    forallb (forallb list_content_safe) remaining = true ->
    forallb (fun it => negb (item_forces_loose it)) remaining = true ->
    forallb list_content_safe item = true -> forallb cb_ok item = true ->
    item_forces_loose item = false ->
    sep_lines (map cb_lines item) = a :: rest ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, st) ->
    parse_lines
      (list_lines Tight (map canonical_item_lines remaining))
      (PList (LSt 0 "-"%char false false (rev completed)) (rev bs) st)
    = [mk (BulletList Tight
             (completed ++ canonical_item_ast item
              :: map canonical_item_ast remaining)%list)].
Proof.
  induction remaining as [|next remaining IH]; intros completed item a rest bs st
    Hokitems Hmarkers Hsafeitems Hforceitems Hsafe Hok Hforce Hlines Hrun.
  - cbn [map list_lines parse_lines].
    pose proof (run_canonical_item item a rest bs st Hsafe Hok Hlines Hrun)
      as Hitem.
    cbn [finish ls_loose ls_items]. rewrite rev_involutive, Hitem.
    cbn [rev]. rewrite rev_involutive. reflexivity.
  - cbn [forallb] in Hokitems, Hmarkers, Hsafeitems, Hforceitems.
    apply andb_true_iff in Hokitems as [Hoknext Hokremaining].
    apply andb_true_iff in Hoknext as [Hnenext Hoknext].
    apply andb_true_iff in Hmarkers as [Hmarknext Hmarkremaining].
    apply andb_true_iff in Hsafeitems as [Hsafenext Hsaferemaining].
    apply andb_true_iff in Hforceitems as [Hforcenext Hforceremaining].
    apply negb_true_iff in Hforcenext.
    assert (Hnextne : next <> []).
    { destruct next; [discriminate Hnenext|discriminate]. }
    destruct (canonical_item_run_exists next Hnextne Hoknext)
      as [na [nr [nbs [nst [Hnext Hnrun]]]]].
    pose proof (run_list_sibling_canonical_tight
      item a rest bs st next na nr nbs nst
      (LSt 0 "-"%char false false (rev completed))
      Hsafe Hok Hlines Hrun Hsafenext Hoknext Hmarknext Hnext Hnrun
      eq_refl eq_refl) as Hprefix.
    pose proof (canonical_item_first_nonblank next na nr
      Hsafenext Hoknext Hnext) as Hnonblank.
    assert (Hnotblank : is_blank na = false).
    { unfold nonblank in Hnonblank. apply negb_true_iff in Hnonblank.
      exact Hnonblank. }
    unfold list_next in Hprefix. rewrite Hnotblank in Hprefix.
    cbn [ls_indent ls_marker ls_loose ls_blanks ls_items orb]
      in Hprefix.
    pose proof (scan_canonical_item_state next na nr 0 "-"%char
      (map cb_ast item :: rev completed)%list
      Hsafenext Hoknext Hnext) as Hscan.
    setoid_rewrite Hscan in Hprefix.
    rewrite Hforcenext in Hprefix.
    assert (Hrev : (canonical_item_ast item :: rev completed)%list =
                   rev (completed ++ [canonical_item_ast item])%list).
    { rewrite rev_app_distr. reflexivity. }
    unfold canonical_item_ast in Hrev.
    setoid_rewrite Hrev in Hprefix.
    destruct remaining as [|next2 remaining'].
    + cbn [map list_lines canonical_item_lines].
      unfold canonical_item_lines.
      rewrite Hnext.
      rewrite (parse_lines_run _ _ _ _ Hprefix).
      cbn [app].
      pose proof
        (IH (completed ++ [canonical_item_ast item])%list next na nr nbs nst
          Hokremaining Hmarkremaining Hsaferemaining Hforceremaining
          Hsafenext Hoknext Hforcenext Hnext Hnrun) as Htail.
      cbn [map list_lines parse_lines] in Htail.
      unfold canonical_item_ast in Htail |- *.
      setoid_rewrite Htail. rewrite <- app_assoc. reflexivity.
    + change (parse_lines
        (canonical_item_lines next ++
         list_lines Tight (map canonical_item_lines (next2 :: remaining')))%list
        (PList (LSt 0 "-"%char false false (rev completed)) (rev bs) st) =
        [mk (BulletList Tight
          (completed ++ canonical_item_ast item ::
            canonical_item_ast next ::
            map canonical_item_ast (next2 :: remaining'))%list)]).
      unfold canonical_item_lines at 1. rewrite Hnext.
      rewrite parse_lines_app_run, Hprefix. cbn [app].
      pose proof
        (IH (completed ++ [canonical_item_ast item])%list next na nr nbs nst
          Hokremaining Hmarkremaining Hsaferemaining Hforceremaining
          Hsafenext Hoknext Hforcenext Hnext Hnrun) as Htail.
      unfold canonical_item_ast in Htail |- *.
      setoid_rewrite Htail. rewrite <- app_assoc. reflexivity.
Qed.

Definition canonical_loose_tail_lines (items : list (list cblock)) : list string :=
  match items with
  | [] => []
  | _ => EmptyString :: list_lines Loose (map canonical_item_lines items)
  end.

Lemma parse_canonical_list_tail_loose :
  forall remaining completed item a rest bs st,
    forallb (fun it => nonempty it && forallb cb_ok it)%bool remaining = true ->
    forallb item_marker_ok remaining = true ->
    forallb (forallb list_content_safe) remaining = true ->
    forallb list_content_safe item = true -> forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, st) ->
    parse_lines
      (canonical_loose_tail_lines remaining)
      (PList (LSt 0 "-"%char true false (rev completed)) (rev bs) st)
    = [mk (BulletList Loose
             (completed ++ canonical_item_ast item
              :: map canonical_item_ast remaining)%list)].
Proof.
  induction remaining as [|next remaining IH]; intros completed item a rest bs st
    Hokitems Hmarkers Hsafeitems Hsafe Hok Hlines Hrun.
  - cbn [canonical_loose_tail_lines map list_lines parse_lines].
    pose proof (run_canonical_item item a rest bs st Hsafe Hok Hlines Hrun)
      as Hitem.
    cbn [finish ls_loose ls_items]. rewrite rev_involutive, Hitem.
    cbn [rev]. rewrite rev_involutive. reflexivity.
  - cbn [forallb] in Hokitems, Hmarkers, Hsafeitems.
    apply andb_true_iff in Hokitems as [Hoknext Hokremaining].
    apply andb_true_iff in Hoknext as [Hnenext Hoknext].
    apply andb_true_iff in Hmarkers as [Hmarknext Hmarkremaining].
    apply andb_true_iff in Hsafeitems as [Hsafenext Hsaferemaining].
    assert (Hnextne : next <> []).
    { destruct next; [discriminate Hnenext|discriminate]. }
    destruct (canonical_item_run_exists next Hnextne Hoknext)
      as [na [nr [nbs [nst [Hnext Hnrun]]]]].
    pose proof (run_list_sibling_canonical_loose
      item a rest bs st next na nr nbs nst
      (LSt 0 "-"%char true false (rev completed))
      Hsafe Hok Hlines Hrun Hsafenext Hoknext Hmarknext Hnext Hnrun
      eq_refl eq_refl) as Hprefix.
    pose proof (canonical_item_first_nonblank next na nr
      Hsafenext Hoknext Hnext) as Hnonblank.
    assert (Hnotblank : is_blank na = false).
    { unfold nonblank in Hnonblank. apply negb_true_iff in Hnonblank.
      exact Hnonblank. }
    unfold list_next, list_blank in Hprefix. rewrite Hnotblank in Hprefix.
    cbn [ls_indent ls_marker ls_loose ls_blanks ls_items orb] in Hprefix.
    pose proof (scan_canonical_item_state_loose next na nr 0 "-"%char
      (map cb_ast item :: rev completed)%list
      Hsafenext Hoknext Hnext) as Hscan.
    setoid_rewrite Hscan in Hprefix.
    assert (Hrev : (map cb_ast item :: rev completed)%list =
                   rev (completed ++ [map cb_ast item])%list).
    { rewrite rev_app_distr. reflexivity. }
    setoid_rewrite Hrev in Hprefix.
    destruct remaining as [|next2 remaining'].
    + cbn [canonical_loose_tail_lines map list_lines].
      unfold canonical_item_lines. rewrite Hnext.
      rewrite (parse_lines_run _ _ _ _ Hprefix). cbn [app].
      pose proof
        (IH (completed ++ [canonical_item_ast item])%list next na nr nbs nst
          Hokremaining Hmarkremaining Hsaferemaining
          Hsafenext Hoknext Hnext Hnrun) as Htail.
      cbn [canonical_loose_tail_lines map list_lines parse_lines] in Htail.
      unfold canonical_item_ast in Htail |- *.
      setoid_rewrite Htail. rewrite <- app_assoc. reflexivity.
    + change (parse_lines
        (EmptyString :: canonical_item_lines next ++
         canonical_loose_tail_lines (next2 :: remaining'))%list
        (PList (LSt 0 "-"%char true false (rev completed)) (rev bs) st) =
        [mk (BulletList Loose
          (completed ++ canonical_item_ast item ::
            canonical_item_ast next ::
            map canonical_item_ast (next2 :: remaining'))%list)]).
      unfold canonical_item_lines at 1. rewrite Hnext.
      rewrite app_comm_cons.
      rewrite (parse_lines_app_run
        (EmptyString :: indent_lines bullet_open bullet_cont (na :: nr))
        (canonical_loose_tail_lines (next2 :: remaining'))
        (PList (LSt 0 "-"%char true false (rev completed)) (rev bs) st)).
      rewrite Hprefix. cbn [app].
      pose proof
        (IH (completed ++ [canonical_item_ast item])%list next na nr nbs nst
          Hokremaining Hmarkremaining Hsaferemaining
          Hsafenext Hoknext Hnext Hnrun) as Htail.
      unfold canonical_item_ast in Htail |- *.
      setoid_rewrite Htail. rewrite <- app_assoc. reflexivity.
Qed.

Lemma list_lines_tight_cons :
  forall item remaining,
    list_lines Tight (map canonical_item_lines (item :: remaining)) =
    (canonical_item_lines item ++
      list_lines Tight (map canonical_item_lines remaining))%list.
Proof.
  intros item remaining. destruct remaining; cbn [map list_lines];
    rewrite ?app_nil_r; reflexivity.
Qed.

Lemma canonical_loose_tail_cons :
  forall item remaining,
    canonical_loose_tail_lines (item :: remaining) =
    (EmptyString :: canonical_item_lines item ++
      canonical_loose_tail_lines remaining)%list.
Proof.
  intros item remaining. destruct remaining; cbn [canonical_loose_tail_lines map list_lines];
    rewrite ?app_nil_r; reflexivity.
Qed.

Lemma run_canonical_list_tail_tight :
  forall remaining completed item a rest bs st,
    forallb (fun it => nonempty it && forallb cb_ok it)%bool remaining = true ->
    forallb item_marker_ok remaining = true ->
    forallb (forallb list_content_safe) remaining = true ->
    forallb (fun it => negb (item_forces_loose it)) remaining = true ->
    forallb list_content_safe item = true -> forallb cb_ok item = true ->
    item_forces_loose item = false ->
    sep_lines (map cb_lines item) = a :: rest ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, st) ->
    exists before last la lr lbs lst,
      (before ++ [canonical_item_ast last])%list =
        (completed ++ canonical_item_ast item ::
          map canonical_item_ast remaining)%list /\
      forallb list_content_safe last = true /\
      forallb cb_ok last = true /\
      item_forces_loose last = false /\
      sep_lines (map cb_lines last) = la :: lr /\
      run_lines (map (fun l => (bullet_cont ++ l)%string) (la :: lr))
        (PPara []) = (lbs, lst) /\
      run_lines (list_lines Tight (map canonical_item_lines remaining))
        (PList (LSt 0 "-"%char false false (rev completed)) (rev bs) st) =
      ([], PList (LSt 0 "-"%char false false (rev before)) (rev lbs) lst).
Proof.
  induction remaining as [|next remaining IH]; intros completed item a rest bs st
    Hokitems Hmarkers Hsafeitems Hforceitems Hsafe Hok Hforce Hlines Hrun.
  - exists completed, item, a, rest, bs, st. repeat split; try assumption.
  - cbn [forallb] in Hokitems, Hmarkers, Hsafeitems, Hforceitems.
    apply andb_true_iff in Hokitems as [Hoknext Hokremaining].
    apply andb_true_iff in Hoknext as [Hnenext Hoknext].
    apply andb_true_iff in Hmarkers as [Hmarknext Hmarkremaining].
    apply andb_true_iff in Hsafeitems as [Hsafenext Hsaferemaining].
    apply andb_true_iff in Hforceitems as [Hforcenext Hforceremaining].
    apply negb_true_iff in Hforcenext.
    assert (Hnextne : next <> []).
    { destruct next; [discriminate Hnenext|discriminate]. }
    destruct (canonical_item_run_exists next Hnextne Hoknext)
      as [na [nr [nbs [nst [Hnext Hnrun]]]]].
    pose proof (run_list_sibling_canonical_tight
      item a rest bs st next na nr nbs nst
      (LSt 0 "-"%char false false (rev completed))
      Hsafe Hok Hlines Hrun Hsafenext Hoknext Hmarknext Hnext Hnrun
      eq_refl eq_refl) as Hprefix.
    pose proof (canonical_item_first_nonblank next na nr
      Hsafenext Hoknext Hnext) as Hnonblank.
    unfold nonblank in Hnonblank. apply negb_true_iff in Hnonblank.
    unfold list_next in Hprefix. rewrite Hnonblank in Hprefix.
    cbn [ls_indent ls_marker ls_loose ls_blanks ls_items orb] in Hprefix.
    pose proof (scan_canonical_item_state next na nr 0 "-"%char
      (map cb_ast item :: rev completed)%list
      Hsafenext Hoknext Hnext) as Hscan.
    setoid_rewrite Hscan in Hprefix. rewrite Hforcenext in Hprefix.
    assert (Hrev : (canonical_item_ast item :: rev completed)%list =
      rev (completed ++ [canonical_item_ast item])%list).
    { rewrite rev_app_distr. reflexivity. }
    unfold canonical_item_ast in Hrev. setoid_rewrite Hrev in Hprefix.
    destruct (IH (completed ++ [canonical_item_ast item])%list
      next na nr nbs nst Hokremaining Hmarkremaining Hsaferemaining
      Hforceremaining Hsafenext Hoknext Hforcenext Hnext Hnrun)
      as (before & last & la & lr & lbs & lst & Hbefore & Hlsafe & Hlok &
          Hlforce & Hllines & Hlrun & Htail).
    exists before, last, la, lr, lbs, lst. repeat split; try assumption.
    + rewrite Hbefore. cbn [map]. rewrite <- app_assoc. reflexivity.
    + rewrite list_lines_tight_cons. unfold canonical_item_lines at 1.
    rewrite Hnext, run_lines_app, Hprefix. cbn [app].
    unfold canonical_item_ast in Htail |- *.
    rewrite Htail. cbn [app].
    reflexivity.
Qed.

Lemma run_canonical_list_tail_loose :
  forall remaining completed item a rest bs st,
    forallb (fun it => nonempty it && forallb cb_ok it)%bool remaining = true ->
    forallb item_marker_ok remaining = true ->
    forallb (forallb list_content_safe) remaining = true ->
    forallb list_content_safe item = true -> forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, st) ->
    exists before last la lr lbs lst,
      (before ++ [canonical_item_ast last])%list =
        (completed ++ canonical_item_ast item ::
          map canonical_item_ast remaining)%list /\
      forallb list_content_safe last = true /\
      forallb cb_ok last = true /\
      sep_lines (map cb_lines last) = la :: lr /\
      run_lines (map (fun l => (bullet_cont ++ l)%string) (la :: lr))
        (PPara []) = (lbs, lst) /\
      run_lines (canonical_loose_tail_lines remaining)
        (PList (LSt 0 "-"%char true false (rev completed)) (rev bs) st) =
      ([], PList (LSt 0 "-"%char true false (rev before)) (rev lbs) lst).
Proof.
  induction remaining as [|next remaining IH]; intros completed item a rest bs st
    Hokitems Hmarkers Hsafeitems Hsafe Hok Hlines Hrun.
  - exists completed, item, a, rest, bs, st. repeat split; try assumption.
  - cbn [forallb] in Hokitems, Hmarkers, Hsafeitems.
    apply andb_true_iff in Hokitems as [Hoknext Hokremaining].
    apply andb_true_iff in Hoknext as [Hnenext Hoknext].
    apply andb_true_iff in Hmarkers as [Hmarknext Hmarkremaining].
    apply andb_true_iff in Hsafeitems as [Hsafenext Hsaferemaining].
    assert (Hnextne : next <> []).
    { destruct next; [discriminate Hnenext|discriminate]. }
    destruct (canonical_item_run_exists next Hnextne Hoknext)
      as [na [nr [nbs [nst [Hnext Hnrun]]]]].
    pose proof (run_list_sibling_canonical_loose
      item a rest bs st next na nr nbs nst
      (LSt 0 "-"%char true false (rev completed))
      Hsafe Hok Hlines Hrun Hsafenext Hoknext Hmarknext Hnext Hnrun
      eq_refl eq_refl) as Hprefix.
    pose proof (canonical_item_first_nonblank next na nr
      Hsafenext Hoknext Hnext) as Hnonblank.
    unfold nonblank in Hnonblank. apply negb_true_iff in Hnonblank.
    unfold list_next, list_blank in Hprefix. rewrite Hnonblank in Hprefix.
    cbn [ls_indent ls_marker ls_loose ls_blanks ls_items orb] in Hprefix.
    pose proof (scan_canonical_item_state_loose next na nr 0 "-"%char
      (map cb_ast item :: rev completed)%list
      Hsafenext Hoknext Hnext) as Hscan.
    setoid_rewrite Hscan in Hprefix.
    assert (Hrev : (canonical_item_ast item :: rev completed)%list =
      rev (completed ++ [canonical_item_ast item])%list).
    { rewrite rev_app_distr. reflexivity. }
    unfold canonical_item_ast in Hrev. setoid_rewrite Hrev in Hprefix.
    destruct (IH (completed ++ [canonical_item_ast item])%list
      next na nr nbs nst Hokremaining Hmarkremaining Hsaferemaining
      Hsafenext Hoknext Hnext Hnrun)
      as (before & last & la & lr & lbs & lst & Hbefore & Hlsafe & Hlok &
          Hllines & Hlrun & Htail).
    exists before, last, la, lr, lbs, lst. repeat split; try assumption.
    + rewrite Hbefore. cbn [map]. rewrite <- app_assoc. reflexivity.
    + rewrite canonical_loose_tail_cons. unfold canonical_item_lines at 1.
      rewrite Hnext, app_comm_cons, run_lines_app, Hprefix. cbn [app].
      unfold canonical_item_ast in Htail |- *. rewrite Htail. reflexivity.
Qed.

(*
Closing the list
----------------

The last step, and the one that constrains the canonical form.  A list
ends at a blank line followed by a line that opens something else; the
blank alone is not enough, since a blank inside a list only sets `loose`.
That is why `cblocks_ok` forbids two adjacent CLists: with only canonical
renderings to look at, a blank line between two lists is indistinguishable
from a blank line inside one, so the boundary is not recoverable and the
roundtrip would be false rather than merely unproven.

The four lemmas below are generic support the closing proofs happen to
need; they belong to no layer in particular.
*)

Lemma negb_existsb_forallb_negb :
  forall {A : Type} (f : A -> bool) xs,
    negb (existsb f xs) = true -> forallb (fun x => negb (f x)) xs = true.
Proof.
  intros A f xs. induction xs as [|x xs IH]; intros H; [reflexivity|].
  cbn [existsb forallb] in H |- *.
  apply negb_true_iff in H. apply orb_false_iff in H as [Hx Hxs].
  rewrite Hx. cbn. apply IH. apply negb_true_iff. exact Hxs.
Qed.

Lemma drop_leading_ws_indent_zero :
  forall l, drop_leading_ws l = l -> indent_of l = 0.
Proof.
  induction l as [|c l IH]; intros H; [reflexivity|].
  cbn [drop_leading_ws] in H. cbn [indent_of].
  destruct (is_ws c) eqn:Hws.
  - pose proof (drop_leading_ws_length l) as Hlen.
    rewrite H in Hlen. cbn [String.length] in Hlen.
    exfalso. exact (Nat.nle_succ_diag_l _ Hlen).
  - reflexivity.
Qed.

Lemma step_blank_lazy_false :
  forall l st, classify l = KBlank -> lazy_ok (snd (step l st)) = false.
Proof.
  intros l st Hblank. induction st as
    [cur|lvl cur|f acc|done inner IH|ls done inner IH].
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hblank eq_refl). reflexivity.
    + rewrite (step_para_flush l c cur' Hblank). reflexivity.
  - unfold step. cbn [step_fuel]. rewrite Hblank. reflexivity.
  - destruct (fence_close f l) eqn:Hclose.
    + rewrite (step_fence_close l f acc Hclose). reflexivity.
    + rewrite (step_fence_content l f acc Hclose). reflexivity.
  - rewrite (step_quote_close l KBlank done inner [] (PPara [])
      Hblank eq_refl eq_refl eq_refl). reflexivity.
  - destruct (step l inner) as [bs inner'] eqn:Hstep.
    rewrite (step_list_blank l ls done inner bs inner' Hblank Hstep).
    cbn [snd lazy_ok]. exact IH.
Qed.

Lemma cb_lines_first_line_ok :
  forall cb first rest,
    is_clist cb = false -> cb_ok cb = true ->
    cb_lines cb = first :: rest -> line_ok first = true.
Proof.
  intros cb first rest Hnonlist Hok Hlines.
  destruct cb as [ls| |info content|lvl ls|inner|sp items].
  - change (para_ok ls = true) in Hok. destruct ls as [|l ls'];
      [discriminate Hok|].
    apply para_ok_parts in Hok as [_ [Hok _]].
    cbn [cb_lines] in Hlines. injection Hlines as <- <-. cbn [forallb] in Hok.
    apply andb_true_iff in Hok as [Hfirst _]. exact Hfirst.
  - cbn [cb_lines] in Hlines. injection Hlines as <- <-. reflexivity.
  - change (code_ok info content = true) in Hok.
    apply code_ok_parts in Hok as [Hinfo _].
    cbn [cb_lines] in Hlines. injection Hlines as <- <-.
    unfold code_open, line_ok. apply andb_true_iff; split.
    + apply andb_true_iff; split.
      * reflexivity.
      * rewrite no_nl_append, (info_no_nl _ Hinfo). reflexivity.
    + apply String.eqb_eq. reflexivity.
  - change (heading_ok lvl ls = true) in Hok.
    apply heading_ok_parts in Hok as [Hlvl [_ [Hok _]]].
    destruct ls as [|l ls']; [discriminate Hlines|].
    cbn [cb_lines map] in Hlines. injection Hlines as <- <-.
    cbn [forallb] in Hok. apply andb_true_iff in Hok as [Hl _].
    unfold line_ok. apply andb_true_iff; split.
    + apply andb_true_iff; split.
      * apply classify_not_blank_nonblank. intros E.
        rewrite (classify_canonical_heading lvl l Hlvl) in E. discriminate.
      * rewrite heading_line_no_nl. apply line_ok_no_nl. exact Hl.
    + apply String.eqb_eq. unfold heading_line.
      rewrite drop_leading_ws_hashes by exact Hlvl. reflexivity.
  - rewrite cb_lines_quote in Hlines.
    destruct (sep_lines (map cb_lines inner)) as [|l ls] eqn:E;
      [discriminate Hlines|].
    cbn [map] in Hlines. injection Hlines as <- <-.
    unfold quote_line, quote_prefix, line_ok, nonblank, nonempty_str.
    cbn [drop_leading_ws is_ws no_nl].
    pose proof (cb_ok_lines_ok (CQuote inner) Hok) as Hall.
    apply lines_ok_parts in Hall as [_ [Hall _]].
    rewrite cb_lines_quote, E in Hall. cbn [map forallb no_nl] in Hall.
    apply andb_true_iff in Hall as [Hl _].
    apply andb_true_iff; split.
    + apply andb_true_iff; split; [reflexivity|exact Hl].
    + apply String.eqb_eq. reflexivity.
  - discriminate Hnonlist.
Qed.

Lemma parse_list_current_then_nonlist :
  forall loose completed item a rest bs st next first more tail,
    forallb list_content_safe item = true ->
    forallb cb_ok item = true ->
    sep_lines (map cb_lines item) = a :: rest ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) (a :: rest))
      (PPara []) = (bs, st) ->
    is_clist next = false -> cb_ok next = true ->
    cb_lines next = first :: more ->
    parse_lines
      (EmptyString :: first :: more ++ tail)%list
      (PList (LSt 0 "-"%char loose false (rev completed)) (rev bs) st)
    = (mk (BulletList (if loose then Loose else Tight)
          (completed ++ [canonical_item_ast item])%list)
       :: parse_lines ((first :: more) ++ tail)%list (PPara []))%list.
Proof.
  intros loose completed item a rest bs st next first more tail
    Hsafe Hok Hlines Hrun Hnonlist Hnext Hnextlines.
  destruct (run_canonical_item_blank item a rest bs st EmptyString
    Hsafe Hok Hlines Hrun (classify_blank EmptyString eq_refl))
    as [closed [inner' [Hblank Hitem]]].
  pose proof (nonlist_cblock_first next Hnonlist Hnext)
    as [first' [more' [Hshape Hnotlist]]].
  rewrite Hnextlines in Hshape. injection Hshape as <- <-.
  pose proof (cb_lines_first_line_ok next first more
    Hnonlist Hnext Hnextlines) as Hline.
  assert (Hindent : Nat.ltb 0 (indent_of first) = false).
  { rewrite (drop_leading_ws_indent_zero first
      (line_ok_no_leading_ws first Hline)). reflexivity. }
  assert (Hlazy : lazy_ok inner' = false).
  { pose proof (step_blank_lazy_false EmptyString st
      (classify_blank EmptyString eq_refl)) as H.
    rewrite Hblank in H. exact H. }
  change (parse_lines (EmptyString :: first :: more ++ tail)%list
      (PList (LSt 0 "-"%char loose false (rev completed)) (rev bs) st) =
    mk (BulletList (if loose then Loose else Tight)
      (completed ++ [canonical_item_ast item])%list) ::
    parse_lines (first :: more ++ tail)%list (PPara [])).
  pose proof (step_list_blank EmptyString
    (LSt 0 "-"%char loose false (rev completed)) (rev bs) st
    closed inner' (classify_blank EmptyString eq_refl) Hblank) as Houterblank.
  rewrite (parse_lines_step EmptyString (first :: more ++ tail)%list
    (PList (LSt 0 "-"%char loose false (rev completed)) (rev bs) st)
    []
    (PList (list_blank (LSt 0 "-"%char loose false (rev completed)))
      (rev closed ++ rev bs)%list inner') Houterblank).
  cbn [app].
  destruct (classify first) as [| |f|q|lvl txt|m listrest|] eqn:Hclass.
  - exfalso. apply line_ok_nonblank in Hline.
    apply classify_kblank_blank in Hclass. congruence.
  - destruct (open_kind first KThematic) as [head opened] eqn:Hopen.
    assert (Hstepopen : step first (PPara []) = (head, opened)).
    { rewrite (step_idle first KThematic Hclass eq_refl). exact Hopen. }
    rewrite (parse_lines_step first (more ++ tail)%list (PPara [])
      head opened Hstepopen).
    cbn [parse_lines].
    rewrite (step_list_close first KThematic
      (list_blank (LSt 0 "-"%char loose false (rev completed)))
      (rev closed ++ rev bs)%list inner' head opened
      Hclass eq_refl ltac:(discriminate) Hindent eq_refl Hopen).
    cbn [app finish list_blank ls_loose ls_items].
    rewrite rev_app_distr, !rev_involutive, <- app_assoc, Hitem.
    cbn [rev]. rewrite rev_involutive.
    reflexivity.
  - destruct (open_kind first (KFence f)) as [head opened] eqn:Hopen.
    assert (Hstepopen : step first (PPara []) = (head, opened)).
    { rewrite (step_idle first (KFence f) Hclass eq_refl). exact Hopen. }
    rewrite (parse_lines_step first (more ++ tail)%list (PPara [])
      head opened Hstepopen).
    cbn [parse_lines].
    rewrite (step_list_close first (KFence f)
      (list_blank (LSt 0 "-"%char loose false (rev completed)))
      (rev closed ++ rev bs)%list inner' head opened
      Hclass eq_refl ltac:(discriminate) Hindent eq_refl Hopen).
    cbn [app finish list_blank ls_loose ls_items].
    rewrite rev_app_distr, !rev_involutive, <- app_assoc, Hitem.
    cbn [rev]. rewrite rev_involutive.
    reflexivity.
  - destruct (step q (PPara [])) as [head opened] eqn:Hdesc.
    cbn [parse_lines].
    rewrite (step_list_quote_close first q
      (list_blank (LSt 0 "-"%char loose false (rev completed)))
      (rev closed ++ rev bs)%list inner' head opened Hclass Hindent Hdesc).
    rewrite (step_quote_open first q head opened Hclass Hdesc).
    cbn [app finish list_blank ls_loose ls_items].
    rewrite rev_app_distr, !rev_involutive, <- app_assoc, Hitem.
    cbn [rev]. rewrite rev_involutive.
    reflexivity.
  - destruct (open_kind first (KHeading lvl txt)) as [head opened] eqn:Hopen.
    assert (Hstepopen : step first (PPara []) = (head, opened)).
    { rewrite (step_idle first (KHeading lvl txt) Hclass eq_refl). exact Hopen. }
    rewrite (parse_lines_step first (more ++ tail)%list (PPara [])
      head opened Hstepopen).
    cbn [parse_lines].
    rewrite (step_list_close first (KHeading lvl txt)
      (list_blank (LSt 0 "-"%char loose false (rev completed)))
      (rev closed ++ rev bs)%list inner' head opened
      Hclass eq_refl ltac:(discriminate) Hindent eq_refl Hopen).
    cbn [app finish list_blank ls_loose ls_items].
    rewrite rev_app_distr, !rev_involutive, <- app_assoc, Hitem.
    cbn [rev]. rewrite rev_involutive.
    reflexivity.
  - exfalso. exact (Hnotlist m listrest eq_refl).
  - destruct (open_kind first KText) as [head opened] eqn:Hopen.
    assert (Hstepopen : step first (PPara []) = (head, opened)).
    { rewrite (step_idle first KText Hclass eq_refl). exact Hopen. }
    rewrite (parse_lines_step first (more ++ tail)%list (PPara [])
      head opened Hstepopen).
    cbn [parse_lines].
    rewrite (step_list_close first KText
      (list_blank (LSt 0 "-"%char loose false (rev completed)))
      (rev closed ++ rev bs)%list inner' head opened
      Hclass eq_refl ltac:(discriminate) Hindent
      ltac:(cbn [is_lazy]; exact Hlazy) Hopen).
    cbn [app finish list_blank ls_loose ls_items].
    rewrite rev_app_distr, !rev_involutive, <- app_assoc, Hitem.
    cbn [rev]. rewrite rev_involutive.
    reflexivity.
Qed.

Lemma parse_canonical_list_end :
  forall sp items,
    cb_ok (CList sp items) = true ->
    parse_lines (cb_lines (CList sp items)) (PPara [])
    = [cb_ast (CList sp items)].
Proof.
  intros sp items H.
  rewrite cb_ok_list in H.
  apply andb_true_iff in H as [Hprefix Hspacing].
  repeat rewrite andb_true_iff in Hprefix.
  destruct Hprefix as [[[Hne Hokitems] Hmarkers] Hsafeitems].
  destruct items as [|first remaining]; [discriminate Hne|].
  cbn [forallb] in Hokitems, Hmarkers, Hsafeitems.
  apply andb_true_iff in Hokitems as [Hokfirst Hokremaining].
  apply andb_true_iff in Hokfirst as [Hnefirst Hokfirst].
  apply andb_true_iff in Hmarkers as [Hmarkfirst Hmarkremaining].
  apply andb_true_iff in Hsafeitems as [Hsafefirst Hsaferemaining].
  assert (Hfirstne : first <> []).
  { destruct first; [discriminate Hnefirst|discriminate]. }
  destruct (canonical_item_run_exists first Hfirstne Hokfirst)
    as [a [rest [bs [st [Hlines Hrun]]]]].
  pose proof (run_first_canonical_item first a rest bs st
    Hsafefirst Hokfirst Hmarkfirst Hlines Hrun) as Hfirst.
  rewrite cb_lines_list, cb_ast_list.
  fold canonical_item_lines.
  destruct sp.
  - assert (Hallforce :
      forallb (fun it => negb (item_forces_loose it)) (first :: remaining)
      = true).
    { apply negb_existsb_forallb_negb. exact Hspacing. }
    cbn [forallb] in Hallforce.
    apply andb_true_iff in Hallforce as [Hforcefirst Hforceremaining].
    apply negb_true_iff in Hforcefirst.
    pose proof (scan_canonical_item_state first a rest 0 "-"%char []
      Hsafefirst Hokfirst Hlines) as Hscan.
    rewrite Hforcefirst in Hscan. setoid_rewrite Hscan in Hfirst.
    destruct remaining as [|second remaining'].
    + cbn [map list_lines]. unfold canonical_item_lines. rewrite Hlines.
      rewrite (parse_lines_run _ _ _ _ Hfirst). cbn [app].
      apply (parse_canonical_list_tail_tight [] [] first a rest bs st);
        assumption.
    + change (parse_lines
        (canonical_item_lines first ++
         list_lines Tight (map canonical_item_lines (second :: remaining')))%list
        (PPara []) =
        [mk (BulletList Tight
          (canonical_item_ast first ::
           map canonical_item_ast (second :: remaining')))]).
      unfold canonical_item_lines at 1. rewrite Hlines.
      rewrite parse_lines_app_run, Hfirst. cbn [app].
      apply (parse_canonical_list_tail_tight (second :: remaining') []
        first a rest bs st); assumption.
  - destruct remaining as [|second remaining'].
    + cbn [length Nat.eqb orb] in Hspacing.
      apply orb_true_iff in Hspacing as [Hbad | Hforce]; [discriminate Hbad|].
      unfold items_force_loose in Hforce. cbn [existsb orb] in Hforce.
      rewrite orb_false_r in Hforce.
      pose proof (scan_canonical_item_state first a rest 0 "-"%char []
        Hsafefirst Hokfirst Hlines) as Hscan.
      rewrite Hforce in Hscan. setoid_rewrite Hscan in Hfirst.
      cbn [map list_lines]. unfold canonical_item_lines. rewrite Hlines.
      rewrite (parse_lines_run _ _ _ _ Hfirst). cbn [app].
      apply (parse_canonical_list_tail_loose [] [] first a rest bs st);
        assumption.
    + cbn [forallb] in Hokremaining, Hmarkremaining, Hsaferemaining.
      apply andb_true_iff in Hokremaining as [Hoksecond Hokrest].
      apply andb_true_iff in Hoksecond as [Hnesecond Hoksecond].
      apply andb_true_iff in Hmarkremaining as [Hmarksecond Hmarkrest].
      apply andb_true_iff in Hsaferemaining as [Hsafesecond Hsaferest].
      assert (Hsecondne : second <> []).
      { destruct second; [discriminate Hnesecond|discriminate]. }
      destruct (canonical_item_run_exists second Hsecondne Hoksecond)
        as [sa [sr [sbs [sst [Hslines Hsrun]]]]].
      pose proof (scan_list_content_fields rest
        (LSt 0 "-"%char false false [])) as [Hind [Hmarker Hitems]].
      cbn in Hind, Hmarker, Hitems.
      pose proof (run_list_sibling_canonical_loose first a rest bs st
        second sa sr sbs sst
        (scan_list_content (LSt 0 "-"%char false false []) rest)
        Hsafefirst Hokfirst Hlines Hrun Hsafesecond Hoksecond Hmarksecond
        Hslines Hsrun Hind Hmarker) as Hsecond.
      pose proof (canonical_item_first_nonblank second sa sr
        Hsafesecond Hoksecond Hslines) as Hsanb.
      unfold nonblank in Hsanb. apply negb_true_iff in Hsanb.
      unfold list_next, list_blank in Hsecond. rewrite Hsanb in Hsecond.
      rewrite Hind, Hmarker, Hitems in Hsecond.
      pose proof (scan_canonical_item_state_loose second sa sr 0 "-"%char
        [canonical_item_ast first] Hsafesecond Hoksecond Hslines) as Hscan2.
      cbn [ls_indent ls_marker ls_loose ls_blanks ls_items orb] in Hsecond.
      rewrite orb_true_r in Hsecond. unfold canonical_item_ast in Hscan2.
      setoid_rewrite Hscan2 in Hsecond.
      assert (Hlayout :
        list_lines Loose
          (map canonical_item_lines (first :: second :: remaining')) =
        (canonical_item_lines first ++
         EmptyString :: canonical_item_lines second ++
         canonical_loose_tail_lines remaining')%list).
      { rewrite list_lines_loose_eq.
        destruct remaining' as [|third rest3].
        - cbn [map sep_lines canonical_loose_tail_lines].
          rewrite ?app_nil_r, ?app_assoc. reflexivity.
        - cbn [canonical_loose_tail_lines]. rewrite list_lines_loose_eq.
          cbn [map sep_lines]. rewrite ?app_nil_r, ?app_assoc. reflexivity. }
      rewrite Hlayout. cbn [map].
      unfold canonical_item_lines at 1. rewrite Hlines.
      rewrite parse_lines_app_run, Hfirst. cbn [app].
      rewrite app_comm_cons.
      rewrite (parse_lines_app_run
        (EmptyString :: canonical_item_lines second)
        (canonical_loose_tail_lines remaining')
        (PList (scan_list_content (LSt 0 "-"%char false false []) rest)
          (rev bs) st)).
      unfold canonical_item_lines at 1. rewrite Hslines.
      rewrite Hsecond. cbn [app].
      apply (parse_canonical_list_tail_loose remaining'
        [canonical_item_ast first] second sa sr sbs sst);
        assumption.
Qed.

Lemma list_lines_loose_first :
  forall first remaining,
    list_lines Loose (map canonical_item_lines (first :: remaining)) =
    (canonical_item_lines first ++ canonical_loose_tail_lines remaining)%list.
Proof.
  intros first remaining. destruct remaining; cbn [map list_lines canonical_loose_tail_lines];
    rewrite ?app_nil_r; reflexivity.
Qed.

Lemma parse_canonical_list_then_nonlist :
  forall sp items next tail,
    cb_ok (CList sp items) = true ->
    is_clist next = false -> cb_ok next = true ->
    parse_lines
      (cb_lines (CList sp items) ++ EmptyString :: cb_lines next ++ tail)%list
      (PPara []) =
    (cb_ast (CList sp items) ::
      parse_lines (cb_lines next ++ tail)%list (PPara []))%list.
Proof.
  intros sp items next tail H Hnonlist Hnextok.
  rewrite cb_ok_list in H.
  apply andb_true_iff in H as [Hprefix Hspacing].
  repeat rewrite andb_true_iff in Hprefix.
  destruct Hprefix as [[[Hne Hokitems] Hmarkers] Hsafeitems].
  destruct items as [|first remaining]; [discriminate Hne|].
  cbn [forallb] in Hokitems, Hmarkers, Hsafeitems.
  apply andb_true_iff in Hokitems as [Hokfirst Hokremaining].
  apply andb_true_iff in Hokfirst as [Hnefirst Hokfirst].
  apply andb_true_iff in Hmarkers as [Hmarkfirst Hmarkremaining].
  apply andb_true_iff in Hsafeitems as [Hsafefirst Hsaferemaining].
  assert (Hfirstne : first <> []).
  { destruct first; [discriminate Hnefirst|discriminate]. }
  destruct (canonical_item_run_exists first Hfirstne Hokfirst)
    as [a [rest [bs [st [Hlines Hrun]]]]].
  pose proof (run_first_canonical_item first a rest bs st
    Hsafefirst Hokfirst Hmarkfirst Hlines Hrun) as Hfirst.
  rewrite cb_lines_list, cb_ast_list. fold canonical_item_lines.
  destruct sp.
  - assert (Hallforce :
      forallb (fun it => negb (item_forces_loose it)) (first :: remaining)
      = true).
    { apply negb_existsb_forallb_negb. exact Hspacing. }
    cbn [forallb] in Hallforce.
    apply andb_true_iff in Hallforce as [Hforcefirst Hforceremaining].
    apply negb_true_iff in Hforcefirst.
    pose proof (scan_canonical_item_state first a rest 0 "-"%char []
      Hsafefirst Hokfirst Hlines) as Hscan.
    rewrite Hforcefirst in Hscan. setoid_rewrite Hscan in Hfirst.
    destruct (run_canonical_list_tail_tight remaining [] first a rest bs st
      Hokremaining Hmarkremaining Hsaferemaining Hforceremaining
      Hsafefirst Hokfirst Hforcefirst Hlines Hrun)
      as (before & last & la & lr & lbs & lst & Hitems & Hlastsafe &
          Hlastok & Hlastforce & Hlastlines & Hlastrun & Htail).
    rewrite list_lines_tight_cons, <- app_assoc.
    unfold canonical_item_lines at 1. rewrite Hlines.
    rewrite (parse_lines_app_run
      (indent_lines bullet_open bullet_cont (a :: rest))
      (list_lines Tight (map canonical_item_lines remaining) ++
       EmptyString :: cb_lines next ++ tail)%list (PPara [])).
    rewrite Hfirst. cbn [app].
    rewrite (parse_lines_app_run
      (list_lines Tight (map canonical_item_lines remaining))
      (EmptyString :: cb_lines next ++ tail)%list
      (PList (LSt 0 "-"%char false false []) (rev bs) st)).
    cbn [rev] in Htail.
    rewrite Htail. cbn [app].
    destruct (cb_lines next) as [|nf nr] eqn:Hnextlines.
    { pose proof (cb_ok_lines_ok next Hnextok) as Hvalid.
      apply lines_ok_parts in Hvalid as [Hne' _]. congruence. }
    change (parse_lines (EmptyString :: nf :: nr ++ tail)%list
      (PList (LSt 0 "-"%char false false (rev before)) (rev lbs) lst) =
      mk (BulletList Tight (map (map cb_ast) (first :: remaining))) ::
      parse_lines (nf :: nr ++ tail)%list (PPara [])).
    rewrite (parse_list_current_then_nonlist false before last la lr lbs lst
      next nf nr tail Hlastsafe Hlastok Hlastlines Hlastrun
      Hnonlist Hnextok Hnextlines).
    unfold canonical_item_ast in Hitems |- *. rewrite Hitems. reflexivity.
  - destruct remaining as [|second remaining'].
    + cbn [length Nat.eqb orb] in Hspacing.
      apply orb_true_iff in Hspacing as [Hbad | Hforce]; [discriminate Hbad|].
      unfold items_force_loose in Hforce. cbn [existsb orb] in Hforce.
      rewrite orb_false_r in Hforce.
      pose proof (scan_canonical_item_state first a rest 0 "-"%char []
        Hsafefirst Hokfirst Hlines) as Hscan.
      rewrite Hforce in Hscan. setoid_rewrite Hscan in Hfirst.
      cbn [map list_lines]. unfold canonical_item_lines. rewrite Hlines.
      rewrite (parse_lines_app_run
        (indent_lines bullet_open bullet_cont (a :: rest))
        (EmptyString :: cb_lines next ++ tail)%list (PPara [])), Hfirst.
      cbn [app].
      destruct (cb_lines next) as [|nf nr] eqn:Hnextlines.
      { pose proof (cb_ok_lines_ok next Hnextok) as Hvalid.
        apply lines_ok_parts in Hvalid as [Hne' _]. congruence. }
      change (parse_lines (EmptyString :: nf :: nr ++ tail)%list
        (PList (LSt 0 "-"%char true false []) (rev bs) st) =
        mk (BulletList Loose [map cb_ast first]) ::
        parse_lines (nf :: nr ++ tail)%list (PPara [])).
      pose proof (parse_list_current_then_nonlist true [] first a rest bs st
        next nf nr tail Hsafefirst Hokfirst Hlines Hrun
        Hnonlist Hnextok Hnextlines) as Hclose.
      cbn [rev] in Hclose. rewrite Hclose. reflexivity.
    + cbn [forallb] in Hokremaining, Hmarkremaining, Hsaferemaining.
      apply andb_true_iff in Hokremaining as [Hoksecond Hokrest].
      apply andb_true_iff in Hoksecond as [Hnesecond Hoksecond].
      apply andb_true_iff in Hmarkremaining as [Hmarksecond Hmarkrest].
      apply andb_true_iff in Hsaferemaining as [Hsafesecond Hsaferest].
      assert (Hsecondne : second <> []).
      { destruct second; [discriminate Hnesecond|discriminate]. }
      destruct (canonical_item_run_exists second Hsecondne Hoksecond)
        as [sa [sr [sbs [sst [Hslines Hsrun]]]]].
      pose proof (scan_list_content_fields rest
        (LSt 0 "-"%char false false [])) as [Hind [Hmarker Hitems0]].
      cbn in Hind, Hmarker, Hitems0.
      pose proof (run_list_sibling_canonical_loose first a rest bs st
        second sa sr sbs sst
        (scan_list_content (LSt 0 "-"%char false false []) rest)
        Hsafefirst Hokfirst Hlines Hrun Hsafesecond Hoksecond Hmarksecond
        Hslines Hsrun Hind Hmarker) as Hsecond.
      pose proof (canonical_item_first_nonblank second sa sr
        Hsafesecond Hoksecond Hslines) as Hsanb.
      unfold nonblank in Hsanb. apply negb_true_iff in Hsanb.
      unfold list_next, list_blank in Hsecond. rewrite Hsanb in Hsecond.
      rewrite Hind, Hmarker, Hitems0 in Hsecond.
      pose proof (scan_canonical_item_state_loose second sa sr 0 "-"%char
        [canonical_item_ast first] Hsafesecond Hoksecond Hslines) as Hscan2.
      cbn [ls_indent ls_marker ls_loose ls_blanks ls_items orb] in Hsecond.
      rewrite orb_true_r in Hsecond. unfold canonical_item_ast in Hscan2.
      setoid_rewrite Hscan2 in Hsecond.
      destruct (run_canonical_list_tail_loose remaining'
        [canonical_item_ast first] second sa sr sbs sst
        Hokrest Hmarkrest Hsaferest Hsafesecond Hoksecond Hslines Hsrun)
        as (before & last & la & lr & lbs & lst & Hitems & Hlastsafe &
            Hlastok & Hlastlines & Hlastrun & Htail).
      rewrite list_lines_loose_first.
      unfold canonical_item_lines at 1. rewrite Hlines.
      rewrite <- app_assoc.
      rewrite (parse_lines_app_run
        (indent_lines bullet_open bullet_cont (a :: rest))
        (canonical_loose_tail_lines (second :: remaining') ++
         EmptyString :: cb_lines next ++ tail)%list (PPara [])), Hfirst.
      cbn [app]. rewrite canonical_loose_tail_cons.
      rewrite app_comm_cons, <- app_assoc.
      rewrite (parse_lines_app_run
        (EmptyString :: canonical_item_lines second)
        (canonical_loose_tail_lines remaining' ++
         EmptyString :: cb_lines next ++ tail)%list
        (PList (scan_list_content (LSt 0 "-"%char false false []) rest)
          (rev bs) st)).
      unfold canonical_item_lines at 1. rewrite Hslines, Hsecond. cbn [app].
      cbn [rev app] in Htail. unfold canonical_item_ast in Htail.
      rewrite parse_lines_app_run, Htail.
      cbn [app].
      destruct (cb_lines next) as [|nf nr] eqn:Hnextlines.
      { pose proof (cb_ok_lines_ok next Hnextok) as Hvalid.
        apply lines_ok_parts in Hvalid as [Hne' _]. congruence. }
      change (parse_lines (EmptyString :: nf :: nr ++ tail)%list
        (PList (LSt 0 "-"%char true false (rev before)) (rev lbs) lst) =
        mk (BulletList Loose
          (map cb_ast first :: map cb_ast second ::
            map (map cb_ast) remaining')) ::
        parse_lines (nf :: nr ++ tail)%list (PPara [])).
      rewrite (parse_list_current_then_nonlist true before last la lr lbs lst
        next nf nr tail Hlastsafe Hlastok Hlastlines Hlastrun
        Hnonlist Hnextok Hnextlines).
      unfold canonical_item_ast in Hitems |- *. rewrite Hitems. reflexivity.
Qed.

(*
Blocks and block sequences
==========================
*)

(* Half two, per block: feeding a canonical block's lines re-emits it and
   returns the parser to idle, whether a blank line follows (the
   in-document case) or the input ends.  Proved for a block and a list of
   blocks together, because a quote's contents are the latter. *)
Lemma parse_cblock :
  forall cb,
    (forall next tail,
       (is_clist cb = true -> is_clist next = false) ->
       cb_ok next = true -> cb_ok cb = true ->
       parse_lines
         (cb_lines cb ++ EmptyString :: cb_lines next ++ tail)%list (PPara [])
       = cb_ast cb :: parse_lines (cb_lines next ++ tail)%list (PPara []))
    /\ (cb_ok cb = true ->
        parse_lines (cb_lines cb) (PPara []) = [cb_ast cb]).
Proof.
  refine (cblock_ind2
            (fun cb =>
               (forall next tail,
                  (is_clist cb = true -> is_clist next = false) ->
                  cb_ok next = true -> cb_ok cb = true ->
                  parse_lines
                    (cb_lines cb ++ EmptyString :: cb_lines next ++ tail)%list
                    (PPara []) =
                  cb_ast cb :: parse_lines (cb_lines next ++ tail)%list (PPara []))
               /\ (cb_ok cb = true ->
                   parse_lines (cb_lines cb) (PPara []) = [cb_ast cb]))
            (fun cbs =>
               no_adjacent_lists cbs = true ->
               forallb cb_ok cbs = true ->
               parse_lines (sep_lines (map cb_lines cbs)) (PPara [])
               = map cb_ast cbs)
            (fun _ => True)
            _ _ _ _ _ _ _ _ I (fun _ _ _ _ => I)).
  - (* paragraph *)
    intros ls. split; [intros next tail _ _ H | intros H];
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
    split; [intros next tail _ _ H | intros H]; cbn [cb_lines app].
    + rewrite parse_lines_thematic_nil by apply classify_canonical_thematic.
      rewrite parse_lines_blank_nil by reflexivity. reflexivity.
    + rewrite parse_lines_thematic_nil by apply classify_canonical_thematic.
      reflexivity.
  - (* code block *)
    intros info content. split; [intros next tail _ _ H | intros H];
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
    intros lvl ls. split; [intros next tail _ _ H | intros H];
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
      apply andb_true_iff in H as [H _].
      apply andb_true_iff in H as [Hne Hok].
      destruct inner as [|c rest]; [discriminate|].
      assert (Hc : lines_ok (cb_lines c) = true).
      { apply cb_ok_lines_ok. cbn [forallb] in Hok.
        apply andb_true_iff in Hok as [H1 _]. exact H1. }
      destruct (sep_lines (map cb_lines (c :: rest))) as [|l L] eqn:E.
      - exfalso. apply (sep_lines_nonempty (cb_lines c) (map cb_lines rest) Hc).
        exact E.
      - eauto. }
    split.
    + intros next tail _ _ H.
      destruct (Hsplit H) as [l [L [E Hok]]].
      assert (Hadj : no_adjacent_lists inner = true).
      { rewrite cb_ok_quote in H.
        apply andb_true_iff in H as [_ Hadj]. exact Hadj. }
      pose proof (IH Hadj Hok) as IHinner.
      rewrite cb_lines_quote, cb_ast_quote, E.
      unfold quote_line, quote_open.
      rewrite parse_lines_quote, <- E, IHinner. reflexivity.
    + intros H. destruct (Hsplit H) as [l [L [E Hok]]].
      assert (Hadj : no_adjacent_lists inner = true).
      { rewrite cb_ok_quote in H.
        apply andb_true_iff in H as [_ Hadj]. exact Hadj. }
      pose proof (IH Hadj Hok) as IHinner.
      rewrite cb_lines_quote, cb_ast_quote, E.
      unfold quote_line, quote_open.
      rewrite quote_uniformity, <- E, IHinner. reflexivity.
  - (* list *)
    intros sp items _. split.
    + intros next tail Hboundary Hnext Hlist.
      apply parse_canonical_list_then_nonlist; try assumption.
      apply Hboundary. reflexivity.
    + apply parse_canonical_list_end.
  - (* the list side: nothing to parse *)
    intros _ _. reflexivity.
  - (* the list side: one block, then the rest after a blank line *)
    intros c rest Hc Hrest Hadj H.
    cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
    destruct Hc as [Hc1 Hc2].
    destruct rest as [|c2 rest'].
    + cbn [map sep_lines]. rewrite (Hc2 H1). reflexivity.
    + pose proof H2 as Hrestallok.
      change (negb (is_clist c && is_clist c2) &&
              no_adjacent_lists (c2 :: rest') = true) in Hadj.
      apply andb_true_iff in Hadj as [Hpair Hrestall].
      assert (Hboundary : is_clist c = true -> is_clist c2 = false).
      { intros Hcl. apply negb_true_iff in Hpair.
        rewrite Hcl in Hpair. cbn in Hpair.
        destruct (is_clist c2); [discriminate|reflexivity]. }
      cbn [forallb] in H2. apply andb_true_iff in H2 as [Hc2ok Hrestok].
      destruct rest' as [|c3 rest''].
      * cbn [map sep_lines].
        pose proof (Hc1 c2 [] Hboundary Hc2ok H1) as Hparse.
        rewrite !app_nil_r in Hparse. rewrite Hparse.
        cbn [map cb_ast]. f_equal. apply Hrest.
        -- reflexivity.
        -- cbn [forallb]. rewrite Hc2ok. reflexivity.
      * cbn [map sep_lines].
        change (parse_lines
          (cb_lines c ++ EmptyString :: cb_lines c2 ++ EmptyString ::
           sep_lines (map cb_lines (c3 :: rest''))) (PPara []) =
          cb_ast c :: cb_ast c2 :: cb_ast c3 :: map cb_ast rest'').
        rewrite (Hc1 c2 (EmptyString :: sep_lines (map cb_lines (c3 :: rest'')))
          Hboundary Hc2ok H1).
        cbn [map cb_ast]. f_equal. apply Hrest.
        -- exact Hrestall.
        -- exact Hrestallok.
Qed.

Lemma parse_sep :
  forall cbs, no_adjacent_lists cbs = true -> forallb cb_ok cbs = true ->
  parse_lines (sep_lines (map cb_lines cbs)) (PPara []) = map cb_ast cbs.
Proof.
  induction cbs as [|cb rest IH]; intros Hadj H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hcb Hrest].
  destruct (parse_cblock cb) as [Hc1 Hc2].
  destruct rest as [|cb2 rest'].
  - cbn [map sep_lines]. rewrite (Hc2 Hcb). reflexivity.
  - pose proof Hrest as Hrestallok.
    change (negb (is_clist cb && is_clist cb2) &&
            no_adjacent_lists (cb2 :: rest') = true) in Hadj.
    apply andb_true_iff in Hadj as [Hpair Hrestall].
    assert (Hboundary : is_clist cb = true -> is_clist cb2 = false).
    { intros Hcl. apply negb_true_iff in Hpair.
      rewrite Hcl in Hpair. cbn in Hpair.
      destruct (is_clist cb2); [discriminate|reflexivity]. }
    cbn [forallb] in Hrest. apply andb_true_iff in Hrest as [Hcb2 Hrest'].
    destruct rest' as [|cb3 rest''].
    + cbn [map sep_lines].
      pose proof (Hc1 cb2 [] Hboundary Hcb2 Hcb) as Hparse.
      rewrite !app_nil_r in Hparse. rewrite Hparse.
      cbn [map cb_ast]. f_equal. apply IH.
      * reflexivity.
      * cbn [forallb]. rewrite Hcb2. reflexivity.
    + cbn [map sep_lines].
      change (parse_lines
        (cb_lines cb ++ EmptyString :: cb_lines cb2 ++ EmptyString ::
         sep_lines (map cb_lines (cb3 :: rest''))) (PPara []) =
        cb_ast cb :: cb_ast cb2 :: cb_ast cb3 :: map cb_ast rest'').
      rewrite (Hc1 cb2 (EmptyString :: sep_lines (map cb_lines (cb3 :: rest'')))
        Hboundary Hcb2 Hcb).
      cbn [map cb_ast]. f_equal. apply IH.
      * exact Hrestall.
      * exact Hrestallok.
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

(* The renderer emits exactly a cblock's canonical lines.  The third
   induction predicate handles a list's list of item lists. *)
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
            (fun items => forallb (forallb cb_ok) items = true ->
                          map (fun it => indent_lines bullet_open bullet_cont
                                   (sep_lines (render_blocks_lines
                                                (map cb_ast it)))) items
                          = map (fun it => indent_lines bullet_open bullet_cont
                                   (sep_lines (map cb_lines it))) items)
            _ _ _ _ _ _ _ _ _ _).
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
    rewrite cb_ok_quote in H. apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [_ Hok].
    rewrite cb_ast_quote. cbn [node_contents mk].
    rewrite render_block_quote, (IH Hok), cb_lines_quote.
    reflexivity.
  - intros sp items IH H.
    rewrite cb_ok_list in H.
    apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [_ Hitems].
    assert (Hokitems : forallb (forallb cb_ok) items = true).
    { refine (forallb_weaken _ _ _ _ Hitems).
      intros item Hitem. apply andb_true_iff in Hitem as [_ Hitem]. exact Hitem. }
    rewrite cb_ast_list. cbn [node_contents mk].
    rewrite render_bullet_list, cb_lines_list, map_map, (IH Hokitems). reflexivity.
  - intros _. reflexivity.
  - intros c rest Hc Hrest H.
    cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
    unfold render_blocks_lines in *. cbn [map].
    rewrite (Hc H1), (Hrest H2). reflexivity.
  - reflexivity.
  - intros item items Hitem Hitems H.
    cbn [forallb] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [map]. rewrite (Hitem Hit), (Hitems Hrest). reflexivity.
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
  forall cbs, cblocks_ok cbs = true ->
  parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof.
  intros cbs H. apply cblocks_ok_parts in H as [Hok Hadj].
  rewrite (render_djot_cblocks _ Hok).
  unfold parse_blocks, blocks_of_cblocks.
  f_equal.
  rewrite split_render by (apply forallb_cb_lines_ok; exact Hok).
  apply parse_sep; assumption.
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
Proof. apply roundtrip_blocks; reflexivity. Qed.

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

Example tight_list_roundtrip :
  let cbs :=
    [CList Tight [[CPara ["a"]]; [CPara ["b"]]]; CPara ["after"]] in
  render_djot (blocks_of_cblocks cbs)
    = ("- a" ++ nl ++ "- b" ++ nl ++ nl ++ "after")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

Example loose_list_roundtrip :
  let cbs := [CList Loose [[CPara ["a"]]; [CPara ["b"]]]] in
  render_djot (blocks_of_cblocks cbs) = ("- a" ++ nl ++ nl ++ "- b")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* Lists are also covered recursively through a quote; only lists nested
   directly inside list items remain outside list_content_safe. *)
Example list_in_quote_roundtrip :
  let cbs := [CQuote [CList Tight [[CPara ["a"]]; [CPara ["b"]]]]] in
  parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. apply roundtrip_blocks; reflexivity. Qed.

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
    (Q := fun cbs => pristine (map cb_ast cbs) = true)
    (R := fun _ => True);
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
  forall cbs, cblocks_ok cbs = true ->
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
