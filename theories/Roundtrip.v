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
     Canonical lists                          the CList case
     Blocks and block sequences               parse_cblock, parse_sep
     The renderer emits exactly the canonical lines
     The theorem                              roundtrip_blocks
     Worked examples                          regression witnesses
     Above the block layer                    roundtrip_doc

   A list is the one construct whose parse cannot be stated
   block-at-a-time, and none of that reasoning lives here: it is
   `Parser.list_uniformity`, stated over line lists.  The Canonical lists
   section only matches `cb_lines`'s shape to `list_lines`'s and reads
   the spacing verdict off `cb_ok`, reaching the two lemmas the block
   layer consumes: `parse_canonical_list_end` and
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
Canonical lists
===============

`Parser.list_uniformity` does all the work: a list's rendering parses
back to a BulletList whose items are the items' own lines parsed at top
level, and whose spacing is a scan of those lines.  It needs only
`item_ok` on each item's rendering, which `cb_ok` now asks for directly,
so nothing here reasons about what is inside an item -- including
another list.

What is left is bookkeeping: `cb_lines`'s shape has to be matched to
`list_lines`'s, the spacing verdict read off `cb_ok`'s conjunct, and the
block that closes the list shown to be a line the parser will not
mistake for a continuation.
*)

Lemma classify_not_blank_nonblank :
  forall l, classify l <> KBlank -> nonblank l = true.
Proof.
  intros l H. unfold nonblank. apply negb_true_iff.
  destruct (is_blank l) eqn:Hblank; [|reflexivity].
  exfalso. apply H. apply classify_blank. exact Hblank.
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

(* The items' contents, as the mutual induction supplies them: each
   item's lines parse at top level to that item's blocks.  Passed in
   rather than assumed, since it is `parse_cblock`'s own induction
   hypothesis. *)
Definition items_parse (items : list (list cblock)) : Prop :=
  map (fun it => parse_lines (item_lines it) (PPara [])) items
  = map (fun it => map cb_ast it) items.

(* cb_lines lays a list out exactly as list_uniformity expects it. *)
Lemma cb_lines_list_uniform :
  forall sp items,
    cb_lines (CList sp items)
    = list_lines sp (map (indent_lines bullet_open bullet_cont)
                       (map item_lines items)).
Proof.
  intros sp items. rewrite cb_lines_list, map_map. reflexivity.
Qed.

Lemma forallb_map :
  forall {A B : Type} (f : B -> bool) (g : A -> B) l,
    forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof. induction l as [|x l IH]; [reflexivity|cbn; rewrite IH; reflexivity]. Qed.

Lemma existsb_map :
  forall {A B : Type} (f : B -> bool) (g : A -> B) l,
    existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof. induction l as [|x l IH]; [reflexivity|cbn; rewrite IH; reflexivity]. Qed.

(* cb_ok's list conjuncts, in the form list_uniformity asks for. *)
Lemma cb_ok_list_parts :
  forall sp items,
    cb_ok (CList sp items) = true ->
    items <> []
    /\ forallb item_ok (map item_lines items) = true
    /\ list_spacing_of sp (map item_lines items) = sp.
Proof.
  intros sp items H. rewrite cb_ok_list in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[[Hne Hitems] Hitemok] _] Hspacing].
  assert (Hne' : items <> []) by (destruct items; [discriminate Hne|discriminate]).
  assert (Hmap : forallb item_ok (map item_lines items) = true).
  { rewrite forallb_map. exact Hitemok. }
  assert (Hforce : existsb (fun L => lines_loose false false L) (map item_lines items)
                   = items_force_loose items).
  { unfold items_force_loose, item_forces_loose. rewrite existsb_map. reflexivity. }
  split; [exact Hne'|]. split; [exact Hmap|].
  unfold list_spacing_of. rewrite Hforce, length_map.
  destruct sp.
  - apply negb_true_iff in Hspacing. rewrite Hspacing. reflexivity.
  - apply orb_true_iff in Hspacing as [Hlen | Hforced].
    + rewrite Hlen, orb_true_r. reflexivity.
    + rewrite Hforced. reflexivity.
Qed.

(* The AST side, likewise. *)
Lemma cb_ast_list_uniform :
  forall sp items,
    items_parse items ->
    cb_ast (CList sp items)
    = mk (BulletList sp (map (fun L => parse_lines L (PPara []))
                           (map item_lines items))).
Proof.
  intros sp items Hitems. rewrite cb_ast_list, map_map, Hitems. reflexivity.
Qed.

Lemma parse_canonical_list_end :
  forall sp items,
    cb_ok (CList sp items) = true ->
    items_parse items ->
    parse_lines (cb_lines (CList sp items)) (PPara [])
    = [cb_ast (CList sp items)].
Proof.
  intros sp items Hok Hitems.
  destruct (cb_ok_list_parts sp items Hok) as (Hne & Hitemok & Hsp).
  rewrite cb_lines_list_uniform, (cb_ast_list_uniform sp items Hitems).
  rewrite (list_uniformity sp (map item_lines items)
             ltac:(destruct items; [congruence|discriminate]) Hitemok).
  rewrite Hsp. reflexivity.
Qed.

(* The line that ends a list has to be one the parser routes out of the
   list rather than into the current item: nonblank (a blank only records
   a gap), not a sibling marker, and not indented.  A canonical non-list
   block's first line is all three. *)
Lemma parse_canonical_list_then_nonlist :
  forall sp items next tail,
    cb_ok (CList sp items) = true ->
    items_parse items ->
    is_clist next = false -> cb_ok next = true ->
    parse_lines
      (cb_lines (CList sp items) ++ EmptyString :: cb_lines next ++ tail)%list
      (PPara []) =
    (cb_ast (CList sp items) ::
      parse_lines (cb_lines next ++ tail)%list (PPara []))%list.
Proof.
  intros sp items next tail Hok Hitems Hnonlist Hnextok.
  destruct (cb_ok_list_parts sp items Hok) as (Hne & Hitemok & Hsp).
  destruct (nonlist_cblock_first next Hnonlist Hnextok)
    as [first [more [Hshape Hnotlist]]].
  pose proof (cb_lines_first_line_ok next first more
                Hnonlist Hnextok Hshape) as Hline.
  rewrite Hshape. cbn [app].
  rewrite cb_lines_list_uniform, (cb_ast_list_uniform sp items Hitems).
  rewrite (list_uniformity_tail sp (map item_lines items) first (more ++ tail)
             ltac:(destruct items; [congruence|discriminate]) Hitemok
             ltac:(intros E; apply classify_kblank_blank in E;
                   apply line_ok_nonblank in Hline;
                   unfold nonblank in Hline; rewrite E in Hline; discriminate)
             Hnotlist
             (drop_leading_ws_indent_zero first (line_ok_no_leading_ws first Hline))).
  rewrite Hsp. reflexivity.
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
            (fun items =>
               forallb no_adjacent_lists items = true ->
               forallb (fun it => (nonempty it && forallb cb_ok it)%bool) items = true ->
               items_parse items)
            _ _ _ _ _ _ _ _ _ _).
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
  - (* list: every item's contents come from the induction hypothesis,
       and Parser.list_uniformity assembles them *)
    intros sp items IH.
    assert (Hparse : cb_ok (CList sp items) = true -> items_parse items).
    { intros H. rewrite cb_ok_list in H.
      repeat rewrite andb_true_iff in H.
      destruct H as [[[[_ Hitems] _] Hadj] _]. exact (IH Hadj Hitems). }
    split.
    + intros next tail Hboundary Hnext Hlist.
      apply parse_canonical_list_then_nonlist; try assumption.
      * exact (Hparse Hlist).
      * apply Hboundary. reflexivity.
    + intros H. exact (parse_canonical_list_end sp items H (Hparse H)).
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
  - (* the item side: no items *)
    intros _ _. reflexivity.
  - (* the item side: one item's contents, then the rest *)
    intros item items IHitem IHrest Hadj Hok.
    cbn [forallb] in Hadj, Hok.
    apply andb_true_iff in Hadj as [Hadjitem Hadjrest].
    apply andb_true_iff in Hok as [Hokitem Hokrest].
    apply andb_true_iff in Hokitem as [_ Hokitem].
    unfold items_parse, item_lines in *. cbn [map].
    rewrite (IHitem Hadjitem Hokitem), (IHrest Hadjrest Hokrest). reflexivity.
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

(* Lists nest, in both directions: through a quote, and directly inside
   another list's item. *)
Example list_in_quote_roundtrip :
  let cbs := [CQuote [CList Tight [[CPara ["a"]]; [CPara ["b"]]]]] in
  parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. apply roundtrip_blocks; reflexivity. Qed.

Example nested_list_roundtrip :
  let cbs := [CList Tight [[CList Tight [[CPara ["b"]]; [CPara ["c"]]]]]] in
  render_djot (blocks_of_cblocks cbs) = ("- - b" ++ nl ++ "  - c")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* A nested list after a paragraph in the same item: the blank the inner
   list needs does not loosen the outer one, which is the rule
   `lines_loose` encodes and `item_forces_loose` mirrors. *)
Example nested_list_after_para_roundtrip :
  let cbs := [CList Tight [[CPara ["a"]; CList Tight [[CPara ["b"]]]]]] in
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
