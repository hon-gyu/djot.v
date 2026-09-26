(* ai-disclosure: autonomous *)

(** * Canonical rendering roundtrips

   The central block theorem states:

   [parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs]

   for canonical blocks (Render.v).  Exact equality: canonicality is in
   the cb_ok hypothesis, so no quotient is needed.

   Proof shape, per block: rendering emits lines; split_lines recovers
   them exactly (Strings.v split/join inversion); the parser folds them
   back via its equation lemmas.  A new construct adds a case to
   `cb_ok_lines_ok`, `parse_cblock` and `render_cb_lines`.

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
   [parse_canonical_list_then_nonlist]. *)

From Stdlib Require Import String Ascii List Bool PeanoNat.
From DjotV Require Import Strings Line Ast Attributes Inline Parser Document Render.
Import ListNotations.

Local Open Scope string_scope.

(* The delimiter table this file is read at.  Implicit, so nothing below
   mentions it: what it buys is that the statements quantify over the
   family rather than over djot's spelling. *)
Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

Local Lemma pristine_task_items_of_items :
  forall checks items,
    Pristine.of_items items = true ->
    Pristine.of_task_items (task_items checks items) = true.
Proof.
  intros checks items. induction items as [|it rest IH] in checks |- *;
    [reflexivity|].
  cbn [Pristine.of_items]. intros H. apply andb_true_iff in H as [Hit Hrest].
  destruct checks; cbn [task_items Pristine.of_task_items]; rewrite Hit;
    apply IH, Hrest.
Qed.

(*
Splitting a rendered document
=============================
*)

(* What the split/join inversion needs of each block's lines: newline-free
   throughout, and a nonempty final line (split_lines drops a trailing
   empty line).  Interior lines may be blank: code content is verbatim. *)
Local Definition lines_ok (ls : list string) : bool :=
  nonempty ls
  && forallb no_nl ls
  && nonempty_str (last ls EmptyString).

Local Lemma nonempty_str_neq :
  forall s, nonempty_str s = true -> s <> EmptyString.
Proof. destruct s; [discriminate | congruence]. Qed.

Local Lemma lines_ok_parts :
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

Local Lemma sep_lines_nonempty :
  forall ls rest, lines_ok ls = true -> sep_lines (ls :: rest) <> [].
Proof.
  intros ls rest H. apply lines_ok_parts in H as (Hne & _ & _).
  destruct rest as [|ls2 rest'].
  - exact Hne.
  - cbn [sep_lines]. destruct ls; [congruence | discriminate].
Qed.

Local Lemma sep_lines_no_nl :
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

Local Lemma sep_lines_last :
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

Local Lemma list_lines_loose_eq : forall lss, list_lines Loose lss = sep_lines lss.
Proof.
  induction lss as [|ls rest IH]; [reflexivity|].
  destruct rest as [|ls2 rest']; [reflexivity|].
  change (list_lines Loose (ls :: ls2 :: rest'))
    with (ls ++ EmptyString :: list_lines Loose (ls2 :: rest'))%list.
  change (sep_lines (ls :: ls2 :: rest'))
    with (ls ++ EmptyString :: sep_lines (ls2 :: rest'))%list.
  rewrite IH. reflexivity.
Qed.

Local Lemma list_lines_tight_nonempty :
  forall ls rest, lines_ok ls = true -> list_lines Tight (ls :: rest) <> [].
Proof.
  intros ls rest H. apply lines_ok_parts in H as (Hne & _ & _).
  destruct rest as [|ls2 rest'].
  - exact Hne.
  - cbn [list_lines]. destruct ls; [congruence | discriminate].
Qed.

Local Lemma list_lines_tight_no_nl :
  forall lss,
    forallb lines_ok lss = true -> forallb no_nl (list_lines Tight lss) = true.
Proof.
  induction lss as [|ls rest IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hls Hrest].
  apply lines_ok_parts in Hls as (_ & Hnl & _).
  destruct rest as [|ls2 rest']; [exact Hnl|].
  cbn [list_lines]. rewrite forallb_app, Hnl. cbn [andb]. apply IH. exact Hrest.
Qed.

Local Lemma list_lines_tight_last :
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

(* A block sequence's layout is lines_ok when each block's is.  Used
   twice: for the loose list layout, and for an item's own contents. *)
Local Lemma sep_lines_ok :
  forall lss, lss <> [] -> forallb lines_ok lss = true ->
  lines_ok (sep_lines lss) = true.
Proof.
  intros lss Hne Hok. destruct lss as [|ls rest]; [congruence|].
  pose proof Hok as Hok0. cbn [forallb] in Hok0.
  apply andb_true_iff in Hok0 as [Hls _].
  unfold lines_ok. apply andb_true_iff. split; [apply andb_true_iff; split|].
  - destruct (sep_lines (ls :: rest)) eqn:E; [|reflexivity].
    exfalso. apply (sep_lines_nonempty ls rest Hls). exact E.
  - apply sep_lines_no_nl. exact Hok.
  - apply nonempty_str_intro, (sep_lines_last ls rest Hok).
Qed.

(* Either spacing: nonempty items with lines_ok lines produce lines_ok
   output.  The single lemma cb_ok_lines_ok's CList case needs. *)
Local Lemma list_lines_ok :
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
  - rewrite list_lines_loose_eq. apply sep_lines_ok; [discriminate | exact Hok].
Qed.

(* Half one of the roundtrip: rendering then splitting recovers the
   per-block lines, laid out by sep_lines. *)
Local Lemma split_render :
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

Local Lemma forallb_line_ok_nonblank :
  forall ls, forallb line_ok ls = true -> forallb nonblank ls = true.
Proof.
  induction ls as [|l ls IH]; intros H; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H as [Hl Hls].
    unfold nonblank. rewrite (line_ok_nonblank _ Hl). simpl.
    apply IH. exact Hls.
Qed.

(* Canonical lines are already flush left, so stripping leading
   whitespace off each one is the identity: the parser's continuation
   rule, which strips, reproduces a canonical cblock's lines
   unchanged. *)
Local Lemma forallb_line_ok_map_drop_leading_ws :
  forall ls, forallb line_ok ls = true -> map drop_leading_ws ls = ls.
Proof.
  induction ls as [|l ls IH]; intros H; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H as [Hl Hls].
    rewrite (line_ok_no_leading_ws _ Hl), (IH Hls). reflexivity.
Qed.

(* Pushing an all-whitespace pad through a mapped nonblank/drop_leading_ws
   check: the two facts parse_cblock_pad's paragraph case needs to reuse
   parse_lines_para_seed (already generic over its lines) with padded
   arguments. *)
Local Lemma forallb_nonblank_map_pad :
  forall pad ls, is_blank pad = true -> forallb nonblank ls = true ->
  forallb nonblank (map (fun l => pad ++ l) ls) = true.
Proof.
  intros pad ls Hpad. induction ls as [|l ls IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hl Hls].
  cbn [map forallb]. unfold nonblank in Hl |- *.
  rewrite is_blank_ws_prefix by exact Hpad. rewrite Hl. cbn [andb]. apply IH, Hls.
Qed.

Local Lemma map_drop_leading_ws_map_pad :
  forall pad ls, is_blank pad = true ->
  map drop_leading_ws (map (fun l => pad ++ l) ls) = map drop_leading_ws ls.
Proof.
  intros pad ls Hpad. rewrite map_map.
  apply map_ext. intros a. apply drop_leading_ws_ws_prefix, Hpad.
Qed.

Local Lemma para_ok_parts :
  forall a ls, para_ok (a :: ls) = true ->
  classify a = KText
  /\ forallb line_ok (a :: ls) = true
  /\ strip_trailing_ws (last (a :: ls) EmptyString) = last (a :: ls) EmptyString
  /\ forallb (fun l => negb (bcuts l)) (a :: ls) = true
  /\ keyless a = true.
Proof.
  intros a ls H. unfold para_ok in H.
  apply andb_true_iff in H as [H Hlast].
  apply andb_true_iff in H as [H Hint].
  apply andb_true_iff in H as [H Hlok].
  apply andb_true_iff in H as [Htext Hkey].
  repeat split.
  - apply is_text_classify. exact Htext.
  - exact Hlok.
  - apply String.eqb_eq. exact Hlast.
  - exact Hint.
  - exact Hkey.
Qed.

Local Lemma forallb_weaken :
  forall {A : Type} (f g : A -> bool),
    (forall x, f x = true -> g x = true) ->
    forall l, forallb f l = true -> forallb g l = true.
Proof.
  intros A f g Hfg.
  induction l as [|x l IH]; intros H; simpl in *; [reflexivity|].
  apply andb_true_iff in H as [Hx Hl].
  rewrite (Hfg _ Hx). simpl. apply IH. exact Hl.
Qed.

Local Lemma info_no_nl :
  forall info, all_info_chars info = true -> no_nl info = true.
Proof.
  induction info as [|c info IH]; intros H; simpl in *; [reflexivity|].
  apply andb_true_iff in H as [Hc Hinfo].
  apply info_char_parts in Hc as (_ & _ & Hn).
  rewrite Hn. simpl. apply IH. exact Hinfo.
Qed.

Local Lemma code_ok_parts :
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

Local Lemma last_cons_app :
  forall {A : Type} (a : A) (l : list A) (x d : A),
    last (a :: l ++ [x])%list d = x.
Proof.
  intros A a l x d.
  change (a :: l ++ [x])%list with ((a :: l) ++ [x])%list.
  apply last_app_singleton.
Qed.

(* Marker-prefixed lines: every construct whose rendering puts a fixed
   marker in front of each line (quotes, headings) needs exactly this.
   Newline-freedom survives, and the last line is nonempty because the
   marker is. *)
Local Lemma no_nl_quote_line :
  forall l, no_nl (quote_line l) = no_nl l.
Proof.
  intros l. unfold quote_line, quote_open.
  rewrite no_nl_append. reflexivity.
Qed.

Local Lemma forallb_no_nl_map_append :
  forall p ls, no_nl p = true -> forallb no_nl ls = true ->
  forallb no_nl (map (fun x => p ++ x) ls) = true.
Proof.
  intros p ls Hp. induction ls as [|l ls IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hl Hls].
  cbn [map forallb]. rewrite no_nl_append, Hp, Hl. cbn [andb]. apply IH, Hls.
Qed.

(* A list item's rendering: marker on the first line, plain indent on the
   rest.  Two prefixes instead of quote_line's one, so this is not quite
   lines_ok_map, but the same shape otherwise. *)
Local Lemma lines_ok_indent :
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

(* Putting an item's marker and continuation pad on preserves the layout
   conditions: both prefixes are one line's worth of text (Line.v), and
   the item's own lines already satisfy them. *)
Local Lemma litem_lines_ok :
  forall m L, marker_ok m = true -> lines_ok L = true ->
  lines_ok (litem_lines (m, L)) = true.
Proof.
  intros m L Hm HL. apply lines_ok_parts in HL as (Hne & Hnl & _).
  unfold litem_lines. cbn [fst snd].
  apply lines_ok_indent;
    auto using mk_open_no_nl, mk_cont_no_nl, mk_open_nonempty, mk_cont_nonempty.
Qed.

Local Lemma litems_lines_ok :
  forall its,
    forallb (fun it => marker_ok (fst it)) its = true ->
    forallb lines_ok (map snd its) = true ->
    forallb lines_ok (map litem_lines its) = true.
Proof.
  induction its as [|[m L] rest IH]; intros Hm HL; [reflexivity|].
  cbn [forallb map fst snd] in Hm, HL |- *.
  apply andb_true_iff in Hm as [Hm Hms]. apply andb_true_iff in HL as [HL HLs].
  rewrite (litem_lines_ok m L Hm HL). cbn [andb]. apply IH; assumption.
Qed.

(* ...and a whole list's items, whichever markers its kind hands out. *)
Local Lemma ck_items_lines_ok :
  forall k lss, ck_ok k (length lss) = true -> forallb lines_ok lss = true ->
  forallb lines_ok (map litem_lines (ck_items k lss)) = true.
Proof.
  intros k lss Hck Hok. apply litems_lines_ok.
  - apply ck_items_markers_ok, Hck.
  - rewrite ck_items_lines. exact Hok.
Qed.

Local Lemma lines_ok_map :
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

Local Lemma lines_ok_quote :
  forall ls, ls <> [] -> forallb no_nl ls = true ->
  lines_ok (map quote_line ls) = true.
Proof.
  intros ls Hne Hnl. apply lines_ok_map; try assumption.
  - intros l Hl. rewrite no_nl_quote_line. exact Hl.
  - intros l. unfold quote_line, quote_open. discriminate.
Qed.

Local Lemma heading_ok_parts :
  forall lvl ls, heading_ok lvl ls = true ->
  1 <= lvl /\ ls <> [] /\ forallb line_ok ls = true
  /\ (bheading_continues || Nat.eqb (List.length ls) 1)%bool = true
  /\ strip_trailing_ws (last ls EmptyString) = last ls EmptyString.
Proof.
  intros lvl ls H. unfold heading_ok in H.
  apply andb_true_iff in H as [H Hlast].
  apply andb_true_iff in H as [H Hcontinues].
  apply andb_true_iff in H as [H Hlok].
  apply andb_true_iff in H as [Hlvl Hne].
  repeat split.
  - apply Nat.leb_le. exact Hlvl.
  - destruct ls; [discriminate | congruence].
  - exact Hlok.
  - exact Hcontinues.
  - apply String.eqb_eq. exact Hlast.
Qed.

(* Where the inline layer enters the block roundtrip, and the only place
   it does.  The parser reaches a paragraph as `para_inlines` of the
   lines it read; `cb_ast` names it as `ci_para` of the canonical view.
   `InlineInvert.para_inlines_ci_para` is what identifies the two, and its
   three hypotheses are exactly what `cb_ok` carries: `cis_ok` per line
   from the inline conjunct, nonemptiness derived from the block
   conjunct's `line_ok`, and the trailing-whitespace condition verbatim. *)
Local Lemma cb_ast_para_of_lines :
  forall lss, cb_ok (CPara lss) = true ->
  mk (Para (para_inlines (map ci_line lss))) = cb_ast (CPara lss).
Proof.
  intros lss H. rewrite cb_ok_para in H.
  apply andb_true_iff in H as [Hp Hc].
  destruct (map ci_line lss) as [|a ls'] eqn:E; [discriminate|].
  apply para_ok_parts in Hp as (_ & Hlok & Hlast & _ & _).
  rewrite <- E in Hlok, Hlast |- *.
  cbn [cb_ast]. f_equal. f_equal.
  apply para_inlines_ci_para;
    [exact Hc | apply cis_nonempty_of_lines; exact Hlok | exact Hlast].
Qed.

Local Lemma cb_ast_heading_of_lines :
  forall lvl lss, cb_ok (CHeading lvl lss) = true ->
  mk (Heading lvl (para_inlines (map ci_line lss))) = cb_ast (CHeading lvl lss).
Proof.
  intros lvl lss H. rewrite cb_ok_heading in H.
  apply andb_true_iff in H as [Hh Hc].
  apply heading_ok_parts in Hh as (_ & _ & Hlok & _ & Hlast).
  cbn [cb_ast]. f_equal. f_equal.
  apply para_inlines_ci_para;
    [exact Hc | apply cis_nonempty_of_lines; exact Hlok | exact Hlast].
Qed.

(* cb_ok is stated per construct; lines_ok is what split_render needs.
   This is the bridge between them.  The quote case needs the same fact
   about its contents' layout, hence the two-predicate induction. *)
(*
Canonical tables
================

A table's lines are the rows', and every one of them is a row line:
there is no interior structure to invert and no column to match, so the
whole construct reads off `ctrow_ok`'s per-line test.
*)

Local Lemma ctrow_lines_ok :
  forall r, ctrow_ok r = true -> forallb line_ok (ctrow_lines r) = true.
Proof.
  intros r H. apply ctrow_ok_parts in H as (_ & _ & Hlok & _).
  destruct r as [cs|als cs];
    cbn [ctrow_lines ctrow_cells forallb] in Hlok |- *;
    rewrite Hlok, ?line_ok_sep_line; reflexivity.
Qed.

Local Lemma ctable_lines_forallb :
  forall rows, forallb ctrow_ok rows = true ->
  forallb line_ok (flat_map ctrow_lines rows) = true.
Proof.
  induction rows as [|r rows IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hr Hrows].
  cbn [flat_map]. rewrite forallb_app, (ctrow_lines_ok _ Hr), (IH Hrows).
  reflexivity.
Qed.

(* A row is at least one line, so a nonempty table renders to a nonempty
   line list -- which is what `sep_lines` needs of every block. *)
Local Lemma ctable_lines_cons :
  forall r rows,
    exists a ls, flat_map ctrow_lines (r :: rows) = a :: ls.
Proof.
  intros [cs|als cs] rows; cbn [flat_map ctrow_lines app]; eauto.
Qed.

(* The parse, one row at a time.  A table records no column and the rows
   are the only lines, so each is `parse_lines_table_row` and the state's
   accumulator grows by the row's `trow`s, reversed.  The range is one a
   row has already reached, which is what opening the table leaves, so
   later rows do not move it. *)
Local Lemma parse_ctrow_cont :
  forall r range acc rest, ctrow_ok r = true -> touch_extent range = range ->
  parse_lines (ctrow_lines r ++ rest) (PTable range acc (TOpen []))
  = parse_lines rest (PTable range (rev (ctrow_trows r) ++ acc) (TOpen [])).
Proof.
  intros r range acc rest H Ht.
  pose proof (ctrow_ok_parts _ H) as (_ & _ & _ & Hcl).
  destruct r as [cs|als cs]; cbn [ctrow_cells] in Hcl;
    cbn [ctrow_lines ctrow_trows rev app].
  - rewrite (parse_lines_table_row _ _ _ _ _ _ (caption_open_cells_line _)
               (is_blank_cells_line _) Hcl), Ht. reflexivity.
  - apply ctrow_ok_head in H as [_ Hsep].
    rewrite (parse_lines_table_row _ _ _ _ _ _ (caption_open_cells_line _)
               (is_blank_cells_line _) Hcl), Ht.
    rewrite (parse_lines_table_row _ _ _ _ _ _ (caption_open_sep_line _)
               (is_blank_sep_line _) Hsep), Ht.
    reflexivity.
Qed.

Local Lemma parse_ctrow_open :
  forall r rest, btables = true -> ctrow_ok r = true ->
  exists range, touch_extent range = range /\
  parse_lines (ctrow_lines r ++ rest) (PPara [])
  = parse_lines rest (PTable range (rev (ctrow_trows r)) (TOpen [])).
Proof.
  intros r rest Htables H.
  pose proof (ctrow_ok_parts _ H) as (_ & _ & _ & Hcl).
  destruct r as [cs|als cs]; cbn [ctrow_cells] in Hcl;
    cbn [ctrow_lines ctrow_trows rev app].
  - rewrite (parse_lines_row_open _ _ _ Htables Hcl).
    eexists; split; [|reflexivity]; reflexivity.
  - apply ctrow_ok_head in H as [_ Hsep].
    rewrite (parse_lines_row_open _ _ _ Htables Hcl).
    rewrite (parse_lines_table_row _ _ _ _ _ _ (caption_open_sep_line _)
               (is_blank_sep_line _) Hsep).
    eexists; split; [|reflexivity]; reflexivity.
Qed.

Local Lemma parse_ctrows :
  forall rows range acc rest, forallb ctrow_ok rows = true ->
  touch_extent range = range ->
  parse_lines (flat_map ctrow_lines rows ++ rest) (PTable range acc (TOpen []))
  = parse_lines rest
      (PTable range (rev (flat_map ctrow_trows rows) ++ acc) (TOpen [])).
Proof.
  induction rows as [|r rows IH]; intros range acc rest H Ht; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hr Hrows].
  cbn [flat_map]. rewrite <- app_assoc.
  rewrite (parse_ctrow_cont _ _ _ _ Hr Ht), (IH _ _ _ Hrows Ht).
  rewrite rev_app_distr, <- app_assoc. reflexivity.
Qed.

(* The whole table, from idle: the state it leaves is the rows in reverse
   source order, which is what `finish` folds. *)
Local Lemma parse_ctable :
  forall rows rest, btables = true ->
  nonempty rows = true -> forallb ctrow_ok rows = true ->
  exists range,
  parse_lines (flat_map ctrow_lines rows ++ rest) (PPara [])
  = parse_lines rest (PTable range (rev (flat_map ctrow_trows rows)) (TOpen [])).
Proof.
  intros [|r rows] rest Htables Hne Hok; [discriminate Hne|].
  cbn [forallb] in Hok. apply andb_true_iff in Hok as [Hr Hrows].
  cbn [flat_map]. rewrite <- app_assoc.
  destruct (parse_ctrow_open r (flat_map ctrow_lines rows ++ rest) Htables Hr)
    as [range [Ht Hopen]].
  exists range.
  rewrite Hopen, (parse_ctrows _ _ _ _ Hrows Ht).
  rewrite rev_app_distr. reflexivity.
Qed.

(* And what that state finishes to.  `table_block` is `table_fold` on the
   rows in source order, which `table_fold_ctable_cells` identifies with
   the canonical fold. *)
Local Lemma table_block_ctable :
  forall rows cap,
    forallb ctrow_ok rows = true ->
    caption_of cap = None ->
    table_block (rev (rev (flat_map ctrow_trows rows))) cap = cb_ast (CTable rows).
Proof.
  intros rows cap Hok Hcap. rewrite rev_involutive.
  unfold table_block. rewrite Hcap, cb_ast_table. f_equal. f_equal.
  apply table_fold_ctable_cells.
  refine (forallb_weaken _ _ _ _ Hok).
  intros r Hr. apply ctrow_ok_parts in Hr as (_ & Hcis & _). exact Hcis.
Qed.

Local Lemma cb_ok_lines_ok :
  forall cb, cb_ok cb = true -> lines_ok (cb_lines cb) = true.
Proof.
  refine (cblock_ind2
            (fun cb => cb_ok cb = true -> lines_ok (cb_lines cb) = true)
            (fun cbs => forallb cb_ok cbs = true ->
                        forallb lines_ok (map cb_lines cbs) = true)
            (Forall (fun cbs => forallb cb_ok cbs = true ->
                                 forallb lines_ok (map cb_lines cbs) = true))
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Forall_nil _) (fun item items Hi Hr => Forall_cons _ Hi Hr)).
  - (* paragraph: line_ok everywhere implies the split conditions.  The
       inline conjunct of cb_ok says nothing about line shape, so this
       case reads exactly as it did over `list string`. *)
    intros lss H. rewrite cb_ok_para in H.
    apply andb_true_iff in H as [H _].
    cbn [cb_lines]. remember (map ci_line lss) as ls eqn:E. clear E lss.
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
    cbn [cb_ok] in H. apply andb_true_iff in H as [H _].
    apply code_ok_parts in H as (Hinfo & Hnl & _).
    unfold lines_ok. cbn [cb_lines].
    apply andb_true_iff. split; [apply andb_true_iff; split|].
    + reflexivity.
    + cbn [forallb].
      unfold code_open. rewrite no_nl_append, (info_no_nl _ Hinfo).
      simpl. rewrite forallb_app, Hnl. reflexivity.
    + rewrite last_cons_app. reflexivity.
  - (* raw block: the `=format` info has the same line obligations *)
    intros format content H.
    cbn [cb_ok] in H. apply andb_true_iff in H as [_ H].
    unfold raw_ok in H.
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
    intros lvl lss H. rewrite cb_ok_heading in H.
    apply andb_true_iff in H as [H _].
    cbn [cb_lines]. remember (map ci_line lss) as ls eqn:E. clear E lss.
    apply heading_ok_parts in H as (Hlvl & Hne & Hlok & _ & _).
    apply lines_ok_map.
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
  - (* div: the fences carry both conditions by themselves.  The last
       line is `:::` whatever the contents are, so unlike the quote case
       there is nothing to prove about nonemptiness *)
    intros inner IH H.
    rewrite cb_ok_div in H. apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [H Hinner].
    apply andb_true_iff in H as [_ Hok].
    rewrite cb_lines_div. unfold lines_ok.
    cbn [nonempty forallb]. rewrite last_cons_app, forallb_app. cbn [forallb].
    rewrite (sep_lines_no_nl _ (IH Hok)). reflexivity.
  - (* list: each item lays out as a document would, then gets its
       marker/pad prefix (ck_items_lines_ok); list_lines_ok closes the
       spacing. *)
    intros k sp items IH H.
    rewrite cb_ok_list in H.
    apply andb_true_iff in H as [H Hcont].
    apply andb_true_iff in H as [H Hspacing].
    apply andb_true_iff in H as [H Hsafe].
    apply andb_true_iff in H as [H Hmarker].
    apply andb_true_iff in H as [H Hckok].
    apply andb_true_iff in H as [Hne Hitems].
    assert (Hlines : forallb lines_ok (map item_lines items) = true).
    { clear Hne Hspacing Hmarker Hsafe Hckok Hcont. revert Hitems.
      induction IH as [|it items' HQ IHrest IHind]; intros Hitems; [reflexivity|].
      cbn [forallb] in Hitems. apply andb_true_iff in Hitems as [Hit Hitems'].
      apply andb_true_iff in Hit as [Hitne Hitok].
      cbn [map forallb]. unfold item_lines at 1.
      rewrite (sep_lines_ok (map cb_lines it)
                 ltac:(destruct it; [discriminate Hitne | discriminate])
                 (HQ Hitok)).
      cbn [andb]. apply IHind. exact Hitems'. }
    rewrite cb_lines_list. apply list_lines_ok.
    + apply ck_lines_nonempty.
      destruct items; [discriminate Hne | discriminate].
    + apply ck_items_lines_ok; [rewrite length_map; exact Hckok | exact Hlines].
  - (* reference definition: one line, and `ref_ok` bounds both halves of
       it away from a line break *)
    intros label dest H. unfold ref_ok in H.
    apply andb_true_iff in H as [H Hd].
    apply andb_true_iff in H as [_ Hnl].
    unfold lines_ok. cbn [cb_lines nonempty forallb last]. unfold ref_line.
    rewrite !no_nl_append, Hnl, (no_ws_no_nl _ Hd). reflexivity.
  - (* table: every line is a row line, so the three conditions come off
       `line_ok` the way a paragraph's do *)
    intros rows H. rewrite cb_ok_table in H.
    apply andb_true_iff in H as [H Hrows].
    apply andb_true_iff in H as [_ Hne].
    pose proof (ctable_lines_forallb _ Hrows) as Hlok.
    rewrite cb_lines_table.
    destruct rows as [|r rows']; [discriminate Hne|].
    destruct (ctable_lines_cons r rows') as [a [ls E]].
    rewrite E in Hlok |- *. unfold lines_ok.
    rewrite (forallb_weaken _ _ line_ok_no_nl _ Hlok).
    pose proof (forallb_last _ _ _ Hlok) as Hl.
    apply line_ok_nonblank, nonblank_nonempty in Hl.
    rewrite Hl. reflexivity.
  - (* explicit id: its attribute line is newline-free, while the last
       line and every inner line come from the wrapped block *)
    intros id inner IH H. rewrite cb_ok_id in H.
    apply andb_true_iff in H as [Hid Hinner].
    apply andb_true_iff in Hid as [Hid _].
    apply andb_true_iff in Hid as [_ Hid].
    unfold explicit_id_ok in Hid. apply andb_true_iff in Hid as [_ Hchars].
    specialize (IH Hinner). unfold lines_ok in IH |- *.
    apply andb_true_iff in IH as [IH Hlast].
    apply andb_true_iff in IH as [Hne Hlines].
    cbn [cb_lines nonempty forallb].
    rewrite !no_nl_append, (id_chars_ok_no_nl _ Hchars), Hlines.
    destruct (cb_lines inner) as [|a rest]; [discriminate Hne|].
    destruct rest; cbn [no_nl last] in Hlast |- *; rewrite Hlast; reflexivity.
  - intros label inner IH H.
    destruct (cb_ok_key_parts label inner H) as (_ & Hl & Hi & _).
    destruct (ckey_label_ok_parts label Hl) as (_ & Hline & _).
    specialize (IH Hi). unfold lines_ok in IH |- *.
    apply andb_true_iff in IH as [IH Hlast].
    apply andb_true_iff in IH as [Hne Hlines].
    cbn [cb_lines nonempty forallb].
    rewrite (line_ok_no_nl _ Hline), Hlines.
    destruct (cb_lines inner) as [|a rest]; [discriminate Hne|].
    destruct rest; cbn [last] in Hlast |- *; rewrite Hlast; reflexivity.
  - reflexivity.
  - intros c rest Hc Hrest H.
    cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
    cbn [map forallb]. rewrite (Hc H1). cbn [andb]. apply Hrest. exact H2.
Qed.

Local Lemma forallb_cb_lines_ok :
  forall cbs, forallb cb_ok cbs = true ->
  forallb lines_ok (map cb_lines cbs) = true.
Proof.
  induction cbs as [|cb cbs IH]; intros H; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H as [Hcb Hcbs].
    rewrite (cb_ok_lines_ok _ Hcb). simpl.
    apply IH. exact Hcbs.
Qed.

Local Lemma rev_cons_shape :
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
`item_ok` on each item's rendering, which `cb_ok` asks for directly, so
nothing here reasons about what is inside an item, another list
included.

What is left is bookkeeping: `cb_lines`'s shape has to be matched to
`list_lines`'s, the spacing verdict read off `cb_ok`'s conjunct, and the
block that closes the list shown to be a line the parser will not
mistake for a continuation.
*)

Local Lemma classify_not_blank_nonblank :
  forall l, classify l <> KBlank -> nonblank l = true.
Proof.
  intros l H. unfold nonblank. apply negb_true_iff.
  destruct (is_blank l) eqn:Hblank; [|reflexivity].
  exfalso. apply H. apply classify_blank. exact Hblank.
Qed.

Local Lemma nonlist_cblock_first :
  forall cb,
    is_clist cb = false -> cb_ok cb = true ->
    exists a rest,
      cb_lines cb = a :: rest /\
      forall m mc chk item, classify a <> KList m mc chk item.
Proof.
  intros cb Hnonlist Hok.
  pose proof (cb_ok_lines_ok cb Hok) as Hlines.
  apply lines_ok_parts in Hlines as (Hne & _ & _).
  destruct cb as [ls| |info content|format content|lvl ls|inner|dinner|k sp items|rl rd|rows|id named|label keyed].
  - rewrite cb_ok_para in Hok. apply andb_true_iff in Hok as [Hok _].
    cbn [cb_lines] in Hne |- *.
    remember (map ci_line ls) as ls' eqn:E. clear E.
    destruct ls' as [|a rest].
    + exfalso. apply Hne. reflexivity.
    + exists a, rest. split; [reflexivity|].
      apply para_ok_parts in Hok as [Ha _].
      intros m mc chk item E. rewrite Ha in E. discriminate.
  - exists thematic_line, []. split; [reflexivity|].
    intros m mc chk item E. unfold thematic_line in E.
    rewrite classify_canonical_thematic in E. discriminate.
  - exists (code_open info), (content ++ [code_close])%list.
    split; [reflexivity|]. intros m mc chk item E.
    cbn [cb_ok] in Hok. apply andb_true_iff in Hok as [Hok _].
    apply code_ok_parts in Hok as [Hinfo _].
    unfold code_open in E.
    rewrite (classify_backtick_fence info Hinfo) in E. discriminate.
  - exists (code_open (String "="%char format)),
      (content ++ [code_close])%list.
    split; [reflexivity|]. intros m mc chk item E.
    cbn [cb_ok] in Hok. apply andb_true_iff in Hok as [_ Hok].
    unfold raw_ok in Hok. apply code_ok_parts in Hok as [Hinfo _].
    unfold code_open in E.
    rewrite (classify_backtick_fence _ Hinfo) in E. discriminate.
  - rewrite cb_ok_heading in Hok. apply andb_true_iff in Hok as [Hok _].
    cbn [cb_lines] in Hne |- *.
    remember (map ci_line ls) as ls' eqn:E. clear E.
    apply heading_ok_parts in Hok as [Hlvl [Hls _]].
    destruct ls' as [|a rest].
    + exfalso. apply Hls. reflexivity.
    + exists (heading_line lvl a), (map (heading_line lvl) rest).
      split; [reflexivity|]. intros m mc chk item E.
      rewrite (classify_canonical_heading lvl a Hlvl) in E. discriminate.
  - rewrite cb_lines_quote.
    destruct (sep_lines (map cb_lines inner)) as [|l rest] eqn:Esep.
    + exfalso. apply Hne. rewrite cb_lines_quote, Esep. reflexivity.
    + exists (quote_line l), (map quote_line rest). split; [reflexivity|].
      intros m mc chk item E. rewrite classify_canonical_quote in E. discriminate.
  - (* div: the opening fence is the first line, whatever the contents *)
    rewrite cb_lines_div.
    exists div_fence, (sep_lines (map cb_lines dinner) ++ [div_fence])%list.
    split; [reflexivity|].
    intros m mc chk item E. rewrite classify_canonical_div in E. discriminate.
  - discriminate Hnonlist.
  - (* reference definition: one line, and it classifies as one *)
    exists (ref_line rl rd), []. split; [reflexivity|].
    intros m mc chk item E. rewrite (ref_ok_classify rl rd Hok) in E. discriminate.
  - (* table: the first line is its first row's, and it classifies as one *)
    rewrite cb_ok_table in Hok. apply andb_true_iff in Hok as [Hok Hrows].
    apply andb_true_iff in Hok as [_ Hrows_nonempty].
    destruct rows as [|r rows']; [discriminate Hrows_nonempty|].
    cbn [forallb] in Hrows. apply andb_true_iff in Hrows as [Hr _].
    apply ctrow_ok_parts in Hr as (_ & _ & _ & Hcl).
    rewrite cb_lines_table.
    destruct r as [cs|als cs]; cbn [ctrow_cells] in Hcl;
      cbn [flat_map ctrow_lines app];
      eexists; eexists; (split; [reflexivity|]);
      intros m mc chk item E; rewrite Hcl in E; discriminate.
  - exists ("{#" ++ id ++ "}"), (cb_lines named). split; [reflexivity|].
    intros m mc chk item E.
    assert (Hm : list_marker ("{#" ++ id ++ "}") = None) by reflexivity.
    unfold classify in E.
    destruct (is_blank ("{#" ++ id ++ "}")); [discriminate|].
    destruct (quote_prefix ("{#" ++ id ++ "}")); [discriminate|].
    destruct (heading_open ("{#" ++ id ++ "}")) as [[lvl r2]|]; [discriminate|].
    destruct (fence_open ("{#" ++ id ++ "}")); [discriminate|].
    destruct (div_open ("{#" ++ id ++ "}")) as [[dn dc]|]; [discriminate|].
    destruct (is_thematic ("{#" ++ id ++ "}")); [discriminate|].
    rewrite Hm in E.
    destruct (Attributes.attr_open ("{#" ++ id ++ "}")); [discriminate|].
    destruct (foot_open ("{#" ++ id ++ "}")) as [[fl fr]|]; [discriminate|].
    destruct (ref_open ("{#" ++ id ++ "}")) as [[rl rv]|]; [discriminate|].
    destruct (table_row ("{#" ++ id ++ "}")); discriminate.
  - destruct (cb_ok_key_parts label keyed Hok) as (_ & Hl & _).
    destruct (ckey_label_ok_parts label Hl) as (_ & _ & Hcl & _).
    exists (ci_line [label] ++ ":"), (cb_lines keyed). split; [reflexivity|].
    intros m mc chk item E. rewrite Hcl in E. discriminate.
Qed.

Local Lemma drop_leading_ws_indent_zero :
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

Local Lemma cb_lines_first_line_ok :
  forall cb first rest,
    is_clist cb = false -> cb_ok cb = true ->
    cb_lines cb = first :: rest -> line_ok first = true.
Proof.
  intros cb first rest Hnonlist Hok Hlines.
  destruct cb as [ls| |info content|format content|lvl ls|inner|dinner|k sp items|rl rd|rows|id named|label keyed].
  - rewrite cb_ok_para in Hok. apply andb_true_iff in Hok as [Hok _].
    cbn [cb_lines] in Hlines.
    remember (map ci_line ls) as ls0 eqn:E. clear E.
    destruct ls0 as [|l ls']; [discriminate Hok|].
    apply para_ok_parts in Hok as [_ [Hok _]].
    injection Hlines as <- <-. cbn [forallb] in Hok.
    apply andb_true_iff in Hok as [Hfirst _]. exact Hfirst.
  - cbn [cb_lines] in Hlines. injection Hlines as <- <-. reflexivity.
  - cbn [cb_ok] in Hok. apply andb_true_iff in Hok as [Hok _].
    apply code_ok_parts in Hok as [Hinfo _].
    cbn [cb_lines] in Hlines. injection Hlines as <- <-.
    unfold code_open, line_ok. apply andb_true_iff; split.
    + apply andb_true_iff; split.
      * reflexivity.
      * rewrite no_nl_append, (info_no_nl _ Hinfo). reflexivity.
    + apply String.eqb_eq. reflexivity.
  - cbn [cb_ok] in Hok. apply andb_true_iff in Hok as [_ Hok].
    unfold raw_ok in Hok. apply code_ok_parts in Hok as [Hinfo _].
    cbn [cb_lines] in Hlines. injection Hlines as <- <-.
    unfold code_open, line_ok. apply andb_true_iff; split.
    + apply andb_true_iff; split.
      * reflexivity.
      * rewrite no_nl_append, (info_no_nl _ Hinfo). reflexivity.
    + apply String.eqb_eq. reflexivity.
  - rewrite cb_ok_heading in Hok. apply andb_true_iff in Hok as [Hok _].
    cbn [cb_lines] in Hlines.
    remember (map ci_line ls) as ls0 eqn:E. clear E.
    apply heading_ok_parts in Hok as [Hlvl [_ [Hok _]]].
    destruct ls0 as [|l ls']; [discriminate Hlines|].
    cbn [map] in Hlines. injection Hlines as <- <-.
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
  - rewrite cb_lines_div in Hlines. cbn [app] in Hlines.
    injection Hlines as <- <-. reflexivity.
  - discriminate Hnonlist.
  - cbn [cb_lines] in Hlines. injection Hlines as <- <-.
    apply (ref_line_ok rl rd Hok).
  - rewrite cb_ok_table in Hok. apply andb_true_iff in Hok as [Hok Hrows].
    apply andb_true_iff in Hok as [_ Hrows_nonempty].
    destruct rows as [|r rows']; [discriminate Hrows_nonempty|].
    cbn [forallb] in Hrows. apply andb_true_iff in Hrows as [Hr _].
    pose proof (ctrow_lines_ok _ Hr) as Hlok.
    rewrite cb_lines_table in Hlines.
    destruct r as [cs|als cs]; cbn [flat_map ctrow_lines app forallb] in *;
      injection Hlines as <- _;
      apply andb_true_iff in Hlok as [Hfirst _]; exact Hfirst.
  - rewrite cb_ok_id in Hok. apply andb_true_iff in Hok as [Hid _].
    apply andb_true_iff in Hid as [Hid _].
    apply andb_true_iff in Hid as [_ Hid]. unfold explicit_id_ok in Hid.
    apply andb_true_iff in Hid as [_ Hchars].
    cbn [cb_lines] in Hlines. injection Hlines as <- <-.
    unfold line_ok. apply andb_true_iff; split.
    + apply andb_true_iff; split; [reflexivity|].
      cbn [no_nl]. rewrite no_nl_append, (id_chars_ok_no_nl _ Hchars).
      reflexivity.
    + apply String.eqb_eq. reflexivity.
  - destruct (cb_ok_key_parts label keyed Hok) as (_ & Hl & _).
    destruct (ckey_label_ok_parts label Hl) as (_ & Hline & _).
    cbn [cb_lines] in Hlines. injection Hlines as <- <-. exact Hline.
Qed.

(* The one symbolic fact the CId roundtrip needs from the attribute
   scanner: feeding identifier characters accumulates exactly that id.
   The token is reversed in the scanner, hence the accumulator form. *)
Local Lemma afeed_id_acc :
  forall id tok key attrs,
    id_chars_ok id = true -> tok <> [] ->
    afeed (id ++ ("}" ++ attr_nl)) (AP AId tok key attrs)
    = (AP ADone [] key (Attr.set "id" (rev_chars tok ++ id) attrs), attr_nl).
Proof.
  induction id as [|c rest IH]; intros tok key attrs Hids Htok.
  - cbn [append afeed ap_st astep].
    assert (Hclose : is_id_char "}" = false) by reflexivity.
    rewrite Hclose. cbn. unfold ap_commit_id, ap_token.
    cbn [ap_tok ap_key ap_attrs].
    destruct (rev_chars tok) eqn:E.
    { destruct tok as [|x tok]; [contradiction|].
      exfalso. eapply rev_chars_nonempty; exact E. }
    cbn [String.eqb]. unfold attr_nl. cbn [afeed ap_st append].
    rewrite append_empty_r. reflexivity.
  - cbn [id_chars_ok] in Hids.
    apply andb_true_iff in Hids as [Hc Hr].
    cbn [append afeed ap_st astep]. rewrite Hc.
    unfold ap_push. cbn [ap_st ap_tok ap_key ap_attrs].
    specialize (IH (c :: tok) key attrs Hr (fun H => match H with end)).
    etransitivity; [exact IH|].
    cbn [rev_chars]. rewrite !append_assoc. reflexivity.
Qed.

Local Lemma attr_open_canonical_id :
  forall id, explicit_id_ok id = true ->
    Attributes.attr_open ("{#" ++ id ++ "}")
    = Some (AP ADone [] "" [("id", id)]).
Proof.
  intros [|c rest] H; [discriminate|].
  unfold explicit_id_ok in H. apply andb_true_iff in H as [_ Hchars].
  cbn [id_chars_ok] in Hchars.
  apply andb_true_iff in Hchars as [Hc Hr].
  unfold Attributes.attr_open.
  cbn [drop_leading_ws is_ws append afeed ap_st astep ap_begin].
  assert (Hb : is_ws "{" = false) by reflexivity. rewrite Hb.
  cbn [append afeed ap_st astep ap_begin].
  cbn [ap_init ap_st astep ap_begin].
  assert (Hws : attr_ws "#" = false) by reflexivity.
  assert (Hneq : Ascii.eqb "#" "}" = false) by reflexivity.
  assert (Heq : Ascii.eqb "#" "#" = true) by reflexivity.
  rewrite Hws, Hneq, Heq. cbn [ap_begin ap_st astep]. rewrite Hc.
  unfold ap_push, ap_begin, ap_init. cbn [ap_st ap_tok ap_key ap_attrs].
  pose proof (afeed_id_acc rest [c] "" [] Hr (fun H => match H with end)) as Ha.
  rewrite append_assoc, Ha.
  cbn [rev_string append ap_failed ap_done blank_to_eol negb andb
       Attr.set alist_set].
  reflexivity.
Qed.

Local Lemma classify_canonical_id :
  forall id, explicit_id_ok id = true ->
    classify ("{#" ++ id ++ "}")
    = KAttr (AP ADone [] "" [("id", id)]).
Proof.
  intros id H. unfold classify.
  assert (Hb : is_blank ("{#" ++ id ++ "}") = false) by reflexivity.
  assert (Hq : quote_prefix ("{#" ++ id ++ "}") = None) by reflexivity.
  assert (Hh : heading_open ("{#" ++ id ++ "}") = None) by reflexivity.
  assert (Hf : fence_open ("{#" ++ id ++ "}") = None) by reflexivity.
  assert (Hd : div_open ("{#" ++ id ++ "}") = None) by reflexivity.
  assert (Ht : is_thematic ("{#" ++ id ++ "}") = false) by reflexivity.
  assert (Hl : list_marker ("{#" ++ id ++ "}") = None) by reflexivity.
  rewrite Hb, Hq, Hh, Hf, Hd, Ht, Hl, (attr_open_canonical_id id H).
  reflexivity.
Qed.

(* The items' contents, as the mutual induction supplies them: each
   item's lines parse at top level to that item's blocks.  Passed in
   rather than assumed, since it is `parse_cblock`'s own induction
   hypothesis. *)
Local Definition items_parse (items : list (list cblock)) : Prop :=
  map (fun it => parse_lines (item_lines it) (PPara [])) items
  = map (fun it => map cb_ast it) items.

Local Lemma forallb_map :
  forall {A B : Type} (f : B -> bool) (g : A -> B) l,
    forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof. induction l as [|x l IH]; [reflexivity|cbn; rewrite IH; reflexivity]. Qed.

Local Lemma existsb_map :
  forall {A B : Type} (f : B -> bool) (g : A -> B) l,
    existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof. induction l as [|x l IH]; [reflexivity|cbn; rewrite IH; reflexivity]. Qed.

(* cb_ok's list conjuncts, in the form ck_uniformity asks for. *)
Local Lemma cb_ok_list_parts :
  forall k sp items,
    cb_ok (CList k sp items) = true ->
    map item_lines items <> []
    /\ ck_ok k (length (map item_lines items)) = true
    /\ forallb (item_ok (ck_first k)) (map item_lines items) = true
    /\ list_spacing_of sp (map item_lines items) = sp.
Proof.
  intros k sp items H. rewrite cb_ok_list in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[Hne Hitems] Hckok] Hitemok] _] Hspacing] _].
  assert (Hne' : map item_lines items <> [])
    by (destruct items; [discriminate Hne|discriminate]).
  assert (Hmap : forallb (item_ok (ck_first k)) (map item_lines items) = true).
  { rewrite forallb_map. exact Hitemok. }
  assert (Hforce : existsb (fun L => item_loose L) (map item_lines items)
                   = items_force_loose items).
  { unfold items_force_loose, item_forces_loose. rewrite existsb_map. reflexivity. }
  split; [exact Hne'|]. split; [rewrite length_map; exact Hckok|].
  split; [exact Hmap|].
  unfold list_spacing_of. rewrite Hforce.
  destruct sp.
  - apply negb_true_iff in Hspacing. rewrite Hspacing. reflexivity.
  - apply orb_true_iff in Hspacing as [Hseps | Hforced].
    + unfold items_seps_loosen in Hseps. rewrite Hseps, orb_true_r. reflexivity.
    + rewrite Hforced. reflexivity.
Qed.

(* A canonical block that is not itself named opens with a line that
   neither drops pending block attributes nor claims them: every
   constructor's first line has a classification of its own, and a list's
   is a marker (`Parser.ck_lines_first_ready`).  This is what lets an id
   reach the block it names. *)
Local Lemma cb_lines_first_ready :
  forall cb a rest,
    is_cid cb = false -> cb_ok cb = true -> cb_lines cb = (a :: rest)%list ->
    pend_ready (PPara []) a = true.
Proof.
  intros cb a rest Hnotid Hok Hlines.
  destruct cb as [ls| |info content|format content|lvl ls|inner|dinner
                 |k sp items|rl rd|rows|id named|label keyed];
    [| | | | | | | | | |discriminate Hnotid|].
  - rewrite cb_ok_para in Hok. apply andb_true_iff in Hok as [Hok _].
    cbn [cb_lines] in Hlines.
    destruct (map ci_line ls) as [|a0 rest0] eqn:E; [discriminate Hlines|].
    injection Hlines as <- _.
    apply para_ok_parts in Hok as [Ha _]. unfold pend_ready. rewrite Ha.
    reflexivity.
  - cbn [cb_lines] in Hlines. injection Hlines as <- _.
    unfold pend_ready, thematic_line. rewrite classify_canonical_thematic.
    reflexivity.
  - cbn [cb_lines] in Hlines. injection Hlines as <- _.
    cbn [cb_ok] in Hok. apply andb_true_iff in Hok as [Hok _].
    apply code_ok_parts in Hok as [Hinfo _].
    unfold pend_ready, code_open. rewrite (classify_backtick_fence info Hinfo).
    reflexivity.
  - cbn [cb_lines] in Hlines. injection Hlines as <- _.
    cbn [cb_ok] in Hok. apply andb_true_iff in Hok as [_ Hok].
    unfold raw_ok in Hok. apply code_ok_parts in Hok as [Hinfo _].
    unfold pend_ready, code_open. rewrite (classify_backtick_fence _ Hinfo).
    reflexivity.
  - rewrite cb_ok_heading in Hok. apply andb_true_iff in Hok as [Hok _].
    apply heading_ok_parts in Hok as [Hlvl [Hls _]].
    cbn [cb_lines] in Hlines.
    destruct (map ci_line ls) as [|a0 rest0] eqn:E; [contradiction|].
    cbn [map] in Hlines. injection Hlines as <- _.
    unfold pend_ready. rewrite (classify_canonical_heading lvl a0 Hlvl).
    reflexivity.
  - rewrite cb_lines_quote in Hlines.
    destruct (sep_lines (map cb_lines inner)) as [|l0 rest0] eqn:Esep;
      [discriminate Hlines|].
    cbn [map] in Hlines. injection Hlines as <- _.
    unfold pend_ready. rewrite classify_canonical_quote. reflexivity.
  - rewrite cb_lines_div in Hlines. injection Hlines as <- _.
    unfold pend_ready. rewrite classify_canonical_div. reflexivity.
  - destruct (cb_ok_list_parts k sp items Hok) as (_ & Hckok & Hitemok & _).
    rewrite cb_lines_list in Hlines.
    exact (ck_lines_first_ready k sp (map item_lines items) a rest
             Hckok Hitemok Hlines).
  - cbn [cb_lines] in Hlines. injection Hlines as <- _.
    unfold pend_ready. rewrite (ref_ok_classify rl rd Hok). reflexivity.
  - rewrite cb_ok_table in Hok. apply andb_true_iff in Hok as [Hok Hrows].
    apply andb_true_iff in Hok as [_ Hne].
    destruct rows as [|r rows']; [discriminate Hne|].
    cbn [forallb] in Hrows. apply andb_true_iff in Hrows as [Hr _].
    apply ctrow_ok_parts in Hr as (_ & _ & _ & Hcl).
    rewrite cb_lines_table in Hlines.
    destruct r as [cs|als cs]; cbn [ctrow_cells] in Hcl;
      cbn [flat_map ctrow_lines app] in Hlines;
      injection Hlines as <- _; unfold pend_ready; rewrite Hcl; reflexivity.
  - destruct (cb_ok_key_parts label keyed Hok) as (_ & Hl & _).
    destruct (ckey_label_ok_parts label Hl) as (_ & _ & Hcl & _).
    change ((ci_line [label] ++ ":") :: cb_lines keyed = a :: rest) in Hlines.
    injection Hlines as <- _. unfold pend_ready.
    cbn [ci_line ci_text] in Hcl. rewrite Hcl. reflexivity.
Qed.

(* Attaching the pending id to the block the parser emits is what
   `cb_ast` does to the block it wraps.  The two spellings agree on the
   attribute sets a canonical block carries -- none, or a div's class --
   which is why the wrapper may not nest. *)
Local Lemma decorate_head_cb_ast :
  forall id cb bs, is_cid cb = false ->
    decorate_head [("id", id)] (cb_ast cb :: bs) = (cb_ast (CId id cb) :: bs)%list.
Proof.
  intros id cb bs Hnotid. cbn [cb_ast add_attr].
  destruct cb; try reflexivity; discriminate Hnotid.
Qed.

Local Lemma fence_block_canonical_code :
  forall info content,
    cb_ok (CCode info content) = true ->
    fence_block (Fence "`"%char 3 info) content = cb_ast (CCode info content).
Proof.
  intros info content H. cbn [cb_ok] in H.
  apply andb_true_iff in H as [_ Hgate].
  unfold fence_block, cb_ast. cbn [f_info].
  destruct info as [|c info]; [reflexivity|].
  destruct c as [[|] [|] [|] [|] [|] [|] [|] [|]];
    try reflexivity; destruct braw_blocks; cbn in Hgate; discriminate || reflexivity.
Qed.

Local Lemma fence_block_canonical_raw :
  forall format content,
    cb_ok (CRaw format content) = true ->
    fence_block (Fence "`"%char 3 (String "="%char format)) content
      = cb_ast (CRaw format content).
Proof.
  intros format content H. cbn [cb_ok] in H.
  apply andb_true_iff in H as [Hgate _].
  unfold fence_block, cb_ast. cbn [f_info]. rewrite Hgate. reflexivity.
Qed.

(* The AST side, likewise. *)
Local Lemma cb_ast_list_uniform :
  forall k sp items,
    items_parse items ->
    cb_ast (CList k sp items)
    = mk (ck_block k sp (map (fun L => parse_lines L (PPara []))
                           (map item_lines items))).
Proof.
  intros k sp items Hitems. rewrite cb_ast_list, map_map, Hitems. reflexivity.
Qed.

Local Lemma parse_canonical_list_end :
  forall k sp items,
    cb_ok (CList k sp items) = true ->
    items_parse items ->
    parse_lines (cb_lines (CList k sp items)) (PPara [])
    = [cb_ast (CList k sp items)].
Proof.
  intros k sp items Hok Hitems.
  destruct (cb_ok_list_parts k sp items Hok) as (Hne & Hckok & Hitemok & Hsp).
  rewrite cb_lines_list, (cb_ast_list_uniform k sp items Hitems).
  rewrite (ck_uniformity k sp (map item_lines items) Hne Hckok Hitemok).
  rewrite Hsp. reflexivity.
Qed.

(* The line that ends a list has to be one the parser routes out of the
   list rather than into the current item: nonblank (a blank only records
   a gap), not a sibling marker, and not indented.  A canonical non-list
   block's first line is all three. *)
Local Lemma parse_canonical_list_then_nonlist :
  forall k sp items next tail,
    cb_ok (CList k sp items) = true ->
    items_parse items ->
    is_clist next = false -> cb_ok next = true ->
    parse_lines
      (cb_lines (CList k sp items) ++ EmptyString :: cb_lines next ++ tail)%list
      (PPara []) =
    (cb_ast (CList k sp items) ::
      parse_lines (cb_lines next ++ tail)%list (PPara []))%list.
Proof.
  intros k sp items next tail Hok Hitems Hnonlist Hnextok.
  destruct (cb_ok_list_parts k sp items Hok) as (Hne & Hckok & Hitemok & Hsp).
  destruct (nonlist_cblock_first next Hnonlist Hnextok)
    as [first [more [Hshape Hnotlist]]].
  pose proof (cb_lines_first_line_ok next first more
                Hnonlist Hnextok Hshape) as Hline.
  rewrite Hshape. cbn [app].
  rewrite cb_lines_list, (cb_ast_list_uniform k sp items Hitems).
  rewrite (ck_uniformity_tail k sp (map item_lines items) first (more ++ tail)
             Hne Hckok Hitemok
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
Local Lemma parse_ckey_open :
  forall label ls, bkeyed = true -> ckey_label_ok label = true ->
    parse_lines ((ci_line [label] ++ ":") :: ls) (PPara [])
    = parse_lines ls
        (PKey (open_extent (ci_line [label] ++ ":") 0)
           (ci_line [label]) (ci_line [label] ++ ":") (PPara [])).
Proof.
  intros label ls Hkeys Hlabel.
  destruct (ckey_label_ok_parts label Hlabel) as (_ & Hline & Htext & _ & Hsplit).
  cbn [parse_lines]. rewrite (step_idle _ _ Htext eq_refl).
  cbn [open_kind]. unfold open_text.
  rewrite (line_ok_no_leading_ws _ Hline), Hkeys, Hsplit. reflexivity.
Qed.

Local Lemma key_close_canonical :
  forall label b bs, ckey_label_ok label = true ->
    key_close (ci_line [label]) (ci_line [label] ++ ":") (b :: bs)
    = mk (Ext_keyed [ci_ast label] b) :: bs.
Proof.
  intros label b bs H.
  destruct (ckey_label_ok_parts label H) as (Hcis & _ & _ & Hstrip & _).
  cbn [key_close]. rewrite para_inlines_one, Hstrip.
  rewrite (parse_inline_line_ci _ Hcis). reflexivity.
Qed.

Local Lemma parse_cblock :
  forall cb,
    (forall next tail,
       cb_pair_ok cb next = true ->
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
                  cb_pair_ok cb next = true ->
                  cb_ok next = true -> cb_ok cb = true ->
                  parse_lines
                    (cb_lines cb ++ EmptyString :: cb_lines next ++ tail)%list
                    (PPara []) =
                  cb_ast cb :: parse_lines (cb_lines next ++ tail)%list (PPara []))
               /\ (cb_ok cb = true ->
                   parse_lines (cb_lines cb) (PPara []) = [cb_ast cb]))
            (fun cbs =>
               cb_pairs_ok cbs = true ->
               forallb cb_ok cbs = true ->
               parse_lines (sep_lines (map cb_lines cbs)) (PPara [])
               = map cb_ast cbs)
            (fun items =>
               forallb cb_pairs_ok items = true ->
               forallb (fun it => (nonempty it && forallb cb_ok it)%bool) items = true ->
               items_parse items)
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* paragraph: the line-level argument, then `cb_ast_para_of_lines`
       identifies what the parser built with what `cb_ast` names.
       `destruct ... eqn:E` abstracts it in `Hast` too, which is why the
       branches close on `Hast` and not on `reflexivity`. *)
    intros lss. split; [intros next tail _ _ H | intros H];
      pose proof (cb_ast_para_of_lines lss H) as Hast;
      rewrite cb_ok_para in H;
      apply andb_true_iff in H as [Hp _];
      cbn [cb_lines];
      destruct (map ci_line lss) as [|a ls'] eqn:E; try discriminate;
      apply para_ok_parts in Hp as (Htext & Hlok & _ & Hint & Hkey);
      pose proof (forallb_line_ok_nonblank _ Hlok) as Hnb;
      cbn [forallb] in Hnb; apply andb_true_iff in Hnb as [_ Hnb'];
      cbn [forallb] in Hint; apply andb_true_iff in Hint as [Hihd Hint'];
      apply negb_true_iff in Hihd;
      destruct (rev_cons_shape a ls') as [c [cur' Erev]].
    + rewrite parse_lines_para_seed by assumption.
      rewrite (forallb_line_ok_map_drop_leading_ws _ Hlok).
      rewrite Erev, remember_lines_cons, parse_lines_blank_cons by reflexivity.
      rewrite <- remember_lines_cons, line_texts_rev_remember_lines.
      rewrite <- Erev, rev_involutive, Hast. reflexivity.
    + rewrite <- (app_nil_r (a :: ls')) at 1.
      rewrite parse_lines_para_seed by assumption.
      rewrite (forallb_line_ok_map_drop_leading_ws _ Hlok).
      rewrite Erev, remember_lines_cons, parse_lines_nil_cons.
      rewrite <- remember_lines_cons, line_texts_rev_remember_lines.
      rewrite <- Erev, rev_involutive, Hast.
      reflexivity.
  - (* thematic break *)
    split; [intros next tail _ _ H | intros H]; cbn [cb_lines app].
    + rewrite parse_lines_thematic_nil by apply classify_canonical_thematic.
      rewrite parse_lines_blank_nil by reflexivity. reflexivity.
    + rewrite parse_lines_thematic_nil by apply classify_canonical_thematic.
      reflexivity.
  - (* code block *)
    intros info content. split; [intros next tail _ _ H | intros H];
      pose proof (fence_block_canonical_code info content H) as Hast;
      cbn [cb_ok] in H; apply andb_true_iff in H as [H _];
      apply code_ok_parts in H as (Hinfo & _ & Hnc); cbn [cb_lines app].
    + rewrite (parse_lines_fence_open _ _ _
                 (classify_backtick_fence info Hinfo)).
      rewrite <- app_assoc.
      rewrite parse_lines_fence_seed by first [exact Hnc | reflexivity].
      rewrite indent_of_code_open, map_drop_ws_upto_0.
      rewrite app_nil_r. cbn [app].
      rewrite parse_lines_fence_close by apply fence_close_canonical.
      rewrite line_texts_rev_remember_lines, rev_involutive, Hast.
      rewrite parse_lines_blank_nil by reflexivity. reflexivity.
    + rewrite (parse_lines_fence_open _ _ _
                 (classify_backtick_fence info Hinfo)).
      rewrite parse_lines_fence_seed by first [exact Hnc | reflexivity].
      rewrite indent_of_code_open, map_drop_ws_upto_0.
      rewrite app_nil_r.
      rewrite parse_lines_fence_close by apply fence_close_canonical.
      rewrite line_texts_rev_remember_lines, rev_involutive, Hast. reflexivity.
  - (* raw block *)
    intros format content. split; [intros next tail _ _ H | intros H];
      pose proof (fence_block_canonical_raw format content H) as Hast;
      cbn [cb_ok] in H; apply andb_true_iff in H as [_ H];
      unfold raw_ok in H;
      apply code_ok_parts in H as (Hinfo & _ & Hnc); cbn [cb_lines app].
    + rewrite (parse_lines_fence_open _ _ _
                 (classify_backtick_fence _ Hinfo)).
      rewrite <- app_assoc.
      rewrite parse_lines_fence_seed by first [exact Hnc | reflexivity].
      rewrite indent_of_code_open, map_drop_ws_upto_0.
      rewrite app_nil_r. cbn [app].
      rewrite parse_lines_fence_close by apply fence_close_canonical.
      rewrite line_texts_rev_remember_lines, rev_involutive, Hast.
      rewrite parse_lines_blank_nil by reflexivity. reflexivity.
    + rewrite (parse_lines_fence_open _ _ _
                 (classify_backtick_fence _ Hinfo)).
      rewrite parse_lines_fence_seed by first [exact Hnc | reflexivity].
      rewrite indent_of_code_open, map_drop_ws_upto_0.
      rewrite app_nil_r.
      rewrite parse_lines_fence_close by apply fence_close_canonical.
      rewrite line_texts_rev_remember_lines, rev_involutive, Hast. reflexivity.
  - (* heading: open on the first line, accumulate the rest, close on the
       blank line or at end of input.  No first-line classification
       condition: the hashes make every rendered line a heading line. *)
    intros lvl ls. split; [intros next tail _ _ H | intros H];
      pose proof (cb_ast_heading_of_lines lvl ls H) as Hast;
      rewrite cb_ok_heading in H;
      apply andb_true_iff in H as [Hh _];
      apply heading_ok_parts in Hh as (Hlvl & Hne & Hlok & Hcontinues & _);
      cbn [cb_lines];
      destruct (map ci_line ls) as [|a ls'] eqn:E; [congruence| |congruence|];
      assert (Htail :
        (bheading_continues || Nat.eqb (List.length ls') 0)%bool = true)
        by (destruct bheading_continues; [reflexivity|];
            cbn in Hcontinues |- *;
            apply Nat.eqb_eq in Hcontinues; apply Nat.eqb_eq;
            inversion Hcontinues; reflexivity);
      pose proof (forallb_line_ok_nonblank _ Hlok) as Hnb;
      cbn [forallb] in Hnb; apply andb_true_iff in Hnb as [Hna Hnb'];
      unfold nonblank in Hna; apply negb_true_iff in Hna;
      cbn [forallb] in Hlok; apply andb_true_iff in Hlok as [Hlok_a Hlok_ls'];
      cbn [map app];
      rewrite (parse_lines_heading_open _ _ _ a
                 (classify_canonical_heading lvl a Hlvl));
      replace (push_text a []) with [remember_line a]
        by (unfold push_text; rewrite Hna;
            rewrite (line_ok_no_leading_ws _ Hlok_a); reflexivity).
    + rewrite <- Hast.
      rewrite parse_lines_heading_seed_ok by first [assumption|reflexivity].
      rewrite (forallb_line_ok_map_drop_leading_ws _ Hlok_ls').
      rewrite parse_lines_heading_close by reflexivity.
      unfold heading_block. sem_para. rewrite line_texts_rev_remember_snoc.
      reflexivity.
    + rewrite <- Hast.
      rewrite <- (app_nil_r (map (heading_line lvl) ls')).
      rewrite parse_lines_heading_seed_ok by first [assumption|reflexivity].
      rewrite (forallb_line_ok_map_drop_leading_ws _ Hlok_ls').
      rewrite parse_lines_nil. cbn [finish]; nopos.
      unfold heading_block. sem_para. rewrite line_texts_rev_remember_snoc.
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
      assert (Hadj : cb_pairs_ok inner = true).
      { rewrite cb_ok_quote in H.
        apply andb_true_iff in H as [_ Hadj]. exact Hadj. }
      pose proof (IH Hadj Hok) as IHinner.
      rewrite cb_lines_quote, cb_ast_quote, E.
      unfold quote_line, quote_open.
      rewrite parse_lines_quote, <- E, IHinner. reflexivity.
    + intros H. destruct (Hsplit H) as [l [L [E Hok]]].
      assert (Hadj : cb_pairs_ok inner = true).
      { rewrite cb_ok_quote in H.
        apply andb_true_iff in H as [_ Hadj]. exact Hadj. }
      pose proof (IH Hadj Hok) as IHinner.
      rewrite cb_lines_quote, cb_ast_quote, E.
      unfold quote_line, quote_open.
      rewrite quote_uniformity, <- E, IHinner. reflexivity.
  - (* div: Parser.div_uniformity, with cb_ok supplying its side
       condition.  Simpler than the quote case in one way (the fences
       make the rendering nonempty on their own, so there is no
       `Hsplit`), and it needs no `cb_pairs_ok` for its own sake, only
       to drive the contents' induction hypothesis. *)
    intros inner IH.
    assert (Hparts : cb_ok (CDiv inner) = true ->
                     bdivs = true
                     /\ parse_lines (sep_lines (map cb_lines inner)) (PPara [])
                     = map cb_ast inner
                     /\ div_content_ok (sep_lines (map cb_lines inner)) = true).
    { intros H. rewrite cb_ok_div in H.
      apply andb_true_iff in H as [H Hcontent].
      apply andb_true_iff in H as [H Hadj].
      apply andb_true_iff in H as [Hdivs Hok].
      repeat split; [exact Hdivs | exact (IH Hadj Hok) | exact Hcontent]. }
    split.
    + intros next tail _ _ H.
      destruct (Hparts H) as [Hdivs [IHinner Hcontent]].
      rewrite cb_lines_div, cb_ast_div. cbn [app]. rewrite <- app_assoc.
      cbn [app].
      rewrite (div_uniformity_tail _ _ Hdivs Hcontent), IHinner. reflexivity.
    + intros H. destruct (Hparts H) as [Hdivs [IHinner Hcontent]].
      rewrite cb_lines_div, cb_ast_div.
      rewrite (div_uniformity _ Hdivs Hcontent), IHinner. reflexivity.
  - (* list: every item's contents come from the induction hypothesis,
       and Parser.ck_uniformity assembles them *)
    intros k sp items IH.
    assert (Hparse : cb_ok (CList k sp items) = true -> items_parse items).
    { intros H. rewrite cb_ok_list in H.
      repeat rewrite andb_true_iff in H.
      destruct H as [[[[[[_ Hitems] _] _] Hadj] _] _]. exact (IH Hadj Hitems). }
    split.
    + intros next tail Hboundary Hnext Hlist.
      apply parse_canonical_list_then_nonlist; try assumption.
      * exact (Hparse Hlist).
      * exact (cb_pair_ok_nonlist (CList k sp items) next eq_refl Hboundary).
    + intros H. exact (parse_canonical_list_end k sp items H (Hparse H)).
  - (* reference definition: the line opens the state, and the blank line
       or the end of input closes it *)
    intros label dest. split; [intros next tail _ _ H | intros H];
      cbn [cb_lines app];
      rewrite (parse_lines_ref_open _ _ _ _ (ref_ok_classify _ _ H)).
    + rewrite (parse_lines_ref_blank EmptyString _ _ _ _ _
                 (classify_blank EmptyString eq_refl)).
      reflexivity.
    + reflexivity.
  - (* table: the rows are the whole of it.  With a next block the blank
       does not close the table -- a caption may still follow -- so the
       close is the next block's own first line, and `cb_pair_ok` is what
       says that line does not caption instead. *)
    intros rows.
    assert (Hparts : cb_ok (CTable rows) = true ->
                     btables = true /\ nonempty rows = true
                     /\ forallb ctrow_ok rows = true).
    { intros H. rewrite cb_ok_table in H.
      apply andb_true_iff in H as [Htn Hrows].
      apply andb_true_iff in Htn as [Htables Hne].
      repeat split; assumption. }
    split.
    + intros next tail Hpair Hnext H.
      destruct (Hparts H) as [Htables [Hne Hrows]].
      destruct (cb_lines next) as [|a ls] eqn:Enext.
      { exfalso. pose proof (cb_ok_lines_ok next Hnext) as Hl.
        rewrite Enext in Hl. discriminate Hl. }
      destruct (cb_pair_ok_closes (CTable rows) next a ls eq_refl Hpair Enext)
        as [Hblank Hcap].
      rewrite cb_lines_table.
      match goal with
      | |- context [parse_lines (flat_map ctrow_lines rows ++ ?rest) (PPara [])] =>
          destruct (parse_ctable rows rest Htables Hne Hrows) as [range Hpc]
      end.
      rewrite Hpc.
      rewrite (parse_lines_table_blank EmptyString _ _ _ _ (eq_refl true)).
      cbn [app].
      rewrite (parse_lines_table_close _ _ _ _ _ Hcap Hblank).
      rewrite (table_block_ctable rows (TAfterBlank []) Hrows (eq_refl None)).
      reflexivity.
    + intros H. destruct (Hparts H) as [Htables [Hne Hrows]].
      rewrite cb_lines_table, <- (app_nil_r (flat_map ctrow_lines rows)).
      destruct (parse_ctable rows [] Htables Hne Hrows) as [range Hpc].
      rewrite Hpc, parse_lines_table_eof.
      rewrite (table_block_ctable rows (TOpen []) Hrows (eq_refl None)). reflexivity.
  - (* explicit id: the spec is complete on its own line, so it resolves
       against the wrapped block's first line and rides on whatever that
       block emits (`Parser.attr_uniformity`).  Nothing else about the
       run changes, which is why the case needs no line-shape reasoning
       of its own beyond `cb_lines_first_ready`. *)
    intros id inner [IHtail IHend].
    assert (Hparts : cb_ok (CId id inner) = true ->
              battrs = true /\ explicit_id_ok id = true
              /\ is_cid inner = false /\ cb_ok inner = true).
    { intros H. rewrite cb_ok_id in H.
      apply andb_true_iff in H as [H Hin].
      apply andb_true_iff in H as [H Hnid].
      apply andb_true_iff in H as [Ha Hid].
      apply negb_true_iff in Hnid. repeat split; assumption. }
    split.
    + intros next tail Hpair Hnext H.
      destruct (Hparts H) as (Hattrs & Hid & Hnid & Hinner).
      destruct (cb_lines inner) as [|a more] eqn:El.
      { exfalso. pose proof (cb_ok_lines_ok inner Hinner) as Hl.
        rewrite El in Hl. discriminate Hl. }
      cbn [cb_lines app]. rewrite El. cbn [app].
      rewrite (attr_uniformity ("{#" ++ id ++ "}") (AP ADone [] "" [("id", id)])
                 (a :: more ++ "" :: cb_lines next ++ tail)%list Hattrs
                 (classify_canonical_id id Hid) eq_refl
                 (cb_lines_first_ready inner a more Hnid Hinner El)).
      cbn [ap_attrs]. rewrite Attr.merge_one.
      cbn [app] in IHtail. rewrite (IHtail next tail Hpair Hnext Hinner).
      apply decorate_head_cb_ast, Hnid.
    + intros H.
      destruct (Hparts H) as (Hattrs & Hid & Hnid & Hinner).
      destruct (cb_lines inner) as [|a more] eqn:El.
      { exfalso. pose proof (cb_ok_lines_ok inner Hinner) as Hl.
        rewrite El in Hl. discriminate Hl. }
      cbn [cb_lines]. rewrite El.
      rewrite (attr_uniformity ("{#" ++ id ++ "}") (AP ADone [] "" [("id", id)])
                 (a :: more)%list Hattrs
                 (classify_canonical_id id Hid) eq_refl
                 (cb_lines_first_ready inner a more Hnid Hinner El)).
      cbn [ap_attrs]. rewrite Attr.merge_one.
      rewrite (IHend Hinner).
      apply decorate_head_cb_ast, Hnid.
  - (* key: the child prefix passes the wrapper until its first output. *)
    intros label inner [IHtail IHend]. split.
    + intros next tail Hpair Hnext H.
      destruct (cb_ok_key_parts label inner H) as (Hkeys & Hl & Hi & Hcontent).
      cbn [cb_lines app]. rewrite (parse_ckey_open _ _ Hkeys Hl).
      rewrite (parse_lines_key_content _ _ _ _ _ _ Hcontent).
      rewrite (IHtail next tail Hpair Hnext Hi).
      apply key_close_canonical, Hl.
    + intros H.
      destruct (cb_ok_key_parts label inner H) as (Hkeys & Hl & Hi & Hcontent).
      cbn [cb_lines]. rewrite (parse_ckey_open _ _ Hkeys Hl).
      rewrite <- (app_nil_r (cb_lines inner)).
      rewrite (parse_lines_key_content _ _ _ _ _ _ Hcontent), app_nil_r, (IHend Hi).
      apply key_close_canonical, Hl.
  - (* the list side: nothing to parse *)
    intros _ _. reflexivity.
  - (* the list side: one block, then the rest after a blank line *)
    intros c rest Hc Hrest Hadj H.
    cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
    destruct Hc as [Hc1 Hc2].
    destruct rest as [|c2 rest'].
    + cbn [map sep_lines]. rewrite (Hc2 H1). reflexivity.
    + pose proof H2 as Hrestallok.
      change (cb_pair_ok c c2 && cb_pairs_ok (c2 :: rest') = true) in Hadj.
      apply andb_true_iff in Hadj as [Hboundary Hrestall].
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

Local Lemma parse_sep :
  forall cbs, cb_pairs_ok cbs = true -> forallb cb_ok cbs = true ->
  parse_lines (sep_lines (map cb_lines cbs)) (PPara []) = map cb_ast cbs.
Proof.
  induction cbs as [|cb rest IH]; intros Hadj H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hcb Hrest].
  destruct (parse_cblock cb) as [Hc1 Hc2].
  destruct rest as [|cb2 rest'].
  - cbn [map sep_lines]. rewrite (Hc2 Hcb). reflexivity.
  - pose proof Hrest as Hrestallok.
    change (cb_pair_ok cb cb2 && cb_pairs_ok (cb2 :: rest') = true) in Hadj.
    apply andb_true_iff in Hadj as [Hboundary Hrestall].
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

(* The renderer emits exactly a cblock's canonical lines.  The third
   induction predicate handles a list's list of item lists. *)
Local Lemma render_cb_lines :
  forall cb, cb_ok cb = true ->
  render_node_lines (cb_ast cb) = cb_lines cb.
Proof.
  refine (cblock_ind2
            (fun cb => cb_ok cb = true ->
                       render_node_lines (cb_ast cb) = cb_lines cb)
            (fun cbs => forallb cb_ok cbs = true ->
                        render_blocks_lines (map cb_ast cbs)
                        = map cb_lines cbs)
            (fun items => forallb (forallb cb_ok) items = true ->
                          map (fun it => sep_lines (render_blocks_lines
                                                      (map cb_ast it))) items
                          = map item_lines items)
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* paragraph: `inline_lines_ci` is the whole case.  The destruct is
       only there to reach `para_ok_parts`, which wants a cons. *)
    intros ls H. rewrite cb_ok_para in H. apply andb_true_iff in H as [Hp Hc].
    destruct (map ci_line ls) as [|a ls'] eqn:E; [discriminate|].
    apply para_ok_parts in Hp as (_ & Hlok & _).
    rewrite <- E in Hlok.
    cbn [render_node_lines id_spec_lines node_attrs alist_lookup app
         cb_ast cb_lines node_contents mk render_block_lines].
    apply inline_lines_ci.
    + exact Hc.
    + apply cis_nonempty_of_lines. exact Hlok.
    + destruct ls; [discriminate E | reflexivity].
  - reflexivity.
  - (* code block *)
    intros info content H.
    cbn [cb_ok] in H. apply andb_true_iff in H as [H _].
    apply code_ok_parts in H as (_ & Hnl & _).
    cbn [render_node_lines id_spec_lines node_attrs alist_lookup app
         cb_ast cb_lines node_contents mk render_block_lines].
    rewrite split_join_nl by exact Hnl. reflexivity.
  - (* raw block *)
    intros format content H.
    cbn [cb_ok] in H. apply andb_true_iff in H as [_ H].
    unfold raw_ok in H. apply code_ok_parts in H as (_ & Hnl & _).
    cbn [render_node_lines id_spec_lines node_attrs alist_lookup app
         cb_ast cb_lines node_contents mk render_block_lines].
    rewrite split_join_nl by exact Hnl. reflexivity.
  - (* heading: the same inline inversion as a paragraph, prefixed *)
    intros lvl ls H.
    rewrite cb_ok_heading in H. apply andb_true_iff in H as [Hh Hc].
    apply heading_ok_parts in Hh as (_ & Hne & Hlok & _ & _).
    cbn [render_node_lines id_spec_lines node_attrs alist_lookup app
         cb_ast cb_lines node_contents mk render_block_lines].
    f_equal.
    apply inline_lines_ci.
    + exact Hc.
    + apply cis_nonempty_of_lines. exact Hlok.
    + destruct ls; [cbn [map] in Hne; congruence | reflexivity].
  - (* quote: prefix the contents' layout *)
    intros inner IH H.
    rewrite cb_ok_quote in H. apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [_ Hok].
    rewrite cb_ast_quote, render_node_lines_mk.
    rewrite render_block_quote, (IH Hok), cb_lines_quote.
    reflexivity.
  - (* div: same shape as the quote, with fences instead of a prefix *)
    intros inner IH H.
    rewrite cb_ok_div in H. apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [_ Hok].
    rewrite cb_ast_div, render_node_lines_mk.
    rewrite render_block_div.
    fold (render_blocks_lines (map cb_ast inner)).
    rewrite (IH Hok), cb_lines_div.
    reflexivity.
  - intros k sp items IH H.
    rewrite cb_ok_list in H.
    apply andb_true_iff in H as [H Hcont].
    apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [H Hitemok].
    apply andb_true_iff in H as [H Hckok].
    apply andb_true_iff in H as [_ Hitems].
    assert (Hokitems : forallb (forallb cb_ok) items = true).
    { refine (forallb_weaken _ _ _ _ Hitems).
      intros item Hitem. apply andb_true_iff in Hitem as [_ Hitem]. exact Hitem. }
    rewrite cb_ast_list, render_node_lines_mk.
    rewrite (render_ck_list _ _ _
               (ck_render_ok_cb k items Hokitems Hckok Hitemok
                  (IH Hokitems) Hcont)).
    rewrite cb_lines_list, map_map, (IH Hokitems). reflexivity.
  - (* reference definition: one line, and the renderer spells it the same
       way `cb_lines` does *)
    intros label dest _. reflexivity.
  - (* table: `table_lines_ctable` is the case.  The caption is `None`, so
       the renderer's caption line is the empty append. *)
    intros rows H. rewrite cb_ok_table in H.
    apply andb_true_iff in H as [_ Hrows].
    rewrite cb_ast_table, render_node_lines_mk. cbn [render_block_lines].
    rewrite app_nil_r, cb_lines_table.
    apply table_lines_ctable. exact Hrows.
  - (* explicit id: the spec is its own line, and the only attribute the
       renderer spells.  Every wrapped block is `mk`-wrapped, so the set
       `add_attr` builds holds exactly the id. *)
    intros id inner IH H.
    rewrite cb_ok_id in H.
    apply andb_true_iff in H as [Hid Hinner].
    apply andb_true_iff in Hid as [_ Hnid]. apply negb_true_iff in Hnid.
    destruct (cb_ast_mk inner Hnid) as [x Ex].
    specialize (IH Hinner). rewrite Ex, render_node_lines_mk in IH.
    cbn [cb_ast cb_lines]. rewrite Ex, add_attr_mk.
    unfold render_node_lines, id_spec_lines.
    cbn [node_attrs node_contents alist_lookup String.eqb Ascii.eqb app].
    rewrite IH. reflexivity.
  - intros label inner IH H.
    destruct (cb_ok_key_parts label inner H) as (_ & _ & Hi & _).
    change ((String.concat "" [InlineView.inline_text (node_contents (ci_ast label))] ++ ":")
              :: render_node_lines (cb_ast inner) = (ci_line [label] ++ ":") :: cb_lines inner).
    rewrite inline_text_ci_ast, (IH Hi). cbn [String.concat ci_line ci_text].
    rewrite !append_empty_r. reflexivity.
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

(* Rendering a canonical document is the same as joining its cb_lines,
   which is what lets split_render/parse_sep take over. *)
Local Lemma render_djot_cblocks :
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

(** Replacing one block in a canonical document leaves the parse of every
    other block untouched.  The right-hand side names `pre` and `post`
    through the same `map cb_ast` they had before the edit, so "the rest
    of the document is preserved" is the statement rather than a reading
    of it.  Only the new document need be canonical: the block coming out
    is not mentioned.

    An address is not needed either.  Splitting the list is what picks the
    block, so nothing has to connect an AST node to a source span.

    The document here is a `cblock` list and the edit is list surgery, so
    an editor holding one has no reparse to skip: this is the guarantee
    that whoever parses its rendering gets the list back.  An editor
    holding arbitrary source text is the case outside this file.  That
    text need not be in the image of `render_djot`, so the block being
    replaced has no `cb_lines` and the statement below does not apply to
    it.  That case is `Uniformity.reparse_only_new`, stated over line
    lists and needing no canonicality at all. *)
Corollary block_replace :
  forall pre new post,
    cblocks_ok (pre ++ new :: post)%list = true ->
    parse_blocks (render_djot (blocks_of_cblocks (pre ++ new :: post)))
    = (map cb_ast pre ++ cb_ast new :: map cb_ast post)%list.
Proof.
  intros pre new post H.
  rewrite (roundtrip_blocks _ H). unfold blocks_of_cblocks.
  rewrite map_app. reflexivity.
Qed.

(* The obligation the corollary leaves an editor is local: `pre` and
   `post` were already canonical, so `cblocks_ok` reduces to `cb_ok new`
   and the two pairs the new block joins.  Neither is bureaucratic -- a
   list dropped next to a list is the pair `cb_pairs_ok` rejects, and it
   is rejected because the separating blank really does make the parser
   continue the first list as loose (`Render.cb_pairs_ok_pair`). *)

(*
Worked examples
===============

The theorem quantifies over cb_ok cblocks; these check that quotes are
really in that set, and that the rendering is the one a human would
write. *)

Definition quote_example : list cblock :=
  [ CQuote [cpara ["a"]; CThematic]; cpara ["after"] ].

End WithTable.

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

(* A paragraph whose text contains a backslash: the renderer escapes it,
   the parser takes it back. *)
Example escape_roundtrip :
  let cbs := [cpara ["a\b"]] in
  render_djot (blocks_of_cblocks cbs) = "a\\b"
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

Example escaped_punct_is_literal :
  parse_blocks "a\*b" = [mk (Para [mk (Str "a*b")])].
Proof. reflexivity. Qed.

(* The delimiter table claims `*`, so a `Str` containing one renders
   escaped, which is what keeps the text a `Str` on the way back. *)
Example star_escaped_in_str : cb_lines (cpara ["*a*"]) = ["\*a\*"].
Proof. reflexivity. Qed.

(* A multi-line heading renders with the hashes repeated on every line,
   which is what makes it reparse as a continuation of itself. *)
Example heading_example_roundtrip :
  let cbs := [cheading 2 ["a"; "b"]; cpara ["p"]] in
  render_djot (blocks_of_cblocks cbs)
    = ("## a" ++ nl ++ "## b" ++ nl ++ nl ++ "p")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* Headings nest inside quotes with no extra machinery. *)
Example heading_in_quote_roundtrip :
  let cbs := [CQuote [cheading 1 ["h"]; cpara ["t"]]] in
  render_djot (blocks_of_cblocks cbs)
    = ("> # h" ++ nl ++ "> " ++ nl ++ "> t")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* Divs roundtrip, and so do the containers inside them: the whole
   content of Parser.div_uniformity, seen end to end. *)
Example div_roundtrip :
  let cbs := [CDiv [cpara ["a"]; cpara ["b"]]] in
  render_djot (blocks_of_cblocks cbs)
    = (":::" ++ nl ++ "a" ++ nl ++ nl ++ "b" ++ nl ++ ":::")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* An empty div is renderable: `cb_ok` has no nonempty obligation for
   `CDiv`, because djot.js accepts `:::` / `:::`. *)
Example empty_div_roundtrip :
  let cbs := [CDiv []] in
  render_djot (blocks_of_cblocks cbs) = (":::" ++ nl ++ ":::")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* A quote inside a div: the two containers' rules do not interact, which
   is the uniformity claim at its narrowest. *)
Example quote_in_div_roundtrip :
  let cbs := [CDiv [CQuote [cpara ["q"]]]] in
  render_djot (blocks_of_cblocks cbs)
    = (":::" ++ nl ++ "> q" ++ nl ++ ":::")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* Literal colons are escaped, so text that resembles a div fence no
   longer closes the container and belongs to the canonical fragment. *)
Example div_containing_literal_fence_roundtrip :
  let cbs := [CDiv [cpara [":::"]]] in
  cblocks_ok cbs = true
  /\ render_djot (blocks_of_cblocks cbs)
    = (":::" ++ nl ++ "\:\:\:" ++ nl ++ ":::")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof.
  split; [reflexivity|].
  split; [reflexivity|apply roundtrip_blocks; reflexivity].
Qed.

(* Nesting roundtrips too, with no extra hypotheses. *)
Example nested_quote_roundtrip :
  let cbs := [CQuote [CQuote [cpara ["deep"]]]] in
  render_djot (blocks_of_cblocks cbs) = "> > deep"
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

Example tight_list_roundtrip :
  let cbs :=
    [CList LKBullet Tight [[cpara ["a"]]; [cpara ["b"]]]; cpara ["after"]] in
  render_djot (blocks_of_cblocks cbs)
    = ("- a" ++ nl ++ "- b" ++ nl ++ nl ++ "after")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

Example loose_list_roundtrip :
  let cbs := [CList LKBullet Loose [[cpara ["a"]]; [cpara ["b"]]]] in
  render_djot (blocks_of_cblocks cbs) = ("- a" ++ nl ++ nl ++ "- b")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* The three ordered numbering schemes roundtrip, at both cases.  Each
   rendering was checked against djot.js, which reads them back as
   `<ol start="2" type="i">`, `<ol type="a">` and `<ol start="4"
   type="I">` respectively. *)
Example roman_list_roundtrip :
  let cbs := [CList (LKRoman false RightPeriod 2) Tight
                [[cpara ["a"]]; [cpara ["b"]]; [cpara ["c"]]]] in
  render_djot (blocks_of_cblocks cbs)
    = ("ii. a" ++ nl ++ "iii. b" ++ nl ++ "iv. c")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

Example alpha_list_roundtrip :
  let cbs := [CList (LKAlpha false RightParen 1) Tight
                [[cpara ["x"]]; [cpara ["y"]]]] in
  render_djot (blocks_of_cblocks cbs) = ("a) x" ++ nl ++ "b) y")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

Example roman_upper_list_roundtrip :
  let cbs := [CList (LKRoman true RightPeriod 4) Tight
                [[cpara ["p"]]; [cpara ["q"]]]] in
  render_djot (blocks_of_cblocks cbs) = ("IV. p" ++ nl ++ "V. q")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* Roman from 1 is in: its first marker `i.` names two styles, but roman
   is the one at the *head*, so a one-item list closes correctly with no
   narrowing and a longer one is narrowed to roman by `ii.`. *)
Example roman_from_one_roundtrip :
  let cbs := [CList (LKRoman false RightPeriod 1) Tight
                [[cpara ["a"]]; [cpara ["b"]]]] in
  render_djot (blocks_of_cblocks cbs) = ("i. a" ++ nl ++ "ii. b")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* `c` and `d` are both roman digits, so `c.` / `d.` leaves the candidate
   set where it was and only `e.` settles it; same for `l`, `m`, `n`.
   With these, every ordered start that can round-trip does. *)
Example alpha_two_roman_digits_roundtrip :
  let from_c := [CList (LKAlpha false RightPeriod 3) Tight
                   [[cpara ["a"]]; [cpara ["b"]]; [cpara ["c"]]]] in
  let from_l := [CList (LKAlpha false RightPeriod 12) Tight
                   [[cpara ["a"]]; [cpara ["b"]]; [cpara ["c"]]]] in
  render_djot (blocks_of_cblocks from_c)
    = ("c. a" ++ nl ++ "d. b" ++ nl ++ "e. c")%string
  /\ render_djot (blocks_of_cblocks from_l)
    = ("l. a" ++ nl ++ "m. b" ++ nl ++ "n. c")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks from_c)) = blocks_of_cblocks from_c
  /\ parse_blocks (render_djot (blocks_of_cblocks from_l)) = blocks_of_cblocks from_l.
Proof.
  repeat split; try reflexivity; apply roundtrip_blocks; reflexivity.
Qed.

(* Excluded and impossible: each of these three cannot round-trip at
   all, so no theorem will ever admit them.  An alpha list from `i` at
   length 1 renders `i. a`, which is also what roman from 1 renders: two
   canonical ASTs, one source, so at most one can round-trip, and it is
   the roman one.  At length 2 the letters `c` and `d` are both roman
   digits, so `c. / d.` is still unresolved after its second marker and
   reads as roman from 100.  The last is the wrap: `z` leaves no 27th
   letter. *)
Example excluded_ordered_starts :
  (cb_ok (CList (LKAlpha false RightPeriod 9) Tight [[cpara ["a"]]]),
   cb_ok (CList (LKAlpha false RightPeriod 3) Tight
            [[cpara ["a"]]; [cpara ["b"]]]),
   cb_ok (CList (LKAlpha false RightPeriod 26) Tight
            [[cpara ["a"]]; [cpara ["b"]]]))
  = (false, false, false).
Proof. reflexivity. Qed.

(* Lists nest, in both directions: through a quote, and directly inside
   another list's item. *)
Example list_in_quote_roundtrip :
  let cbs := [CQuote [CList LKBullet Tight [[cpara ["a"]]; [cpara ["b"]]]]] in
  parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. apply roundtrip_blocks; reflexivity. Qed.

Example nested_list_roundtrip :
  let cbs := [CList LKBullet Tight [[CList LKBullet Tight [[cpara ["b"]]; [cpara ["c"]]]]]] in
  render_djot (blocks_of_cblocks cbs) = ("- - b" ++ nl ++ "  - c")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* The total source renderer also covers empty task items, which sit outside
   [cblock]'s nonempty-item canonical fragment. *)
Example task_list_source_render_roundtrip :
  let b := TaskList Tight
             [(Incomplete, [mk (Para [mk (Str "a")])]);
              (Complete, []); (Complete, [mk (Para [mk (Str "b")])])] in
  render_block_lines b
    = ["- [ ] a"; "- [x]"; "- [x] b"]
  /\ parse_blocks (render_djot [mk b]) = [mk b].
Proof. split; reflexivity. Qed.

(* Inside the canonical fragment, task lists use the ordinary [CList] case:
   [LKTask] carries source-order statuses and [ck_ok] ties them to the item
   count, so the public theorem needs no task-specific branch. *)
Example canonical_task_list_roundtrip :
  let cbs :=
    [CList (LKTask [Incomplete; Complete]) Tight
       [[cpara ["a"; "a2"]]; [cpara ["b"]]]] in
  render_djot (blocks_of_cblocks cbs)
    = ("- [ ] a" ++ nl ++ "      a2" ++ nl ++ "- [x] b")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity|apply roundtrip_blocks; reflexivity]. Qed.

(* A div's closing line arms the enclosing list, so an item that ends
   with one hands a gap to the next marker and the list comes back loose.
   `- ::: / a / ::: / - t` is the shape, and `Tight` is unspellable for
   it, correctly, since the parser cannot produce it.

   The second half is the coverage this costs (the residue named in
   `.project/djotjs-divergences.md`): `item_ok` asks the gap of every
   item, including the last, where nothing follows to spend it.  So the
   two below are rejected although their renderings do round-trip.
   Lifting it means carrying the gap through `list_loose_of` as a fold
   rather than an `existsb`; this example is the boundary, and its
   deletion is the confirmation that the fix was real. *)
Example div_ending_item_excluded :
  let tight_last := [CList LKBullet Tight [[CDiv [cpara ["a"]]]]] in
  let loose_mid :=
    [CList LKBullet Loose [[CDiv [cpara ["a"]]]; [cpara ["t"]]]] in
  (cblocks_ok tight_last, cblocks_ok loose_mid) = (false, false)
  /\ parse_blocks (render_djot (blocks_of_cblocks tight_last))
     = blocks_of_cblocks tight_last.
Proof. split; reflexivity. Qed.

(* And the one it excludes for cause: as `Tight` this AST is unreachable,
   because the closer arms the list before the next marker arrives. *)
Example div_then_item_is_loose :
  parse_blocks ("- :::" ++ nl ++ "  a" ++ nl ++ "  :::" ++ nl ++ "- t")
  = [mk (BulletList Loose
           [[mk (Div [mk (Para [mk (Str "a")])])]; [mk (Para [mk (Str "t")])]])].
Proof. reflexivity. Qed.

(* A nested list after a paragraph in the same item: the blank the inner
   list needs does not loosen the outer one, which is the rule
   `lines_loose` encodes and `item_forces_loose` mirrors. *)
Example nested_list_after_para_roundtrip :
  let cbs := [CList LKBullet Tight [[cpara ["a"]; CList LKBullet Tight [[cpara ["b"]]]]]] in
  parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. apply roundtrip_blocks; reflexivity. Qed.

(*
Tables
------

The header's separator is the only line a table's AST does not record
cell-for-cell, and `ctrow_ok`'s one-alignment-per-cell condition is what
lets the renderer put it back.
*)

Example table_roundtrip :
  let cbs := [CTable [CTHead [AlignRight; AlignDefault] [[CIStr "h"]; [CIStr "i"]];
                      CTBody [[CIStr "b"]; [CIStr "c"]]];
              cpara ["p"]] in
  render_djot (blocks_of_cblocks cbs)
    = ("| h | i |" ++ nl ++ "|--:|---|" ++ nl ++ "| b | c |" ++ nl ++ nl ++ "p")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* An empty cell renders as the two spaces the padding supplies, and
   `parse_inline_line ""` gives the empty inline list back. *)
Example empty_cell_roundtrip :
  let cbs := [CTable [CTBody [[]]]] in
  render_djot (blocks_of_cblocks cbs) = "|  |"
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

Example table_in_quote_roundtrip :
  let cbs := [CQuote [CTable [CTBody [[CIStr "a"]]]]] in
  render_djot (blocks_of_cblocks cbs) = "> | a |"
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* What the per-line test excludes, and what it does not.  A `Str`
   holding a bare bar renders it bare -- `|` is not in `needs_escape` --
   so the row would come back with two cells; the same bar inside a
   verbatim is part of the cell.  A table with no rows renders to no
   lines at all, which `sep_lines` cannot place. *)
Example table_exclusions :
  (cb_ok (CTable [CTBody [[CIStr "a|b"]]]),
   cb_ok (CTable [CTBody [[CIVerb "a|b"]]]),
   cb_ok (CTable []))
  = (false, true, false).
Proof. reflexivity. Qed.

(*
Explicit ids
------------
*)

(* A named block: the spec is its own line, and the id comes back on the
   block the spec names. *)
Example id_para_roundtrip :
  let cbs := [CId "x" (cpara ["a"])] in
  render_djot (blocks_of_cblocks cbs) = ("{#x}" ++ nl ++ "a")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* The spec line separates two lists that would otherwise merge across
   the blank, which is why `cb_pair_ok` reads `is_clist` of its second
   argument and `ends_clist` of its first. *)
Example id_list_after_list_roundtrip :
  let l := CList LKBullet Tight [[cpara ["a"]]] in
  let cbs := [l; CId "x" l] in
  render_djot (blocks_of_cblocks cbs)
    = ("- a" ++ nl ++ nl ++ "{#x}" ++ nl ++ "- a")%string
  /\ parse_blocks (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_blocks; reflexivity]. Qed.

(* And what naming does not buy: a named *list* still closes into the
   next one, since the spec sits in front of it and not behind. *)
Example id_list_before_list_excluded :
  let l := CList LKBullet Tight [[cpara ["a"]]] in
  cb_pairs_ok [CId "x" l; l] = false.
Proof. reflexivity. Qed.

(* Three spellings outside the canonical view.  Two specs in a row have
   one AST between them; an empty id is not an id; and a definition
   item's head is where its term comes from, and `Ast.def_split` drops
   that paragraph's attributes. *)
Example id_exclusions :
  (cb_ok (CId "x" (CId "y" (cpara ["a"]))),
   cb_ok (CId "" (cpara ["a"])),
   cb_ok (CList LKDef Tight [[CId "x" (cpara ["a"])]]))
  = (false, false, false).
Proof. reflexivity. Qed.

(*
Above the block layer
=====================

roundtrip_blocks is about `parse_blocks`, the line fold.  The parser's
actual entry point is `Document.parse_doc`, which runs the whole-document
pass on top.  The primary theorem therefore says render-and-parse
commutes with that pass and retains all of its derived data.  The
erasure theorem `roundtrip_doc` remains useful on the pristine fragment:
cb_ast builds bare `mk` nodes, so no heading carries an explicit id, and
it builds no sections.
*)

(* Back into the family: the document-level roundtrip is a theorem about
   any admissible table, like the block-level one it rests on. *)
Section WithTableDoc.
Context {T : dtable}.
Context {K : bconfig}.

(** The whole-document pass commutes with canonical render-and-parse.
    Unlike [roundtrip_doc] below, this statement retains the derived side
    tables and needs no pristine-input hypothesis: the block roundtrip
    supplies exactly the input on which [doc_pass] is run. *)
Theorem roundtrip_doc_pass :
  forall cbs, cblocks_ok cbs = true ->
  parse_doc (render_djot (blocks_of_cblocks cbs))
  = doc_pass (blocks_of_cblocks cbs).
Proof.
  intros cbs H. unfold parse_doc. f_equal. apply roundtrip_blocks, H.
Qed.

(** The roundtrip at the parser's entry point: render, parse, undo the
    whole-document pass, and you are back where you started.  Explicitly
    named canonical blocks are outside this erasure view: the general
    result for them is [roundtrip_doc_pass] above. *)
Theorem roundtrip_doc :
  forall cbs, cblocks_ok cbs = true ->
  Pristine.of_list (blocks_of_cblocks cbs) = true ->
  Undo.pass (doc_blocks (parse_doc (render_djot (blocks_of_cblocks cbs))))
  = blocks_of_cblocks cbs.
Proof.
  intros cbs H Hpristine. unfold parse_doc.
  rewrite (roundtrip_blocks _ H).
  apply pass_erase, Hpristine.
Qed.

End WithTableDoc.

(* The sections and identifiers the pass adds are exactly what the
   erasure above takes back out. *)
Example heading_roundtrip_doc :
  let cbs := [cheading 1 ["h"]; cpara ["p"]] in
  doc_blocks (parse_doc (render_djot (blocks_of_cblocks cbs)))
  = [ Node NoPos [("id", "h")]
        (Section [ mk (Heading 1 [mk (Str "h")]); mk (Para [mk (Str "p")]) ]) ]
  /\ Undo.pass (doc_blocks (parse_doc (render_djot (blocks_of_cblocks cbs))))
     = blocks_of_cblocks cbs.
Proof. split; [reflexivity | apply roundtrip_doc; reflexivity]. Qed.

(* A four-backtick source fence can contain a line of three backticks.
   The current renderer always chooses three, which closes at that body
   line and changes the parse.  Normalization therefore needs an adaptive
   fence before it can quantify over all parsed documents. *)
Example normalization_code_fence_counterexample :
  parse_blocks (render_djot (parse_blocks "````
```
````"))
  <> parse_blocks "````
```
````".
Proof. discriminate. Qed.
