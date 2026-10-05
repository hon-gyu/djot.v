(* ai-disclosure: autonomous *)

(** * Inline content is a slice of its source line

   `InlineSpans.para_inlines_spans` states the emphasis rules (M2, M3) on
   the text the block layer hands the inline scanner.  This file carries
   them to the document: the located parse reads every inline sequence
   from text that sits, byte for byte, at the position it is recorded at
   in the source.  For a paragraph that is because the block layer cuts
   lines from the left only, so every stored line is a suffix of its
   source line (`Line.classify_sfx`); for a table cell, because the row
   scan records where the cell's text starts.

   The statement is `parse_blocks_located_spans`.  Keys are off: a key
   that gets no block retracts to a paragraph read by the semantic scan,
   whose delimiter nodes carry no position. *)

From Stdlib Require Import String Ascii List Bool Lia Arith Sorted.
From DjotV Require Import Strings Line Ast Attributes InlineTable InlineView
  InlineScan InlineLocated InlineSpans Step Reparse.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

(*
The source, read as windows
===========================

Every source line is one window, whole, starting at its full length.
*)

Fixpoint src_windows_from (k : nat) (src : list string) : list window :=
  match src with
  | [] => []
  | l :: rest => (k, String.length l, l) :: src_windows_from (S k) rest
  end.

Definition src_windows (src : list string) : list window := src_windows_from 0 src.

Definition line_at (src : list string) (k : nat) : string := nth k src EmptyString.

Lemma wfind_src_from : forall src n j,
  wfind (src_windows_from n src) (n + j) =
  option_map (fun l => (String.length l, l)) (nth_error src j).
Proof.
  induction src as [|l src IH]; intros n j; [destruct j; reflexivity|].
  cbn [src_windows_from wfind]. destruct j as [|j].
  - rewrite Nat.add_0_r, Nat.eqb_refl. reflexivity.
  - replace (Nat.eqb n (n + S j)) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (n + S j) with (S n + j) by lia. apply IH.
Qed.

Lemma wfind_src : forall src k,
  k < length src ->
  wfind (src_windows src) k = Some (String.length (line_at src k), line_at src k).
Proof.
  intros src k Hk. unfold src_windows. rewrite <- (Nat.add_0_l k) at 1.
  rewrite wfind_src_from. unfold line_at.
  destruct (nth_error src k) as [l|] eqn:E.
  - rewrite (nth_error_nth src k EmptyString E). reflexivity.
  - apply nth_error_None in E. lia.
Qed.

(*
From content to source
----------------------

A window is embedded in the source when it is a run of its line that
starts where the window says.  Every byte a delimiter clause reads is
inside the window, so the clause reads the same byte in the source.
*)

Definition embeds (W : list window) (src : list string) : Prop :=
  forall k r w, wfind W k = Some (r, w) ->
    k < length src /\ r <= String.length (line_at src k) /\
    exists more, sdrop (String.length (line_at src k) - r) (line_at src k) = (w ++ more)%string.

Lemma sdrop_app : forall n a b,
  n <= String.length a -> sdrop n (a ++ b) = (sdrop n a ++ b)%string.
Proof.
  induction n as [|n IH]; intros a b H; [reflexivity|].
  destruct a as [|c a]; cbn in H; [lia|]. cbn. apply IH. lia.
Qed.

Lemma sdrop_add : forall m n s, sdrop (m + n) s = sdrop n (sdrop m s).
Proof.
  induction m as [|m IH]; intros n s; [reflexivity|].
  destruct s as [|c s]; [destruct n; reflexivity|]. cbn. apply IH.
Qed.

Lemma sfx_embeds : forall W src p s,
  embeds W src -> sfx W p = Some s ->
  exists more, sfx (src_windows src) p = Some (s ++ more)%string.
Proof.
  intros W src [k rem] s HE Hs. unfold sfx in Hs. cbn [spot_line spot_rem] in Hs.
  destruct (wfind W k) as [[r w]|] eqn:Hw; [|discriminate].
  destruct (HE k r w Hw) as (Hk & Hr & more & Hm).
  destruct (Nat.leb (String.length w) r && Nat.leb rem r
            && Nat.leb (r - String.length w) rem)%bool eqn:Hc; [|discriminate].
  apply andb_true_iff in Hc as [Hc H3]. apply andb_true_iff in Hc as [H1 H2].
  apply Nat.leb_le in H1, H2, H3. injection Hs as <-.
  exists more. unfold sfx. cbn [spot_line spot_rem]. rewrite (wfind_src src k Hk).
  set (n := String.length (line_at src k)).
  replace (Nat.leb n n && Nat.leb rem n && Nat.leb (n - n) rem)%bool with true
    by (symmetry; rewrite Nat.leb_refl, Nat.sub_diag;
        replace (Nat.leb rem n) with true by (symmetry; apply Nat.leb_le; lia);
        reflexivity).
  replace (n - rem) with ((n - r) + (r - rem)) by lia.
  rewrite sdrop_add. fold n in Hm. rewrite Hm, sdrop_app by lia. reflexivity.
Qed.

Lemma byte_at_embeds : forall W src p c,
  embeds W src -> byte_at W p = Some c -> byte_at (src_windows src) p = Some c.
Proof.
  intros W src p c HE H. unfold byte_at in *.
  destruct (sfx W p) as [[|c' s]|] eqn:Hs; try discriminate.
  destruct (sfx_embeds W src p (String c' s) HE Hs) as (more & ->). exact H.
Qed.

Lemma dspan_embeds : forall W src k r,
  embeds W src -> dspan_ok W k r -> dspan_ok (src_windows src) k r.
Proof.
  intros W src k r HE (m & (rest & Ho & Hob) & (rest' & Hc & Hcb) & Hlt).
  exists m. split; [|split; [|exact Hlt]].
  - destruct (sfx_embeds W src _ _ HE Ho) as (more & Hm).
    exists (rest ++ more)%string. split.
    + rewrite Hm, append_assoc. reflexivity.
    + intros Hm0. destruct (Hob Hm0) as (c & Hb & Hn).
      exists c. split; [exact (byte_at_embeds W src _ _ HE Hb)|exact Hn].
  - destruct (sfx_embeds W src _ _ HE Hc) as (more & Hm).
    exists (rest' ++ more)%string. split.
    + rewrite Hm, append_assoc. reflexivity.
    + intros Hm0. destruct (Hcb Hm0) as (c & Hb & Hn).
      exists c. split; [exact (byte_at_embeds W src _ _ HE Hb)|exact Hn].
Qed.

Lemma dn_inline_embeds : forall W src,
  embeds W src -> forall x p, dn_inline W p x -> dn_inline (src_windows src) p x.
Proof.
  intros W src HE.
  assert (Hpos : forall p x, dpos_ok W p x -> dpos_ok (src_windows src) p x).
  { intros p x. unfold dpos_ok. destruct (dkind x); [|tauto].
    intros (pr & -> & H). exists pr. split; [reflexivity|].
    exact (dspan_embeds W src _ _ HE H). }
  intros x.
  apply (inline_ind2
    (fun x => forall p, dn_inline W p x -> dn_inline (src_windows src) p x)
    (fun ils => Forall (dn_node W) ils -> Forall (dn_node (src_windows src)) ils));
    intros; cbn [dn_inline] in *;
    try (destruct H0 as [Hp Hc]; split; [exact (Hpos _ _ Hp)|];
         apply dn_children; apply H; apply dn_children; exact Hc);
    try (destruct H as [Hp _]; split; [exact (Hpos _ _ Hp)|exact I]).
  - constructor.
  - inversion H1 as [|? ? Hx Hr]; subst. constructor; [exact (H p Hx)|exact (H0 Hr)].
Qed.

Lemma dn_node_embeds : forall W src n,
  embeds W src -> dn_node W n -> dn_node (src_windows src) n.
Proof. intros W src [p a x] HE H. exact (dn_inline_embeds W src HE x p H). Qed.

(*
Stored lines
============

An accumulator holds its lines newest first, so its line indices
decrease, and each text is a suffix of its line.  `i` bounds them from
above: the line being stepped is `i`, and everything stored before it is
from an earlier line.
*)

Fixpoint acc_ok (src : list string) (i : nat) (cur : list stored_line) : Prop :=
  match cur with
  | [] => True
  | (k, t) :: rest =>
      k < i /\ k < length src /\ is_sfx t (line_at src k) /\ acc_ok src k rest
  end.

Lemma acc_ok_mono : forall src cur i j, i <= j -> acc_ok src i cur -> acc_ok src j cur.
Proof.
  intros src [|[k t] cur] i j Hij H; [exact I|].
  destruct H as (H1 & H2). split; [lia|exact H2].
Qed.

Lemma acc_ok_lt : forall src cur i k t, acc_ok src i cur -> In (k, t) cur ->
  k < i /\ k < length src /\ is_sfx t (line_at src k).
Proof.
  intros src cur. induction cur as [|[k0 t0] cur IH]; intros i k t H Hin; [destruct Hin|].
  destruct H as (H1 & H2 & H3 & H4). destruct Hin as [E|Hin].
  - injection E as <- <-. auto.
  - destruct (IH k0 k t H4 Hin) as (Ha & Hb & Hc). split; [lia|auto].
Qed.

Lemma sorted_snoc : forall l k,
  StronglySorted Nat.lt l -> Forall (fun j => j < k) l ->
  StronglySorted Nat.lt (l ++ [k]).
Proof.
  induction l as [|a l IH]; intros k Hs Hl.
  - repeat constructor.
  - inversion Hs as [|? ? Hs' Ha]; subst. inversion Hl as [|? ? Hak Hl']; subst.
    cbn [app]. constructor; [apply IH; assumption|].
    apply Forall_app. split; [exact Ha|constructor; [exact Hak|constructor]].
Qed.

Lemma acc_ok_sorted : forall src cur i, acc_ok src i cur ->
  StronglySorted Nat.lt (map fst (rev cur)).
Proof.
  intros src cur. induction cur as [|[k t] cur IH]; intros i H; [constructor|].
  destruct H as (_ & _ & _ & H). cbn [rev]. rewrite map_app. cbn [map fst].
  apply sorted_snoc; [exact (IH k H)|].
  apply Forall_forall. intros j Hj. apply in_map_iff in Hj as ([k' t'] & <- & Hin).
  apply in_rev in Hin. exact (proj1 (acc_ok_lt src cur k k' t' H Hin)).
Qed.

Lemma sdrop_prefix : forall p x, sdrop (String.length p) (p ++ x) = x.
Proof. induction p as [|c p IH]; intros x; [reflexivity|exact (IH x)]. Qed.

Lemma wfind_in : forall W k r w, wfind W k = Some (r, w) -> In (k, r, w) W.
Proof.
  induction W as [|[[j r0] w0] W IH]; intros k r w H; [discriminate|].
  cbn [wfind] in H. destruct (Nat.eqb j k) eqn:E.
  - apply Nat.eqb_eq in E. subst j. injection H as <- <-. left. reflexivity.
  - right. exact (IH k r w H).
Qed.

Lemma para_windows_in : forall l k r w, In (k, r, w) (para_windows l) ->
  exists x, In (k, x) l /\ r = String.length x /\ exists more, x = (w ++ more)%string.
Proof.
  induction l as [|[k0 x0] l IH]; intros k r w Hin; [destruct Hin|].
  destruct l as [|y l'].
  - destruct Hin as [E|[]]. injection E as <- <- <-. exists x0.
    split; [left; reflexivity|split; [reflexivity|]].
    destruct (strip_trailing_split x0) as (ws & _ & E). exists ws. exact E.
  - change (para_windows ((k0, x0) :: y :: l'))
      with ((k0, String.length x0, x0) :: para_windows (y :: l')) in Hin.
    destruct Hin as [E|Hin].
    + injection E as <- <- <-. exists x0. split; [left; reflexivity|].
      split; [reflexivity|exists EmptyString; symmetry; apply append_empty_r].
    + destruct (IH k r w Hin) as (x & Hx & Hr & Hm). exists x. split; [right; exact Hx|auto].
Qed.

Lemma para_windows_embeds : forall src i cur,
  acc_ok src i cur -> embeds (para_windows (rev cur)) src.
Proof.
  intros src i cur H k r w Hw.
  destruct (para_windows_in _ _ _ _ (wfind_in _ _ _ _ Hw)) as (x & Hx & -> & more & Em).
  apply in_rev in Hx. destruct (acc_ok_lt src cur i k x H Hx) as (_ & Hk & p & Ep).
  split; [exact Hk|]. rewrite Ep, length_append. split; [lia|].
  exists more. replace (String.length p + String.length x - String.length x)
    with (String.length p) by lia.
  rewrite sdrop_prefix. exact Em.
Qed.

(** A paragraph's lines, stored as the block layer stores them, give
    delimiter spans that hold of the source. *)
Lemma para_spans_src : forall src i cur off,
  acc_ok src i cur ->
  Forall (dn_node (src_windows src)) (@para_inlines_at T located_pos off (rev cur)).
Proof.
  intros src i cur off H.
  pose proof (para_inlines_spans off (rev cur) (acc_ok_sorted src cur i H)) as Hs.
  eapply Forall_impl; [|exact Hs].
  intros n. apply dn_node_embeds, (para_windows_embeds src i cur H).
Qed.

(** One window, a trimmed run of its line: a cell, a callout title. *)
Lemma line_spans_src : forall src k rem s,
  k < length src -> rem <= String.length (line_at src k) ->
  (exists more, sdrop (String.length (line_at src k) - rem) (line_at src k) = (s ++ more)%string) ->
  String.length s <= rem ->
  Forall (dn_node (src_windows src)) (@parse_inline_line_located T located_pos k rem s).
Proof.
  intros src k rem s Hk Hr Hm Hl.
  eapply Forall_impl; [|exact (cell_inlines_spans k rem s Hl)].
  intros n. apply dn_node_embeds. intros j r w Hw. cbn [wfind] in Hw.
  destruct (Nat.eqb k j) eqn:E; [|discriminate].
  apply Nat.eqb_eq in E. subst j. injection Hw as <- <-. auto.
Qed.

(*
Blocks whose inlines are all good
=================================

`inl_all I b`: every inline sequence in `b`, at any depth, satisfies
`I`.  It is only ever built, never computed, so it is an inductive
predicate rather than a traversal.
*)

Inductive inl_all (I : inlines -> Prop) : node block -> Prop :=
  | ia_para p a ils : I ils -> inl_all I (Node p a (Para ils))
  | ia_section p a bs : Forall (inl_all I) bs -> inl_all I (Node p a (Section bs))
  | ia_heading p a lvl ils : I ils -> inl_all I (Node p a (Heading lvl ils))
  | ia_quote p a bs : Forall (inl_all I) bs -> inl_all I (Node p a (BlockQuote bs))
  | ia_code p a lang code : inl_all I (Node p a (CodeBlock lang code))
  | ia_div p a name bs : Forall (inl_all I) bs -> inl_all I (Node p a (Div name bs))
  | ia_olist p a oa sp items :
      Forall (fun it => Forall (inl_all I) (node_contents it)) items ->
      inl_all I (Node p a (OrderedList oa sp items))
  | ia_blist p a bc sp items :
      Forall (fun it => Forall (inl_all I) (node_contents it)) items ->
      inl_all I (Node p a (BulletList bc sp items))
  | ia_tlist p a sp items :
      Forall (fun it => Forall (inl_all I) (snd (node_contents it))) items ->
      inl_all I (Node p a (TaskList sp items))
  | ia_dlist p a sp items :
      Forall (fun it => I (node_contents (fst (node_contents it))) /\
                        Forall (inl_all I) (node_contents (snd (node_contents it)))) items ->
      inl_all I (Node p a (DefinitionList sp items))
  | ia_thematic p a : inl_all I (Node p a ThematicBreak)
  | ia_table p a cap rows : I (node_contents cap) ->
      Forall (fun r => Forall (fun c => match node_contents c with Cell _ _ ils => I ils end)
                         (node_contents r)) rows ->
      inl_all I (Node p a (Table cap rows))
  | ia_raw p a fmt c : inl_all I (Node p a (RawBlock fmt c))
  | ia_foot p a lbl bs : Forall (inl_all I) bs -> inl_all I (Node p a (FootnoteDef lbl bs))
  | ia_ref p a lbl dest : inl_all I (Node p a (RefDef lbl dest))
  | ia_keyed p a lbl b : I lbl -> inl_all I b -> inl_all I (Node p a (Ext_keyed lbl b))
  | ia_callout p a kind fold title bs : I title -> Forall (inl_all I) bs ->
      inl_all I (Node p a (Ext_callout kind fold title bs)).

(* Only the contents are read: the position and the attributes are free. *)
Lemma inl_all_node : forall I p a q a' x,
  inl_all I (Node p a x) -> inl_all I (Node q a' x).
Proof. intros I p a q a' x H. inversion H; subst; constructor; assumption. Qed.

Lemma inl_all_set_pos : forall I pr b,
  inl_all I b -> inl_all I (@set_pos located_pos block pr b).
Proof.
  intros I pr [p a x] H. unfold set_pos. cbn [mkpos located_pos].
  exact (inl_all_node I p a _ a x H).
Qed.

Local Lemma contents_set_pos : forall `{PosPolicy} {A : Type} pr (n : node A),
  node_contents (set_pos pr n) = node_contents n.
Proof. intros P A pr [q a x]. unfold set_pos. destruct (mkpos pr); reflexivity. Qed.

Local Lemma contents_set_each : forall `{PosPolicy} {A : Type} rs (ns : list (node A)),
  map node_contents (set_each rs ns) = map node_contents ns.
Proof.
  intros P A rs. induction rs as [|r rs IH]; intros [|n ns]; try reflexivity.
  cbn [set_each map]. rewrite contents_set_pos, IH. reflexivity.
Qed.

Local Lemma Forall_contents : forall {A : Type} (Q : A -> Prop) (xs ys : list (node A)),
  map node_contents xs = map node_contents ys ->
  Forall (fun n => Q (node_contents n)) ys -> Forall (fun n => Q (node_contents n)) xs.
Proof.
  intros A Q xs ys E H. apply Forall_map in H. apply Forall_map. rewrite E. exact H.
Qed.

(* Ranges copied onto a list's or table's parts leave their contents. *)
Lemma inl_all_set_parts : forall I ps b,
  inl_all I b -> inl_all I (@set_parts located_pos ps b).
Proof.
Proof.
  intros I ps [p a x] H. cbn [set_parts pos_records located_pos].
  destruct ps as [rs|rs|cap rs], x; cbn [parts_onto]; try exact H;
    inversion H; subst; constructor.
  1-2: apply (Forall_contents (fun x => Forall (inl_all I) x) _ items);
    [apply contents_set_each|exact H1].
  - apply (Forall_contents (fun x => Forall (inl_all I) (snd x)) _ items);
    [apply contents_set_each|exact H1].
  - clear H. revert items H1. induction rs as [|[[i t] d] rs IH];
      intros [|[q b [term def]] its] Hits; try exact Hits.
    inversion Hits as [|? ? Hit Hrest]; subst. cbn [set_defs].
    constructor; [|apply IH, Hrest].
    cbn [set_pos mkpos located_pos node_contents fst snd] in *.
    destruct term, def. exact Hit.
  - destruct cap; [rewrite contents_set_pos|]; exact H2.
  - clear H. revert rows H5. induction rs as [|[r cs] rs IH];
      intros [|[q b cells] rows] Hrows; try exact Hrows.
    inversion Hrows as [|? ? Hr Hrest]; subst. cbn [set_rows].
    constructor; [|apply IH, Hrest].
    cbn [set_pos mkpos located_pos node_contents] in *.
    apply (Forall_contents (fun c => match c with Cell _ _ ils => I ils end) _ cells);
      [apply contents_set_each|exact Hr].
Qed.

Lemma inl_all_decorate_head : forall I pend bs,
  Forall (inl_all I) bs -> Forall (inl_all I) (decorate_head pend bs).
Proof.
  intros I pend [|[p a x] bs] H; [constructor|].
  inversion H as [|? ? Hb Hbs]; subst. constructor; [|exact Hbs].
  exact (inl_all_node I p a p _ x Hb).
Qed.

Lemma inl_all_add_roles_head : forall I rs bs,
  Forall (inl_all I) bs -> Forall (inl_all I) (@add_roles_head located_pos block rs bs).
Proof.
  intros I rs [|[p a x] bs] H; [constructor|].
  inversion H as [|? ? Hb Hbs]; subst. cbn [add_roles_head pos_records located_pos].
  constructor; [|exact Hbs]. unfold add_roles. cbn [pos_records located_pos].
  destruct p; exact (inl_all_node I _ a _ a x Hb).
Qed.

Lemma inl_all_pos_head : forall I pr bs,
  Forall (inl_all I) bs -> Forall (inl_all I) (@pos_head located_pos block pr bs).
Proof.
  intros I pr [|b bs] H; [constructor|].
  inversion H as [|? ? Hb Hbs]; subst. cbn [pos_head mkpos located_pos].
  constructor; [apply inl_all_set_pos, Hb|exact Hbs].
Qed.

Lemma def_split_ok : forall I bs ils rest,
  Forall (inl_all I) bs -> def_split bs = Some (ils, rest) ->
  I ils /\ Forall (inl_all I) rest.
Proof.
  intros I bs. induction bs as [|[q a x] bs IH]; intros ils rest H E; [discriminate|].
  inversion H as [|? ? Hb Hbs]; subst. cbn [def_split] in E.
  destruct x; try (destruct (invisible_block _)); try discriminate;
    try (injection E as <- <-; inversion Hb; subst; split; assumption);
    (destruct (def_split bs) as [[ils' more]|] eqn:Ed; [|discriminate];
     injection E as <- <-; destruct (IH _ _ Hbs eq_refl) as [Hi Hm];
     split; [exact Hi|constructor; assumption]).
Qed.

Lemma def_items_ok : forall I its, I [] ->
  Forall (Forall (inl_all I)) its ->
  Forall (fun it => I (node_contents (fst (node_contents it))) /\
                    Forall (inl_all I) (node_contents (snd (node_contents it))))
    (def_items its).
Proof.
  intros I its H0 H. unfold def_items. apply Forall_map.
  refine (Forall_impl _ _ H). intros bs Hb. cbn beta. unfold def_node, def_item.
  destruct (def_split bs) as [[ils rest]|] eqn:E.
  - exact (def_split_ok I bs ils rest Hb E).
  - split; [exact H0|exact Hb].
Qed.

Lemma task_items_ok : forall I chks its,
  Forall (Forall (inl_all I)) its ->
  Forall (fun it => Forall (inl_all I) (snd (node_contents it))) (task_items chks its).
Proof.
  intros I chks its. revert chks. induction its as [|it its IH]; intros chks H; [constructor|].
  inversion H as [|? ? Hi Hs]; subst.
  destruct chks; cbn [task_items]; constructor; auto.
Qed.

(*
The state invariant
===================

What every state the located parse reaches keeps, at line `i` of `src`:
its stored lines are suffixes of earlier source lines (`acc_ok`), a
callout title is a suffix of its line, every table cell it recorded is
where its row part says, and every block a container already closed has
good inlines.  A key is excluded: see the header.
*)

(*
Moving a piece into place
=========================

The located parse reads each piece from line 0 and then shifts it
(`Shift.of_blocks`).  Reading a shifted spot in the source is reading
the unshifted one in the source from the piece's first line on.
*)

Lemma wfind_src_any : forall src k,
  wfind (src_windows src) k = option_map (fun l => (String.length l, l)) (nth_error src k).
Proof. intros src k. unfold src_windows. exact (wfind_src_from src 0 k). Qed.

Lemma sfx_shift : forall src d p,
  sfx (src_windows (skipn d src)) p = sfx (src_windows src) (Shift.of_spot d p).
Proof.
  intros src d [k rem]. unfold sfx, Shift.of_spot. cbn [spot_line spot_rem].
  rewrite !wfind_src_any, nth_error_skipn. reflexivity.
Qed.

Lemma byte_at_shift : forall src d p,
  byte_at (src_windows (skipn d src)) p = byte_at (src_windows src) (Shift.of_spot d p).
Proof. intros src d p. unfold byte_at. rewrite sfx_shift. reflexivity. Qed.

Lemma dspan_shift : forall src d k r,
  dspan_ok (src_windows (skipn d src)) k r ->
  dspan_ok (src_windows src) k (Shift.of_span d r).
Proof.
  intros src d k [a b] (m & (rest & Ho & Hob) & (rest' & Hc & Hcb) & Hlt).
  exists m. cbn [Shift.of_span span_start span_stop] in *.
  repeat split.
  - exists rest. split.
    + change (sfx (src_windows src) (Shift.of_spot d a) = Some (otok k m ++ rest)%string).
      rewrite <- sfx_shift. exact Ho.
    + intros Hm. destruct (Hob Hm) as (c & Hb & Hn). exists c. split; [|exact Hn].
      change (sright (String.length (otok k m)) (Shift.of_spot d a))
        with (Shift.of_spot d (sright (String.length (otok k m)) a)).
      rewrite <- byte_at_shift. exact Hb.
  - exists rest'. split.
    + change (sleft (String.length (ctok k m)) (Shift.of_spot d b))
        with (Shift.of_spot d (sleft (String.length (ctok k m)) b)).
      rewrite <- sfx_shift. exact Hc.
    + intros Hm. destruct (Hcb Hm) as (c & Hb & Hn). exists c. split; [|exact Hn].
      change (sleft 1 (sleft (String.length (ctok k m)) (Shift.of_spot d b)))
        with (Shift.of_spot d (sleft 1 (sleft (String.length (ctok k m)) b))).
      rewrite <- byte_at_shift. exact Hb.
  - unfold spot_lt, Shift.of_spot, sright, sleft in *. cbn in *. lia.
Qed.

Lemma dkind_shift : forall d x, dkind (Shift.of_inline d x) = dkind x.
Proof. intros d [] ; reflexivity. Qed.

Lemma dn_shift : forall src d,
  (forall x p, dn_inline (src_windows (skipn d src)) p x ->
     dn_inline (src_windows src) (Shift.of_pos d p) (Shift.of_inline d x)) /\
  (forall ils, Forall (dn_node (src_windows (skipn d src))) ils ->
     Forall (dn_node (src_windows src)) (Shift.of_inlines d ils)).
Proof.
  intros src d.
  set (W := src_windows (skipn d src)). set (W' := src_windows src).
  assert (Hpos : forall p x, dpos_ok W p x -> dpos_ok W' (Shift.of_pos d p) (Shift.of_inline d x)).
  { intros p x. unfold dpos_ok. rewrite dkind_shift. destruct (dkind x); [|tauto].
    intros (pr & -> & H). eexists. split; [reflexivity|]. cbn [node_span].
    exact (dspan_shift src d _ _ H). }
  assert (Hl : forall ils, (forall x p, dn_inline W p x ->
                 dn_inline W' (Shift.of_pos d p) (Shift.of_inline d x)) ->
               Forall (dn_node W) ils -> Forall (dn_node W') (Shift.of_inlines d ils)).
  { intros ils Hx. induction ils as [|[p a x] ils IH]; intros H; [constructor|].
    inversion H as [|? ? H1 H2]; subst. cbn [Shift.of_inlines]. constructor; [exact (Hx x p H1)|auto]. }
  assert (Hx : forall x p, dn_inline W p x ->
                 dn_inline W' (Shift.of_pos d p) (Shift.of_inline d x)).
  { intros x. apply (inline_ind2
      (fun x => forall p, dn_inline W p x -> dn_inline W' (Shift.of_pos d p) (Shift.of_inline d x))
      (fun ils => Forall (dn_node W) ils -> Forall (dn_node W') (Shift.of_inlines d ils)));
      intros; cbn [Shift.of_inline dn_inline] in *; rewrite ?Shift.inline_children;
      try (destruct H0 as [Hp Hc]; split; [exact (Hpos _ _ Hp)|];
           apply dn_children; apply H; apply dn_children; exact Hc);
      try (destruct H as [Hp _]; split; [exact (Hpos _ _ Hp)|exact I]).
    - constructor.
    - inversion H1 as [|? ? Hx Hr]; subst. cbn [Shift.of_inlines].
      constructor; [exact (H p Hx)|exact (H0 Hr)]. }
  split; [exact Hx|]. intros ils. exact (Hl ils Hx).
Qed.

Section Invariant.
Context {K : bconfig}.
Variable src : list string.

Definition good : inlines -> Prop := Forall (dn_node (src_windows src)).
Definition bgood : node block -> Prop := inl_all good.

Definition cgood (c : cell) : Prop := match c with Cell _ _ ils => good ils end.

(* A trimmed run of line `k` that starts `rem` bytes before its end. *)
Definition run_at (k rem : nat) (c : string) : Prop :=
  k < length src /\ rem <= String.length (line_at src k) /\
  (exists more, sdrop (String.length (line_at src k) - rem) (line_at src k)
                = (c ++ more)%string) /\
  String.length c <= rem.

Definition cells_ok (cs : list string) (cps : list cell_part) : Prop :=
  Forall2 (fun c cp => run_at (spot_line (cell_text_start cp))
                              (spot_rem (cell_text_start cp)) c) cs cps.

(* Rows in source order against their parts: a separator has none, a row
   of cells one. *)
Fixpoint rows_fwd (rows : list trow) (parts : list row_part) : Prop :=
  match rows with
  | [] => parts = []
  | TSep _ :: rest => rows_fwd rest parts
  | TCells cs :: rest =>
      match parts with
      | [] => False
      | (_, cps) :: ps => cells_ok cs cps /\ rows_fwd rest ps
      end
  end.

Definition cap_ok (i : nat) (rows : list trow) (cap : tcap) : Prop :=
  match cap with
  | TOpen ps | TAfterBlank ps => rows_fwd (rev rows) (rev ps)
  | TCaption ps _ ls => rows_fwd (rev rows) (rev ps) /\ acc_ok src i ls
  end.

Definition header_ok (h : option (string * option callout_fold * stored_line)) : Prop :=
  match h with
  | None => True
  | Some (_, _, (k, t)) => k < length src /\ is_sfx t (line_at src k)
  end.

Fixpoint st_ok (i : nat) (st : pstate) : Prop :=
  match st with
  | PPara cur | PParaOff _ cur | PHeading _ _ cur => acc_ok src i cur
  | PFence _ _ _ _ _ | PRef _ _ _ _ => True
  | PAttr _ _ _ _ _ slices => acc_ok src i slices
  | PQuote _ h done inner => header_ok h /\ Forall bgood done /\ st_ok i inner
  | PDiv _ _ _ _ done inner | PFoot _ _ _ done inner =>
      Forall bgood done /\ st_ok i inner
  | PList ls done inner =>
      Forall (Forall bgood) (ls_items ls) /\ Forall bgood done /\ st_ok i inner
  | PTable _ rows cap => cap_ok i rows cap
  | PPend _ _ inner => st_ok i inner
  | PKey _ _ _ _ => False
  end.

Lemma st_ok_mono : forall st i j, i <= j -> st_ok i st -> st_ok j st.
Proof.
  induction st; intros i j Hij H; cbn [st_ok] in *;
    try (eapply acc_ok_mono; eassumption); try exact H; try tauto.
  all: try (match goal with c : tcap |- _ => destruct c; cbn [cap_ok] in *; try exact H;
          destruct H as [? ?]; split; [assumption|eapply acc_ok_mono; eassumption] end).
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; eauto.
Qed.

(*
Closing a state
---------------
*)

Lemma cells_of_located_ok : forall ct als cs cps,
  cells_ok cs cps -> Forall cgood (@Step.cells_of_located T located_pos ct als cs cps).
Proof.
  intros ct als cs cps H. revert als.
  induction H as [|c cp cs cps Hc Hcs IH]; intros als; [constructor|].
  cbn [Step.cells_of_located]. constructor; [|apply IH].
  destruct Hc as (Hk & Hr & Hm & Hl). exact (line_spans_src src _ _ c Hk Hr Hm Hl).
Qed.

Lemma head_of_ok : forall als r, Forall cgood r -> Forall cgood (head_of als r).
Proof.
  intros als r H. revert als. induction H as [|[ct al ils] r Hc Hr IH]; intros als;
    [constructor|]. destruct als; cbn [head_of]; constructor; auto.
Qed.

Lemma table_fold_located_ok : forall rows parts als acc,
  rows_fwd rows parts -> Forall (Forall cgood) acc ->
  Forall (Forall cgood) (@Step.table_fold_located T located_pos rows parts als acc).
Proof.
  induction rows as [|[a|cs] rows IH]; intros parts als acc Hr Hacc.
  - apply Forall_rev, Hacc.
  - cbn [Step.table_fold_located rows_fwd] in *. apply IH; [exact Hr|].
    destruct acc as [|r acc]; [constructor|].
    inversion Hacc as [|? ? H1 H2]; subst. constructor; [apply head_of_ok, H1|exact H2].
  - cbn [Step.table_fold_located rows_fwd] in *.
    destruct parts as [|[sp cps] parts]; [contradiction|]. destruct Hr as [Hc Hr].
    apply IH; [exact Hr|]. constructor; [apply cells_of_located_ok, Hc|exact Hacc].
Qed.

Lemma caption_ok : forall i rows cap,
  cap_ok i rows cap -> good (@caption_of T located_pos cap).
Proof.
  intros i rows [ps|ps|ps start ls] H; cbn [caption_of]; try constructor.
  destruct H as [_ H]. exact (para_spans_src src i ls 0 H).
Qed.

Lemma table_block_ok : forall i rows cap,
  cap_ok i rows cap -> bgood (@table_block T located_pos (rev rows) cap).
Proof.
  intros i rows cap H. unfold table_block. cbn [pos_records located_pos].
  constructor; [exact (caption_ok i rows cap H)|].
  apply Forall_map. eapply Forall_impl; [|apply table_fold_located_ok; [|constructor]].
  - intros r Hr. apply Forall_map. exact Hr.
  - destruct cap; cbn [Step.cap_row_parts cap_ok] in *; try exact H; apply H.
Qed.

Lemma para_ok : forall i cur off,
  acc_ok src i cur -> good (@para_inlines_at T located_pos off (rev cur)).
Proof. intros i cur off H. exact (para_spans_src src i cur off H). Qed.

Lemma callout_title_ok : forall sl,
  header_ok (Some (EmptyString, None, sl)) -> good (@callout_title T located_pos sl).
Proof.
  intros [k t] (Hk & p & Ep). unfold callout_title. cbn [pos_records located_pos].
  apply (line_spans_src src); [exact Hk| | |apply strip_length].
  - rewrite Ep, length_append. lia.
  - destruct (strip_trailing_split t) as (w & _ & Ew). exists w.
    rewrite Ep, length_append.
    replace (String.length p + String.length t - String.length t)
      with (String.length p) by lia.
    rewrite sdrop_prefix. exact Ew.
Qed.

Lemma quote_block_ok : forall h bs,
  header_ok h -> Forall bgood bs ->
  bgood (mk (@quote_block T located_pos h bs)).
Proof.
  intros [[[kind fold] sl]|] bs Hh Hbs; cbn [quote_block]; constructor; try exact Hbs.
  apply callout_title_ok. destruct sl. exact Hh.
Qed.

Lemma list_block_ok : forall ls last,
  Forall (Forall bgood) (ls_items ls) -> Forall bgood last ->
  bgood (list_block ls last).
Proof.
  intros ls last Hi Hl.
  assert (Hr : Forall (Forall bgood) (rev (last :: ls_items ls)))
    by (apply Forall_rev; constructor; assumption).
  unfold list_block, styles_list_checked.
  destruct (ls_styles ls) as [|[sty start] rest]; [constructor; apply Forall_map, Hr|].
  destruct sty; cbn [styles_list]; try (destruct (_ && _)%bool); constructor;
    first [apply def_items_ok; [constructor|exact Hr] | apply Forall_map, Hr
          | apply task_items_ok, Hr].
Qed.

Lemma div_block_ok : forall cls bs, Forall bgood bs -> bgood (div_block cls bs).
Proof.
  intros cls bs H. unfold div_block. destruct bdiv_names; [|destruct (String.eqb cls EmptyString)]; constructor; exact H.
Qed.

Lemma fence_block_ok : forall f c, bgood (fence_block f c).
Proof.
  intros f c. unfold fence_block.
  destruct (f_info f) as [|ch rest]; [constructor|].
  destruct ch as [[] [] [] [] [] [] [] []]; try constructor.
  destruct braw_blocks; constructor.
Qed.

Lemma finish_recover_ok : forall i slices,
  acc_ok src i slices -> Forall bgood (@finish_para_recover T located_pos slices).
Proof.
  intros i [|sl slices] H; [constructor|]. unfold finish_para_recover.
  constructor; [|constructor]. apply inl_all_set_pos. constructor. apply (para_ok i), H.
Qed.

Lemma finish_ok : forall st i, st_ok i st -> Forall bgood (@finish T K located_pos st).
Proof.
  induction st; intros i H; cbn [st_ok finish] in *.
  - destruct cur as [|c cur]; [constructor|].
    constructor; [|constructor]. apply inl_all_set_pos. constructor. apply (para_ok i), H.
  - constructor; [|constructor]. apply inl_all_set_pos. constructor. apply (para_ok i), H.
  - constructor; [|constructor]. apply inl_all_set_pos, fence_block_ok.
  - destruct H as (Hh & Hd & Hs). constructor; [|constructor].
    apply inl_all_set_pos, quote_block_ok; [exact Hh|].
    apply Forall_app. split; [apply Forall_rev, Hd|exact (IHst i Hs)].
  - destruct H as (Hd & Hs). constructor; [|constructor].
    apply inl_all_set_pos, div_block_ok.
    apply Forall_app. split; [apply Forall_rev, Hd|exact (IHst i Hs)].
  - destruct H as (Hi & Hd & Hs). constructor; [|constructor].
    apply inl_all_set_pos, inl_all_set_parts, list_block_ok; [exact Hi|].
    apply Forall_app. split; [apply Forall_rev, Hd|exact (IHst i Hs)].
  - destruct (ap_done ap); [constructor|].
    apply inl_all_add_roles_head, inl_all_decorate_head, (finish_recover_ok i), H.
  - constructor; [|constructor]. apply inl_all_set_pos. constructor. apply (para_ok i), H.
  - constructor; [|constructor]. apply inl_all_set_pos. constructor.
  - destruct H as (Hd & Hs). constructor; [|constructor].
    apply inl_all_set_pos. constructor.
    apply Forall_app. split; [apply Forall_rev, Hd|exact (IHst i Hs)].
  - constructor; [|constructor]. apply inl_all_set_pos, inl_all_set_parts, (table_block_ok i), H.
  - apply inl_all_add_roles_head, inl_all_decorate_head, (IHst i), H.
  - contradiction.
Qed.

(*
One line
--------

`ok i r`: the blocks a step emitted are good and the state it left is
good at the next line.  Every lemma below is at the ambient line index
`lix`, for a line handed to `step` that is a suffix of source line
`lix`.
*)

Definition ok (i : nat) (r : blocks * pstate) : Prop :=
  Forall bgood (fst r) /\ st_ok i (snd r).

Section AtLine.
Context {LI : LineIx}.
Hypothesis Hlix : lix < length src.
Hypothesis Hkeyed : bkeyed = false.

Definition here (l : string) : Prop := is_sfx l (line_at src lix).

Lemma acc_push : forall cur t,
  here t -> acc_ok src lix cur -> acc_ok src (S lix) (remember_line t :: cur).
Proof. intros cur t Ht H. unfold remember_line. cbn. repeat split; auto. Qed.

Lemma here_trans : forall a b, is_sfx a b -> here b -> here a.
Proof. intros a b H1 H2. exact (is_sfx_trans _ _ _ H1 H2). Qed.

Lemma push_text_ok : forall rest cur,
  here rest -> acc_ok src lix cur -> acc_ok src (S lix) (push_text rest cur).
Proof.
  intros rest cur Hr H. unfold push_text. destruct (is_blank rest).
  - exact (acc_ok_mono src cur lix (S lix) (le_S _ _ (le_n _)) H).
  - apply acc_push; [|exact H]. exact (here_trans _ _ (drop_leading_ws_sfx rest) Hr).
Qed.

Lemma st_ok_next : forall st, st_ok lix st -> st_ok (S lix) st.
Proof. intros st. apply st_ok_mono. lia. Qed.

Lemma feed_lazy_ok : forall l st,
  here l -> st_ok lix st -> st_ok (S lix) (feed_lazy l st).
Proof.
  intros l st Hl. assert (Hd : here (drop_leading_ws l))
    by exact (here_trans _ _ (drop_leading_ws_sfx l) Hl).
  induction st; intros H; cbn [feed_lazy st_ok] in *;
    try (apply acc_push; assumption);
    try exact I; try (apply st_ok_next; exact H).
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; auto.
  - exact (acc_ok_mono src slices lix (S lix) (le_S _ _ (le_n _)) H).
  - exact (st_ok_mono (PTable range rows cap) lix (S lix) (le_S _ _ (le_n _)) H).
Qed.

Lemma table_row_part_ok : forall l cs,
  here l -> classify l = KRow (TCells cs) ->
  exists sp cps, table_row_part l (TCells cs) = Some (sp, cps) /\ cells_ok cs cps.
Proof.
  intros l cs Hl Hc.
  destruct (table_row_trace l cs (classify_row l _ Hc))
    as (body & cells & Eb & Et & -> & Hat).
  unfold table_row_part. rewrite Eb, Et.
  eexists _, _. split; [reflexivity|].
  unfold cells_ok. clear Hc Et Eb. induction Hat as [|[[[c a] b] ts] cells Hx _ IH]; [constructor|].
  cbn [map]. constructor; [clear IH|exact IH].
  destruct Hx as (pre & more & ED & Hts). cbn [cell_text_start spot_line spot_rem].
  destruct Hl as (p & Ep). destruct (drop_leading_ws_split l) as (w & _ & Ew).
  assert (Hlen : String.length (line_at src lix)
                 = String.length p + String.length w + ts + String.length c
                   + String.length more)
    by (rewrite Ep, Ew, ED, !length_append; lia).
  rewrite ED, !length_append.
  split; [exact Hlix|]. split; [lia|]. split; [|lia].
  exists more.
  replace (String.length (line_at src lix)
           - (String.length pre + (String.length c + String.length more) - ts))
    with (String.length (p ++ w ++ pre)) by (rewrite !length_append; lia).
  rewrite Ep, Ew, ED.
  replace (p ++ (w ++ pre ++ c ++ more))%string with ((p ++ w ++ pre) ++ c ++ more)%string
    by (rewrite !append_assoc; reflexivity).
  apply sdrop_prefix.
Qed.

Lemma rows_fwd_sep : forall rows parts a,
  rows_fwd rows parts -> rows_fwd (rows ++ [TSep a]) parts.
Proof.
  induction rows as [|[a'|cs] rows IH]; intros parts a H; cbn [app rows_fwd] in *; auto.
  destruct parts as [|[sp cps] parts]; [contradiction|]. destruct H. split; auto.
Qed.

Lemma rows_fwd_cells : forall rows parts cs sp cps,
  rows_fwd rows parts -> cells_ok cs cps ->
  rows_fwd (rows ++ [TCells cs]) (parts ++ [(sp, cps)]).
Proof.
  induction rows as [|[a'|cs'] rows IH]; intros parts cs sp cps H Hc;
    cbn [app rows_fwd] in *.
  - subst parts. cbn. split; [exact Hc|reflexivity].
  - auto.
  - destruct parts as [|[sp' cps'] parts]; [contradiction|]. destruct H. cbn [app].
    split; auto.
Qed.

Lemma configured_list_rest_sfx : forall chk rest l,
  is_sfx (task_literal_rest chk rest) l -> is_sfx (configured_list_rest chk rest) l.
Proof.
  intros chk rest l H. unfold configured_list_rest. destruct btasks.
  - exact (is_sfx_trans _ _ _ (task_literal_rest_sfx chk rest) H).
  - destruct chk; exact H.
Qed.

Lemma table_row_part_sep : forall l a, table_row_part l (TSep a) = None.
Proof. intros l a. unfold table_row_part. destruct (row_body l); reflexivity. Qed.

Lemma row_open_ok : forall l r,
  here l -> classify l = KRow r ->
  cap_ok (S lix) [r] (TOpen (match table_row_part l r with Some p => [p] | None => [] end)).
Proof.
  intros l [a|cs] Hl Hc; cbn [cap_ok rev app rows_fwd].
  - rewrite table_row_part_sep. reflexivity.
  - destruct (table_row_part_ok l cs Hl Hc) as (sp & cps & -> & Hcs).
    cbn. split; [exact Hcs|reflexivity].
Qed.

Lemma row_next_ok : forall l r rows parts,
  here l -> classify l = KRow r -> rows_fwd (rev rows) (rev parts) ->
  rows_fwd (rev (r :: rows))
    (rev (match table_row_part l r with Some p => p :: parts | None => parts end)).
Proof.
  intros l [a|cs] rows parts Hl Hc H; cbn [rev].
  - rewrite table_row_part_sep. apply rows_fwd_sep, H.
  - destruct (table_row_part_ok l cs Hl Hc) as (sp & cps & -> & Hcs).
    cbn [rev]. apply rows_fwd_cells; assumption.
Qed.

Lemma open_kind_ok : forall l,
  here l -> ok (S lix) (@open_kind T LI located_pos K l (classify l)).
Proof.
  intros l Hl. pose proof (classify_sfx l) as Hs.
  assert (Hd : here (drop_leading_ws l))
    by exact (here_trans _ _ (drop_leading_ws_sfx l) Hl).
  destruct (classify l) eqn:Hc; cbn [open_kind];
    try (destruct bdivs); try (destruct btables); try (unfold open_text; rewrite Hkeyed);
    unfold ok; cbn [fst snd st_ok]; split;
    try solve [repeat constructor].
  all: first [apply acc_push; [exact Hd|exact I]
           | apply push_text_ok; [exact (here_trans _ _ Hs Hl)|exact I]
           | cbn [pos_records located_pos]; exact (row_open_ok l r Hl Hc)].
Qed.

Lemma close_reopen_ok : forall st r,
  st_ok lix st -> ok (S lix) r -> ok (S lix) (@close_reopen T K located_pos st r).
Proof.
  intros st [bs st'] H [Hb Hs]. unfold close_reopen, ok. cbn [fst snd] in *.
  split; [apply Forall_app; split; [exact (finish_ok st lix H)|exact Hb]|exact Hs].
Qed.

Lemma pend_result_ok : forall pend specs r,
  ok (S lix) r -> ok (S lix) (@pend_result located_pos pend specs r).
Proof.
  intros pend specs [[|b bs] st'] [Hb Hs]; unfold ok in *; cbn [pend_result fst snd] in *.
  - split; [constructor|exact Hs].
  - split; [apply inl_all_add_roles_head, inl_all_decorate_head, Hb|exact Hs].
Qed.

Lemma open_line_ok : forall descend ind l,
  here l ->
  (forall rest, is_sfx rest l -> ok (S lix) (descend rest)) ->
  ok (S lix) (@open_line T K LI located_pos descend ind l (classify l)).
Proof.
  intros descend ind l Hl Hdesc. pose proof (classify_sfx l) as Hs.
  assert (Hd : here (drop_leading_ws l))
    by exact (here_trans _ _ (drop_leading_ws_sfx l) Hl).
  destruct (classify l) eqn:Hc; cbn [open_line];
    try (rewrite <- Hc; apply open_kind_ok, Hl).
  all: unfold ok, open_fence, open_ref, open_attr, open_foot, open_list, open_quote,
         open_callout, quote_header in *.
  all: try (destruct battrs); try (destruct bfootnotes); try (destruct bcallouts).
  all: try (destruct (callout_header rest) as [[[kind fold] title]|] eqn:Eh).
  all: try (destruct (Hdesc rest Hs) as [Hb Hi]; destruct (descend rest) as [bs inner]).
  all: try (destruct (Hdesc _ (configured_list_rest_sfx chk rest l Hs)) as [Hb Hi];
            destruct (descend (configured_list_rest chk rest)) as [bs inner]).
  all: cbn [fst snd st_ok list_opened ls_items header_ok remember_line] in *.
  all: repeat split; try constructor; try exact I; try (apply Forall_rev; assumption);
    try assumption; try (apply acc_push; [exact Hd|exact I]); try exact Hlix;
    try (exact (here_trans _ _ (is_sfx_trans _ _ _ (callout_header_sfx _ _ _ _ Eh) Hs) Hl)).
Qed.

Lemma open_line_at : forall descend ind l k,
  classify l = k -> here l ->
  (forall rest, is_sfx rest l -> ok (S lix) (descend rest)) ->
  ok (S lix) (@open_line T K LI located_pos descend ind l k).
Proof. intros descend ind l k <-. apply open_line_ok. Qed.

Lemma open_kind_at : forall l k,
  classify l = k -> here l -> ok (S lix) (@open_kind T LI located_pos K l k).
Proof. intros l k <-. apply open_kind_ok. Qed.

(* A branch that closes the state and reopens on the line. *)
Local Ltac reopen Hst Ec Hl Hd :=
  first [ apply close_reopen_ok; [exact Hst|apply (open_line_at _ _ _ _ Ec Hl Hd)]
        | apply close_reopen_ok; [exact Hst|apply (open_kind_at _ _ Ec Hl)]
        | apply (open_line_at _ _ _ _ Ec Hl Hd) ].

(** One line: from a good state, a line that is a suffix of source line
    `lix` emits good blocks and leaves a state good at the next line. *)
Lemma step_fuel_ok : forall n off l st,
  here l -> st_ok lix st -> ok (S lix) (@step_fuel T K LI located_pos n off l st).
Proof.
  intros n. induction n as [|n IH]; intros off l st Hl Hst.
  { split; [constructor|exact (st_ok_next st Hst)]. }
  assert (Hd : forall rest, is_sfx rest l ->
    ok (S lix) (@step_fuel T K LI located_pos n (off + consumed l rest) rest (PPara [])))
    by (intros rest Hr; apply IH; [exact (here_trans _ _ Hr Hl)|exact I]).
  assert (Hdl : here (drop_leading_ws l))
    by exact (here_trans _ _ (drop_leading_ws_sfx l) Hl).
  pose proof (classify_sfx l) as Hcs.
  destruct st; cbn [step_fuel].
  - (* PPara *)
    destruct cur as [|c cur']; [apply (open_line_at _ _ _ _ eq_refl Hl Hd)|].
    destruct (bunderline_of l) as [lvl|].
    + split; [|exact I]. constructor; [|constructor].
      apply inl_all_set_pos. constructor. exact (para_ok lix _ 0 Hst).
    + destruct (classify l) eqn:Ec; try destruct (binterrupt _);
        try (reopen Hst Ec Hl Hd);
        (split; [constructor|apply acc_push; [exact Hdl|exact Hst]]).
  - (* PHeading *)
    destruct (classify l) eqn:Ec; try (reopen Hst Ec Hl Hd).
    + destruct bheading_continues; [destruct (Nat.eqb _ _)|];
        try (reopen Hst Ec Hl Hd).
      split; [constructor|apply push_text_ok; [exact (here_trans _ _ Hcs Hl)|exact Hst]].
    + destruct bheading_continues; try (reopen Hst Ec Hl Hd).
      split; [constructor|apply acc_push; [exact Hdl|exact Hst]].
  - (* PFence *)
    destruct (fence_close f l).
    + split; [|exact I]. constructor; [apply inl_all_set_pos, fence_block_ok|constructor].
    + split; [constructor|exact I].
  - (* PQuote *)
    destruct Hst as (Hh & Hdn & Hi).
    destruct (classify l) eqn:Ec; cbn [is_lazy];
      try (reopen (conj Hh (conj Hdn Hi) : st_ok lix (PQuote range header done st)) Ec Hl Hd).
    + destruct (IH (off + consumed l rest) rest st (here_trans _ _ Hcs Hl) Hi) as [Hb Hi'].
      destruct (step_fuel n (off + consumed l rest) rest st) as [bs inner'].
      split; [constructor|]. cbn [snd st_ok fst] in *.
      split; [exact Hh|split; [apply Forall_app; split; [apply Forall_rev, Hb|exact Hdn]|exact Hi']].
    + destruct (lazy_ok st).
      * split; [constructor|]. cbn [snd st_ok].
        split; [exact Hh|split; [exact Hdn|exact (feed_lazy_ok l st Hl Hi)]].
      * reopen (conj Hh (conj Hdn Hi) : st_ok lix (PQuote range header done st)) Ec Hl Hd.
  - (* PDiv *)
    destruct Hst as (Hdn & Hi).
    destruct (negb (in_fence st) && div_close len l)%bool.
    + split; [|exact I]. constructor; [|constructor]. apply inl_all_set_pos, div_block_ok.
      apply Forall_app. split; [apply Forall_rev, Hdn|exact (finish_ok st lix Hi)].
    + destruct (IH off l st Hl Hi) as [Hb Hi'].
      destruct (step_fuel n off l st) as [bs inner'].
      split; [constructor|]. cbn [snd st_ok fst] in *.
      split; [apply Forall_app; split; [apply Forall_rev, Hb|exact Hdn]|exact Hi'].
  - (* PList *)
    destruct Hst as (Hit & Hdn & Hi).
    assert (Hst : st_ok lix (PList ls done st)) by (split; [exact Hit|split; assumption]).
    destruct (classify l) eqn:Ec.
    all: try (destruct (list_takes ls off l st)).
    all: try (destruct (IH off l st Hl Hi) as [Hb Hi'];
              destruct (step_fuel n off l st) as [bs inner'];
              split; [constructor|]; cbn [snd st_ok fst] in *;
              split; [try destruct (blank_absorbed st); exact Hit|];
              split; [apply Forall_app; split; [apply Forall_rev, Hb|exact Hdn]|exact Hi']).
    all: cbn [is_lazy].
    all: try (destruct (lazy_ok st);
              [split; [constructor|]; cbn [snd st_ok];
               split; [exact Hit|split; [exact Hdn|exact (feed_lazy_ok l st Hl Hi)]]
              |reopen Hst Ec Hl Hd]).
    all: try (reopen Hst Ec Hl Hd).
    destruct (Marker.narrow (ls_styles ls) (configured_list_styles sty chk)) as [|p0 ps].
    + reopen Hst Ec Hl Hd.
    + destruct (Hd _ (configured_list_rest_sfx chk rest l Hcs)) as [Hb Hi'].
      destruct (step_fuel n (off + consumed l (configured_list_rest chk rest))
                 (configured_list_rest chk rest) (PPara [])) as [bs inner'].
      split; [constructor|]. cbn [snd st_ok fst list_next list_narrow ls_items] in *.
      split; [constructor; [|exact Hit]|split; [apply Forall_rev, Hb|exact Hi']].
      apply Forall_app. split; [apply Forall_rev, Hdn|exact (finish_ok st lix Hi)].
  - (* PAttr *)
    destruct (ap_done ap); [apply IH; [exact Hl|exact I]|].
    destruct (Nat.ltb ind (off + indent_of l)).
    + destruct (ap_failed (attr_feed l ap)).
      * apply pend_result_ok, IH; [exact Hl|exact Hst].
      * split; [constructor|]. apply push_text_ok; [exact Hl|exact Hst].
    + destruct (is_blank l).
      * split; [constructor|].
        exact (acc_ok_mono src slices lix (S lix) (le_S _ _ (le_n _)) Hst).
      * apply pend_result_ok, IH; [exact Hl|exact Hst].
  - (* PParaOff *)
    destruct (bunderline_of l) as [lvl|].
    + split; [|exact I]. constructor; [|constructor].
      apply inl_all_set_pos. constructor. exact (para_ok lix _ _ Hst).
    + destruct (classify l) eqn:Ec; try destruct (binterrupt _);
        try (reopen Hst Ec Hl Hd);
        (split; [constructor|apply acc_push; [exact Hdl|exact Hst]]).
  - (* PRef *)
    destruct (if Nat.ltb ind (off + indent_of l) then ref_cont l else None);
      [split; [constructor|exact I]|].
    destruct (IH off l (PPara []) Hl I) as [Hb Hs'].
    destruct (step_fuel n off l (PPara [])) as [bs st'].
    split; [constructor; [apply inl_all_set_pos; constructor|exact Hb]|exact Hs'].
  - (* PFoot *)
    destruct Hst as (Hdn & Hi).
    assert (Hdesc : ok (S lix) (@step_fuel T K LI located_pos n off l st) ->
       ok (S lix) (let (bs, inner') := @step_fuel T K LI located_pos n off l st in
                   ([], PFoot (touch_extent range) ind lbl (rev bs ++ done)%list inner'))).
    { intros [Hb Hi']. destruct (@step_fuel T K LI located_pos n off l st) as [bs inner'].
      split; [constructor|]. cbn [snd st_ok fst] in *.
      split; [apply Forall_app; split; [apply Forall_rev, Hb|exact Hdn]|exact Hi']. }
    destruct (is_blank l); [exact (Hdesc (IH off l st Hl Hi))|].
    destruct (foot_takes ind off l st); [exact (Hdesc (IH off l st Hl Hi))|].
    destruct (is_lazy (classify l) st).
    + split; [constructor|]. split; [exact Hdn|exact (feed_lazy_ok l st Hl Hi)].
    + destruct (IH off l (PPara []) Hl I) as [Hb Hs'].
      destruct (step_fuel n off l (PPara [])) as [bs st'].
      split; [|exact Hs']. constructor; [|exact Hb].
      apply inl_all_set_pos. constructor.
      apply Forall_app. split; [apply Forall_rev, Hdn|exact (finish_ok st lix Hi)].
  - (* PTable *)
    cbn [st_ok] in Hst.
    assert (Hrows : rows_fwd (rev rows) (rev (Step.cap_row_parts cap)))
      by (destruct cap; cbn [cap_ok Step.cap_row_parts] in *; tauto).
    assert (Hclose : ok (S lix) (@step_fuel T K LI located_pos n off l (PPara [])) ->
      ok (S lix) (let (bs, st') := @step_fuel T K LI located_pos n off l (PPara []) in
        ((@set_pos located_pos _ (prov_at (extent_span range))
            (@set_parts located_pos (table_parts cap) (@table_block T located_pos (rev rows) cap)) :: bs)%list, st'))).
    { intros [Hb Hs']. destruct (@step_fuel T K LI located_pos n off l (PPara [])) as [bs st'].
      split; [|exact Hs']. constructor; [|exact Hb].
      apply inl_all_set_pos, inl_all_set_parts, (table_block_ok lix), Hst. }
    destruct cap as [parts|parts|parts start ls].
    3: { destruct (is_blank l).
         - split; [|exact I]. constructor; [|constructor].
           apply inl_all_set_pos, inl_all_set_parts, (table_block_ok lix), Hst.
         - split; [constructor|]. cbn [snd st_ok cap_ok] in *.
           destruct Hst as [Hr Ha]. split; [exact Hr|apply acc_push; [exact Hdl|exact Ha]]. }
    all: destruct (caption_open l) as [crest|] eqn:Eco;
      [split; [constructor|]; cbn [snd st_ok cap_ok Step.cap_row_parts] in *;
       split; [exact Hrows|apply push_text_ok;
                 [exact (here_trans _ _ (caption_open_sfx _ _ Eco) Hl)|exact I]]|].
    all: destruct (is_blank l); [split; [constructor|exact Hrows]|].
    all: destruct (classify l) eqn:Ec; try (exact (Hclose (IH off l (PPara []) Hl I))).
    split; [constructor|]. cbn [snd st_ok cap_ok pos_records located_pos].
    exact (row_next_ok l r rows parts Hl Ec Hst).
  - (* PPend *)
    destruct (classify l) eqn:Ec; try (destruct (is_idle st));
      try (apply pend_result_ok, IH; [exact Hl|exact Hst]).
    + split; [constructor|exact I].
    + unfold open_attr.
      destruct battrs; (split; [constructor|apply acc_push; [exact Hdl|exact I]]).
  - (* PKey *)
    contradiction.
Qed.

End AtLine.

End Invariant.

Lemma inl_all_shift : forall src d b p a,
  inl_all (good (skipn d src)) (Node p a b) ->
  inl_all (good src) (Node (Shift.of_pos d p) a (Shift.of_block d b)).
Proof.
  intros src d.
  destruct (dn_shift src d) as [_ Hils].
  set (G := good (skipn d src)). set (G' := good src).
  assert (Hg : forall ils, G ils -> G' (Shift.of_inlines d ils)) by exact Hils.
  assert (Hgo : forall bs,
    (fix go (bs : blocks) : blocks :=
       match bs with
       | [] => []
       | Node p a x :: rest => Node (Shift.of_pos d p) a (Shift.of_block d x) :: go rest
       end) bs = Shift.of_blocks d bs)
    by (induction bs as [|[p a x] bs IH];
        [reflexivity|cbn [Shift.of_blocks]; rewrite IH; reflexivity]).
  (* The item traversals of `Shift.of_block`, as maps. *)
  set (ishift := fun n : node blocks =>
         match n with Node p a it => Node (Shift.of_pos d p) a (Shift.of_blocks d it) end).
  set (tshift := fun n : node (task_status * blocks) =>
         match n with
         | Node p a (c, it) => Node (Shift.of_pos d p) a (c, Shift.of_blocks d it)
         end).
  set (dshift := fun n : node (node inlines * node blocks) =>
         match n with
         | Node p a (t, Node q b it) =>
             Node (Shift.of_pos d p) a
               (Shift.inlines_node d t, Node (Shift.of_pos d q) b (Shift.of_blocks d it))
         end).
  intros b. apply (block_ind2
    (fun b => forall p a, inl_all G (Node p a b) ->
       inl_all G' (Node (Shift.of_pos d p) a (Shift.of_block d b)))
    (fun bs => Forall (inl_all G) bs -> Forall (inl_all G') (Shift.of_blocks d bs))
    (fun its => Forall (fun it => Forall (inl_all G) (node_contents it)) its ->
       Forall (fun it => Forall (inl_all G') (node_contents it)) (map ishift its))
    (fun its => Forall (fun it => G (node_contents (fst (node_contents it))) /\
                          Forall (inl_all G) (node_contents (snd (node_contents it)))) its ->
       Forall (fun it => G' (node_contents (fst (node_contents it))) /\
                         Forall (inl_all G') (node_contents (snd (node_contents it))))
         (map dshift its))
    (fun its => Forall (fun it => Forall (inl_all G) (snd (node_contents it))) its ->
       Forall (fun it => Forall (inl_all G') (snd (node_contents it))) (map tshift its)));
    intros; cbn [Shift.of_block]; rewrite ?Hgo.
  all: try (inversion H0; subst; constructor; auto; fail).
  all: try (inversion H; subst; constructor; auto; fail).
  (* A list's items are shifted by an inner fixpoint: name it as a map. *)
  all: try match goal with
    | |- context [OrderedList _ _ (?F ?xs)] =>
        let E := fresh "E" in
        assert (E : forall ys, F ys = map ishift ys)
          by (intros ys; induction ys as [|[p' a' it] ys IH]; [reflexivity|];
              cbn [map]; rewrite <- IH; unfold ishift; rewrite <- (Hgo it); reflexivity);
        rewrite E
    | |- context [BulletList _ _ (?F ?xs)] =>
        let E := fresh "E" in
        assert (E : forall ys, F ys = map ishift ys)
          by (intros ys; induction ys as [|[p' a' it] ys IH]; [reflexivity|];
              cbn [map]; rewrite <- IH; unfold ishift; rewrite <- (Hgo it); reflexivity);
        rewrite E
    | |- context [TaskList _ (?F ?xs)] =>
        let E := fresh "E" in
        assert (E : forall ys, F ys = map tshift ys)
          by (intros ys; induction ys as [|[p' a' [c it]] ys IH]; [reflexivity|];
              cbn [map]; rewrite <- IH; unfold tshift; rewrite <- (Hgo it); reflexivity);
        rewrite E
    | |- context [DefinitionList _ (?F ?xs)] =>
        let E := fresh "E" in
        assert (E : forall ys, F ys = map dshift ys)
          by (intros ys; induction ys as [|[p' a' [t [q' b' it]]] ys IH]; [reflexivity|];
              cbn [map]; rewrite <- IH; unfold dshift; rewrite <- (Hgo it); reflexivity);
        rewrite E
    end.
  all: try (inversion H0; subst; constructor; auto; fail).
  - inversion H as [| | | | | | | | | | |? ? ? ? Hcap Hrows| | | | |]; subst.
    constructor; [destruct caption; apply Hg; assumption|].
    rewrite Forall_map. refine (Forall_impl _ _ Hrows). intros [rp ra cs] Hr.
    cbn [Shift.row node_contents] in *.
    rewrite Forall_map. refine (Forall_impl _ _ Hr). intros [cp ca [ct al ils]] Hc.
    exact (Hg _ Hc).
  - destruct b0 as [p0 a0 x]. inversion H0; subst. constructor; [apply Hg; assumption|].
    assert (Hk : Forall (inl_all G') (Shift.of_blocks d [Node p0 a0 x]))
      by (apply H; constructor; auto).
    inversion Hk; assumption.
  - inversion H1; subst. cbn [Shift.of_blocks]. constructor; auto.
  - inversion H1; subst. cbn [map]. constructor; auto.
  - inversion H1 as [|? ? [Ht Hi] Hr]; subst. cbn [map fst snd] in *.
    constructor; [|auto]. cbn [dshift node_contents fst snd] in *.
    destruct term. split; [exact (Hg _ Ht)|auto].
  - inversion H1 as [|? ? Hi Hr]; subst. cbn [map snd] in *. constructor; auto.
Qed.

Lemma blocks_shift : forall src d bs,
  Forall (bgood (skipn d src)) bs -> Forall (bgood src) (Shift.of_blocks d bs).
Proof.
  intros src d bs H. induction H as [|[p a x] bs Hb _ IH]; [constructor|].
  cbn [Shift.of_blocks]. constructor; [exact (inl_all_shift src d x p a Hb)|exact IH].
Qed.

(*
The document
============
*)

Lemma skipn_cons_nth : forall (S : list string) n l rest,
  skipn n S = l :: rest -> n < length S /\ nth n S EmptyString = l.
Proof.
  induction S as [|x S IH]; intros n l rest H; [destruct n; discriminate|].
  destruct n as [|n]; cbn in H.
  - injection H as -> ->. cbn. split; [lia|reflexivity].
  - destruct (IH n l rest H) as [H1 H2]. cbn. split; [lia|exact H2].
Qed.

Lemma line_at_skipn : forall S base k,
  line_at (skipn base S) k = nth (base + k) S EmptyString.
Proof.
  intros S base k. unfold line_at. revert S k.
  induction base as [|base IH]; intros S k; [reflexivity|].
  destruct S as [|x S]; [destruct k; reflexivity|]. cbn [skipn]. apply IH.
Qed.

Section Document.
Context {K : bconfig}.
Hypothesis Hkeyed : bkeyed = false.
Variable L : list string.

Lemma cut_ok : forall ls p base,
  ls = skipn (base + pend_count p) L ->
  length (pend_lines p) = pend_count p ->
  Forall (bgood (skipn base L)) (pend_blocks p) ->
  st_ok (skipn base L) (pend_count p) (pend_state p) ->
  Forall (bgood L)
    (assemble base (fst (cut (@loc_step T K) ls p)
                    ++ close (@finish T K located_pos) (snd (cut (@loc_step T K) ls p)))).
Proof.
  induction ls as [|l rest IH]; intros p base Hls Hlen Hbs Hst.
  - cbn [cut fst snd app]. unfold close.
    destruct (pend_lines p) as [|x xs]; [constructor|].
    cbn [assemble]. rewrite app_nil_r. apply blocks_shift, Forall_app.
    split; [exact Hbs|exact (finish_ok _ _ _ Hst)].
  - destruct (skipn_cons_nth L _ l rest (eq_sym Hls)) as [Hlt Hnth].
    assert (Hk : @lix (LineIxAt (pend_count p)) < length (skipn base L))
      by (cbn; rewrite length_skipn; lia).
    assert (Hl : is_sfx l (line_at (skipn base L) (pend_count p)))
      by (rewrite line_at_skipn, Hnth; apply is_sfx_refl).
    assert (Hok : ok (skipn base L) (S (pend_count p))
                    (@loc_step T K (pend_count p) l (pend_state p)))
      by exact (@step_fuel_ok K (skipn base L) (LineIxAt (pend_count p)) Hk Hkeyed
                  (S (String.length l + pstate_depth (pend_state p))) 0 l (pend_state p)
                  Hl Hst).
    cbn [cut].
    destruct (@loc_step T K (pend_count p) l (pend_state p)) as [out st].
    destruct Hok as [Hout Hst']. cbn [fst snd] in Hout, Hst'.
    assert (Hbs' : Forall (bgood (skipn base L)) (pend_blocks p ++ out))
      by (apply Forall_app; split; assumption).
    assert (Hrest : rest = skipn (base + S (pend_count p)) L).
    { replace (base + S (pend_count p)) with (1 + (base + pend_count p)) by lia.
      rewrite <- skipn_skipn, <- Hls. reflexivity. }
    destruct (is_idle st).
    + specialize (IH fresh (base + S (pend_count p))).
      destruct (cut (@loc_step T K) rest fresh) as [cs p'].
      cbn [fst snd app assemble] in *. apply Forall_app. split.
      * apply blocks_shift, Hbs'.
      * cbn [piece_lines]. rewrite length_rev. cbn [length]. rewrite Hlen.
        apply IH; [|reflexivity|constructor|exact I].
        cbn [pend_count]. rewrite Nat.add_0_r. exact Hrest.
    + apply IH; cbn [pend_count pend_lines pend_blocks pend_state].
      * exact Hrest.
      * cbn [length]. rewrite Hlen. reflexivity.
      * exact Hbs'.
      * exact Hst'.
Qed.

End Document.

(** M2 and M3 over every document: every delimiter node the located parse
    builds, in any inline sequence at any depth, has a span that starts
    with its row's opener and ends with its closer as the source lines
    read them; a bare opener is followed by a byte that is not
    whitespace and a bare closer preceded by one; and at least one byte
    or line break lies between the two.  Keys are off. *)
Theorem parse_blocks_located_spans : forall `{K : bconfig} s,
  bkeyed = false ->
  Forall (bgood (split_lines s)) (@parse_blocks_located T K s).
Proof.
  intros K s Hk. unfold parse_blocks_located, loc_pieces, pieces.
  pose proof (@cut_ok K Hk (split_lines s) (split_lines s) fresh 0 eq_refl eq_refl
                (Forall_nil _) I) as H.
  destruct (cut (@loc_step T K) (split_lines s) fresh) as [cs p].
  exact H.
Qed.

End WithTable.
