(* ai-disclosure: autonomous *)

(** * Block structure does not depend on inline syntax

   The syntax reference: "block structure can be discerned prior to
   inline parsing and takes priority over inline structure".  Stated
   here as a projection: erase every inline, and what is left of the
   block tree is the same under every delimiter table
   (`block_shape_independent`).

   Keyed blocks are off.  Where a key's label ends is found by the
   inline scanner (`key_split`), so that extension breaks the rule on
   purpose.

   The proof is a simulation over `step_fuel`, with the shape of the
   state in place of the state, in the form of `Step.step_fuel_erase`:
   with keys off no transition reads an inline, so each branch closes by
   pushing the projection through the constructors it builds. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast Attributes Inline InlineLocated Marker Step.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.

Module Shape.

(*
The projection
==============
*)

Definition of_cell (c : cell) : cell :=
  match c with Cell ct al _ => Cell ct al [] end.

(* A node's payload shaped by `f`, its position dropped. *)
Definition shape {A : Type} (f : A -> A) (n : node A) : node A :=
  match n with Node _ a x => Node NoPos a (f x) end.

Definition clear {A : Type} (_ : list A) : list A := [].

Fixpoint of_block (b : block) : block :=
  let go := map (fun n : node block =>
              match n with Node _ a x => Node NoPos a (of_block x) end) in
  match b with
  | Para _ => Para []
  | Section bs => Section (go bs)
  | Heading lvl _ => Heading lvl []
  | BlockQuote bs => BlockQuote (go bs)
  | Div name bs => Div name (go bs)
  | OrderedList attrs sp items => OrderedList attrs sp (map (shape go) items)
  | BulletList sp items => BulletList sp (map (shape go) items)
  | TaskList sp items =>
      TaskList sp (map (shape (fun it => (fst it, go (snd it)))) items)
  | DefinitionList sp items =>
      DefinitionList sp
        (map (shape (fun it => (shape clear (fst it), shape go (snd it)))) items)
  | Table cap rows => Table (shape clear cap) (map (shape (map (shape of_cell))) rows)
  | FootnoteDef label bs => FootnoteDef label (go bs)
  | Ext_keyed _ (Node _ a x) => Ext_keyed [] (Node NoPos a (of_block x))
  | Ext_callout kind fold _ bs => Ext_callout kind fold [] (go bs)
  | x => x
  end.

Definition of_node (n : node block) : node block :=
  match n with Node _ a x => Node NoPos a (of_block x) end.

Definition of_blocks : blocks -> blocks := map of_node.

Ltac unfold_block :=
  cbn [of_block];
  change (map (fun n : node block =>
            match n with Node _ a x => Node NoPos a (of_block x) end))
    with of_blocks.

Lemma blocks_cons : forall p a b rest,
  of_blocks (Node p a b :: rest) = Node NoPos a (of_block b) :: of_blocks rest.
Proof. reflexivity. Qed.

Lemma blocks_app : forall xs ys,
  of_blocks (xs ++ ys) = (of_blocks xs ++ of_blocks ys)%list.
Proof. intros. apply map_app. Qed.

Lemma blocks_rev : forall xs, of_blocks (rev xs) = rev (of_blocks xs).
Proof. intros. apply map_rev. Qed.

Lemma of_cell_idem : forall c, of_cell (of_cell c) = of_cell c.
Proof. intros []; reflexivity. Qed.

(* Shaping twice is shaping once. *)
Local Lemma block_idem : forall b, of_block (of_block b) = of_block b.
Proof.
  set (dshape := shape (fun it : node inlines * node blocks =>
                          (shape clear (fst it), shape of_blocks (snd it)))).
  set (tshape := shape (fun it : task_status * blocks => (fst it, of_blocks (snd it)))).
  apply (block_ind2
    (fun b => of_block (of_block b) = of_block b)
    (fun bs => of_blocks (of_blocks bs) = of_blocks bs)
    (fun items => map (shape of_blocks) (map (shape of_blocks) items) =
                  map (shape of_blocks) items)
    (fun items => map dshape (map dshape items) = map dshape items)
    (fun items => map tshape (map tshape items) = map tshape items));
    intros; unfold_block; unfold_block; cbn [map fst snd shape] in *;
    repeat match goal with H : _ = _ |- _ => rewrite H; clear H end;
    try reflexivity.
  1-4: f_equal; exact H.
  - f_equal; [destruct caption; reflexivity|].
    rewrite map_map. apply map_ext. intros [p a r]. cbn [shape]. rewrite map_map.
    f_equal. apply map_ext. intros [q b c]. cbn [shape]. rewrite of_cell_idem.
    reflexivity.
  - destruct b as [q c x]. cbn [of_blocks map of_node] in H.
    injection H as H. cbn [of_block]. rewrite H. reflexivity.
  - cbn [of_blocks map of_node].
    change (map of_node (map of_node rest)) with (of_blocks (of_blocks rest)).
    change (map of_node rest) with (of_blocks rest).
    rewrite H0, H. reflexivity.
  - subst dshape. cbn [shape fst snd]. rewrite H. destruct term. reflexivity.
  - subst tshape. cbn [shape fst snd]. rewrite H. reflexivity.
Qed.

Lemma blocks_idem : forall bs, of_blocks (of_blocks bs) = of_blocks bs.
Proof.
  intros bs. unfold of_blocks. rewrite map_map. apply map_ext.
  intros [p a b]. cbn [of_node]. rewrite block_idem. reflexivity.
Qed.

(*
Assembly helpers
----------------
*)

Lemma blocks_set_pos : forall `{PosPolicy} p (n : node block) rest,
  of_blocks (set_pos p n :: rest) = of_blocks (n :: rest).
Proof.
  intros P p [q a b] rest. unfold set_pos. destruct (mkpos p); reflexivity.
Qed.

Lemma blocks_pos_head : forall `{PosPolicy} p (bs : blocks),
  of_blocks (pos_head p bs) = of_blocks bs.
Proof.
  intros P p bs. unfold pos_head. destruct (mkpos p); [reflexivity|].
  destruct bs as [|n rest]; [reflexivity|]. apply blocks_set_pos.
Qed.

Lemma blocks_add_roles_head : forall `{PosPolicy} rs (bs : blocks),
  of_blocks (add_roles_head rs bs) = of_blocks bs.
Proof.
  intros P rs bs. unfold add_roles_head, add_roles.
  destruct pos_records; [|reflexivity].
  destruct bs as [|[[|q] a x] rest]; reflexivity.
Qed.

Lemma shape_set_pos : forall `{PosPolicy} {A : Type} (f : A -> A) p (n : node A),
  shape f (set_pos p n) = shape f n.
Proof. intros P A f p [q a x]. unfold set_pos. destruct (mkpos p); reflexivity. Qed.

Local Lemma shape_set_each : forall `{PosPolicy} {A : Type} (f : A -> A) rs (ns : list (node A)),
  map (shape f) (set_each rs ns) = map (shape f) ns.
Proof.
  intros P A f rs. induction rs as [|r rs IH]; intros [|n ns]; try reflexivity.
  cbn [set_each map]. rewrite shape_set_pos, IH. reflexivity.
Qed.

(* Copying ranges onto parts writes only positions, which the shape
   drops. *)
Lemma blocks_set_parts : forall `{PosPolicy} ps (n : node block) rest,
  of_blocks (set_parts ps n :: rest) = of_blocks (n :: rest).
Proof.
  intros P ps [p a x] rest. unfold set_parts. destruct pos_records; [|reflexivity].
  rewrite !blocks_cons. do 2 f_equal.
  destruct ps as [rs|rs|cap rs], x; cbn [parts_onto]; try reflexivity;
    cbn [of_block]; rewrite ?shape_set_each; try reflexivity.
  - f_equal. revert items. induction rs as [|[[i t] d] rs IH];
      intros [|[q b [term def]] its]; try reflexivity.
    cbn [set_defs map]. rewrite shape_set_pos, IH. cbn [shape fst snd].
    rewrite !shape_set_pos. reflexivity.
  - f_equal; [destruct cap; [apply shape_set_pos|reflexivity]|].
    revert rows. induction rs as [|[r cs] rs IH]; intros [|[q b cells] rows];
      try reflexivity.
    cbn [set_rows map]. rewrite shape_set_pos, IH. cbn [shape].
    rewrite shape_set_each. reflexivity.
Qed.

Lemma blocks_decorate_head : forall pend bs,
  of_blocks (decorate_head pend bs) = decorate_head pend (of_blocks bs).
Proof. intros pend [|[p a x] rest]; reflexivity. Qed.

Local Lemma def_split_shape : forall bs,
  def_split (of_blocks bs) =
  option_map (fun r => ([] : inlines, of_blocks (snd r))) (def_split bs).
Proof.
  induction bs as [|[p a b] rest IH]; [reflexivity|].
  rewrite blocks_cons.
  destruct b; cbn [def_split of_block invisible_block]; try reflexivity.
  1-2: rewrite IH; destruct (def_split rest) as [[t more]|]; reflexivity.
  destruct b; reflexivity.
Qed.

Lemma def_items_shape : forall items,
  map (shape (fun it : node inlines * node blocks =>
                (shape clear (fst it), shape of_blocks (snd it)))) (def_items items) =
  map (shape (fun it : node inlines * node blocks =>
                (shape clear (fst it), shape of_blocks (snd it))))
    (def_items (map of_blocks items)).
Proof.
  intros items. unfold def_items. rewrite !map_map.
  apply map_ext. intros it. unfold def_node, def_item. rewrite def_split_shape.
  destruct (def_split it) as [[t rest]|]; cbn; rewrite ?blocks_idem; reflexivity.
Qed.

Lemma task_items_shape : forall checks items,
  map (shape (fun it : task_status * blocks => (fst it, of_blocks (snd it))))
    (task_items checks items) =
  map (shape (fun it : task_status * blocks => (fst it, of_blocks (snd it))))
    (task_items checks (map of_blocks items)).
Proof.
  intros checks items. revert checks.
  induction items as [|it items IH]; intros checks; [reflexivity|].
  destruct checks as [|c checks]; cbn [task_items map shape mk fst snd];
    rewrite blocks_idem, IH; reflexivity.
Qed.

(* Items the parser builds are bare nodes. *)
Lemma items_shape : forall items : list blocks,
  map (shape of_blocks) (map mk items) = map mk (map of_blocks items).
Proof. intros items. rewrite !map_map. reflexivity. Qed.

Local Lemma goitems_idem : forall items,
  map of_blocks (map of_blocks items) = map of_blocks items.
Proof. intros items. rewrite map_map. apply map_ext, blocks_idem. Qed.

(*
Parser states
-------------
*)

Definition of_list_state (ls : list_state) : list_state :=
  LSt (ls_indent ls) (ls_extent ls) (ls_item_extent ls) (ls_item_extents ls)
    (ls_styles ls) (ls_loose ls) (ls_blanks ls)
    (map of_blocks (ls_items ls)) (ls_check ls) (ls_checks ls).

Fixpoint state (st : pstate) : pstate :=
  match st with
  | PQuote range header done inner =>
      PQuote range header (of_blocks done) (state inner)
  | PDiv len cls range opener done inner =>
      PDiv len cls range opener (of_blocks done) (state inner)
  | PList ls done inner =>
      PList (of_list_state ls) (of_blocks done) (state inner)
  | PFoot range ind lbl done inner =>
      PFoot range ind lbl (of_blocks done) (state inner)
  | PPend pend specs inner => PPend pend specs (state inner)
  | PKey range lbl src inner => PKey range lbl src (state inner)
  | st => st
  end.

Definition result (r : blocks * pstate) : blocks * pstate :=
  (of_blocks (fst r), state (snd r)).

Lemma list_state_idem : forall ls,
  of_list_state (of_list_state ls) = of_list_state ls.
Proof. intros []. unfold of_list_state; cbn. rewrite goitems_idem. reflexivity. Qed.

Lemma state_idem : forall st, state (state st) = state st.
Proof.
  induction st; cbn [state]; rewrite ?IHst, ?blocks_idem, ?list_state_idem;
    reflexivity.
Qed.

End Shape.

(*
Decisions read no inline
========================

Every question `step_fuel` asks of a state has the same answer on its
shape, because none of them looks inside a closed block.
*)

Section Decisions.
Context {K : bconfig}.

Local Lemma lazy_ok_shape : forall st, lazy_ok (Shape.state st) = lazy_ok st.
Proof. induction st; cbn [Shape.state lazy_ok]; auto. Qed.

Local Lemma in_fence_shape : forall st, in_fence (Shape.state st) = in_fence st.
Proof. induction st; cbn [Shape.state in_fence]; auto. Qed.

Local Lemma blank_held_shape : forall st,
  blank_held (Shape.state st) = blank_held st.
Proof.
  induction st; cbn [Shape.state blank_held]; auto.
  rewrite IHst. destruct st; reflexivity.
Qed.

Local Lemma blank_absorbed_shape : forall st,
  blank_absorbed (Shape.state st) = blank_absorbed st.
Proof.
  induction st; cbn [Shape.state blank_absorbed]; auto.
  - apply blank_held_shape.
  - rewrite IHst. destruct st; reflexivity.
Qed.

Local Lemma keeps_line_shape : forall off l st,
  keeps_line off l (Shape.state st) = keeps_line off l st.
Proof.
  intros off l st. induction st; cbn [Shape.state keeps_line]; auto;
    rewrite lazy_ok_shape; reflexivity.
Qed.

Local Lemma is_idle_shape : forall st, is_idle (Shape.state st) = is_idle st.
Proof. intros []; reflexivity. Qed.

Local Lemma announces_end_shape : forall st,
  announces_end (Shape.state st) = announces_end st.
Proof. intros []; reflexivity. Qed.

Local Lemma key_claims_shape : forall l st,
  key_claims l (Shape.state st) = key_claims l st.
Proof.
  intros l st. induction st; cbn [Shape.state key_claims];
    rewrite ?IHst, ?is_idle_shape, ?announces_end_shape; reflexivity.
Qed.

Local Lemma list_takes_shape : forall ls off l st,
  list_takes (Shape.of_list_state ls) off l (Shape.state st) =
  list_takes ls off l st.
Proof.
  intros ls off l st. unfold list_takes. rewrite key_claims_shape.
  destruct ls. reflexivity.
Qed.

Local Lemma pstate_depth_shape : forall st,
  pstate_depth (Shape.state st) = pstate_depth st.
Proof. induction st; cbn [Shape.state pstate_depth]; auto. Qed.

End Decisions.

(*
State updates
-------------
*)

Local Lemma list_blank_shape : forall ls,
  Shape.of_list_state (list_blank ls) = list_blank (Shape.of_list_state ls).
Proof. intros []; reflexivity. Qed.

Local Lemma list_narrow_shape : forall ls ns,
  Shape.of_list_state (list_narrow ls ns) =
  list_narrow (Shape.of_list_state ls) ns.
Proof. intros [] ns; reflexivity. Qed.

Local Lemma list_content_shape : forall `{LI : LineIx} ls k kept,
  Shape.of_list_state (list_content ls k kept) =
  list_content (Shape.of_list_state ls) k kept.
Proof. intros LI [] k kept; destruct k; reflexivity. Qed.

Local Lemma list_next_shape : forall `{LI : LineIx} ls item chk l,
  Shape.of_list_state (list_next ls item chk l) =
  list_next (Shape.of_list_state ls) (Shape.of_blocks item) chk l.
Proof. intros LI [] item chk l. reflexivity. Qed.

Local Lemma feed_lazy_shape : forall `{LI : LineIx} l st,
  Shape.state (feed_lazy l st) = feed_lazy l (Shape.state st).
Proof.
  intros LI l st. induction st; cbn [feed_lazy Shape.state];
    rewrite ?IHst, ?list_content_shape; reflexivity.
Qed.

(*
Blocks built from inlines
-------------------------

The builders that read the delimiter table are the ones that make
inlines, and the shape drops what they make.
*)

Local Lemma of_cell_erase : forall c, Shape.of_cell (Erase.of_cell c) = Shape.of_cell c.
Proof. intros []; reflexivity. Qed.

Local Lemma head_of_shape : forall als r,
  map Shape.of_cell (head_of als r) = head_of als (map Shape.of_cell r).
Proof.
  intros als r. revert als.
  induction r as [|[ct al ils] r IH]; intros als; [reflexivity|].
  destruct als; cbn [head_of map Shape.of_cell]; rewrite IH; reflexivity.
Qed.

Local Lemma cells_of_shape : forall T T' ct als cs,
  map Shape.of_cell (@cells_of T ct als cs) =
  map Shape.of_cell (@cells_of T' ct als cs).
Proof.
  intros T T' ct als cs. revert als.
  induction cs as [|c cs IH]; intros als; [reflexivity|].
  destruct als; cbn [cells_of map Shape.of_cell]; rewrite IH; reflexivity.
Qed.

Local Lemma table_fold_shape : forall T T' rows als acc acc',
  map (map Shape.of_cell) acc = map (map Shape.of_cell) acc' ->
  map (map Shape.of_cell) (@table_fold T rows als acc) =
  map (map Shape.of_cell) (@table_fold T' rows als acc').
Proof.
  intros T T' rows. induction rows as [|r rows IH]; intros als acc acc' H.
  - cbn [table_fold]. rewrite !map_rev, H. reflexivity.
  - destruct r as [als'|cs]; cbn [table_fold]; apply IH.
    + destruct acc as [|row acc], acc' as [|row' acc']; try discriminate;
        [reflexivity|].
      cbn [map] in H |- *. injection H as Hr Hacc.
      rewrite !head_of_shape, Hr, Hacc. reflexivity.
    + cbn [map]. rewrite (cells_of_shape T T'), H. reflexivity.
Qed.

Local Lemma rows_erase : forall rows,
  map (map Shape.of_cell) (map Erase.row rows) = map (map Shape.of_cell) rows.
Proof.
  intros rows. rewrite map_map. apply map_ext. intros r.
  unfold Erase.row. rewrite map_map. apply map_ext, of_cell_erase.
Qed.

Local Lemma table_block_shape : forall T T' P rows c rest rest',
  Shape.of_blocks rest = Shape.of_blocks rest' ->
  Shape.of_blocks (@table_block T P rows c :: rest) =
  Shape.of_blocks (@table_block T' P rows c :: rest').
Proof.
  intros T T' P rows c rest rest' H. unfold table_block, mk.
  rewrite !Shape.blocks_cons, H. cbn [Shape.of_block]. do 3 f_equal.
  rewrite !map_map. cbn [Shape.shape].
  assert (Hg : forall X : list (list cell),
    map (fun x : list cell => Node NoPos [] (map (Shape.shape Shape.of_cell)
           (map (fun x0 : cell => Node NoPos [] x0) x))) X =
    map (fun x => Node NoPos [] (map (fun x0 : cell => Node NoPos [] x0) x))
      (map (map Shape.of_cell) X)).
  { intros X. rewrite map_map. apply map_ext. intros x. rewrite !map_map. reflexivity. }
  rewrite !Hg. f_equal.
  destruct pos_records.
  - rewrite <- (rows_erase (Step.table_fold_located _ _ _ _)),
      <- (rows_erase (@Step.table_fold_located T' P _ _ _ _)).
    rewrite !(@Step.StateErase.of_table_fold_located).
    apply table_fold_shape. reflexivity.
  - apply table_fold_shape. reflexivity.
Qed.

Local Lemma list_block_shape : forall `{K : bconfig} ls last,
  Shape.of_blocks [list_block ls last] =
  Shape.of_blocks [list_block (Shape.of_list_state ls) (Shape.of_blocks last)].
Proof.
  intros K ls last.
  destruct ls as [li le lie lies styles loose blanks items check checks].
  unfold list_block, styles_list_checked, Shape.of_list_state.
  cbn [ls_styles ls_loose ls_check ls_checks ls_items].
  change (Shape.of_blocks last :: map Shape.of_blocks items)
    with (map Shape.of_blocks (last :: items)).
  rewrite <- map_rev.
  destruct styles as [|[sty start] styles]; [|destruct sty];
    cbn [styles_list mk Shape.of_blocks map Shape.of_node]; Shape.unfold_block;
    rewrite ?Shape.items_shape, ?Shape.goitems_idem; try reflexivity.
  - destruct (_ && bdeflists)%bool; cbn [mk Shape.of_node]; Shape.unfold_block;
      rewrite ?Shape.items_shape, ?Shape.goitems_idem; [|reflexivity].
    do 3 f_equal. apply Shape.def_items_shape.
  - do 3 f_equal. apply Shape.task_items_shape.
Qed.

(*
Closing a state
---------------
*)

Local Lemma finish_shape : forall T T' `{K : bconfig} `{P : PosPolicy} st,
  Shape.of_blocks (@finish T K P st) =
  Shape.of_blocks (@finish T' K P (Shape.state st)).
Proof.
  intros T T' K P st.
  induction st; cbn [finish Shape.state];
    rewrite ?Shape.blocks_set_pos, ?Shape.blocks_set_parts; try reflexivity.
  - destruct cur; [reflexivity|]. rewrite !Shape.blocks_set_pos. reflexivity.
  - destruct header as [[[k f] t]|]; unfold quote_block, mk;
      rewrite !Shape.blocks_cons; Shape.unfold_block;
      rewrite !Shape.blocks_app, !Shape.blocks_rev, Shape.blocks_idem, IHst;
      reflexivity.
  - unfold div_block. destruct bdiv_names; [|destruct (String.eqb cls EmptyString)]; unfold mk;
      rewrite !Shape.blocks_cons; Shape.unfold_block;
      rewrite !Shape.blocks_app, !Shape.blocks_rev, Shape.blocks_idem, IHst;
      reflexivity.
  - rewrite list_block_shape, Shape.blocks_app, Shape.blocks_rev, IHst.
    symmetry.
    rewrite list_block_shape, Shape.list_state_idem, Shape.blocks_app,
      Shape.blocks_rev, Shape.blocks_idem.
    reflexivity.
  - destruct (ap_done ap); [reflexivity|].
    rewrite !Shape.blocks_add_roles_head, !Shape.blocks_decorate_head.
    unfold finish_para_recover. destruct slices; [reflexivity|].
    rewrite !Shape.blocks_set_pos. reflexivity.
  - unfold foot_block, mk. rewrite !Shape.blocks_cons; Shape.unfold_block;
      rewrite !Shape.blocks_app, !Shape.blocks_rev, Shape.blocks_idem, IHst;
      reflexivity.
  - apply table_block_shape. reflexivity.
  - rewrite !Shape.blocks_add_roles_head, !Shape.blocks_decorate_head, IHst.
    reflexivity.
  - (* a key retracts exactly when the state under it closed to nothing *)
    rewrite !Shape.blocks_pos_head.
    destruct (@finish T K P st) as [|[p a b] rest] eqn:E;
      destruct (@finish T' K P (Shape.state st)) as [|[p' a' b'] rest'] eqn:E';
      try discriminate; cbn [key_close]; [reflexivity|].
    unfold mk. rewrite !Shape.blocks_cons in IHst |- *.
    injection IHst as Ha Hb Hrest. cbn [Shape.of_block].
    rewrite Ha, Hb, Hrest. reflexivity.
Qed.

(*
Transition results
------------------
*)

Local Lemma close_reopen_shape : forall T T' `{K : bconfig} `{P : PosPolicy} st r r',
  Shape.result r = Shape.result r' ->
  Shape.result (@close_reopen T K P st r) =
  Shape.result (@close_reopen T' K P (Shape.state st) r').
Proof.
  intros T T' K P st [bs s] [bs' s'] H. unfold Shape.result in *.
  cbn [fst snd] in H. injection H as Hbs Hs.
  unfold close_reopen. cbn [fst snd].
  rewrite !Shape.blocks_app, (finish_shape T T'), Hbs, Hs. reflexivity.
Qed.

Local Lemma pend_result_shape : forall `{P : PosPolicy} pend specs r r',
  Shape.result r = Shape.result r' ->
  Shape.result (pend_result pend specs r) = Shape.result (pend_result pend specs r').
Proof.
  intros P pend specs [bs s] [bs' s'] H. unfold Shape.result in *.
  cbn [fst snd] in H. injection H as Hbs Hs.
  destruct bs as [|b bs], bs' as [|b' bs']; try discriminate;
    unfold pend_result; cbn [fst snd Shape.state]; rewrite ?Hs; [reflexivity|].
  rewrite !Shape.blocks_add_roles_head, !Shape.blocks_decorate_head, Hbs.
  reflexivity.
Qed.

Local Lemma key_result_shape : forall T T' `{P : PosPolicy} range lbl src r r',
  Shape.result r = Shape.result r' ->
  Shape.result (@key_result T P range lbl src r) =
  Shape.result (@key_result T' P range lbl src r').
Proof.
  intros T T' P range lbl src [bs s] [bs' s'] H. unfold Shape.result in *.
  cbn [fst snd] in H. injection H as Hbs Hs.
  destruct bs as [|[p a b] rest], bs' as [|[p' a' b'] rest']; try discriminate;
    unfold key_result; cbn [fst snd Shape.state]; rewrite ?Hs; [reflexivity|].
  rewrite !Shape.blocks_pos_head. cbn [key_close]. unfold mk.
  rewrite !Shape.blocks_cons in Hbs |- *. injection Hbs as Ha Hb Hrest.
  cbn [Shape.of_block]. rewrite Ha, Hb, Hrest. reflexivity.
Qed.

(* An opener reads no table, except that a key's split point is found by
   the inline scanner (`key_split`): that is what the keyed setting is,
   and why it is off here. *)
Local Lemma open_kind_shape :
  forall T T' `{LI : LineIx} `{P : PosPolicy} `{K : bconfig} l k,
  bkeyed = false ->
  @open_kind T LI P K l k = @open_kind T' LI P K l k.
Proof.
  intros T T' LI P K l k Hk. destruct k; try reflexivity.
  unfold open_kind, open_text. rewrite Hk. reflexivity.
Qed.

Local Lemma open_line_shape :
  forall T T' `{K : bconfig} `{LI : LineIx} `{P : PosPolicy} dl ds ind l k,
  bkeyed = false ->
  (forall rest, Shape.result (dl rest) = Shape.result (ds rest)) ->
  Shape.result (@open_line T K LI P dl ind l k) =
  Shape.result (@open_line T' K LI P ds ind l k).
Proof.
  intros T T' K LI P dl ds ind l k Hk H.
  destruct k; cbn [open_line];
    try (rewrite (open_kind_shape T T' _ _ Hk); reflexivity);
    try reflexivity.
  - destruct (quote_header rest) as [[[kind fold] title]|]; [reflexivity|].
    specialize (H rest). destruct (dl rest) as [bs s], (ds rest) as [bs' s'].
    unfold Shape.result in *. cbn [fst snd] in H. injection H as Hbs Hs.
    unfold open_quote. cbn [fst snd Shape.state].
    rewrite !Shape.blocks_rev, Hbs, Hs. reflexivity.
  - specialize (H (configured_list_rest chk rest)).
    destruct (dl _) as [bs s], (ds _) as [bs' s'].
    unfold Shape.result in *. cbn [fst snd] in H. injection H as Hbs Hs.
    unfold open_list. cbn [fst snd Shape.state].
    rewrite !Shape.blocks_rev, Hbs, Hs. reflexivity.
  - specialize (H rest). destruct (dl rest) as [bs s], (ds rest) as [bs' s'].
    unfold Shape.result in *. cbn [fst snd] in H. injection H as Hbs Hs.
    unfold open_foot. destruct bfootnotes; [|reflexivity].
    cbn [fst snd Shape.state]. rewrite !Shape.blocks_rev, Hbs, Hs. reflexivity.
Qed.

(* Two results with the same shape, taken apart. *)
Ltac split_same H :=
  match type of H with
  | Shape.result ?a = Shape.result ?b =>
      let bs := fresh "bs" in let s := fresh "s" in
      let bs' := fresh "bs" in let s' := fresh "s" in
      destruct a as [bs s], b as [bs' s'];
      unfold Shape.result in H; cbn [fst snd] in H;
      let Hbs := fresh "Hbs" in let Hs := fresh "Hs" in
      injection H as Hbs Hs
  end.

(*
The transition
==============
*)

Local Lemma step_fuel_shape :
  forall T T' `{K : bconfig} `{LI : LineIx} `{P : PosPolicy},
  bkeyed = false ->
  forall n off l st,
  Shape.result (@step_fuel T K LI P n off l st) =
  Shape.result (@step_fuel T' K LI P n off l (Shape.state st)).
Proof.
  intros T T' K LI P Hk n. induction n as [|n IH]; intros off l st.
  { unfold Shape.result; cbn [step_fuel fst snd].
    rewrite Shape.state_idem. reflexivity. }
  (* The one recursion, at the state every descent starts from. *)
  assert (Hd : forall rest,
    Shape.result (@step_fuel T K LI P n (off + consumed l rest) rest (PPara []))
    = Shape.result (@step_fuel T' K LI P n (off + consumed l rest) rest (PPara [])))
    by (intros rest; apply (IH (off + consumed l rest) rest (PPara []))).
  destruct st; cbn [step_fuel Shape.state].
  - (* PPara *)
    destruct cur as [|c cur']; [apply open_line_shape; assumption|].
    destruct (bunderline_of l) as [lvl|].
    { unfold Shape.result; cbn [fst snd]. rewrite !Shape.blocks_set_pos.
      reflexivity. }
    destruct (classify l).
    all: try (apply (close_reopen_shape T T' (PPara (c :: cur')));
              rewrite (open_kind_shape T T' _ _ Hk); reflexivity).
    all: destruct (binterrupt _);
      [ apply (close_reopen_shape T T' (PPara (c :: cur')));
        apply open_line_shape; assumption
      | reflexivity ].
  - (* PHeading *)
    destruct (classify l);
      try (apply (close_reopen_shape T T' (PHeading level range cur));
           apply open_line_shape; assumption);
      try (destruct bheading_continues; [try destruct (Nat.eqb _ _)|];
           try reflexivity;
           apply (close_reopen_shape T T' (PHeading level range cur));
           rewrite (open_kind_shape T T' _ _ Hk); reflexivity).
  - (* PFence *)
    destruct (fence_close f l); [|reflexivity].
    unfold Shape.result; cbn [fst snd]. rewrite !Shape.blocks_set_pos.
    reflexivity.
  - (* PQuote *)
    destruct (classify l) eqn:E; cbn [is_lazy];
      try (apply (close_reopen_shape T T' (PQuote range header done st));
           apply open_line_shape; assumption).
    + pose proof (IH (off + consumed l rest) rest st) as H. split_same H.
      unfold Shape.result; cbn [fst snd Shape.state].
      rewrite !Shape.blocks_app, !Shape.blocks_rev, Hbs, Shape.blocks_idem, Hs.
      reflexivity.
    + rewrite lazy_ok_shape. destruct (lazy_ok st).
      * unfold Shape.result; cbn [fst snd Shape.state].
        rewrite !feed_lazy_shape, Shape.blocks_idem, Shape.state_idem.
        reflexivity.
      * apply (close_reopen_shape T T' (PQuote range header done st)).
        apply open_line_shape; assumption.
  - (* PDiv *)
    rewrite in_fence_shape.
    destruct (negb (in_fence st) && div_close len l)%bool.
    + unfold Shape.result; cbn [fst snd]. rewrite !Shape.blocks_set_pos.
      unfold div_block. destruct bdiv_names; [|destruct (String.eqb cls EmptyString)]; unfold mk;
        rewrite !Shape.blocks_cons; Shape.unfold_block;
        rewrite !Shape.blocks_app, !Shape.blocks_rev, Shape.blocks_idem,
          (finish_shape T T');
        reflexivity.
    + pose proof (IH off l st) as H. split_same H.
      unfold Shape.result; cbn [fst snd Shape.state].
      rewrite !Shape.blocks_app, !Shape.blocks_rev, Hbs, Shape.blocks_idem, Hs.
      reflexivity.
  - (* PList.  Every kind but a blank first asks whether the item takes
       the line; what is left is the blank, a sibling marker and a lazy
       line. *)
    destruct (classify l) eqn:E.
    all: try (rewrite list_takes_shape; destruct (list_takes ls off l st)).
    all: try (pose proof (IH off l st) as H; split_same H;
         unfold Shape.result; cbn [fst snd Shape.state];
         rewrite ?list_content_shape, ?keeps_line_shape, ?Shape.list_state_idem,
           !Shape.blocks_app, !Shape.blocks_rev, Hbs, Shape.blocks_idem, Hs;
         reflexivity).
    all: try (cbn [is_lazy];
              apply (close_reopen_shape T T' (PList ls done st));
              apply open_line_shape; assumption).
    + rewrite blank_absorbed_shape. pose proof (IH off l st) as H. split_same H.
      unfold Shape.result; cbn [fst snd Shape.state].
      rewrite !Shape.blocks_app, !Shape.blocks_rev, Hbs, Shape.blocks_idem, Hs.
      destruct (blank_absorbed st);
        rewrite ?list_blank_shape, Shape.list_state_idem; reflexivity.
    + cbn [ls_styles Shape.of_list_state].
      destruct (narrow (ls_styles ls) (configured_list_styles sty chk))
        as [|p l0].
      { apply (close_reopen_shape T T' (PList ls done st)).
        apply open_line_shape; assumption. }
      pose proof (Hd (configured_list_rest chk rest)) as H. split_same H.
      unfold Shape.result; cbn [fst snd Shape.state].
      rewrite !list_next_shape, !list_narrow_shape, Shape.list_state_idem,
        !Shape.blocks_rev, Hbs, Hs, !Shape.blocks_app, !Shape.blocks_rev,
        (finish_shape T T'), Shape.blocks_idem.
      reflexivity.
    + cbn [is_lazy]. rewrite lazy_ok_shape. destruct (lazy_ok st).
      * unfold Shape.result; cbn [fst snd Shape.state].
        rewrite !list_content_shape, !feed_lazy_shape, Shape.list_state_idem,
          Shape.blocks_idem, Shape.state_idem.
        reflexivity.
      * apply (close_reopen_shape T T' (PList ls done st)).
        apply open_line_shape; assumption.
  - (* PAttr *)
    destruct (ap_done ap).
    + apply (IH off l (PPend _ _ (PPara []))).
    + destruct (Nat.ltb ind (off + indent_of l));
        [destruct (ap_failed _)|destruct (is_blank l)];
        try reflexivity;
        apply pend_result_shape; apply (IH off l (para_recover _ _)).
  - (* PParaOff *)
    destruct (bunderline_of l) as [lvl|].
    { unfold Shape.result; cbn [fst snd]. rewrite !Shape.blocks_set_pos.
      reflexivity. }
    destruct (classify l).
    all: try (apply (close_reopen_shape T T' (PParaOff k cur));
              rewrite (open_kind_shape T T' _ _ Hk); reflexivity).
    all: destruct (binterrupt _);
      [ apply (close_reopen_shape T T' (PParaOff k cur));
        apply open_line_shape; assumption
      | reflexivity ].
  - (* PRef *)
    destruct (if Nat.ltb ind (off + indent_of l) then ref_cont l else None);
      [reflexivity|].
    pose proof (IH off l (PPara [])) as H. cbn [Shape.state] in H. split_same H.
    unfold Shape.result; cbn [fst snd]. rewrite !Shape.blocks_set_pos.
    unfold ref_block, mk. rewrite !Shape.blocks_cons, Hbs, Hs. reflexivity.
  - (* PFoot *)
    destruct (is_blank l); [|destruct (Nat.ltb ind (off + indent_of l))].
    1-2: pose proof (IH off l st) as H; split_same H;
      unfold Shape.result; cbn [fst snd Shape.state];
      rewrite !Shape.blocks_app, !Shape.blocks_rev, Hbs, Shape.blocks_idem, Hs;
      reflexivity.
    unfold is_lazy. rewrite lazy_ok_shape.
    destruct (match classify l with KText => lazy_ok st | _ => false end).
    + unfold Shape.result; cbn [fst snd Shape.state].
      rewrite !feed_lazy_shape, Shape.blocks_idem, Shape.state_idem.
      reflexivity.
    + pose proof (IH off l (PPara [])) as H. cbn [Shape.state] in H.
      split_same H.
      unfold Shape.result; cbn [fst snd]. rewrite !Shape.blocks_set_pos.
      unfold foot_block, mk. rewrite !Shape.blocks_cons, Hbs, Hs.
      Shape.unfold_block.
      rewrite !Shape.blocks_app, !Shape.blocks_rev, Shape.blocks_idem,
        (finish_shape T T').
      reflexivity.
  - (* PTable: the caption's inlines are read only when the table closes,
       and the shape drops them there *)
    pose proof (IH off l (PPara [])) as H. cbn [Shape.state] in H.
    destruct cap as [parts|parts|parts start lines].
    3: { destruct (is_blank l); [|reflexivity].
         unfold Shape.result; cbn [fst snd].
         rewrite !Shape.blocks_set_pos, !Shape.blocks_set_parts.
         f_equal. apply table_block_shape. reflexivity. }
    all: destruct (caption_open l) as [crest|]; [reflexivity|].
    all: destruct (is_blank l); [reflexivity|].
    all: destruct (classify l); try reflexivity.
    all: split_same H; unfold Shape.result; cbn [fst snd];
      rewrite !Shape.blocks_set_pos, !Shape.blocks_set_parts, Hs; f_equal;
      apply table_block_shape; exact Hbs.
  - (* PPend *)
    rewrite is_idle_shape.
    destruct (classify l); try (apply pend_result_shape; apply IH).
    all: destruct (is_idle st); [reflexivity|].
    all: apply pend_result_shape; apply IH.
  - (* PKey *)
    rewrite is_idle_shape.
    destruct (is_blank l && is_idle st)%bool; [reflexivity|].
    apply key_result_shape. apply IH.
Qed.

Local Lemma step_shape :
  forall T T' `{K : bconfig} `{LI : LineIx} `{P : PosPolicy},
  bkeyed = false ->
  forall l st,
  Shape.result (@step T K LI P l st) =
  Shape.result (@step T' K LI P l (Shape.state st)).
Proof.
  intros T T' K LI P Hk l st. unfold step. rewrite pstate_depth_shape.
  apply step_fuel_shape, Hk.
Qed.

Local Lemma parse_lines_shape :
  forall `{K : bconfig} `{LI : LineIx} `{P : PosPolicy},
  bkeyed = false ->
  forall lines T T' st,
  Shape.of_blocks (@parse_lines T K LI P lines st) =
  Shape.of_blocks (@parse_lines T' K LI P lines (Shape.state st)).
Proof.
  intros K LI P Hk lines.
  induction lines as [|l rest IH]; intros T T' st.
  - apply finish_shape.
  - cbn [parse_lines].
    pose proof (step_shape T T' Hk l st) as H. split_same H.
    rewrite !Shape.blocks_app, Hbs, (IH T T' s), (IH T' T' s0), Hs.
    reflexivity.
Qed.

(*
The theorem
===========
*)

(** Block structure, read with every inline erased, is the same
    under any two delimiter tables.  The keyed setting is the one block
    setting that asks the inline scanner a question (where a key's label
    ends), so it is off; every other block setting is free. *)
Theorem block_shape_independent :
  forall T T' `{K : bconfig} `{LI : LineIx} `{P : PosPolicy} s,
  bkeyed = false ->
  Shape.of_blocks (@parse_blocks T K LI P s) =
  Shape.of_blocks (@parse_blocks T' K LI P s).
Proof.
  intros T T' K LI P s Hk. unfold parse_blocks.
  apply (parse_lines_shape Hk _ T T' (PPara [])).
Qed.
