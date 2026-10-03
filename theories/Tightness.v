(* ai-disclosure: ai-generated *)

(** * List tightness, as the syntax reference states it

   "A list is classed as *tight* if it does not contain blank lines
   between items, or between blocks inside an item.  Blank lines at the
   start or end of a list do not count against tightness."

   `ListUniformity.item_loose` and `seps_loosen` decide tightness by
   running the parser's own scan.  This file states the rule without the
   scan, on the parses of the item's lines, and proves that the parser
   loosens a list only for a blank the rule counts.  The converse is
   proved for a blank between items (`separates_after_loosens`); for a
   blank inside an item it is open.

   "Between two blocks" has no source positions to lean on, so it is said
   with parses: cutting the item's lines at the blank and parsing the two
   halves gives the whole's blocks, and a paragraph line written after
   the blank would start a block of its own.  The first catches a blank
   followed by a line that continues something (a footnote's indented
   paragraph, a table's caption); the second a blank inside a block that
   is still open (a div or code block whose closer comes later).

   The blank after an item is between items unless it is text of the
   item's last block (a line of an open code block) or ends a nested
   list.  A block still open there ends with the item, before the blank,
   so an open div does not hold it (`djotjs-divergences.md`,
   2026-09-30).

   The reference's exemption for the start and end of a list is read as
   applying to a nested list: a blank directly before a nested list
   inside an item (its `- two` / blank / `  - sub` example), and a blank
   directly after one ends (djot.js's `lists.test` 242 and 308).  "Ends"
   looks through a footnote and a keyed block to their last block, since
   those stay open across a blank and the list inside them ends there. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast Attributes Inline Step Uniformity ListUniformity.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
The rule
========
*)

(** Does this block end in a list?  A list does, and so do a footnote and
    a keyed block whose last block does.  On the payload, as `Wf`'s
    recursions are, so the nested fix passes the guard. *)
Fixpoint ends_in_list_b (x : block) : bool :=
  match x with
  | OrderedList _ _ _ | BulletList _ _ | TaskList _ _ | DefinitionList _ _ => true
  | FootnoteDef _ bs =>
      (fix go (bs : list (node block)) : bool :=
         match bs with
         | [] => false
         | [Node _ _ y] => ends_in_list_b y
         | _ :: rest => go rest
         end) bs
  | Ext_keyed _ (Node _ _ y) => ends_in_list_b y
  | _ => false
  end.

Definition ends_in_list (b : node block) : bool := ends_in_list_b (node_contents b).

(** Does a run of blocks end in a list? *)
Definition ends_list (bs : blocks) : bool := last (map ends_in_list bs) false.

Definition opens_list (l : string) : bool :=
  match classify l with KList _ _ _ _ => true | _ => false end.

(** A blank after `pre` closes everything `pre` opened: a paragraph line
    written after it would start a block of its own. *)
Definition closes_at (pre : list string) : Prop :=
  parse_lines (pre ++ [""; "x"]) (PPara [])
  = (parse_lines pre (PPara []) ++ parse_lines ["x"] (PPara []))%list.

(** The blank at index `i` of an item's lines lies between two of the
    item's blocks, and not directly after a nested list ends or directly
    before one starts. *)
Definition separates (L : list string) (i : nat) : Prop :=
  let pre := firstn i L in
  let post := skipn (S i) L in
  is_blank (nth i L "") = true
  /\ existsb nonblank pre = true
  /\ closes_at pre
  /\ parse_lines L (PPara []) = (parse_lines pre (PPara []) ++ parse_lines post (PPara []))%list
  /\ ends_list (parse_lines pre (PPara [])) = false
  /\ (exists l, find nonblank post = Some l /\ opens_list l = false).

(** The blank after an item separates it from the next one: it leaves the
    item's blocks as they were, so it is text of none of them, and the
    last of them is not a nested list.  A block still open at the blank
    ends with the item, at the line before the blank, so an unclosed div
    does not hold the blank as `closes_at` would say. *)
Definition separates_after (L : list string) : Prop :=
  parse_lines (L ++ [""]) (PPara []) = parse_lines L (PPara [])
  /\ ends_list (parse_lines L (PPara [])) = false.

(*
Proof
=====
*)

(*
Ending in a list
----------------
*)

Lemma ends_in_list_foot : forall p a lbl bs,
  ends_in_list (Node p a (FootnoteDef lbl bs)) = ends_list bs.
Proof.
  intros p a lbl bs. unfold ends_in_list, ends_list. cbn [node_contents ends_in_list_b].
  induction bs as [|[q b x] rest IH]; [reflexivity|].
  destruct rest as [|c' rest']; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma ends_list_app : forall xs ys : blocks,
  ys <> [] -> ends_list (xs ++ ys)%list = ends_list ys.
Proof.
  intros xs ys H. unfold ends_list. rewrite map_app.
  destruct ys as [|y ys]; [congruence|].
  cbn [map]. induction xs as [|x xs IH]; [reflexivity|].
  cbn [map app]. rewrite <- IH. cbn [last].
  destruct (map ends_in_list xs ++ ends_in_list y :: map ends_in_list ys)%list eqn:E;
    [destruct (map ends_in_list xs); discriminate|reflexivity].
Qed.

(* `ends_list` reads each block only through `ends_in_list`. *)
Lemma ends_list_map : forall xs ys : blocks,
  map ends_in_list xs = map ends_in_list ys -> ends_list xs = ends_list ys.
Proof. intros xs ys H. unfold ends_list. rewrite H. reflexivity. Qed.

(*
The invariant
-------------

A blank loosens a list only when the item's state does not absorb it,
and the rule needs the item's blocks so far not to end in a list at that
point.  `tail_ok E st` says so of blocks `E` already emitted and the
state `st` still open.  It is kept through every line of a run; the
three states a blank can rest inside without closing (a footnote,
pending attributes, a key) carry what it needs of their own contents in
`state_ok`.
*)

Definition tail_ok (E : blocks) (st : pstate) : Prop :=
  blank_absorbed st = false -> ends_list (E ++ finish st)%list = false.

(* What one line emits, together with the state it leaves, ends in no
   list, whatever came before. *)
Definition tail_new (bs : blocks) (st : pstate) : Prop :=
  blank_absorbed st = false ->
  (bs ++ finish st)%list <> [] /\ ends_list (bs ++ finish st)%list = false.

Fixpoint state_ok (st : pstate) : Prop :=
  match st with
  | PFoot _ _ _ done inner => state_ok inner /\ tail_ok (rev done) inner
  (* Pending attributes never wait over an idle state: a blank drops
     them.  This is `blank_safe`'s condition on them too. *)
  | PPend _ _ inner => state_ok inner /\ is_idle inner = false
  | PKey _ _ _ inner => state_ok inner
  (* What a div or a list item holds meets a blank that reaches it. *)
  | PDiv _ _ _ _ _ inner | PList _ _ inner => state_ok inner
  | _ => True
  end.

(* What `step` keeps, line by line. *)
Definition step_ok (st : pstate) (l : string) (r : blocks * pstate) : Prop :=
  state_ok (snd r)
  /\ (forall E, tail_ok E st -> tail_ok (E ++ fst r)%list (snd r))
  /\ (is_blank l = false -> tail_new (fst r) (snd r))
  /\ (is_idle st = false -> fst r = [] -> is_idle (snd r) = false).

(* A result that needs nothing from the state before it: most of them. *)
Definition fresh (bs : blocks) (st : pstate) : Prop :=
  state_ok st /\ tail_new bs st /\ (bs = [] -> is_idle st = false).

Lemma tail_new_ok : forall E bs st,
  tail_new bs st -> tail_ok (E ++ bs)%list st.
Proof.
  intros E bs st H Ha. destruct (H Ha) as [Hne Hend].
  rewrite <- app_assoc, ends_list_app by exact Hne. exact Hend.
Qed.

Lemma fresh_step_ok : forall st l r,
  fresh (fst r) (snd r) -> step_ok st l r.
Proof.
  intros st l r [Hs [Hn Hi]]. split; [exact Hs|]. split; [|split].
  - intros E _. apply tail_new_ok. exact Hn.
  - intros _. exact Hn.
  - intros _. exact Hi.
Qed.

(* Emitting in front keeps a result fresh: the last block is still the
   result's own. *)
Lemma fresh_prefix : forall pre bs st,
  fresh bs st -> fresh (pre ++ bs)%list st.
Proof.
  intros pre bs st [Hs [Hn Hi]]. split; [exact Hs|]. split.
  - intros Ha. destruct (Hn Ha) as [Hne Hend]. rewrite <- app_assoc. split.
    + intros H. apply app_eq_nil in H as [_ H]. exact (Hne H).
    + rewrite ends_list_app by exact Hne. exact Hend.
  - intros H. apply app_eq_nil in H as [_ H]. exact (Hi H).
Qed.

Lemma fresh_absorbing : forall bs st,
  blank_absorbed st = true -> state_ok st -> fresh bs st.
Proof.
  intros bs st Ha Hs. split; [exact Hs|]. split.
  - intros H. congruence.
  - intros _. destruct st as [[|]| | | | | | | | | | | |]; try reflexivity.
    discriminate Ha.
Qed.

Lemma fresh_emit : forall bs,
  bs <> [] -> ends_list bs = false -> fresh bs (PPara []).
Proof.
  intros bs Hne Hend. split; [exact I|]. split.
  - intros _. cbn [finish]. rewrite app_nil_r. split; assumption.
  - intros H. congruence.
Qed.

(* A state that finishes to one block that is not a list. *)
Lemma fresh_single : forall bs st b,
  state_ok st -> is_idle st = false -> finish st = [b] -> ends_in_list b = false ->
  fresh bs st.
Proof.
  intros bs st b Hs Hi Hf Hb. split; [exact Hs|]. split.
  - intros _. rewrite Hf. split.
    + intros H. apply app_eq_nil in H as [_ H]. discriminate H.
    + rewrite ends_list_app by discriminate. exact Hb.
  - intros _. exact Hi.
Qed.

(*
What the wrappers do to the last block
--------------------------------------

Pending attributes and a key touch only the first block they get, and
neither changes whether it is a list.
*)

Lemma decorate_head_ends : forall pend bs,
  map ends_in_list (decorate_head pend bs) = map ends_in_list bs.
Proof. intros pend [|[p a x] bs]; reflexivity. Qed.

Lemma key_close_ends : forall start lbl src bs,
  bs <> [] -> map ends_in_list (key_close start lbl src bs) = map ends_in_list bs.
Proof. intros start lbl src [|[p a x] bs] H; [congruence|reflexivity]. Qed.

Lemma key_close_ne : forall start lbl src bs, key_close start lbl src bs <> [].
Proof. intros start lbl src [|b bs]; discriminate. Qed.

Lemma ends_list_key_close : forall start lbl src bs,
  ends_list (key_close start lbl src bs) = ends_list bs.
Proof.
  intros start lbl src [|b bs]; [reflexivity|].
  apply ends_list_map, key_close_ends. discriminate.
Qed.

Lemma finish_pend_ends : forall pend specs st,
  map ends_in_list (finish (PPend pend specs st)) = map ends_in_list (finish st).
Proof. intros. cbn [finish]. nopos. apply decorate_head_ends. Qed.

Lemma tail_ok_pend : forall E pend specs st,
  tail_ok E (PPend pend specs st) <-> tail_ok E st.
Proof.
  intros E pend specs st. unfold tail_ok. cbn [blank_absorbed].
  rewrite (ends_list_map (E ++ finish (PPend pend specs st))%list (E ++ finish st)%list)
    by (rewrite !map_app, finish_pend_ends; reflexivity).
  reflexivity.
Qed.

(* A key finishes to a paragraph when nothing came under it, so what it
   ends in does not depend on what was emitted before it. *)
Lemma tail_ok_key : forall E range lbl src st,
  tail_ok E (PKey range lbl src st) <-> tail_ok [mk (Para [])] st.
Proof.
  intros E range lbl src st. unfold tail_ok. cbn [blank_absorbed finish]. nopos.
  rewrite ends_list_app by apply key_close_ne. rewrite ends_list_key_close.
  assert (Hr : ends_list (finish st) = ends_list ([mk (Para [])] ++ finish st)%list).
  { destruct (finish st) as [|b bs] eqn:Ef; [reflexivity|].
    rewrite ends_list_app by discriminate. reflexivity. }
  rewrite Hr. split; intros H Ha.
  - destruct (announces_end st) eqn:Hann; [|exact (H Ha)].
    destruct st; try discriminate Hann; [discriminate Ha|].
    cbn [finish app]. nopos. cbn [ends_list map last ends_in_list node_contents].
    unfold div_block. destruct bdiv_names; [|destruct (String.eqb _ _)]; reflexivity.
  - apply orb_false_iff in Ha as [_ Ha]. exact (H Ha).
Qed.

Lemma fresh_foot : forall bs range ind lbl done inner,
  state_ok (PFoot range ind lbl done inner) -> fresh bs (PFoot range ind lbl done inner).
Proof.
  intros bs range ind lbl done inner Hs. split; [exact Hs|]. split; [|intros _; reflexivity].
  intros Ha. cbn [blank_absorbed] in Ha. cbn [finish]. nopos. split.
  - intros H. apply app_eq_nil in H as [_ H]. discriminate H.
  - rewrite ends_list_app by discriminate.
    unfold foot_block, mk, ends_list. cbn [map last].
    rewrite ends_in_list_foot. exact (proj2 Hs Ha).
Qed.

Lemma fresh_pend_result : forall pend specs bs st,
  fresh bs st -> fresh (fst (pend_result pend specs (bs, st)))
                       (snd (pend_result pend specs (bs, st))).
Proof.
  intros pend specs bs st [Hs [Hn Hi]]. destruct bs as [|b bs'].
  - cbn [pend_result fst snd]. split; [split; [exact Hs | exact (Hi eq_refl)]|].
    split; [|intros _; reflexivity]. intros Ha. cbn [blank_absorbed] in Ha.
    destruct (Hn Ha) as [Hne Hend]. cbn [app] in *.
    rewrite (ends_list_map _ (finish st)) by apply finish_pend_ends.
    split; [|exact Hend].
    intros H. apply Hne. apply (f_equal (map ends_in_list)) in H.
    rewrite finish_pend_ends in H. destruct (finish st); [reflexivity|discriminate H].
  - cbn [pend_result fst snd]. nopos. split; [exact Hs|]. split.
    + intros Ha. destruct (Hn Ha) as [Hne Hend]. split.
      * intros H. destruct b; discriminate H.
      * rewrite <- Hend. apply ends_list_map. rewrite !map_app, decorate_head_ends.
        reflexivity.
    + intros H. destruct b; discriminate H.
Qed.

Lemma fresh_key_result : forall range lbl src bs st,
  fresh bs st -> fresh (fst (key_result range lbl src (bs, st)))
                       (snd (key_result range lbl src (bs, st))).
Proof.
  intros range lbl src bs st [Hs [Hn Hi]]. destruct bs as [|b bs'].
  - cbn [key_result fst snd]. split; [exact Hs|]. split; [|intros _; reflexivity].
    intros Ha. cbn [blank_absorbed finish app] in *. nopos.
    split; [apply key_close_ne|]. rewrite ends_list_key_close.
    apply orb_false_iff in Ha as [_ Ha].
    destruct (Hn Ha) as [_ Hend]. exact Hend.
  - cbn [key_result fst snd]. nopos. split; [exact Hs|]. split.
    + intros Ha. destruct (Hn Ha) as [Hne Hend]. split.
      * intros H. apply app_eq_nil in H as [H _]. exact (key_close_ne _ _ _ _ H).
      * rewrite <- Hend. apply ends_list_map. rewrite !map_app, key_close_ends
          by discriminate. reflexivity.
    + intros H. destruct (key_close_ne _ _ _ _ H).
Qed.

(*
One line
--------
*)

Lemma fresh_key_para : forall range lbl src cur,
  fresh [] (PKey range lbl src (PPara cur)).
Proof.
  intros range lbl src cur. split; [exact I|]. split; [|intros _; reflexivity].
  intros _. cbn [finish app]. nopos. split; [apply key_close_ne|].
  rewrite ends_list_key_close. destruct cur; reflexivity.
Qed.

(* What a nonblank line opens from idle.  `descend` is the parse of a
   container prefix's residue, which is shorter than the line. *)
Lemma open_line_fresh : forall descend ind l,
  is_blank l = false ->
  (forall rest, String.length rest < String.length l ->
     step_ok (PPara []) rest (descend rest)) ->
  fresh (fst (open_line descend ind l (classify l)))
        (snd (open_line descend ind l (classify l))).
Proof.
  intros descend ind l Hl Hd.
  destruct (classify l) as [| |f|len cls|rest|lvl rest|sty core chk rest|ap|lbl rest|lbl v|r|]
    eqn:E; cbn [open_line open_kind].
  - apply classify_kblank_blank in E. congruence.
  - apply fresh_emit; [discriminate|reflexivity].
  - apply fresh_absorbing; [reflexivity|exact I].
  - destruct bdivs; cbn [fst snd].
    + eapply fresh_single; [exact I|reflexivity|cbn [finish]; nopos; reflexivity|].
      unfold div_block. destruct bdiv_names; [|destruct (String.eqb cls "")]; reflexivity.
    + eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
  - destruct (quote_header rest) as [[[kind fold] title]|].
    + unfold open_callout. cbn [fst snd].
      eapply fresh_single; [exact I|reflexivity|cbn [finish]; nopos; reflexivity|reflexivity].
    + unfold open_quote. destruct (descend rest) as [bs inner]. cbn [fst snd].
      eapply fresh_single; [exact I|reflexivity|cbn [finish]; nopos; reflexivity|reflexivity].
  - eapply fresh_single; [exact I|reflexivity|cbn [finish]; nopos; reflexivity|reflexivity].
  - unfold open_list.
    destruct (Hd _ (configured_list_rest_length _ _ _ _ _ E)) as [Hs _].
    destruct (descend _) as [bs inner]. cbn [fst snd] in *.
    apply fresh_absorbing; [reflexivity|exact Hs].
  - unfold open_attr. destruct battrs; cbn [fst snd].
    + apply fresh_absorbing; [reflexivity|exact I].
    + eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
  - unfold open_foot. destruct bfootnotes.
    + destruct (Hd rest (classify_foot_length l lbl rest E)) as [Hs [Ht _]].
      destruct (descend rest) as [bs inner]. cbn [fst snd] in *.
      apply fresh_foot. split; [exact Hs|]. rewrite rev_involutive.
      apply (Ht []). intros _. reflexivity.
    + eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
  - eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
  - destruct btables; cbn [fst snd].
    + eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
    + eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
  - unfold open_text. destruct (if bkeyed then key_split _ else None) as [[k v]|].
    + apply fresh_key_para.
    + eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
Qed.

Lemma list_block_ends : forall ls x, ends_in_list (list_block ls x) = true.
Proof.
  intros ls x. unfold list_block, styles_list_checked, styles_list.
  destruct (ls_styles ls) as [|[[c|t|n d] start] rest]; try reflexivity.
  destruct (Ascii.eqb c ":" && bdeflists)%bool; reflexivity.
Qed.

Lemma key_close_map : forall start lbl src xs ys,
  map ends_in_list xs = map ends_in_list ys ->
  map ends_in_list (key_close start lbl src xs) = map ends_in_list (key_close start lbl src ys).
Proof.
  intros start lbl src [|x xs] [|y ys] H; try discriminate H; [reflexivity|].
  rewrite !key_close_ends by discriminate. exact H.
Qed.

Lemma feed_lazy_text : forall l st, blank_held (feed_lazy l st) = blank_held st.
Proof.
  intros l st. induction st; cbn [feed_lazy blank_held]; auto.
  rewrite IHst. destruct st; reflexivity.
Qed.

(* A lazy line lands in a paragraph somewhere down the spine, so it
   changes no container and no block kind. *)
Lemma feed_lazy_ok : forall l st,
  lazy_ok st = true -> state_ok st ->
  state_ok (feed_lazy l st)
  /\ blank_absorbed (feed_lazy l st) = blank_absorbed st
  /\ map ends_in_list (finish (feed_lazy l st)) = map ends_in_list (finish st)
  /\ is_idle (feed_lazy l st) = false.
Proof.
  intros l st. induction st as
    [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hl Hs; cbn [lazy_ok] in Hl; try discriminate Hl.
  - destruct cur; [discriminate Hl|]. repeat split; reflexivity.
  - repeat split; reflexivity.
  - cbn [feed_lazy blank_absorbed finish]. nopos. repeat split; try reflexivity.
    destruct qhead as [[[kind fold] title]|]; reflexivity.
  - destruct (IH Hl Hs) as [Hs' _].
    cbn [feed_lazy blank_absorbed finish state_ok]. nopos. rewrite feed_lazy_text.
    split; [exact Hs'|]. repeat split; try reflexivity.
    unfold div_block. destruct bdiv_names; [|destruct (String.eqb dcls "")]; reflexivity.
  - destruct (IH Hl Hs) as [Hs' _].
    cbn [feed_lazy blank_absorbed finish state_ok]. nopos.
    split; [exact Hs'|]. repeat split; try reflexivity.
    cbn [map]. rewrite !list_block_ends. reflexivity.
  - repeat split; reflexivity.
  - destruct Hs as [Hs Ht]. destruct (IH Hl Hs) as [Hs' [Ha [Hm _]]].
    cbn [feed_lazy blank_absorbed finish state_ok]. nopos.
    assert (Hmap : map ends_in_list (rev fdone ++ finish (feed_lazy l finner))%list
                   = map ends_in_list (rev fdone ++ finish finner)%list)
      by (rewrite !map_app, Hm; reflexivity).
    split; [split; [exact Hs'|]|split; [exact Ha|split; [|reflexivity]]].
    + intros Ha'. rewrite (ends_list_map _ _ Hmap). apply Ht. congruence.
    + unfold foot_block, mk. cbn [map].
      rewrite !ends_in_list_foot, (ends_list_map _ _ Hmap). reflexivity.
  - destruct Hs as [Hs _]. destruct (IH Hl Hs) as [Hs' [Ha [Hm Hi]]].
    cbn [feed_lazy blank_absorbed state_ok].
    split; [split; [exact Hs'|exact Hi]|split; [exact Ha|split; [|reflexivity]]].
    rewrite !finish_pend_ends. exact Hm.
  - destruct (IH Hl Hs) as [Hs' [Ha [Hm Hi]]].
    cbn [feed_lazy blank_absorbed state_ok finish]. nopos.
    assert (Hann : announces_end (feed_lazy l kinner) = announces_end kinner)
      by (destruct kinner; reflexivity).
    split; [exact Hs'|split; [rewrite Hann, Ha; reflexivity|split; [|reflexivity]]].
    apply key_close_map. exact Hm.
Qed.

Lemma nonblank_of_kind : forall l k,
  classify l = k -> k <> KBlank -> is_blank l = false.
Proof.
  intros l k E Hk. destruct (is_blank l) eqn:B; [|reflexivity].
  unfold classify in E. rewrite B in E. congruence.
Qed.

Lemma step_ok_idle_nil : forall l,
  is_blank l = true -> step_ok (PPara []) l ([], PPara []).
Proof.
  intros l Hl. split; [exact I|]. split; [|split].
  - intros E H. rewrite app_nil_r. exact H.
  - intros H. congruence.
  - intros H. discriminate H.
Qed.

Lemma open_line_fresh_k : forall descend ind l k,
  classify l = k -> k <> KBlank ->
  (forall rest, String.length rest < String.length l ->
     step_ok (PPara []) rest (descend rest)) ->
  fresh (fst (open_line descend ind l k)) (snd (open_line descend ind l k)).
Proof.
  intros descend ind l k E Hk Hd. subst k.
  apply open_line_fresh; [exact (nonblank_of_kind l _ eq_refl Hk)|exact Hd].
Qed.

Lemma open_kind_fresh : forall l k,
  classify l = k -> k <> KBlank -> direct_open k = true ->
  fresh (fst (open_kind l k)) (snd (open_kind l k)).
Proof.
  intros l k E Hk Hdir.
  destruct k as [| |f|len cls|rest|lvl rest|sty core chk rest|ap|lbl rest|lbl v|r|];
    try discriminate Hdir.
  all: cbn [open_kind].
  - congruence.
  - apply fresh_emit; [discriminate|reflexivity].
  - destruct bdivs; cbn [fst snd].
    + eapply fresh_single; [exact I|reflexivity|cbn [finish]; nopos; reflexivity|].
      unfold div_block. destruct bdiv_names; [|destruct (String.eqb cls "")]; reflexivity.
    + eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
  - eapply fresh_single; [exact I|reflexivity|cbn [finish]; nopos; reflexivity|reflexivity].
  - destruct btables; cbn [fst snd].
    + eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
    + eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
  - unfold open_text. destruct (if bkeyed then key_split _ else None) as [[k v]|].
    + apply fresh_key_para.
    + eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
Qed.

(* A blank closing a state that finishes to one block that is not a
   list. *)
Lemma close_blank_ok : forall st l b,
  classify l = KBlank -> finish st = [b] -> ends_in_list b = false ->
  step_ok st l (close_reopen st (open_kind l KBlank)).
Proof.
  intros st l b E Hf Hb. apply fresh_step_ok. cbn [open_kind close_reopen fst snd].
  rewrite Hf. apply fresh_emit; [discriminate|exact Hb].
Qed.

Lemma close_reopen_fresh : forall st r,
  fresh (fst r) (snd r) -> fresh (fst (close_reopen st r)) (snd (close_reopen st r)).
Proof.
  intros st [bs st'] H. cbn [close_reopen fst snd]. apply fresh_prefix. exact H.
Qed.

(* A nonblank line's result is fresh by itself: it cannot leave an idle
   state having emitted nothing. *)
Lemma step_ok_fresh : forall st l r,
  is_blank l = false -> step_ok st l r -> fresh (fst r) (snd r).
Proof.
  intros st l r Hl [Hs [_ [Hn _]]]. specialize (Hn Hl).
  split; [exact Hs|]. split; [exact Hn|].
  intros Hb. destruct (snd r) as [[|c cur]| | | | | | | | | | | |] eqn:E; try reflexivity.
  exfalso. destruct (Hn eq_refl) as [Hne _]. rewrite Hb in Hne. apply Hne. reflexivity.
Qed.

(* A closed block that is not a list, then the line from idle. *)
Lemma emit_step_ok : forall st l b r,
  ends_in_list b = false -> step_ok (PPara []) l r ->
  step_ok st l ((b :: fst r)%list, snd r).
Proof.
  intros st l b [bs st'] Hb [Hs [Ht [Hn _]]]. cbn [fst snd] in *.
  unfold step_ok. cbn [fst snd]. split; [exact Hs|]. split; [|split].
  - intros E _. replace (E ++ b :: bs)%list with ((E ++ [b]) ++ bs)%list
      by (rewrite <- app_assoc; reflexivity).
    apply Ht. intros _. cbn [finish]. rewrite app_nil_r.
    rewrite ends_list_app by discriminate. exact Hb.
  - intros Hl Ha. destruct (Hn Hl Ha) as [Hne Hend]. split; [discriminate|].
    replace ((b :: bs) ++ finish st')%list with ([b] ++ (bs ++ finish st'))%list
      by reflexivity.
    rewrite (ends_list_app [b] (bs ++ finish st')%list Hne). exact Hend.
  - intros _ H. discriminate H.
Qed.

Lemma pend_step_ok : forall pend specs inner l r,
  is_idle inner = false -> step_ok inner l r ->
  step_ok (PPend pend specs inner) l (pend_result pend specs r).
Proof.
  intros pend specs inner l [bs st'] Hni Hr.
  pose proof Hr as [Hs [Ht [Hn Hi]]]. cbn [fst snd] in *.
  unfold step_ok. split; [|split; [|split]].
  - destruct bs; cbn [pend_result snd state_ok];
      [split; [exact Hs|exact (Hi Hni eq_refl)]|exact Hs].
  - intros E HE. apply tail_ok_pend in HE. specialize (Ht E HE).
    destruct bs as [|b bs']; cbn [pend_result fst snd].
    + apply tail_ok_pend. exact Ht.
    + nopos. intros Ha. rewrite <- (Ht Ha). apply ends_list_map.
      rewrite !map_app, decorate_head_ends. reflexivity.
  - intros Hl. pose proof (step_ok_fresh _ l _ Hl Hr) as Hf. cbn [fst snd] in Hf.
    exact (proj1 (proj2 (fresh_pend_result pend specs bs st' Hf))).
  - intros _. destruct bs as [|b bs']; cbn [pend_result fst snd].
    + intros _. reflexivity.
    + nopos. intros H. destruct b; discriminate H.
Qed.

Lemma key_step_ok : forall range range' lbl src inner l r,
  step_ok inner l r ->
  step_ok (PKey range lbl src inner) l (key_result range' lbl src r).
Proof.
  intros range range' lbl src inner l [bs st'] Hr.
  pose proof Hr as [Hs [Ht [Hn Hi]]]. cbn [fst snd] in *.
  unfold step_ok. split; [|split; [|split]].
  - destruct bs; exact Hs.
  - intros E HE. apply tail_ok_key in HE. specialize (Ht _ HE).
    destruct bs as [|b bs']; cbn [key_result fst snd].
    + rewrite app_nil_r. apply (proj2 (tail_ok_key E range' lbl src st')).
      rewrite app_nil_r in Ht. exact Ht.
    + nopos. intros Ha. specialize (Ht Ha). rewrite <- app_assoc.
      rewrite ends_list_app
        by (intros H; apply app_eq_nil in H as [H _]; exact (key_close_ne _ _ _ _ H)).
      rewrite <- app_assoc in Ht. rewrite ends_list_app in Ht by discriminate.
      rewrite <- Ht. apply ends_list_map. rewrite !map_app, key_close_ends by discriminate.
      reflexivity.
  - intros Hl. pose proof (step_ok_fresh _ l _ Hl Hr) as Hf. cbn [fst snd] in Hf.
    exact (proj1 (proj2 (fresh_key_result range' lbl src bs st' Hf))).
  - intros _. destruct bs as [|b bs']; cbn [key_result fst snd].
    + intros _. reflexivity.
    + nopos. intros H. destruct (key_close_ne _ _ _ _ H).
Qed.

Lemma step_fuel_ok : forall n off l st,
  String.length l + pstate_depth st < n -> pad_safe st = true -> state_ok st ->
  step_ok st l (step_fuel n off l st).
Proof.
  induction n as [|n IH]; intros off l st Hn Hp Hs; [lia|].
  assert (Hd : forall rest, String.length rest < String.length l ->
            step_ok (PPara []) rest (step_fuel n (off + consumed l rest) rest (PPara []))).
  { intros rest Hr. apply IH; [cbn [pstate_depth]; lia|reflexivity|exact I]. }
  assert (Hol : forall k, classify l = k -> k <> KBlank ->
            fresh (fst (open_line (fun rest => step_fuel n (off + consumed l rest) rest (PPara [])) (off + indent_of l) l k))
                  (snd (open_line (fun rest => step_fuel n (off + consumed l rest) rest (PPara [])) (off + indent_of l) l k))).
  { intros k E Hk. apply (open_line_fresh_k _ _ l k E Hk). exact Hd. }
  cbn [step_fuel].
  destruct st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner|dlen dcls drng dop ddone dinner
    |ls done inner|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner|trng trows tcap|ppend pspecs pinner|krng klbl ksrc kinner].
  - (* paragraph *)
    destruct cur as [|c cur'].
    + destruct (classify l) eqn:E.
      1: { cbn [open_line open_kind]. apply step_ok_idle_nil. exact (classify_kblank_blank l E). }
      all: apply fresh_step_ok; apply Hol; [reflexivity|discriminate].
    + destruct (bunderline_of l) as [ulvl|].
      { apply fresh_step_ok. apply fresh_emit; [discriminate|cbn [ends_list map last]; nopos; reflexivity]. }
      destruct (classify l) eqn:E.
      1: { eapply close_blank_ok; [exact E|reflexivity|reflexivity]. }
      all: destruct (binterrupt _);
        [apply fresh_step_ok, close_reopen_fresh, Hol; [reflexivity|discriminate]
        |apply fresh_step_ok; eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity]].
  - (* heading *)
    destruct (classify l) eqn:E.
    1: { cbn [open_line]. eapply close_blank_ok; [exact E|reflexivity|reflexivity]. }
    all: try (apply fresh_step_ok, close_reopen_fresh, Hol; [reflexivity|discriminate]).
    + destruct bheading_continues; [destruct (Nat.eqb _ _)|].
      * apply fresh_step_ok; eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
      * apply fresh_step_ok, close_reopen_fresh. apply (open_kind_fresh l); [exact E|discriminate|reflexivity].
      * apply fresh_step_ok, close_reopen_fresh. apply (open_kind_fresh l); [exact E|discriminate|reflexivity].
    + destruct bheading_continues.
      * apply fresh_step_ok; eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
      * apply fresh_step_ok, close_reopen_fresh. apply (open_kind_fresh l); [exact E|discriminate|reflexivity].
  - (* code block *)
    destruct (fence_close f l).
    + apply fresh_step_ok, fresh_emit; [discriminate|].
      cbn [ends_list map last]. nopos. unfold fence_block.
      destruct (f_info f) as [|a rest]; [reflexivity|].
      destruct a as [[] [] [] [] [] [] [] []]; try reflexivity;
      destruct braw_blocks; reflexivity.
    + apply fresh_step_ok, fresh_absorbing; [reflexivity|exact I].
  - (* quote *)
    assert (Hq : forall done' inner' r, fresh [] (PQuote r qhead done' inner')).
    { intros done' inner' r. eapply fresh_single; [exact I|reflexivity|cbn [finish]; nopos; reflexivity|].
      destruct qhead as [[[kind fold] title]|]; reflexivity. }
    destruct (classify l) eqn:E.
    1: { cbn [is_lazy open_line]. eapply close_blank_ok; [exact E|cbn [finish]; nopos; reflexivity|].
         destruct qhead as [[[kind fold] title]|]; reflexivity. }
    4: { destruct (step_fuel n (off + consumed l rest) rest inner) as [bs inner']. apply fresh_step_ok, Hq. }
    all: destruct (is_lazy _ inner); [apply fresh_step_ok, Hq|].
    all: apply fresh_step_ok, close_reopen_fresh, Hol; [reflexivity|discriminate].
  - (* div *)
    destruct (negb (in_fence dinner) && div_close dlen l)%bool.
    + apply fresh_step_ok, fresh_emit; [discriminate|].
      cbn [ends_list map last]. nopos. unfold div_block.
      destruct bdiv_names; [|destruct (String.eqb dcls "")]; reflexivity.
    + cbn [pad_safe state_ok pstate_depth] in Hp, Hs, Hn.
      assert (Hin : step_ok dinner l (step_fuel n off l dinner))
        by (apply IH; [lia|exact Hp|exact Hs]).
      destruct (step_fuel n off l dinner) as [bs inner']. destruct Hin as [Hs' _].
      apply fresh_step_ok. eapply fresh_single;
        [exact Hs'|reflexivity|cbn [finish]; nopos; reflexivity|].
      unfold div_block. destruct bdiv_names; [|destruct (String.eqb dcls "")]; reflexivity.
  - (* list *)
    cbn [pad_safe state_ok pstate_depth] in Hp, Hs, Hn.
    assert (Hin : state_ok (snd (step_fuel n off l inner)))
      by (apply IH; [lia|exact Hp|exact Hs]).
    destruct (classify l) eqn:E.
    1: { destruct (step_fuel n off l inner) as [bs inner'].
         apply fresh_step_ok, fresh_absorbing; [reflexivity|exact Hin]. }
    all: destruct (list_takes ls off l inner);
      [destruct (step_fuel n off l inner) as [bs inner'];
       apply fresh_step_ok, fresh_absorbing; [reflexivity|exact Hin]|].
    6: { destruct (Marker.narrow _ _).
         - apply fresh_step_ok, close_reopen_fresh, Hol; [reflexivity|discriminate].
         - destruct (Hd _ (configured_list_rest_length _ _ _ _ _ E)) as [Hs' _].
           destruct (step_fuel n _ _ (PPara [])) as [bs inner'].
           apply fresh_step_ok, fresh_absorbing; [reflexivity|exact Hs']. }
    all: destruct (is_lazy _ inner) eqn:Hlz;
      [|apply fresh_step_ok, close_reopen_fresh, Hol; [reflexivity|discriminate]].
    all: unfold is_lazy in Hlz; try discriminate Hlz.
    all: apply fresh_step_ok, fresh_absorbing; [reflexivity|].
    all: exact (proj1 (feed_lazy_ok l inner Hlz Hs)).
  - (* an attribute spec is excluded *)
    discriminate Hp.
  - (* the recovery's paragraph *)
    destruct (bunderline_of l) as [ulvl|].
    { apply fresh_step_ok. apply fresh_emit; [discriminate|cbn [ends_list map last]; nopos; reflexivity]. }
    destruct (classify l) eqn:E.
    1: { eapply close_blank_ok; [exact E|reflexivity|reflexivity]. }
    all: destruct (binterrupt _);
      [apply fresh_step_ok, close_reopen_fresh, Hol; [reflexivity|discriminate]
      |apply fresh_step_ok; eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity]].
  - (* reference definition *)
    destruct (if Nat.ltb rind (off + indent_of l) then ref_cont l else None).
    + apply fresh_step_ok; eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity].
    + assert (Hr : step_ok (PPara []) l (step_fuel n off l (PPara [])))
        by (apply IH; [cbn [pstate_depth] in *; lia|reflexivity|exact I]).
      destruct (step_fuel n off l (PPara [])) as [bs st'].
      apply (emit_step_ok _ l _ (bs, st')); [reflexivity|exact Hr].
  - (* footnote *)
    cbn [pad_safe state_ok pstate_depth] in Hp, Hs, Hn. destruct Hs as [Hsi Hti].
    assert (Hin : step_ok finner l (step_fuel n off l finner)) by (apply IH; [lia|exact Hp|exact Hsi]).
    assert (Hcont : forall r, step_ok finner l r ->
              step_ok (PFoot frng find flbl fdone finner) l
                (let (bs, inner') := r in
                 ([], PFoot (touch_extent frng) find flbl (rev bs ++ fdone)%list inner'))).
    { intros [bs inner'] [Hs' [Ht' _]]. apply fresh_step_ok. cbn [fst snd]. apply fresh_foot.
      cbn [state_ok]. split; [exact Hs'|]. rewrite rev_app_distr, rev_involutive. apply Ht'. exact Hti. }
    destruct (is_blank l) eqn:Hb; [apply Hcont, Hin|].
    destruct (Nat.ltb find (off + indent_of l)); [apply Hcont, Hin|].
    destruct (is_lazy (classify l) finner) eqn:Hlz.
    + apply fresh_step_ok. cbn [fst snd]. apply fresh_foot. cbn [state_ok].
      assert (Hlo : lazy_ok finner = true)
        by (unfold is_lazy in Hlz; destruct (classify l); try discriminate; exact Hlz).
      destruct (feed_lazy_ok l finner Hlo Hsi) as [Hs' [Ha [Hm _]]].
      split; [exact Hs'|]. intros Ha'. rewrite Ha in Ha'.
      rewrite (ends_list_map _ (rev fdone ++ finish finner)%list)
        by (rewrite !map_app, Hm; reflexivity).
      exact (Hti Ha').
    + assert (Hr : step_ok (PPara []) l (step_fuel n off l (PPara [])))
        by (apply IH; [cbn [pstate_depth]; lia|reflexivity|exact I]).
      destruct (step_fuel n off l (PPara [])) as [bs st'].
      apply fresh_step_ok. cbn [fst snd]. apply (fresh_prefix [_]).
      exact (step_ok_fresh _ l (bs, st') Hb Hr).
  - (* table *)
    assert (Htb : forall r rows cap, fresh [] (PTable r rows cap))
      by (intros; eapply fresh_single; [exact I|reflexivity|reflexivity|reflexivity]).
    assert (Hr : step_ok (PPara []) l (step_fuel n off l (PPara [])))
      by (apply IH; [cbn [pstate_depth] in *; lia|reflexivity|exact I]).
    destruct tcap as [parts|parts|parts start cur].
    + destruct (caption_open l); [apply fresh_step_ok, Htb|].
      destruct (is_blank l); [apply fresh_step_ok, Htb|].
      destruct (classify l); try (apply fresh_step_ok, Htb).
      all: destruct (step_fuel n off l (PPara [])) as [bs st'];
        apply (emit_step_ok _ l _ (bs, st')); [reflexivity|exact Hr].
    + destruct (caption_open l); [apply fresh_step_ok, Htb|].
      destruct (is_blank l); [apply fresh_step_ok, Htb|].
      destruct (classify l).
      all: destruct (step_fuel n off l (PPara [])) as [bs st'];
        apply (emit_step_ok _ l _ (bs, st')); [reflexivity|exact Hr].
    + destruct (is_blank l).
      * apply fresh_step_ok, fresh_emit; [discriminate|reflexivity].
      * apply fresh_step_ok, Htb.
  - (* pending attributes *)
    cbn [pad_safe state_ok pstate_depth] in Hp, Hs, Hn. destruct Hs as [Hsi Hni].
    assert (Hin : step_ok pinner l (step_fuel n off l pinner))
      by (apply IH; [lia|exact Hp|exact Hsi]).
    destruct (classify l); rewrite ?Hni; apply pend_step_ok; assumption.
  - (* key *)
    cbn [pad_safe state_ok pstate_depth] in Hp, Hs, Hn.
    assert (Hin : step_ok kinner l (step_fuel n off l kinner))
      by (apply IH; [lia|exact Hp|exact Hs]).
    destruct (is_blank l && is_idle kinner)%bool eqn:Hbi.
    + apply fresh_step_ok, fresh_emit; [discriminate|].
      cbn [ends_list map last]. nopos. reflexivity.
    + apply key_step_ok. exact Hin.
Qed.

Lemma step_ok_step : forall l st,
  pad_safe st = true -> state_ok st -> step_ok st l (step l st).
Proof. intros l st Hp Hs. unfold step. apply step_fuel_ok; [lia|exact Hp|exact Hs]. Qed.

Lemma tail_ok_idle_nil : tail_ok [] (PPara []).
Proof. intros _. reflexivity. Qed.

(* Over a run: the invariant holds at every line boundary. *)
Lemma run_ok : forall A R st E,
  run_safe (A ++ R)%list st = true -> state_ok st -> tail_ok E st ->
  state_ok (snd (run_lines A st)) /\ tail_ok (E ++ fst (run_lines A st))%list (snd (run_lines A st)).
Proof.
  induction A as [|l A IH]; intros R st E Hsafe Hs Ht.
  - cbn [run_lines fst snd]. rewrite app_nil_r. split; assumption.
  - cbn [app run_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hp Hsafe].
    destruct (step_ok_step l st Hp Hs) as [Hs' [Ht' _]].
    cbn [run_lines]. destruct (step l st) as [bs st'] eqn:Es. cbn [fst snd] in *.
    destruct (IH R st' (E ++ bs)%list Hsafe Hs' (Ht' E Ht)) as [Hs'' Ht''].
    destruct (run_lines A st') as [more st''] eqn:Er. cbn [fst snd] in *.
    rewrite app_assoc. split; assumption.
Qed.

(*
After a blank
-------------

A blank that nothing absorbs closes everything but a div, a footnote and
a table, which can still continue, and whatever pending attributes or a
key hold of those.  The line after it either continues one of them
(`keeps_line`) or is parsed as if the item had just started.
*)

Fixpoint settled (st : pstate) : Prop :=
  match st with
  | PPara [] => True
  | PTable _ _ (TAfterBlank _) => True
  | PDiv _ _ _ _ _ inner => blank_safe inner = true /\ lazy_ok inner = false
  | PFoot _ _ _ _ inner => settled inner
  | PPend _ _ inner => settled inner /\ is_idle inner = false
  | PKey _ _ _ inner =>
      settled inner /\ is_idle inner = false /\ announces_end inner = false
  | _ => False
  end.

Local Lemma state_ok_held_safe : forall st,
  state_ok st -> blank_held st = false -> blank_safe st = true.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hs Ha; cbn [blank_held state_ok] in Ha, Hs; try discriminate Ha; try reflexivity.
  - apply IH; assumption.
  - apply IH; assumption.
  - apply IH; [exact (proj1 Hs)|exact Ha].
  - cbn [blank_safe]. destruct Hs as [Hs Hi]. rewrite (IH Hs Ha), Hi. reflexivity.
  - apply orb_false_iff in Ha as [Hann Ha].
    cbn [blank_safe]. rewrite (IH Hs Ha), Hann. reflexivity.
Qed.

Lemma state_ok_blank_safe : forall st,
  state_ok st -> blank_absorbed st = false -> blank_safe st = true.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hs Ha; cbn [blank_absorbed state_ok] in Ha, Hs; try discriminate Ha; try reflexivity.
  - exact (state_ok_held_safe dinner Hs Ha).
  - apply IH; [exact (proj1 Hs)|exact Ha].
  - cbn [blank_safe]. destruct Hs as [Hs Hi]. rewrite (IH Hs Ha), Hi. reflexivity.
  - apply orb_false_iff in Ha as [Hann Ha].
    cbn [blank_safe]. rewrite (IH Hs Ha), Hann. reflexivity.
Qed.

Lemma settled_absorbed : forall st, settled st -> blank_absorbed st = false.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H; cbn [settled] in H; try contradiction; try reflexivity.
  - cbn [blank_absorbed]. apply blank_safe_not_held, H.
  - apply IH, H.
  - apply IH, H.
  - destruct H as [H [_ Hann]]. cbn [blank_absorbed]. rewrite Hann, (IH H). reflexivity.
Qed.

Lemma settled_blank_safe : forall st, settled st -> blank_safe st = true.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H; cbn [settled] in H; try contradiction; try reflexivity.
  - exact (proj1 H).
  - apply IH, H.
  - destruct H as [H Hi]. cbn [blank_safe]. rewrite (IH H), Hi. reflexivity.
  - destruct H as [H [_ Hann]]. cbn [blank_safe]. rewrite (IH H), Hann. reflexivity.
Qed.

Lemma settled_lazy : forall st, settled st -> lazy_ok st = false.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H; cbn [settled] in H; try contradiction; try reflexivity.
  - destruct cur; [reflexivity|contradiction].
  - exact (proj2 H).
  - apply IH, H.
  - apply IH, H.
  - apply IH, H.
Qed.

Lemma settled_finish : forall st,
  settled st -> is_idle st = false -> finish st <> [].
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H Hi; cbn [settled] in H; try contradiction; cbn [finish]; nopos; try discriminate.
  - destruct cur; [discriminate Hi|contradiction].
  - destruct H as [H Hi']. specialize (IH H Hi').
    destruct (finish pinner) as [|[p a x] bs]; [contradiction|discriminate].
  - apply key_close_ne.
Qed.

(* A blank that nothing absorbs leaves a settled state. *)
Lemma blank_settles : forall l st,
  classify l = KBlank -> blank_safe st = true -> blank_absorbed st = false ->
  settled (snd (step l st)).
Proof.
  intros l st Hl.
  pose proof (classify_kblank_blank l Hl) as Hb.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe Ha; cbn [blank_absorbed] in Ha; try discriminate Ha; try discriminate Hsafe.
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hl eq_refl). exact I.
    + rewrite (step_para_flush l c cur' Hl). exact I.
  - rewrite (step_heading_close l lvl hrng cur Hl). exact I.
  - rewrite (step_quote_close l KBlank qrng qhead done inner _ _ Hl eq_refl eq_refl
               (surjective_pairing _)). exact I.
  - cbn [blank_safe] in Hsafe.
    destruct (step l dinner) as [bs inner'] eqn:Es.
    rewrite (step_div_cont l dlen dcls drng dop ddone dinner bs inner'
               (div_stays_open_blank l dinner dlen Hb) Es).
    pose proof (proj1 (step_blank_safe l dinner Hl Hsafe)) as Hs'.
    pose proof (step_blank_lazy_false l dinner Hl Hsafe) as Hz.
    rewrite Es in Hs', Hz. cbn [snd] in *. exact (conj Hs' Hz).
  - rewrite (step_para_off_flush l okoff ocur Hl). exact I.
  - rewrite (step_ref_blank l rrng rind rlbl rval Hl). exact I.
  - cbn [blank_safe] in Hsafe. specialize (IH Hsafe Ha).
    unfold step. cbn [step_fuel open_line]. rewrite Hb.
    replace (step_fuel (String.length l + S (pstate_depth finner)) 0 l finner)
      with (step l finner)
      by (unfold step; symmetry; apply step_fuel_enough; cbn [pstate_depth]; lia).
    destruct (step l finner) as [bs i]. exact IH.
  - unfold step. cbn [step_fuel open_line]. rewrite (caption_open_blank l Hb), Hb.
    destruct tcap; exact I.
  - cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe Hni].
    apply negb_true_iff in Hni. specialize (IH Hsafe Ha).
    pose proof (proj2 (step_blank_safe l pinner Hl Hsafe) Hni) as Hset.
    unfold step. cbn [step_fuel open_line]. rewrite Hl, Hni.
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l pinner) as [bs st'] eqn:Es. cbn [fst snd] in IH, Hset.
    destruct bs as [|b bs']; cbn [pend_result snd].
    + exact (conj IH (Hset eq_refl)).
    + destruct b. exact IH.
  - cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe Hann].
    apply negb_true_iff in Hann. apply orb_false_iff in Ha as [_ Ha].
    specialize (IH Hsafe Ha).
    destruct (is_idle kinner) eqn:Hki.
    { destruct kinner as [cur| | | | | | | | | | | |]; try discriminate Hki.
      destruct cur; [|discriminate Hki].
      rewrite (step_key_retract l krng klbl ksrc Hb). exact I. }
    rewrite (step_key_pass l krng klbl ksrc kinner ltac:(rewrite Hki, andb_false_r; reflexivity)).
    pose proof (step_blank_inner_settled l kinner Hl Hsafe Hann Hki) as Hset.
    destruct (step l kinner) as [bs st'] eqn:Es. cbn [fst snd] in IH, Hset.
    destruct bs as [|b bs']; cbn [key_result snd].
    + destruct (Hset eq_refl) as [Hi Ha']. exact (conj IH (conj Hi Ha')).
    + exact IH.
Qed.

(* Further blanks change nothing a settled state would emit. *)
Lemma settled_blank : forall l st,
  classify l = KBlank -> settled st ->
  fst (step l st) = [] /\ settled (snd (step l st))
  /\ finish (snd (step l st)) = finish st.
Proof.
  intros l st Hl Hset.
  assert (Hnil : fst (step l st) = []).
  { pose proof (classify_kblank_blank l Hl) as Hb. clear -Hl Hb Hset.
    induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
      |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
      |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
      cbn [settled] in Hset; try contradiction.
    - destruct cur; [|contradiction]. rewrite (step_idle l KBlank Hl eq_refl). reflexivity.
    - destruct (step l dinner) as [bs inner'] eqn:Es.
      rewrite (step_div_cont l dlen dcls drng dop ddone dinner bs inner'
                 (div_stays_open_blank l dinner dlen Hb) Es). reflexivity.
    - unfold step. cbn [step_fuel open_line]. rewrite Hb.
      destruct (step_fuel _ 0 l finner). reflexivity.
    - destruct tcap; try contradiction.
      unfold step. cbn [step_fuel open_line]. rewrite (caption_open_blank l Hb), Hb. reflexivity.
    - destruct Hset as [Hset Hni]. specialize (IH Hset).
      unfold step. cbn [step_fuel open_line]. rewrite Hl, Hni.
      rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
      destruct (step l pinner) as [bs st']. cbn [fst] in IH. subst bs. reflexivity.
    - destruct Hset as [Hset [Hni _]]. specialize (IH Hset).
      rewrite (step_key_pass l krng klbl ksrc kinner ltac:(rewrite Hni, andb_false_r; reflexivity)).
      destruct (step l kinner) as [bs st']. cbn [fst] in IH. subst bs. reflexivity. }
  split; [exact Hnil|]. split.
  - exact (blank_settles l st Hl (settled_blank_safe st Hset) (settled_absorbed st Hset)).
  - pose proof (step_blank_finish l st Hl (settled_blank_safe st Hset)) as Hf.
    rewrite Hnil in Hf. exact Hf.
Qed.

(* The line after the blanks, when the state does not keep it, starts
   the item afresh. *)
Lemma settled_restart : forall l st,
  settled st -> is_blank l = false -> keeps_line 0 l st = false ->
  step l st = ((finish st ++ fst (step l (PPara [])))%list, snd (step l (PPara []))).
Proof.
  intros l st Hset Hb.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hk; cbn [settled] in Hset; try contradiction.
  - destruct cur; [|contradiction]. destruct (step l (PPara [])). reflexivity.
  - cbn [keeps_line] in Hk. rewrite (proj2 Hset) in Hk. discriminate Hk.
  - cbn [keeps_line] in Hk. rewrite (settled_lazy finner Hset) in Hk. cbn [negb andb] in Hk.
    rewrite (step_foot_close l frng find flbl fdone finner (fst (step l (PPara [])))
               (snd (step l (PPara []))) Hb Hk).
    + cbn [finish]. nopos. reflexivity.
    + unfold is_lazy. rewrite (settled_lazy finner Hset). destruct (classify l); reflexivity.
    + apply surjective_pairing.
  - destruct tcap as [parts|parts|parts start cur]; try contradiction.
    cbn [keeps_line] in Hk. destruct (caption_open l) eqn:Ec; [discriminate Hk|].
    rewrite (step_table_close l trng trows parts _ _ Ec Hb (surjective_pairing _)).
    reflexivity.
  - destruct Hset as [Hset Hni]. cbn [keeps_line] in Hk. specialize (IH Hset Hk).
    unfold step at 1. cbn [step_fuel open_line]. rewrite Hni. cbn [pstate_depth].
    rewrite (step_fuel_enough (String.length l + S (pstate_depth pinner)) l pinner) by lia.
    rewrite IH. pose proof (settled_finish pinner Hset Hni) as Hne.
    destruct (finish pinner) as [|b bs] eqn:Ef; [contradiction|].
    cbn [finish]. rewrite Ef. nopos.
    assert (Hr : pend_result ppend pspecs
                   (((b :: bs) ++ fst (step l (PPara [])))%list, snd (step l (PPara [])))
                 = ((decorate_head ppend (b :: bs) ++ fst (step l (PPara [])))%list,
                    snd (step l (PPara [])))).
    { cbn [pend_result app]. nopos. destruct b. reflexivity. }
    destruct (classify l); exact Hr.
  - destruct Hset as [Hset [Hni _]]. cbn [keeps_line] in Hk. specialize (IH Hset Hk).
    rewrite (step_key_pass l krng klbl ksrc kinner ltac:(rewrite Hb; reflexivity)).
    rewrite IH. pose proof (settled_finish kinner Hset Hni) as Hne.
    destruct (finish kinner) as [|b bs] eqn:Ef; [contradiction|].
    cbn [finish key_result app]. rewrite Ef. nopos. reflexivity.
Qed.

(*
A div on top
------------

A div that the blank left open keeps every line the item still has, so
the blank lay inside it.  Whether one is open is a fact about the state
before the blank, the same after any number of them.
*)

Fixpoint div_top (st : pstate) : bool :=
  match st with
  | PDiv _ _ _ _ _ _ => true
  | PPend _ _ inner | PKey _ _ _ inner => div_top inner
  | _ => false
  end.

Lemma blank_div_top : forall l st,
  classify l = KBlank -> blank_safe st = true ->
  div_top (snd (step l st)) = div_top st.
Proof.
  intros l st Hl.
  pose proof (classify_kblank_blank l Hl) as Hb.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe; try discriminate Hsafe.
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hl eq_refl). reflexivity.
    + rewrite (step_para_flush l c cur' Hl). reflexivity.
  - rewrite (step_heading_close l lvl hrng cur Hl). reflexivity.
  - rewrite (step_quote_close l KBlank qrng qhead done inner _ _ Hl eq_refl eq_refl
               (surjective_pairing _)). reflexivity.
  - destruct (step l dinner) as [bs inner'] eqn:Es.
    rewrite (step_div_cont l dlen dcls drng dop ddone dinner bs inner'
               (div_stays_open_blank l dinner dlen Hb) Es). reflexivity.
  - destruct (step l inner) as [bs inner'] eqn:Es.
    rewrite (step_list_blank l ls done inner bs inner' Hl Es). reflexivity.
  - rewrite (step_para_off_flush l okoff ocur Hl). reflexivity.
  - rewrite (step_ref_blank l rrng rind rlbl rval Hl). reflexivity.
  - unfold step. cbn [step_fuel open_line]. rewrite Hb.
    destruct (step_fuel _ 0 l finner). reflexivity.
  - unfold step. cbn [step_fuel open_line]. rewrite (caption_open_blank l Hb), Hb.
    destruct tcap; reflexivity.
  - cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe Hni].
    apply negb_true_iff in Hni. specialize (IH Hsafe).
    unfold step. cbn [step_fuel open_line]. rewrite Hl, Hni.
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l pinner) as [bs st'] eqn:Es. cbn [snd] in IH.
    destruct bs as [|b bs']; cbn [pend_result snd div_top]; [exact IH|].
    destruct b. exact IH.
  - cbn [blank_safe] in Hsafe. apply andb_true_iff in Hsafe as [Hsafe _].
    specialize (IH Hsafe).
    destruct (is_idle kinner) eqn:Hki.
    { destruct kinner as [cur| | | | | | | | | | | |]; try discriminate Hki.
      destruct cur; [|discriminate Hki].
      rewrite (step_key_retract l krng klbl ksrc Hb). reflexivity. }
    rewrite (step_key_pass l krng klbl ksrc kinner ltac:(rewrite Hki, andb_false_r; reflexivity)).
    destruct (step l kinner) as [bs st'] eqn:Es. cbn [snd] in IH.
    destruct bs as [|b bs']; cbn [key_result snd div_top]; exact IH.
Qed.

(* A settled state keeps a paragraph line exactly when a div is on top,
   and a div on top keeps every line. *)
Lemma settled_keeps_x : forall st, settled st -> keeps_line 0 "x" st = div_top st.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H; cbn [settled] in H; try contradiction; cbn [keeps_line div_top]; try reflexivity.
  - rewrite (proj2 H). reflexivity.
  - destruct (negb (lazy_ok finner)); [|reflexivity]. cbn. destruct find; reflexivity.
  - apply IH, H.
  - apply IH, H.
Qed.

Lemma settled_div_keeps : forall l st,
  settled st -> div_top st = true -> keeps_line 0 l st = true.
Proof.
  intros l.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H Hd; cbn [settled] in H; try contradiction; cbn [div_top] in Hd;
    try discriminate Hd; cbn [keeps_line].
  - rewrite (proj2 H). reflexivity.
  - apply IH; [exact (proj1 H)|exact Hd].
  - apply IH; [exact (proj1 H)|exact Hd].
Qed.

(*
Where the scan loosens
----------------------
*)

Lemma classify_blank : forall l, is_blank l = true -> classify l = KBlank.
Proof. intros l H. unfold classify. rewrite H. reflexivity. Qed.

Lemma run_lines_snd_cons : forall x xs st,
  snd (run_lines (x :: xs) st) = snd (run_lines xs (snd (step x st))).
Proof.
  intros x xs st. cbn [run_lines]. destruct (step x st) as [bs st'].
  cbn [snd]. destruct (run_lines xs st'). reflexivity.
Qed.

Lemma run_lines_snd_app : forall xs ys st,
  snd (run_lines (xs ++ ys)%list st) = snd (run_lines ys (snd (run_lines xs st))).
Proof.
  induction xs as [|x xs IH]; intros ys st; [reflexivity|].
  cbn [app]. rewrite !run_lines_snd_cons. apply IH.
Qed.

(* `lines_loose` turns true at a line that neither opens a list nor is
   kept by an open div, footnote or table, with a blank since the last
   nonblank line that the state did not absorb.  Read off the scan: that
   line, the blanks before it, and the first of them. *)
Lemma loose_witness : forall L st lo gap,
  lines_loose lo gap st L = true ->
  lo = true
  \/ (gap = true
      /\ exists B l C, L = (B ++ l :: C)%list /\ forallb is_blank B = true
         /\ is_blank l = false /\ opens_list l = false
         /\ keeps_line 0 l (snd (run_lines B st)) = false)
  \/ (exists A b B l C, L = (A ++ b :: B ++ l :: C)%list /\ is_blank b = true
      /\ blank_absorbed (snd (run_lines A st)) = false
      /\ forallb is_blank B = true /\ is_blank l = false /\ opens_list l = false
      /\ keeps_line 0 l (snd (run_lines (A ++ b :: B) st)) = false).
Proof.
  induction L as [|x rest IH]; intros st lo gap H.
  - left. exact H.
  - cbn [lines_loose] in H.
    assert (Hshift : (exists A b B l C, rest = (A ++ b :: B ++ l :: C)%list /\ is_blank b = true
      /\ blank_absorbed (snd (run_lines A (snd (step x st)))) = false
      /\ forallb is_blank B = true /\ is_blank l = false /\ opens_list l = false
      /\ keeps_line 0 l (snd (run_lines (A ++ b :: B) (snd (step x st)))) = false) ->
      exists A b B l C, (x :: rest)%list = (A ++ b :: B ++ l :: C)%list /\ is_blank b = true
      /\ blank_absorbed (snd (run_lines A st)) = false
      /\ forallb is_blank B = true /\ is_blank l = false /\ opens_list l = false
      /\ keeps_line 0 l (snd (run_lines (A ++ b :: B) st)) = false).
    { intros (A & b & B & l & C & Hr & Hb & Ha & HB & Hl & Ho & Hk). subst rest.
      exists (x :: A), b, B, l, C.
      cbn [app]. rewrite !run_lines_snd_cons. repeat split; assumption. }
    destruct (classify x) eqn:E.
    1: { destruct (IH _ _ _ H) as [Hlo|[[Hg (B & l & C & -> & HB & Hl & Ho & Hk)]|Hin]].
      * left. exact Hlo.
      * destruct (blank_absorbed st) eqn:Ha.
        -- right. left. split; [exact Hg|]. exists (x :: B), l, C.
           rewrite run_lines_snd_cons. cbn [forallb app].
           rewrite (classify_kblank_blank x E), HB. repeat split; assumption.
        -- right. right. exists [], x, B, l, C.
           cbn [app]. rewrite run_lines_snd_cons. cbn [run_lines snd].
           repeat split; try assumption. exact (classify_kblank_blank x E).
      * right. right. apply Hshift. exact Hin. }
    (* a list marker spends the flag without loosening *)
    6: { destruct (IH _ _ _ H) as [Hlo|[[Hg _]|Hin]];
         [left; exact Hlo|discriminate Hg|right; right; apply Hshift; exact Hin]. }
    all: destruct (IH _ _ _ H) as [Hlo|[[Hg _]|Hin]];
         [|discriminate Hg|right; right; apply Hshift; exact Hin].
    all: destruct (keeps_line 0 x st) eqn:Hk; [left; exact Hlo|].
    all: apply orb_true_iff in Hlo as [Hlo|Hg]; [left; exact Hlo|].
    all: right; left; split; [exact Hg|]; exists [], x, rest; cbn [app forallb run_lines snd].
    all: repeat split; try assumption; try reflexivity;
         [apply (nonblank_of_kind x _ E); discriminate|unfold opens_list; rewrite E; reflexivity].
Qed.

(*
Cutting at the blank
--------------------
*)

Lemma settled_run_blanks : forall B s,
  settled s -> forallb is_blank B = true ->
  fst (run_lines B s) = [] /\ settled (snd (run_lines B s))
  /\ finish (snd (run_lines B s)) = finish s.
Proof.
  induction B as [|x B IH]; intros s Hs HB; [repeat split; assumption|].
  cbn [forallb] in HB. apply andb_true_iff in HB as [Hx HB].
  destruct (settled_blank x s (classify_blank x Hx) Hs) as [Hnil [Hs' Hf]].
  cbn [run_lines]. destruct (step x s) as [bs s'] eqn:Es. cbn [fst snd] in *. subst bs.
  destruct (IH s' Hs' HB) as [Hnil' [Hs'' Hf']].
  destruct (run_lines B s') as [more s''] eqn:Er. cbn [fst snd] in *.
  subst more. rewrite Hf', Hf. repeat split; assumption.
Qed.

Lemma run_blanks_div_top : forall B s,
  forallb is_blank B = true -> settled s ->
  div_top (snd (run_lines B s)) = div_top s.
Proof.
  induction B as [|x B IH]; intros s HB Hs; [reflexivity|].
  cbn [forallb] in HB. apply andb_true_iff in HB as [Hx HB].
  rewrite run_lines_snd_cons.
  destruct (settled_blank x s (classify_blank x Hx) Hs) as [_ [Hs' _]].
  rewrite (IH _ HB Hs').
  exact (blank_div_top x s (classify_blank x Hx) (settled_blank_safe s Hs)).
Qed.

Lemma parse_blanks_idle : forall B R,
  forallb is_blank B = true ->
  parse_lines (B ++ R)%list (PPara []) = parse_lines R (PPara []).
Proof.
  induction B as [|x B IH]; intros R HB; [reflexivity|].
  cbn [forallb] in HB. apply andb_true_iff in HB as [Hx HB].
  cbn [app]. rewrite (parse_lines_blank_nil x _ (classify_blank x Hx)). apply IH, HB.
Qed.

Lemma find_after_blanks : forall B l C,
  forallb is_blank B = true -> is_blank l = false ->
  find nonblank (B ++ l :: C)%list = Some l.
Proof.
  induction B as [|x B IH]; intros l C HB Hl.
  - cbn. unfold nonblank. rewrite Hl. reflexivity.
  - cbn [forallb] in HB. apply andb_true_iff in HB as [Hx HB].
    cbn. unfold nonblank at 1. rewrite Hx. apply IH; assumption.
Qed.

(* A blank that the state does not absorb, then blanks, then a line the
   state does not keep: the state's blocks end at the blank, and the rest
   parses as if from the start. *)
Lemma blank_split : forall s b B l C,
  blank_safe s = true -> blank_absorbed s = false -> is_blank b = true ->
  forallb is_blank B = true -> is_blank l = false ->
  keeps_line 0 l (snd (run_lines B (snd (step b s)))) = false ->
  parse_lines (b :: B ++ l :: C)%list s
  = (finish s ++ parse_lines (l :: C) (PPara []))%list.
Proof.
  intros s b B l C Hsafe Ha Hb HB Hl Hk.
  pose proof (classify_blank b Hb) as Eb.
  pose proof (step_blank_finish b s Eb Hsafe) as Hf.
  pose proof (blank_settles b s Eb Hsafe Ha) as Hs1.
  destruct (step b s) as [bs s1] eqn:Es. cbn [fst snd] in Hf, Hs1, Hk.
  rewrite (parse_lines_step _ _ _ _ _ Es), parse_lines_app_run.
  destruct (settled_run_blanks B s1 Hs1 HB) as [Hnil [HsB HfB]].
  destruct (run_lines B s1) as [more sB] eqn:Er. cbn [fst snd] in Hnil, HsB, HfB, Hk.
  subst more. rewrite app_nil_l.
  cbn [parse_lines]. rewrite (settled_restart l sB HsB Hl Hk).
  destruct (step l (PPara [])) as [bs' s'] eqn:El. cbn [fst snd].
  rewrite HfB, <- Hf, !app_assoc. reflexivity.
Qed.

(* The blank closes everything when it leaves no div on top. *)
Lemma closes_at_blank : forall A,
  blank_safe (snd (run_lines A (PPara []))) = true ->
  blank_absorbed (snd (run_lines A (PPara []))) = false ->
  div_top (snd (run_lines A (PPara []))) = false ->
  closes_at A.
Proof.
  intros A Hsafe Ha Hd. unfold closes_at.
  rewrite parse_lines_app_run, (parse_lines_run A (PPara []) _ _ (surjective_pairing _)).
  destruct (run_lines A (PPara [])) as [bs s] eqn:Er. cbn [fst snd] in *.
  change [""; "x"] with ("" :: [] ++ "x" :: [])%list.
  rewrite (blank_split s "" [] "x" [] Hsafe Ha eq_refl eq_refl eq_refl).
  - rewrite app_assoc. reflexivity.
  - cbn [run_lines snd].
    rewrite (settled_keeps_x _ (blank_settles "" s eq_refl Hsafe Ha)),
      (blank_div_top "" s eq_refl Hsafe).
    exact Hd.
Qed.

(*
The theorems
============
*)

(** The parser loosens an item only at a blank the rule counts. *)
Theorem item_loose_separates : forall L,
  run_safe L (PPara []) = true -> is_blank (hd "" L) = false ->
  item_loose L = true -> exists i, separates L i.
Proof.
  intros L Hsafe Hhd Hloose. unfold item_loose in Hloose.
  destruct (loose_witness L (PPara []) false false Hloose)
    as [H|[[H _]|(A & b & B & l & C & -> & Hb & Ha & HB & Hl & Ho & Hk)]];
    try discriminate H.
  exists (length A).
  destruct (run_ok A (b :: B ++ l :: C)%list (PPara []) [] Hsafe I tail_ok_idle_nil)
    as [Hs Ht].
  pose proof (state_ok_blank_safe _ Hs Ha) as Hbs.
  assert (HA : A <> []) by (intros ->; cbn [hd app] in Hhd; congruence).
  unfold separates.
  rewrite nth_middle, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
  replace (skipn (S (length A)) (A ++ b :: B ++ l :: C))%list with (B ++ l :: C)%list
    by (rewrite skipn_app, skipn_all2 by lia;
        replace (S (length A) - length A) with 1 by lia; reflexivity).
  split; [exact Hb|]. split; [|split; [|split; [|split]]].
  - destruct A as [|a A']; [congruence|]. cbn [hd app] in Hhd. cbn [existsb].
    unfold nonblank at 1. rewrite Hhd. reflexivity.
  - apply (closes_at_blank A Hbs Ha).
    rewrite run_lines_snd_app, run_lines_snd_cons in Hk.
    set (s := snd (run_lines A (PPara []))) in *.
    pose proof (blank_settles b s (classify_blank b Hb) Hbs Ha) as Hs1.
    destruct (settled_run_blanks B _ Hs1 HB) as [_ [HsB _]].
    rewrite <- (blank_div_top b s (classify_blank b Hb) Hbs),
      <- (run_blanks_div_top B _ HB Hs1).
    destruct (div_top (snd (run_lines B (snd (step b s))))) eqn:Hd; [|reflexivity].
    rewrite (settled_div_keeps l _ HsB Hd) in Hk. discriminate Hk.
  - rewrite parse_lines_app_run, (parse_lines_run A (PPara []) _ _ (surjective_pairing _)).
    rewrite (parse_blanks_idle B (l :: C) HB).
    rewrite run_lines_snd_app, run_lines_snd_cons in Hk.
    destruct (run_lines A (PPara [])) as [bs s] eqn:Er. cbn [fst snd] in *.
    rewrite (blank_split s b B l C Hbs Ha Hb HB Hl Hk).
    rewrite app_assoc. reflexivity.
  - rewrite (parse_lines_run A (PPara []) _ _ (surjective_pairing _)).
    exact (Ht Ha).
  - exists l. split; [exact (find_after_blanks B l C HB Hl)|exact Ho].
Qed.

(** And between items only at a blank the rule counts. *)
Theorem separator_separates : forall L,
  run_safe L (PPara []) = true -> ends_open_container L = false ->
  separates_after L.
Proof.
  intros L Hsafe Ha. unfold ends_open_container in Ha.
  destruct (run_ok L [] (PPara []) [] ltac:(rewrite app_nil_r; exact Hsafe) I tail_ok_idle_nil)
    as [Hs Ht].
  split.
  - pose proof (state_ok_blank_safe _ Hs Ha) as Hbs.
    rewrite parse_lines_app_run, (parse_lines_run L (PPara []) _ _ (surjective_pairing _)).
    destruct (run_lines L (PPara [])) as [bs s] eqn:Er. cbn [fst snd] in *.
    pose proof (step_blank_finish "" s eq_refl Hbs) as Hf.
    destruct (step "" s) as [b1 s1] eqn:Es. cbn [fst snd] in Hf.
    rewrite (parse_lines_step _ _ _ _ _ Es). cbn [parse_lines]. rewrite Hf. reflexivity.
  - rewrite (parse_lines_run L (PPara []) _ _ (surjective_pairing _)). exact (Ht Ha).
Qed.

(* A blank that the item can meet and that does not reach the list ends a
   nested list. *)
Lemma absorbed_ends_list : forall st,
  blank_safe st = true -> blank_absorbed st = true ->
  finish st <> [] /\ ends_list (finish st) = true.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hs Ha; cbn [blank_absorbed blank_safe] in Ha, Hs;
    try discriminate Ha; try discriminate Hs.
  - rewrite (blank_safe_not_held dinner Hs) in Ha. discriminate Ha.
  - cbn [finish]. nopos. split; [discriminate|].
    cbn [ends_list map last]. apply list_block_ends.
  - destruct (IH Hs Ha) as [Hne Hend]. cbn [finish]. nopos. split; [discriminate|].
    unfold foot_block, mk, ends_list. cbn [map last]. rewrite ends_in_list_foot.
    rewrite ends_list_app by exact Hne. exact Hend.
  - apply andb_true_iff in Hs as [Hs _]. destruct (IH Hs Ha) as [Hne Hend].
    cbn [finish]. nopos. split.
    + destruct (finish pinner) as [|[p a x] bs]; [contradiction|discriminate].
    + rewrite <- Hend. apply ends_list_map. apply decorate_head_ends.
  - apply andb_true_iff in Hs as [Hs Hann]. apply negb_true_iff in Hann.
    rewrite Hann in Ha. destruct (IH Hs Ha) as [Hne Hend].
    cbn [finish]. nopos. split; [apply key_close_ne|].
    rewrite <- Hend. apply ends_list_map, key_close_ends, Hne.
Qed.

(** The converse between items: a blank the rule counts after an item
    that is not the last reaches the list. *)
Theorem separates_after_reaches : forall L,
  run_safe L (PPara []) = true -> separates_after L ->
  ends_open_container L = false.
Proof.
  intros L Hsafe [_ Hend]. unfold ends_open_container.
  destruct (blank_absorbed (snd (run_lines L (PPara [])))) eqn:Ha; [|reflexivity].
  exfalso.
  destruct (absorbed_ends_list _ (run_safe_final L _ Hsafe) Ha) as [Hne Hl].
  rewrite (parse_lines_run L (PPara []) _ _ (surjective_pairing _)),
    ends_list_app in Hend by exact Hne.
  congruence.
Qed.

Lemma seps_loosen_separates : forall itemss,
  forallb (fun L => run_safe L (PPara [])) itemss = true ->
  seps_loosen itemss = true ->
  exists pre L M post, itemss = (pre ++ L :: M :: post)%list /\ separates_after L.
Proof.
  induction itemss as [|L rest IH]; intros Hsafe Hs; [discriminate Hs|].
  cbn [forallb] in Hsafe. apply andb_true_iff in Hsafe as [HL Hrest].
  destruct rest as [|M rest']; [discriminate Hs|].
  cbn [seps_loosen] in Hs. apply orb_true_iff in Hs as [Hs|Hs].
  - exists [], L, M, rest'. split; [reflexivity|].
    apply separator_separates; [exact HL|]. apply negb_true_iff, Hs.
  - destruct (IH Hrest Hs) as (pre & L' & M' & post & Heq & Hsep).
    exists (L :: pre), L', M', post. rewrite Heq. split; [reflexivity|exact Hsep].
Qed.

(** A list the parser calls loose has a blank the rule counts: inside an
    item, or, when it was written with blank lines between its items,
    after one. *)
Corollary list_spacing_separates : forall sp itemss,
  forallb (fun L => run_safe L (PPara []) && negb (is_blank (hd "" L))) itemss = true ->
  list_spacing_of sp itemss = Loose ->
  (exists L, In L itemss /\ exists i, separates L i)
  \/ (sp = Loose
      /\ exists pre L M post, itemss = (pre ++ L :: M :: post)%list /\ separates_after L).
Proof.
  intros sp itemss Hok H. unfold list_spacing_of in H.
  destruct (existsb (fun L => item_loose L) itemss) eqn:Ei.
  - left. apply existsb_exists in Ei as [L [Hin HL]].
    rewrite forallb_forall in Hok. specialize (Hok L Hin).
    apply andb_true_iff in Hok as [Hs Hh]. apply negb_true_iff in Hh.
    exists L. split; [exact Hin|]. exact (item_loose_separates L Hs Hh HL).
  - right. cbn [orb] in H. destruct sp; [discriminate H|].
    destruct (seps_loosen itemss) eqn:Es; [|discriminate H].
    split; [reflexivity|]. apply seps_loosen_separates; [|exact Es].
    rewrite forallb_forall in Hok |- *. intros L Hin.
    specialize (Hok L Hin). apply andb_true_iff in Hok as [Hs _]. exact Hs.
Qed.

Lemma separates_seps_loosen : forall pre L M post,
  forallb (fun L => run_safe L (PPara [])) (pre ++ L :: M :: post)%list = true ->
  separates_after L -> seps_loosen (pre ++ L :: M :: post)%list = true.
Proof.
  induction pre as [|P pre IH]; intros L M post Hsafe Hsep.
  - cbn [app forallb] in Hsafe. apply andb_true_iff in Hsafe as [HL _].
    cbn [app seps_loosen]. rewrite (separates_after_reaches L HL Hsep). reflexivity.
  - cbn [app forallb] in Hsafe. apply andb_true_iff in Hsafe as [_ Hsafe].
    pose proof (IH L M post Hsafe Hsep) as Hrest.
    cbn [app seps_loosen]. destruct (pre ++ L :: M :: post)%list eqn:E;
      [destruct pre; discriminate E|].
    rewrite Hrest. apply orb_true_r.
Qed.

(** A list written with blank lines between its items is loose when the
    rule counts one of them. *)
Corollary separates_after_loosens : forall pre L M post,
  forallb (fun L => run_safe L (PPara [])) (pre ++ L :: M :: post)%list = true ->
  separates_after L -> list_spacing_of Loose (pre ++ L :: M :: post)%list = Loose.
Proof.
  intros pre L M post Hsafe Hsep. unfold list_spacing_of.
  rewrite (separates_seps_loosen pre L M post Hsafe Hsep), orb_true_r. reflexivity.
Qed.

End WithTable.
