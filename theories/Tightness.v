(* ai-disclosure: ai-generated *)

(** * List tightness, as the syntax reference states it

   "A list is classed as *tight* if it does not contain blank lines
   between items, or between blocks inside an item.  Blank lines at the
   start or end of a list do not count against tightness."

   Read as `.project/list-tightness.md` proposes: a list item, and a
   footnote, ends with its last nonblank line, so a blank after an item
   is between items and always counts; inside an item a blank counts when
   it lies between two of the item's blocks, unless it is directly
   before or directly after a list nested in the item.  A blank inside a
   block nested in the item counts only for that block.

   `ListUniformity.item_loose` and `seps_loosen` decide tightness by
   running the parser's own scan.  This file states the rule inside an
   item without the scan, on the parses of the item's lines, and proves
   that the parser loosens an item only for a blank the rule counts
   (`item_loose_separates`), and for every such blank
   (`separates_item_loose`).  The converse is for a blank that the lines
   before it do not leave inside a code block: such a blank is the
   block's text, and showing that it fails the rule needs two parses that
   differ only in that text.

   "Between two blocks" has no source positions to lean on, so it is said
   with parses (`starts_block`): the next nonblank line, written directly
   after the blank, parses to a block of its own after the blocks of the
   lines before the blank, and so does a paragraph line at its
   indentation.  The first catches a line that continues a table as its
   caption; the second a line inside a block still open, a div or a
   footnote the line is indented into, and it does so for a line that
   makes no block of its own to count.

   "Directly after a nested list" is said with the parse too: the blocks
   of the lines before the blank end in a list, looking through a
   footnote and a keyed block to their last block.  The theorems are for
   items whose lines leave no attribute spec open at a line boundary
   (`run_safe`), where no block attribute is dropped between a list and a
   blank; a blank before a block attribute is decided by the block the
   attribute attaches to (`Step.line_fate`), and counts when it attaches
   to none (`Step.list_settle`), as if the attributes were a block of
   their own. *)

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
  | OrderedList _ _ _ | BulletList _ _ _ | TaskList _ _ | DefinitionList _ _ => true
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

(* A line that decides a blank before it: not a list marker, which opens
   a nested list directly after the blank, and not a block attribute,
   which leaves the blank to the block it attaches to. *)
Definition settles_blank (l : string) : bool :=
  match classify l with
  | KList _ _ _ _ => false
  | KAttr _ => negb battrs
  | _ => true
  end.

(** `l`, written directly after the blank `b` that follows `pre`, starts
    a block of its own: nothing `pre` left open takes it. *)
Definition starts_block (pre : list string) (b l : string) : Prop :=
  parse_lines (pre ++ [b; l]) (PPara [])
  = (parse_lines pre (PPara []) ++ parse_lines [l] (PPara []))%list.

(** The blank at index `i` of an item's lines lies between two of the
    item's blocks, and not directly after a nested list ends or directly
    before one starts.  The next nonblank line starts a block of its own,
    and so would a paragraph line at its indentation. *)
Definition separates (L : list string) (i : nat) : Prop :=
  let pre := firstn i L in
  let b := nth i L "" in
  is_blank b = true
  /\ existsb nonblank pre = true
  /\ ends_list (parse_lines pre (PPara [])) = false
  /\ (exists l, find nonblank (skipn (S i) L) = Some l /\ settles_blank l = true
        /\ starts_block pre b l
        /\ starts_block pre b (blanks (indent_of l) ++ "x")).

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

The rule needs the item's blocks not to end in a list at a blank that
counts, and a blank lands in a block that holds it whenever they do.
`holds_blank` says where a blank lands in such a block: a code block, a
nested list, an unfinished spec, a div holding one of those, a key whose
block announces its end, or pending attributes, a key or a footnote
around one of those.  `tail_ok E st` says that blocks `E` already
emitted and the state `st` still open end in no list when a blank would
not land in such a block.  It is kept through every line of a run; the
three states a blank can rest inside without closing (a footnote,
pending attributes, a key) carry what it needs of their own contents in
`state_ok`, and an open code block carries that a blank cannot close it.
*)

(* Whether a blank here is held by a block below: a line of an open code
   block or of an unfinished attribute spec, or a line of a key's block
   that the key keeps until the block's closing fence.  Read down through
   every container a blank reaches without closing it. *)
Fixpoint held (st : pstate) : bool :=
  match st with
  | PFence _ _ _ _ _ | PAttr _ _ _ _ _ _ => true
  | PKey _ _ _ inner => (announces_end inner || held inner)%bool
  | PDiv _ _ _ _ _ inner | PList _ _ inner | PFoot _ _ _ _ inner
  | PPend _ _ inner => held inner
  | _ => false
  end.

Fixpoint holds_blank (st : pstate) : bool :=
  match st with
  | PFence _ _ _ _ _ | PList _ _ _ | PAttr _ _ _ _ _ _ => true
  | PDiv _ _ _ _ _ inner => held inner
  | PKey _ _ _ inner => (announces_end inner || holds_blank inner)%bool
  | PPend _ _ inner | PFoot _ _ _ _ inner => holds_blank inner
  | _ => false
  end.

Definition tail_ok (E : blocks) (st : pstate) : Prop :=
  holds_blank st = false -> ends_list (E ++ finish st)%list = false.

(* What one line emits, together with the state it leaves, ends in no
   list, whatever came before. *)
Definition tail_new (bs : blocks) (st : pstate) : Prop :=
  holds_blank st = false ->
  (bs ++ finish st)%list <> [] /\ ends_list (bs ++ finish st)%list = false.

Fixpoint state_ok (st : pstate) : Prop :=
  match st with
  (* A blank never closes it. *)
  | PFence f _ _ _ _ => 0 < f_len f
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
  holds_blank st = true -> state_ok st -> fresh bs st.
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
  intros E pend specs st. unfold tail_ok. cbn [holds_blank].
  rewrite (ends_list_map (E ++ finish (PPend pend specs st))%list (E ++ finish st)%list)
    by (rewrite !map_app, finish_pend_ends; reflexivity).
  reflexivity.
Qed.

(* A key finishes to a paragraph when nothing came under it, so what it
   ends in does not depend on what was emitted before it. *)
Lemma tail_ok_key : forall E range lbl src st,
  tail_ok E (PKey range lbl src st) <-> tail_ok [mk (Para [])] st.
Proof.
  intros E range lbl src st. unfold tail_ok. cbn [holds_blank finish]. nopos.
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
  intros Ha. cbn [holds_blank] in Ha. cbn [finish]. nopos. split.
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
    split; [|intros _; reflexivity]. intros Ha. cbn [holds_blank] in Ha.
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
    intros Ha. cbn [holds_blank finish app] in *. nopos.
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

(* A fence a line opens is at least three characters long, so a blank
   never closes it. *)
Lemma classify_fence_len : forall l f, classify l = KFence f -> 3 <= f_len f.
Proof.
  intros l f H. unfold classify in H.
  destruct (is_blank l); [discriminate H|].
  destruct (quote_prefix l); [discriminate H|].
  destruct (heading_open l) as [[? ?]|]; [discriminate H|].
  destruct (fence_open l) as [f'|] eqn:E.
  - injection H as <-. unfold fence_open in E.
    destruct (drop_leading_ws l) as [|c l']; [discriminate E|].
    destruct (Ascii.eqb c "`" || Ascii.eqb c "~")%bool; [|discriminate E].
    destruct (count_run c (String c l')) as [n r].
    destruct (Nat.leb 3 n) eqn:Hn; [|discriminate E].
    repeat match type of E with
           | context [let (_, _) := ?x in _] => destruct x
           | context [if ?b then _ else _] => destruct b
           end; try discriminate E.
    injection E as <-. cbn. apply Nat.leb_le. exact Hn.
  - repeat match type of H with
           | context [match ?x with _ => _ end] => destruct x
           | context [if ?b then _ else _] => destruct b
           end; discriminate H.
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
  - apply fresh_absorbing; [reflexivity|].
    cbn [open_fence snd state_ok]. pose proof (classify_fence_len l f E). lia.
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

Lemma feed_lazy_text : forall l st, held (feed_lazy l st) = held st.
Proof.
  intros l st. induction st; cbn [feed_lazy held]; auto.
  rewrite IHst. destruct st; reflexivity.
Qed.

(* A lazy line lands in a paragraph somewhere down the spine, so it
   changes no container and no block kind. *)
Lemma feed_lazy_ok : forall l st,
  lazy_ok st = true -> state_ok st ->
  state_ok (feed_lazy l st)
  /\ holds_blank (feed_lazy l st) = holds_blank st
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
  - cbn [feed_lazy holds_blank finish]. nopos. repeat split; try reflexivity.
    destruct qhead as [[[kind fold] title]|]; reflexivity.
  - destruct (IH Hl Hs) as [Hs' _].
    cbn [feed_lazy holds_blank finish state_ok]. nopos. rewrite feed_lazy_text.
    split; [exact Hs'|]. repeat split; try reflexivity.
    unfold div_block. destruct bdiv_names; [|destruct (String.eqb dcls "")]; reflexivity.
  - destruct (IH Hl Hs) as [Hs' _].
    cbn [feed_lazy holds_blank finish state_ok]. nopos.
    split; [exact Hs'|]. repeat split; try reflexivity.
    cbn [map]. rewrite !list_block_ends. reflexivity.
  - repeat split; reflexivity.
  - destruct Hs as [Hs Ht]. destruct (IH Hl Hs) as [Hs' [Ha [Hm _]]].
    cbn [feed_lazy holds_blank finish state_ok]. nopos.
    assert (Hmap : map ends_in_list (rev fdone ++ finish (feed_lazy l finner))%list
                   = map ends_in_list (rev fdone ++ finish finner)%list)
      by (rewrite !map_app, Hm; reflexivity).
    split; [split; [exact Hs'|]|split; [exact Ha|split; [|reflexivity]]].
    + intros Ha'. rewrite (ends_list_map _ _ Hmap). apply Ht. congruence.
    + unfold foot_block, mk. cbn [map].
      rewrite !ends_in_list_foot, (ends_list_map _ _ Hmap). reflexivity.
  - destruct Hs as [Hs _]. destruct (IH Hl Hs) as [Hs' [Ha [Hm Hi]]].
    cbn [feed_lazy holds_blank state_ok].
    split; [split; [exact Hs'|exact Hi]|split; [exact Ha|split; [|reflexivity]]].
    rewrite !finish_pend_ends. exact Hm.
  - destruct (IH Hl Hs) as [Hs' [Ha [Hm Hi]]].
    cbn [feed_lazy holds_blank state_ok finish]. nopos.
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
    + apply fresh_step_ok, fresh_absorbing; [reflexivity|exact Hs].
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
    destruct (foot_takes find off l finner); [apply Hcont, Hin|].
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
  (* No key under the div still claims a line: a blank retracts a key
     that was waiting, and `blank_safe` excludes one holding a block. *)
  | PDiv _ _ _ _ _ inner =>
      blank_safe inner = true /\ lazy_ok inner = false
      /\ (forall next, key_claims next inner = false)
  | PFoot _ _ _ _ inner => settled inner
  | PPend _ _ inner => settled inner /\ is_idle inner = false
  | PKey _ _ _ inner =>
      settled inner /\ is_idle inner = false /\ announces_end inner = false
  | _ => False
  end.

Local Lemma state_ok_held_safe : forall st,
  state_ok st -> held st = false -> blank_safe st = true.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hs Ha; cbn [held state_ok] in Ha, Hs; try discriminate Ha; try reflexivity.
  - apply IH; assumption.
  - apply IH; assumption.
  - apply IH; [exact (proj1 Hs)|exact Ha].
  - cbn [blank_safe]. destruct Hs as [Hs Hi]. rewrite (IH Hs Ha), Hi. reflexivity.
  - apply orb_false_iff in Ha as [Hann Ha].
    cbn [blank_safe]. rewrite (IH Hs Ha), Hann. reflexivity.
Qed.

Lemma state_ok_blank_safe : forall st,
  state_ok st -> holds_blank st = false -> blank_safe st = true.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hs Ha; cbn [holds_blank state_ok] in Ha, Hs; try discriminate Ha; try reflexivity.
  - exact (state_ok_held_safe dinner Hs Ha).
  - apply IH; [exact (proj1 Hs)|exact Ha].
  - cbn [blank_safe]. destruct Hs as [Hs Hi]. rewrite (IH Hs Ha), Hi. reflexivity.
  - apply orb_false_iff in Ha as [Hann Ha].
    cbn [blank_safe]. rewrite (IH Hs Ha), Hann. reflexivity.
Qed.

(* No blank a state can safely meet is held below. *)
Lemma blank_safe_not_held : forall st, blank_safe st = true -> held st = false.
Proof.
  induction st; intros H; cbn [blank_safe] in H; cbn [held];
    try discriminate H; try reflexivity; try (apply IHst; exact H).
  - apply andb_true_iff in H as [H _]. apply IHst, H.
  - apply andb_true_iff in H as [H Hn]. apply negb_true_iff in Hn.
    rewrite Hn, (IHst H). reflexivity.
Qed.

Lemma settled_absorbed : forall st, settled st -> holds_blank st = false.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H; cbn [settled] in H; try contradiction; try reflexivity.
  - cbn [holds_blank]. apply blank_safe_not_held, H.
  - apply IH, H.
  - apply IH, H.
  - destruct H as [H [_ Hann]]. cbn [holds_blank]. rewrite Hann, (IH H). reflexivity.
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
  - exact (proj1 (proj2 H)).
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

(* A list a footnote ends in holds a blank. *)
Lemma holds_list_holds : forall st, holds_list st = true -> holds_blank st = true.
Proof.
  induction st; cbn [holds_list holds_blank]; intros H; auto; try discriminate H.
  rewrite (IHst H). apply orb_true_r.
Qed.

Lemma settled_holds_list : forall st, settled st -> holds_list st = false.
Proof.
  intros st H. destruct (holds_list st) eqn:E; [|reflexivity].
  apply holds_list_holds in E. rewrite (settled_absorbed st H) in E. discriminate E.
Qed.

(* A settled state holds no key that claims a line out of column. *)
Lemma settled_no_claim : forall st,
  settled st -> forall l, key_claims l st = false.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H l; cbn [settled] in H; try contradiction; cbn [key_claims];
    try reflexivity.
  - apply H.
  - apply IH, H.
  - apply IH, H.
  - destruct H as [_ [Hni Hann]]. rewrite Hni. exact Hann.
Qed.

(* A blank that nothing absorbs leaves a settled state. *)
Lemma blank_settles : forall l st,
  classify l = KBlank -> blank_safe st = true -> holds_blank st = false ->
  settled (snd (step l st)).
Proof.
  intros l st Hl.
  pose proof (classify_kblank_blank l Hl) as Hb.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe Ha; cbn [holds_blank] in Ha; try discriminate Ha; try discriminate Hsafe.
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
    pose proof (step_blank_key_claims l dinner Hl Hsafe) as Hkc.
    rewrite Es in Hs', Hz, Hkc. cbn [snd] in *.
    exact (conj Hs' (conj Hz Hkc)).
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
  - cbn [keeps_line] in Hk. rewrite (proj1 (proj2 Hset)) in Hk. discriminate Hk.
  - cbn [keeps_line] in Hk. rewrite (settled_lazy finner Hset) in Hk. cbn [negb andb] in Hk.
    apply orb_false_iff in Hk as [Hft _].
    rewrite (step_foot_close l frng find flbl fdone finner (fst (step l (PPara [])))
               (snd (step l (PPara []))) Hb Hft).
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
What a settled state keeps
--------------------------

A div that the blank left open keeps every line the item still has, so
the blank lay inside it.  Whether one is open is a fact about the state
before the blank, the same after any number of them, and so is whether
a footnote or a table keeps a given line.
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

(* A div on top keeps every line. *)
Lemma settled_div_keeps : forall l st,
  settled st -> div_top st = true -> keeps_line 0 l st = true.
Proof.
  intros l.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H Hd; cbn [settled] in H; try contradiction; cbn [div_top] in Hd;
    try discriminate Hd; cbn [keeps_line].
  - rewrite (proj1 (proj2 H)). reflexivity.
  - apply IH; [exact (proj1 H)|exact Hd].
  - apply IH; [exact (proj1 H)|exact Hd].
Qed.

(* Further blanks change nothing about which lines a settled state
   keeps. *)
Lemma settled_blank_keeps : forall l y st,
  classify l = KBlank -> settled st ->
  keeps_line 0 y (snd (step l st)) = keeps_line 0 y st.
Proof.
  intros l y st Hl.
  pose proof (classify_kblank_blank l Hl) as Hb.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hset; pose proof Hset as Hset0; cbn [settled] in Hset; try contradiction.
  - destruct cur; [|contradiction]. rewrite (step_idle l KBlank Hl eq_refl). reflexivity.
  - destruct (settled_blank l _ Hl Hset0) as [_ [Hs' _]].
    rewrite (settled_div_keeps y _ Hs'), (settled_div_keeps y _ Hset0); try reflexivity.
    rewrite (blank_div_top l _ Hl (settled_blank_safe _ Hset0)). reflexivity.
  - destruct (settled_blank l _ Hl Hset) as [_ [Hs' _]].
    unfold step. cbn [step_fuel open_line]. rewrite Hb.
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l finner) as [bs i] eqn:Es. cbn [snd keeps_line] in *.
    rewrite (settled_lazy _ Hs'), (settled_lazy _ Hset).
    unfold foot_takes. rewrite (settled_no_claim _ Hs'), (settled_no_claim _ Hset).
    rewrite (settled_holds_list _ Hs'), (settled_holds_list _ Hset). reflexivity.
  - destruct tcap; try contradiction.
    unfold step. cbn [step_fuel open_line]. rewrite (caption_open_blank l Hb), Hb. reflexivity.
  - destruct Hset as [Hset Hni]. specialize (IH Hset).
    destruct (settled_blank l _ Hl Hset) as [Hnil _].
    unfold step. cbn [step_fuel open_line]. rewrite Hl, Hni.
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l pinner) as [bs st']. cbn [fst snd] in *. subst bs. exact IH.
  - destruct Hset as [Hset [Hni _]]. specialize (IH Hset).
    destruct (settled_blank l _ Hl Hset) as [Hnil _].
    rewrite (step_key_pass l krng klbl ksrc kinner ltac:(rewrite Hni, andb_false_r; reflexivity)).
    destruct (step l kinner) as [bs st']. cbn [fst snd] in *. subst bs. exact IH.
Qed.

(* A paragraph line at `l`'s indentation is kept by a div and by a
   footnote exactly when `l` is, and never by a table. *)
Lemma indent_of_blanks_x : forall n, indent_of (blanks n ++ "x") = n.
Proof.
  intros n. rewrite (indent_of_ws_prefix _ _ (blanks_blank n)), blanks_length.
  cbn. lia.
Qed.

(* In a settled state no key claims a line, so a footnote takes a line by
   its column alone. *)
Lemma keeps_line_para : forall l st,
  settled st -> keeps_line 0 l st = false ->
  keeps_line 0 (blanks (indent_of l) ++ "x") st = false.
Proof.
  intros l. induction st; cbn [keeps_line settled]; intros Hs H; try contradiction; auto.
  - unfold foot_takes in *. rewrite !(settled_no_claim _ Hs) in *.
    rewrite indent_of_blanks_x. exact H.
  - rewrite (caption_open_ws_prefix _ _ (blanks_blank _)). reflexivity.
  - apply IHst; [exact (proj1 Hs)|exact H].
  - apply IHst; [exact (proj1 Hs)|exact H].
Qed.

Lemma kept_cases : forall l st,
  settled st -> keeps_line 0 l st = true ->
  keeps_line 0 (blanks (indent_of l) ++ "x") st = true \/ caption_open l <> None.
Proof.
  intros l. induction st; cbn [keeps_line settled]; intros Hs H;
    try contradiction; auto; try discriminate H.
  - left. unfold foot_takes in *. rewrite !(settled_no_claim _ Hs) in *.
    rewrite indent_of_blanks_x. exact H.
  - right. destruct (caption_open l); [discriminate|discriminate H].
  - apply IHst; [exact (proj1 Hs)|exact H].
  - apply IHst; [exact (proj1 Hs)|exact H].
Qed.

Lemma keeps_not_idle : forall y st, keeps_line 0 y st = true -> is_idle st = false.
Proof. intros y [[|c cur]| | | | | | | | | | | |] H; try reflexivity. discriminate H. Qed.

(* A line a settled state keeps joins the block that is open: the state
   still closes to one block. *)
Lemma kept_one_block : forall y st,
  settled st -> is_blank y = false -> keeps_line 0 y st = true ->
  length (fst (step y st) ++ finish (snd (step y st)))%list = 1.
Proof.
  intros y st Hset Hy.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hk; cbn [settled] in Hset; try contradiction; cbn [keeps_line] in Hk; try discriminate Hk.
  - unfold step. cbn [step_fuel].
    destruct (negb (in_fence dinner) && div_close dlen y)%bool; [reflexivity|].
    destruct (step_fuel _ 0 y dinner). cbn [fst snd finish]. nopos. reflexivity.
  - apply andb_true_iff in Hk as [_ Hk].
    unfold foot_takes in Hk.
    rewrite (settled_no_claim _ Hset), (settled_holds_list _ Hset), orb_false_r in Hk.
    rewrite (step_foot_cont y frng find flbl fdone finner _ _
               ltac:(cbn [Nat.add orb] in Hk; rewrite Hk; apply orb_true_r) (surjective_pairing _)).
    cbn [fst snd finish]. nopos. reflexivity.
  - destruct tcap as [parts|parts|parts start cur]; try contradiction.
    unfold step. cbn [step_fuel]. destruct (caption_open y); [|discriminate Hk].
    cbn [fst snd finish]. nopos. reflexivity.
  - destruct Hset as [Hset Hni]. specialize (IH Hset Hk).
    unfold step. cbn [step_fuel]. rewrite Hni.
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    assert (Hr : length (fst (pend_result ppend pspecs (step y pinner))
                         ++ finish (snd (pend_result ppend pspecs (step y pinner))))%list = 1).
    { destruct (step y pinner) as [[|b bs] st']; cbn [pend_result fst snd app] in *.
      - cbn [finish]. nopos. destruct (finish st') as [|[p a x] r]; [discriminate IH|exact IH].
      - nopos. destruct b. exact IH. }
    destruct (classify y); exact Hr.
  - destruct Hset as [Hset [Hni _]]. specialize (IH Hset Hk).
    rewrite (step_key_pass y krng klbl ksrc kinner ltac:(rewrite Hy; reflexivity)).
    destruct (step y kinner) as [[|b bs] st']; cbn [key_result fst snd app] in *.
    + cbn [finish]. nopos. destruct (finish st') as [|c r]; [discriminate IH|exact IH].
    + nopos. exact IH.
Qed.

(* A nonblank line parsed alone gives a block, unless it is a complete
   attribute spec, which waits for one. *)
Lemma parse_one_ne : forall l,
  is_blank l = false -> (forall ap, classify l <> KAttr ap) ->
  (fst (step l (PPara [])) ++ finish (snd (step l (PPara []))))%list <> [].
Proof.
  intros l Hl Ha. unfold step. cbn [step_fuel].
  destruct (classify l) as [| |f|len cls|rest|lvl rest|sty core chk rest|ap|lbl rest|lbl v|r|]
    eqn:E; cbn [open_line open_kind].
  - apply classify_kblank_blank in E. congruence.
  - discriminate.
  - unfold open_fence. cbn [fst snd finish app]. nopos. discriminate.
  - destruct bdivs; cbn [fst snd finish app]; nopos; discriminate.
  - destruct (quote_header rest) as [[[kind fold] title]|].
    + unfold open_callout. cbn [fst snd finish app]. nopos. discriminate.
    + unfold open_quote. destruct (step_fuel _ _ rest _). cbn [fst snd finish app]. nopos. discriminate.
  - cbn [fst snd finish app]. nopos. discriminate.
  - unfold open_list. destruct (step_fuel _ _ _ _). cbn [fst snd finish app]. nopos. discriminate.
  - destruct (Ha ap eq_refl).
  - unfold open_foot. destruct bfootnotes; [destruct (step_fuel _ _ rest _)|];
      cbn [fst snd finish app]; nopos; discriminate.
  - unfold open_ref. cbn [fst snd finish app]. nopos. discriminate.
  - destruct btables; cbn [fst snd finish app]; nopos; discriminate.
  - unfold open_text. destruct (if bkeyed then key_split _ else None) as [[k v]|];
      cbn [fst snd finish app]; nopos; [apply key_close_ne|discriminate].
Qed.

Lemma caption_not_attr : forall l ap, caption_open l <> None -> classify l <> KAttr ap.
Proof.
  intros l ap Hc E. apply classify_attr_open in E. unfold attr_open in E.
  unfold caption_open in Hc.
  destruct (drop_leading_ws l) as [|c rest]; [discriminate E|].
  destruct c as [[] [] [] [] [] [] [] []]; try discriminate E; cbn in Hc; congruence.
Qed.

Lemma para_not_attr : forall n ap, classify (blanks n ++ "x") <> KAttr ap.
Proof. intros n ap. rewrite (classify_ws_prefix _ _ (blanks_blank n)). discriminate. Qed.

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

(* The nonblank lines a blank stays armed across: lines that leave it to
   a block after them (`Waits`). *)
Fixpoint waits_run (st : pstate) (B : list string) : Prop :=
  match B with
  | [] => True
  | x :: rest =>
      is_blank x = false /\ line_fate 0 x (classify x) st = Waits
      /\ waits_run (snd (step x st)) rest
  end.

(* `lines_loose` turns true at a line that spends a blank armed before
   it.  Read off the scan: that line, the lines the blank stayed armed
   across, and the last blank before them.  Or at a point where block
   attributes wait for a block: a blank they waited on is spent when they
   stop waiting (`Step.stops_waiting`), which a run the theorems admit
   never reaches. *)
Lemma loose_witness : forall L st lo gap,
  lines_loose lo gap st L = true ->
  lo = true
  \/ (gap = true
      /\ exists B l C, L = (B ++ l :: C)%list /\ waits_run st B
         /\ is_blank l = false
         /\ line_fate 0 l (classify l) (snd (run_lines B st)) = Spends)
  \/ (exists A b B l C, L = (A ++ b :: B ++ l :: C)%list /\ is_blank b = true
      /\ waits_run (snd (run_lines (A ++ [b]) st)) B /\ is_blank l = false
      /\ line_fate 0 l (classify l) (snd (run_lines (A ++ b :: B) st)) = Spends)
  \/ (exists A R, L = (A ++ R)%list /\ attr_waits (snd (run_lines A st)) = true).
Proof.
  induction L as [|x rest IH]; intros st lo gap H.
  - cbn [lines_loose] in H. apply orb_true_iff in H as [H|H]; [left; exact H|].
    right; right; right. exists [], []. split; [reflexivity|].
    apply andb_true_iff in H as [H _]. exact H.
  - destruct (attr_waits st) eqn:Haw.
    { right; right; right. exists [], (x :: rest). split; [reflexivity|exact Haw]. }
    (* nothing waits here, so the line decides as `line_fate` says *)
    cbn [lines_loose] in H. unfold fate_after, stops_waiting in H. rewrite Haw in H.
    cbn [andb orb] in H. rewrite ?orb_false_r in H.
    assert (Hshift : (exists A b B l C, rest = (A ++ b :: B ++ l :: C)%list /\ is_blank b = true
      /\ waits_run (snd (run_lines (A ++ [b]) (snd (step x st)))) B /\ is_blank l = false
      /\ line_fate 0 l (classify l) (snd (run_lines (A ++ b :: B) (snd (step x st)))) = Spends) ->
      exists A b B l C, (x :: rest)%list = (A ++ b :: B ++ l :: C)%list /\ is_blank b = true
      /\ waits_run (snd (run_lines (A ++ [b]) st)) B /\ is_blank l = false
      /\ line_fate 0 l (classify l) (snd (run_lines (A ++ b :: B) st)) = Spends).
    { intros (A & b & B & l & C & Hr & Hb & Hw & Hl & Hf). subst rest.
      exists (x :: A), b, B, l, C.
      cbn [app]. rewrite !run_lines_snd_cons. repeat split; assumption. }
    assert (Hshift2 : (exists A R, rest = (A ++ R)%list
                        /\ attr_waits (snd (run_lines A (snd (step x st)))) = true) ->
      exists A R, (x :: rest)%list = (A ++ R)%list /\ attr_waits (snd (run_lines A st)) = true).
    { intros (A & R & Hr & Hw). subst rest. exists (x :: A), R.
      cbn [app]. rewrite run_lines_snd_cons. split; [reflexivity|exact Hw]. }
    destruct (classify x) eqn:E.
    1: { destruct (IH _ _ _ H) as [Hlo|[[_ (B & l & C & -> & Hw & Hl & Hf)]|[Hin|Hin]]].
      * left. exact Hlo.
      * right. right. left. exists [], x, B, l, C.
        cbn [app]. rewrite !run_lines_snd_cons. cbn [run_lines snd].
        repeat split; try assumption. exact (classify_kblank_blank x E).
      * right. right. left. apply Hshift. exact Hin.
      * right. right. right. apply Hshift2. exact Hin. }
    all: destruct (line_fate 0 x _ st) eqn:Hfx.
    all: destruct (IH _ _ _ H) as [Hlo|[[Hg (B & l & C & -> & Hw & Hl & Hf)]|[Hin|Hin]]];
         try (right; right; left; apply Hshift; exact Hin);
         try (right; right; right; apply Hshift2; exact Hin).
    (* spends: the incoming flag is in the verdict *)
    all: try (apply orb_true_iff in Hlo as [Hlo|Hg];
              [left; exact Hlo
              |right; left; split; [exact Hg|]; exists [], x, rest;
               cbn [app run_lines snd waits_run];
               repeat split; [exact (nonblank_of_kind x _ E ltac:(discriminate))|];
               rewrite E; exact Hfx]).
    all: try (discriminate Hg).
    all: try (left; exact Hlo).
    (* waits: the flag rides across the line *)
    all: right; left; split; [exact Hg|]; exists (x :: B), l, C.
    all: cbn [app waits_run]. all: rewrite run_lines_snd_cons.
    all: repeat split; try assumption;
         [exact (nonblank_of_kind x _ E ltac:(discriminate))|rewrite E; exact Hfx].
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

Lemma run_blanks_keeps : forall B y s,
  forallb is_blank B = true -> settled s ->
  keeps_line 0 y (snd (run_lines B s)) = keeps_line 0 y s.
Proof.
  induction B as [|x B IH]; intros y s HB Hs; [reflexivity|].
  cbn [forallb] in HB. apply andb_true_iff in HB as [Hx HB].
  rewrite run_lines_snd_cons.
  destruct (settled_blank x s (classify_blank x Hx) Hs) as [_ [Hs' _]].
  rewrite (IH _ _ HB Hs').
  exact (settled_blank_keeps x y s (classify_blank x Hx) Hs).
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
  blank_safe s = true -> holds_blank s = false -> is_blank b = true ->
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

Lemma parse_one : forall y st,
  parse_lines [y] st = (fst (step y st) ++ finish (snd (step y st)))%list.
Proof. intros y st. cbn [parse_lines]. destruct (step y st). reflexivity. Qed.

(* A line the state after the blank does not keep starts a block of its
   own. *)
Lemma starts_block_unkept : forall A b y,
  blank_safe (snd (run_lines A (PPara []))) = true ->
  holds_blank (snd (run_lines A (PPara []))) = false ->
  is_blank b = true -> is_blank y = false ->
  keeps_line 0 y (snd (step b (snd (run_lines A (PPara []))))) = false ->
  starts_block A b y.
Proof.
  intros A b y Hsafe Ha Hb Hy Hk. unfold starts_block.
  rewrite parse_lines_app_run, (parse_lines_run A (PPara []) _ _ (surjective_pairing _)).
  destruct (run_lines A (PPara [])) as [bs s] eqn:Er. cbn [fst snd] in *.
  change [b; y] with (b :: [] ++ y :: [])%list.
  rewrite (blank_split s b [] y [] Hsafe Ha Hb eq_refl Hy Hk), app_assoc. reflexivity.
Qed.

(* And one it keeps does not: the block it joins and the block it would
   start are one block too many. *)
Lemma kept_not_starts : forall A b y,
  blank_safe (snd (run_lines A (PPara []))) = true ->
  holds_blank (snd (run_lines A (PPara []))) = false ->
  is_blank b = true -> is_blank y = false -> (forall ap, classify y <> KAttr ap) ->
  keeps_line 0 y (snd (step b (snd (run_lines A (PPara []))))) = true ->
  ~ starts_block A b y.
Proof.
  intros A b y Hsafe Ha Hb Hy Hattr Hk H. unfold starts_block in H.
  rewrite parse_lines_app_run, (parse_lines_run A (PPara []) _ _ (surjective_pairing _)) in H.
  destruct (run_lines A (PPara [])) as [bs s] eqn:Er. cbn [fst snd] in *.
  pose proof (classify_blank b Hb) as Eb.
  pose proof (step_blank_finish b s Eb Hsafe) as Hf.
  pose proof (blank_settles b s Eb Hsafe Ha) as Hs1.
  destruct (step b s) as [bs1 s1] eqn:Es. cbn [fst snd] in Hf, Hs1, Hk.
  rewrite (parse_lines_step _ _ _ _ _ Es), !parse_one, <- Hf in H.
  pose proof (kept_one_block y s1 Hs1 Hy Hk) as H1.
  pose proof (settled_finish s1 Hs1 (keeps_not_idle y s1 Hk)) as Hne.
  pose proof (parse_one_ne y Hy Hattr) as Hne0.
  set (P1 := (fst (step y s1) ++ finish (snd (step y s1)))%list) in *.
  set (P0 := (fst (step y (PPara [])) ++ finish (snd (step y (PPara []))))%list) in *.
  apply (f_equal (@length _)) in H. rewrite !length_app, H1 in H.
  destruct (finish s1); [congruence|]. destruct P0; [congruence|].
  cbn [length] in H. lia.
Qed.

Lemma is_blank_para : forall n, is_blank (blanks n ++ "x") = false.
Proof. intros n. rewrite (is_blank_ws_prefix _ _ (blanks_blank n)). reflexivity. Qed.

(* A blank that the item can meet and that does not reach the list ends a
   nested list. *)
Lemma absorbed_ends_list : forall st,
  blank_safe st = true -> holds_blank st = true ->
  finish st <> [] /\ ends_list (finish st) = true.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hs Ha; cbn [holds_blank blank_safe] in Ha, Hs;
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

(*
A blank a block holds
---------------------

A blank that lands in a block holding it changes nothing that block will
emit.  The next line either stays in that block, or, when the block is a
footnote that does not take the line, closes everything before the line,
since a footnote ends with its last nonblank line.
*)

(* A blank leaves no paragraph open where no spec is. *)
Lemma blank_lazy : forall l st,
  classify l = KBlank -> pad_safe st = true -> lazy_ok (snd (step l st)) = false.
Proof.
  intros l st Hblank. induction st as
    [cur|lvl cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe; cbn [pad_safe] in Hsafe; try discriminate Hsafe.
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hblank eq_refl). reflexivity.
    + rewrite (step_para_flush l c cur' Hblank). reflexivity.
  - unfold step. cbn [step_fuel open_line]. destruct bheading_continues;
      rewrite Hblank; reflexivity.
  - unfold step. cbn [step_fuel]. destruct (fence_close f l); reflexivity.
  - rewrite (step_quote_close l KBlank qrng qhead done inner [] (PPara [])
      Hblank eq_refl eq_refl eq_refl). reflexivity.
  - destruct (step l dinner) as [bs inner'] eqn:Hstep.
    rewrite (step_div_cont l dlen dcls drng dop ddone dinner bs inner'
               (div_stays_open_blank l dinner dlen (classify_kblank_blank l Hblank)) Hstep).
    cbn [snd lazy_ok]. exact (IH Hsafe).
  - destruct (step l inner) as [bs inner'] eqn:Hstep.
    rewrite (step_list_blank l ls done inner bs inner' Hblank Hstep).
    cbn [snd lazy_ok]. exact (IH Hsafe).
  - rewrite (step_para_off_flush l okoff ocur Hblank). reflexivity.
  - rewrite (step_ref_blank l rrng rind rlbl rval Hblank). reflexivity.
  - unfold step. cbn [step_fuel open_line]. rewrite (classify_kblank_blank l Hblank).
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l finner) as [bs inner'] eqn:Hs.
    specialize (IH Hsafe). cbn [snd lazy_ok] in IH |- *. exact IH.
  - pose proof (classify_kblank_blank l Hblank) as Hb.
    unfold step. cbn [step_fuel open_line].
    rewrite (caption_open_blank l Hb), Hb.
    destruct tcap; reflexivity.
  - unfold step. cbn [step_fuel open_line]. rewrite Hblank.
    destruct (is_idle pinner); [reflexivity|].
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l pinner) as [bs st'] eqn:Hs.
    specialize (IH Hsafe). cbn [snd] in IH.
    destruct bs as [|b bs']; cbn [pend_result snd lazy_ok]; [exact IH|].
    destruct b. exact IH.
  - destruct (is_idle kinner) eqn:Hidle.
    { destruct kinner as [cur| | | | | | | | | | | |]; try discriminate Hidle.
      destruct cur; [|discriminate Hidle].
      rewrite (step_key_retract l krng klbl ksrc (classify_kblank_blank l Hblank)).
      reflexivity. }
    rewrite (step_key_pass l krng klbl ksrc kinner
               ltac:(rewrite Hidle, andb_false_r; reflexivity)).
    destruct (step l kinner) as [bs st'] eqn:Hs.
    specialize (IH Hsafe). cbn [snd] in IH.
    destruct bs; cbn [key_result snd lazy_ok]; exact IH.
Qed.

(* A blank opens no spec. *)
Lemma blank_pad_safe : forall l st,
  classify l = KBlank -> pad_safe st = true -> pad_safe (snd (step l st)) = true.
Proof.
  intros l st Hblank. induction st as
    [cur|lvl cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe; cbn [pad_safe] in Hsafe; try discriminate Hsafe.
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hblank eq_refl). reflexivity.
    + rewrite (step_para_flush l c cur' Hblank). reflexivity.
  - unfold step. cbn [step_fuel open_line]. destruct bheading_continues;
      rewrite Hblank; reflexivity.
  - unfold step. cbn [step_fuel]. destruct (fence_close f l); reflexivity.
  - rewrite (step_quote_close l KBlank qrng qhead done inner [] (PPara [])
      Hblank eq_refl eq_refl eq_refl). reflexivity.
  - destruct (step l dinner) as [bs inner'] eqn:Hstep.
    rewrite (step_div_cont l dlen dcls drng dop ddone dinner bs inner'
               (div_stays_open_blank l dinner dlen (classify_kblank_blank l Hblank)) Hstep).
    cbn [snd pad_safe]. exact (IH Hsafe).
  - destruct (step l inner) as [bs inner'] eqn:Hstep.
    rewrite (step_list_blank l ls done inner bs inner' Hblank Hstep).
    cbn [snd pad_safe]. exact (IH Hsafe).
  - rewrite (step_para_off_flush l okoff ocur Hblank). reflexivity.
  - rewrite (step_ref_blank l rrng rind rlbl rval Hblank). reflexivity.
  - unfold step. cbn [step_fuel open_line]. rewrite (classify_kblank_blank l Hblank).
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l finner) as [bs inner'] eqn:Hs.
    specialize (IH Hsafe). cbn [snd pad_safe] in IH |- *. exact IH.
  - pose proof (classify_kblank_blank l Hblank) as Hb.
    unfold step. cbn [step_fuel open_line].
    rewrite (caption_open_blank l Hb), Hb.
    destruct tcap; reflexivity.
  - unfold step. cbn [step_fuel open_line]. rewrite Hblank.
    destruct (is_idle pinner); [reflexivity|].
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (step l pinner) as [bs st'] eqn:Hs.
    specialize (IH Hsafe). cbn [snd] in IH.
    destruct bs as [|b bs']; cbn [pend_result snd pad_safe]; [exact IH|].
    destruct b. exact IH.
  - destruct (is_idle kinner) eqn:Hidle.
    { destruct kinner as [cur| | | | | | | | | | | |]; try discriminate Hidle.
      destruct cur; [|discriminate Hidle].
      rewrite (step_key_retract l krng klbl ksrc (classify_kblank_blank l Hblank)).
      reflexivity. }
    rewrite (step_key_pass l krng klbl ksrc kinner
               ltac:(rewrite Hidle, andb_false_r; reflexivity)).
    destruct (step l kinner) as [bs st'] eqn:Hs.
    specialize (IH Hsafe). cbn [snd] in IH.
    destruct bs; cbn [key_result snd pad_safe]; exact IH.
Qed.

(* No attributes wait in a state the invariant admits: `pad_safe` rules
   out a spec, and `state_ok` pending attributes over nothing. *)
Lemma ok_attr_waits : forall st,
  pad_safe st = true -> state_ok st -> attr_waits st = false.
Proof.
  intros st Hp Hs. destruct st as [| | | | | | | | | | |pend specs inner|]; try reflexivity.
  - discriminate Hp.
  - cbn [state_ok] in Hs. destruct Hs as [_ Hni]. exact Hni.
Qed.

(* A blank changes nothing a state with no spec open will emit: what it
   closes it emits, and a code block it lands in drops it again. *)
Lemma blank_finish_ok : forall l st,
  classify l = KBlank -> pad_safe st = true -> state_ok st ->
  (fst (step l st) ++ finish (snd (step l st)))%list = finish st.
Proof.
  intros l st Hl.
  pose proof (classify_kblank_blank l Hl) as Hbl.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
                  |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
                  |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe Hok; cbn [pad_safe state_ok] in Hsafe, Hok; try discriminate Hsafe.
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hl eq_refl). cbn [open_kind fst snd finish app].
      reflexivity.
    + rewrite (step_para_flush l c cur' Hl). reflexivity.
  - rewrite (step_heading_close l lvl hrng cur Hl). reflexivity.
  - (* the blank is a line of the code block, which `finish` drops *)
    assert (Hc : fence_close f l = false).
    { unfold fence_close. rewrite (drop_leading_ws_blank l Hbl). cbn [count_run].
      destruct (f_len f) as [|n]; [lia|reflexivity]. }
    rewrite (step_fence_content l f fnd crng cop acc Hc).
    cbn [fst snd finish app drop_blank_lines remember_line].
    rewrite is_blank_drop_ws_upto, Hbl. reflexivity.
  - rewrite (step_quote_close l KBlank qrng qhead done inner _ _ Hl eq_refl eq_refl
               (surjective_pairing _)).
    cbn [fst snd open_kind finish app]. reflexivity.
  - rewrite (step_div_cont l dlen dcls drng dop ddone dinner _ _
               (div_stays_open_blank l dinner dlen Hbl) (surjective_pairing _)).
    cbn [fst snd finish app].
    rewrite rev_app_distr, rev_involutive, <- app_assoc, (IH Hsafe Hok).
    reflexivity.
  - rewrite (step_list_blank l ls done inner _ _ Hl (surjective_pairing _)).
    cbn [fst snd finish app list_blank ls_loose ls_items].
    rewrite rev_app_distr, rev_involutive, <- app_assoc, (IH Hsafe Hok).
    (* no attributes wait on either side of the blank *)
    pose proof (step_ok_step l inner Hsafe Hok) as (Hok' & _).
    unfold stops_waiting.
    rewrite (ok_attr_waits inner Hsafe Hok),
      (ok_attr_waits _ (blank_pad_safe l inner Hl Hsafe) Hok').
    rewrite !list_settle_false. reflexivity.
  - rewrite (step_para_off_flush l okoff ocur Hl). reflexivity.
  - rewrite (step_ref_blank l rrng rind rlbl rval Hl). reflexivity.
  - destruct Hok as [Hok _].
    destruct (step l finner) as [bs inner'] eqn:Hs.
    assert (Hfoot : step l (PFoot frng find flbl fdone finner) =
              ([], PFoot (touch_extent frng) find flbl (rev bs ++ fdone)%list inner')).
    { unfold step. cbn [step_fuel open_line pstate_depth]. rewrite Hbl.
      rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
      rewrite Hs. reflexivity. }
    rewrite Hfoot. cbn [fst snd finish app].
    specialize (IH Hsafe Hok). cbn [fst snd] in IH.
    rewrite rev_app_distr, rev_involutive, <- app_assoc, IH.
    reflexivity.
  - unfold step. cbn [step_fuel open_line].
    rewrite (caption_open_blank l Hbl), Hbl.
    destruct tcap; cbn [finish app]; reflexivity.
  - destruct Hok as [Hok Hni].
    unfold step. cbn [step_fuel open_line]. rewrite Hl, Hni.
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    specialize (IH Hsafe Hok).
    destruct (step l pinner) as [bs st'] eqn:Hs.
    cbn [fst snd] in IH. cbn [pend_result]; nopos.
    destruct bs as [|b bs'].
    + cbn [fst snd finish app]. rewrite <- IH. reflexivity.
    + cbn [fst snd finish]. rewrite decorate_head_cons_app, <- IH. reflexivity.
  - destruct (is_idle kinner) eqn:Hidle.
    { destruct kinner as [cur| | | | | | | | | | | |]; try discriminate Hidle.
      destruct cur; [|discriminate Hidle].
      rewrite (step_key_retract l krng klbl ksrc Hbl).
      reflexivity. }
    rewrite (step_key_pass l krng klbl ksrc kinner
               ltac:(rewrite Hidle, andb_false_r; reflexivity)).
    specialize (IH Hsafe Hok).
    destruct (step l kinner) as [bs st'] eqn:Hs.
    cbn [fst snd] in IH. cbn [key_result].
    destruct bs as [|b bs'].
    cbn [app] in IH.
    + cbn [fst snd]. rewrite !finish_key, IH. reflexivity.
    + cbn [fst snd]. rewrite finish_key, <- IH.
      cbn [key_close]. rewrite <- app_comm_cons. reflexivity.
Qed.

(* A blank held below stays held, and nothing is emitted. *)
Lemma held_step : forall l st,
  classify l = KBlank -> pad_safe st = true -> state_ok st -> held st = true ->
  fst (step l st) = [] /\ held (snd (step l st)) = true.
Proof.
  intros l st Hl.
  pose proof (classify_kblank_blank l Hl) as Hbl.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
                  |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
                  |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hsafe Hok Hh; cbn [pad_safe state_ok held] in Hsafe, Hok, Hh;
    try discriminate Hsafe; try discriminate Hh.
  - assert (Hc : fence_close f l = false).
    { unfold fence_close. rewrite (drop_leading_ws_blank l Hbl). cbn [count_run].
      destruct (f_len f) as [|n]; [lia|reflexivity]. }
    rewrite (step_fence_content l f fnd crng cop acc Hc). split; reflexivity.
  - destruct (step l dinner) as [bs inner'] eqn:Hs.
    rewrite (step_div_cont l dlen dcls drng dop ddone dinner bs inner'
               (div_stays_open_blank l dinner dlen Hbl) Hs).
    destruct (IH Hsafe Hok Hh) as [_ IH']. split; [reflexivity|exact IH'].
  - destruct (step l inner) as [bs inner'] eqn:Hs.
    rewrite (step_list_blank l ls done inner bs inner' Hl Hs).
    destruct (IH Hsafe Hok Hh) as [_ IH']. split; [reflexivity|exact IH'].
  - destruct Hok as [Hok _].
    destruct (step l finner) as [bs inner'] eqn:Hs.
    assert (Hfoot : step l (PFoot frng find flbl fdone finner) =
              ([], PFoot (touch_extent frng) find flbl (rev bs ++ fdone)%list inner')).
    { unfold step. cbn [step_fuel open_line pstate_depth]. rewrite Hbl.
      rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
      rewrite Hs. reflexivity. }
    rewrite Hfoot. destruct (IH Hsafe Hok Hh) as [_ IH']. split; [reflexivity|exact IH'].
  - destruct Hok as [Hok Hni].
    unfold step. cbn [step_fuel open_line]. rewrite Hl, Hni.
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    destruct (IH Hsafe Hok Hh) as [Hnil IH'].
    destruct (step l pinner) as [bs st'] eqn:Hs. cbn [fst snd] in Hnil, IH'. subst bs.
    split; [reflexivity|exact IH'].
  - assert (Hni : is_idle kinner = false)
      by (destruct kinner as [[|]| | | | | | | | | | | |]; try reflexivity; discriminate Hh).
    rewrite (step_key_pass l krng klbl ksrc kinner
               ltac:(rewrite Hni, andb_false_r; reflexivity)).
    destruct (held kinner) eqn:Hk.
    + destruct (IH Hsafe Hok eq_refl) as [Hnil IH'].
      destruct (step l kinner) as [bs st'] eqn:Hs. cbn [fst snd] in Hnil, IH'. subst bs.
      cbn [key_result fst snd held]. rewrite IH'. split; [reflexivity|apply orb_true_r].
    + (* a key whose block announces its end: a code block, which a fence
         is held by, or a div, which a blank does not close *)
      rewrite orb_false_r in Hh. destruct kinner; try discriminate Hh.
      * cbn [held] in Hk. discriminate Hk.
      * destruct (step l kinner) as [bs inner'] eqn:Hs.
        rewrite (step_div_cont l len cls range open_line_span done kinner bs inner'
                   (div_stays_open_blank l kinner len Hbl) Hs).
        cbn [key_result fst snd held announces_end]. split; reflexivity.
Qed.

(* A held blank's block, when it is not a list, ends in no list. *)
Lemma held_not_list : forall st,
  pad_safe st = true -> holds_blank st = true -> holds_list st = false ->
  finish st <> [] /\ ends_list (finish st) = false.
Proof.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hs Ha Hl; cbn [holds_blank holds_list pad_safe] in Ha, Hl, Hs;
    try discriminate Ha; try discriminate Hl; try discriminate Hs.
  - cbn [finish]. nopos. split; [discriminate|].
    cbn [ends_list map last]. unfold fence_block.
    destruct (f_info f) as [|a rest]; [reflexivity|].
    destruct a as [[] [] [] [] [] [] [] []]; try reflexivity;
    destruct braw_blocks; reflexivity.
  - cbn [finish]. nopos. split; [discriminate|].
    cbn [ends_list map last]. unfold div_block.
    destruct bdiv_names; [|destruct (String.eqb dcls "")]; reflexivity.
  - destruct (IH Hs Ha Hl) as [Hne Hend]. cbn [finish]. nopos. split; [discriminate|].
    unfold foot_block, mk, ends_list. cbn [map last]. rewrite ends_in_list_foot.
    rewrite ends_list_app by exact Hne. exact Hend.
  - destruct (IH Hs Ha Hl) as [Hne Hend]. cbn [finish]. nopos. split.
    + destruct (finish pinner) as [|[p a x] bs]; [contradiction|discriminate].
    + rewrite <- Hend. apply ends_list_map. apply decorate_head_ends.
  - cbn [finish]. nopos. split; [apply key_close_ne|]. rewrite ends_list_key_close.
    destruct (holds_blank kinner) eqn:Hk.
    + exact (proj2 (IH Hs eq_refl Hl)).
    + rewrite orb_false_r in Ha. destruct kinner; try discriminate Ha.
      * cbn [finish]. nopos. cbn [ends_list map last]. unfold fence_block.
        destruct (f_info f) as [|a rest]; [reflexivity|].
        destruct a as [[] [] [] [] [] [] [] []]; try reflexivity;
        destruct braw_blocks; reflexivity.
      * cbn [finish]. nopos. cbn [ends_list map last]. unfold div_block.
        destruct bdiv_names; [|destruct (String.eqb cls "")]; reflexivity.
Qed.

(* A key that claims a paragraph line claims every line. *)
Lemma key_claims_para : forall n y st,
  key_claims (blanks n ++ "x") st = true -> key_claims y st = true.
Proof.
  intros n y st. induction st; cbn [key_claims]; intros H; auto.
  destruct (is_idle st); [|exact H].
  rewrite (classify_ws_prefix _ _ (blanks_blank n)) in H. discriminate H.
Qed.

(* A held blank leaves the state holding, emitting nothing; a line the
   state then does not keep closes everything before it, which ends in no
   list, and a paragraph line at its indentation is not kept either. *)
Lemma held_blank : forall b st,
  classify b = KBlank -> pad_safe st = true -> state_ok st -> holds_blank st = true ->
  let st' := snd (step b st) in
  fst (step b st) = [] /\ pad_safe st' = true /\ state_ok st'
  /\ holds_blank st' = true /\ finish st' = finish st
  /\ (forall y, is_blank y = false -> keeps_line 0 y st' = false ->
        step y st' = ((finish st' ++ fst (step y (PPara [])))%list, snd (step y (PPara [])))
        /\ finish st <> [] /\ ends_list (finish st) = false
        /\ keeps_line 0 (blanks (indent_of y) ++ "x") st' = false).
Proof.
  intros b st Hb. pose proof (classify_kblank_blank b Hb) as Hbl.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
                  |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
                  |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros Hp Hs Hh; cbv zeta;
    pose proof (blank_pad_safe b _ Hb Hp) as Hp';
    pose proof (proj1 (step_ok_step b _ Hp Hs)) as Hs';
    pose proof (blank_finish_ok b _ Hb Hp Hs) as Hfin;
    cbn [holds_blank] in Hh; try discriminate Hh; cbn [pad_safe] in Hp; try discriminate Hp.
  - (* a code block keeps every line after the blank *)
    cbn [state_ok] in Hs.
    assert (Hc : fence_close f b = false).
    { unfold fence_close. rewrite (drop_leading_ws_blank b Hbl). cbn [count_run].
      destruct (f_len f) as [|n]; [lia|reflexivity]. }
    rewrite (step_fence_content b f fnd crng cop acc Hc) in *. cbn [fst snd app] in *.
    split; [reflexivity|]. split; [exact Hp'|]. split; [exact Hs'|]. split; [reflexivity|].
    split; [exact Hfin|]. intros y Hy Hk. discriminate Hk.
  - (* so does a div, with no paragraph open after the blank *)
    cbn [state_ok] in Hs.
    pose proof (held_step b dinner Hb Hp Hs Hh) as [_ Hh'].
    pose proof (blank_lazy b dinner Hb Hp) as Hlz.
    destruct (step b dinner) as [bs inner'] eqn:Es. cbn [snd] in Hh', Hlz.
    rewrite (step_div_cont b dlen dcls drng dop ddone dinner bs inner'
               (div_stays_open_blank b dinner dlen Hbl) Es) in *. cbn [fst snd app] in *.
    split; [reflexivity|]. split; [exact Hp'|]. split; [exact Hs'|]. split; [exact Hh'|].
    split; [exact Hfin|]. intros y Hy Hk. cbn [keeps_line] in Hk. rewrite Hlz in Hk. discriminate Hk.
  - (* and a nested list *)
    cbn [state_ok] in Hs.
    pose proof (blank_lazy b inner Hb Hp) as Hlz.
    destruct (step b inner) as [bs inner'] eqn:Es. cbn [snd] in Hlz.
    rewrite (step_list_blank b ls done inner bs inner' Hb Es) in *. cbn [fst snd app] in *.
    split; [reflexivity|]. split; [exact Hp'|]. split; [exact Hs'|]. split; [reflexivity|].
    split; [exact Hfin|]. intros y Hy Hk. cbn [keeps_line] in Hk. rewrite Hlz in Hk. discriminate Hk.
  - (* a footnote that does not take the line closes before it *)
    cbn [state_ok] in Hs. destruct Hs as [Hsi _].
    pose proof (blank_lazy b finner Hb Hp) as Hlz.
    destruct (IH Hp Hsi Hh) as (Hnil & Hpi & Hsi' & Hhi & Hfini & _). cbv zeta in *.
    destruct (step b finner) as [bs inner'] eqn:Es. cbn [fst snd] in *. subst bs.
    assert (Hfoot : step b (PFoot frng find flbl fdone finner) =
              ([], PFoot (touch_extent frng) find flbl (rev [] ++ fdone)%list inner')).
    { unfold step. cbn [step_fuel open_line pstate_depth]. rewrite Hbl.
      rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
      rewrite Es. reflexivity. }
    rewrite Hfoot in *. cbn [fst snd rev app] in *.
    split; [reflexivity|]. split; [exact Hp'|]. split; [exact Hs'|]. split; [exact Hhi|].
    split; [exact Hfin|].
    intros y Hy Hk. cbn [keeps_line] in Hk. rewrite Hlz in Hk. cbn [negb andb] in Hk.
    apply orb_false_iff in Hk as [Hft Hhl].
    destruct (held_not_list inner' Hpi Hhi Hhl) as [Hne Hend]. rewrite Hfini in Hne, Hend.
    split; [|split; [|split]].
    + rewrite (step_foot_close y (touch_extent frng) find flbl fdone inner'
                 (fst (step y (PPara []))) (snd (step y (PPara []))) Hy Hft).
      * cbn [finish]. nopos. reflexivity.
      * unfold is_lazy. rewrite Hlz. destruct (classify y); reflexivity.
      * apply surjective_pairing.
    + cbn [finish]. nopos. discriminate.
    + cbn [finish]. nopos.
      unfold foot_block, mk, ends_list. cbn [map last]. rewrite ends_in_list_foot.
      rewrite ends_list_app by exact Hne. exact Hend.
    + cbn [keeps_line]. rewrite Hlz, Hhl. cbn [negb andb]. rewrite orb_false_r.
      unfold foot_takes in Hft |- *. apply orb_false_iff in Hft as [Hkc Hcol].
      destruct (key_claims (blanks (indent_of y) ++ "x") inner') eqn:Hkx.
      * rewrite (key_claims_para _ y _ Hkx) in Hkc. discriminate Hkc.
      * rewrite indent_of_blanks_x. exact Hcol.
  - (* pending attributes wait over what is under them *)
    cbn [state_ok] in Hs. destruct Hs as [Hsi Hni].
    pose proof (step_ok_step b pinner Hp Hsi) as (_ & _ & _ & Hidle).
    destruct (IH Hp Hsi Hh) as (Hnil & Hpi & Hsi' & Hhi & Hfini & Hcli). cbv zeta in *.
    destruct (step b pinner) as [bs inner'] eqn:Es. cbn [fst snd] in *. subst bs.
    specialize (Hidle Hni eq_refl).
    assert (Hpend : step b (PPend ppend pspecs pinner) = ([], PPend ppend pspecs inner')).
    { unfold step. cbn [step_fuel open_line]. rewrite Hb, Hni.
      rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
      rewrite Es. reflexivity. }
    rewrite Hpend in *. cbn [fst snd app] in *.
    split; [reflexivity|]. split; [exact Hp'|]. split; [exact Hs'|]. split; [exact Hhi|].
    split; [exact Hfin|].
    intros y Hy Hk. cbn [keeps_line] in Hk.
    destruct (Hcli y Hy Hk) as (Hry & Hne & Hend & Hkx).
    split; [|split; [|split]].
    + assert (Hst : step y (PPend ppend pspecs inner')
                    = pend_result ppend pspecs (step y inner')).
      { unfold step at 1. cbn [step_fuel open_line].
        rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
        destruct (classify y) eqn:Ey; try reflexivity.
        - apply classify_kblank_blank in Ey. congruence.
        - rewrite Hidle. reflexivity. }
      rewrite Hst, Hry. rewrite <- Hfini in Hne.
      destruct (finish inner') as [|c cs] eqn:Ef; [contradiction|].
      cbn [pend_result app finish]. rewrite Ef. nopos.
      rewrite decorate_head_cons_app. reflexivity.
    + cbn [finish]. nopos.
      destruct (finish pinner) as [|[p a x] bs]; [contradiction|discriminate].
    + rewrite (ends_list_map _ (finish pinner)) by apply finish_pend_ends. exact Hend.
    + cbn [keeps_line]. exact Hkx.
  - (* a key: over a block that holds the blank, as that block does; over
       a code block or div whose end it announces, keeping every line *)
    cbn [state_ok] in Hs.
    assert (Hni : is_idle kinner = false).
    { destruct kinner as [[|]| | | | | | | | | | | |]; try reflexivity; discriminate Hh. }
    pose proof (step_key_pass b krng klbl ksrc kinner
                 ltac:(rewrite Hni, andb_false_r; reflexivity)) as Hkp.
    pose proof (blank_lazy b kinner Hb Hp) as Hlz.
    destruct (holds_blank kinner) eqn:Hk.
    + destruct (IH Hp Hs eq_refl) as (Hnil & Hpi & Hsi' & Hhi & Hfini & Hcli). cbv zeta in *.
      destruct (step b kinner) as [bs inner'] eqn:Es. cbn [fst snd] in *. subst bs.
      cbn [key_result] in Hkp. rewrite Hkp in *. cbn [fst snd app] in *.
      split; [reflexivity|]. split; [exact Hp'|]. split; [exact Hs'|].
      split; [cbn [holds_blank]; rewrite Hhi; apply orb_true_r|].
      split; [exact Hfin|].
      intros y Hy Hky. cbn [keeps_line] in Hky.
      destruct (Hcli y Hy Hky) as (Hry & Hne & Hend & Hkx).
      split; [|split; [|split]].
      * rewrite (step_key_pass y (touch_extent krng) klbl ksrc inner'
                   ltac:(rewrite Hy; reflexivity)).
        rewrite Hry. rewrite <- Hfini in Hne.
        destruct (finish inner') as [|c cs] eqn:Ef; [contradiction|].
        cbn [key_result app]. rewrite finish_key, Ef. nopos. reflexivity.
      * rewrite finish_key. nopos. apply key_close_ne.
      * rewrite finish_key. nopos. rewrite ends_list_key_close. exact Hend.
      * cbn [keeps_line]. exact Hkx.
    + rewrite orb_false_r in Hh. destruct kinner; try discriminate Hh.
      * cbn [state_ok] in Hs.
        assert (Hc : fence_close f b = false).
        { unfold fence_close. rewrite (drop_leading_ws_blank b Hbl). cbn [count_run].
          destruct (f_len f) as [|n]; [lia|reflexivity]. }
        rewrite (step_fence_content b f ind range open_line_span acc Hc) in Hkp.
        cbn [key_result] in Hkp. rewrite Hkp in *. cbn [fst snd app] in *.
        split; [reflexivity|]. split; [exact Hp'|]. split; [exact Hs'|]. split; [reflexivity|].
        split; [exact Hfin|]. intros y Hy Hky. discriminate Hky.
      * destruct (step b kinner) as [bs inner'] eqn:Es.
        rewrite (step_div_cont b len cls range open_line_span done kinner bs inner'
                   (div_stays_open_blank b kinner len Hbl) Es) in Hkp, Hlz.
        cbn [key_result] in Hkp. rewrite Hkp in *. cbn [fst snd app] in *.
        split; [reflexivity|]. split; [exact Hp'|]. split; [exact Hs'|]. split; [reflexivity|].
        split; [exact Hfin|]. intros y Hy Hky. cbn [keeps_line lazy_ok] in Hky, Hlz.
        rewrite Hlz in Hky. discriminate Hky.
Qed.

(*
The theorems
============
*)

(* The run past a prefix is safe from where the prefix leaves it. *)
Lemma run_safe_app : forall A R st,
  run_safe (A ++ R)%list st = true -> run_safe R (snd (run_lines A st)) = true.
Proof.
  induction A as [|x A IH]; intros R st H; [exact H|].
  cbn [app run_safe] in H. apply andb_true_iff in H as [_ H].
  rewrite run_lines_snd_cons. apply IH, H.
Qed.

(* A line that spends a blank is one the state does not keep, and one
   that settles it. *)
Lemma spends_facts : forall l st,
  line_fate 0 l (classify l) st = Spends ->
  spec_open st = false /\ keeps_line 0 l st = false /\ settles_blank l = true.
Proof.
  intros l st H. unfold line_fate in H.
  destruct (spec_open st); [discriminate H|].
  destruct (keeps_line 0 l st); [discriminate H|].
  split; [reflexivity|]. split; [reflexivity|]. unfold settles_blank.
  destruct (classify l); try reflexivity; try discriminate H.
  destruct (@battrs K); [discriminate H|reflexivity].
Qed.

(* A line that waits where no spec is open and the state does not keep it
   is a block attribute, and it opens a spec from idle. *)
Lemma waits_opens_spec : forall x st,
  spec_open st = false -> keeps_line 0 x st = false ->
  line_fate 0 x (classify x) st = Waits ->
  pad_safe (snd (step x (PPara []))) = false.
Proof.
  intros x st Hs Hk H. unfold line_fate in H. rewrite Hs, Hk in H.
  destruct (classify x) eqn:E; try discriminate H.
  destruct (@battrs K) eqn:Hb; [|discriminate H].
  unfold step. cbn [step_fuel]. rewrite E. cbn [open_line]. unfold open_attr. rewrite Hb.
  reflexivity.
Qed.

Lemma settled_spec : forall st, settled st -> spec_open st = false.
Proof. intros [] H; cbn [settled] in H; try contradiction; reflexivity. Qed.

(* After a blank, a line that waits would open a spec, and the run would
   not be safe at the line after it. *)
Lemma waits_nil : forall B st y R,
  (forall x, is_blank x = false -> keeps_line 0 x st = false ->
     snd (step x st) = snd (step x (PPara []))) ->
  spec_open st = false ->
  waits_run st B -> run_safe (B ++ y :: R)%list st = true -> B = [].
Proof.
  intros [|x B] st y R Hr Hs Hw Hsafe; [reflexivity|exfalso].
  cbn [waits_run] in Hw. destruct Hw as [Hx [Hf _]].
  destruct (keeps_line 0 x st) eqn:Hk.
  { unfold line_fate in Hf. rewrite Hs, Hk in Hf. discriminate Hf. }
  pose proof (waits_opens_spec x st Hs Hk Hf) as Hp.
  rewrite <- (Hr x Hx Hk) in Hp.
  cbn [app run_safe] in Hsafe. apply andb_true_iff in Hsafe as [_ Hsafe].
  destruct (B ++ y :: R)%list as [|z rest] eqn:E;
    [destruct B; discriminate E|].
  cbn [run_safe] in Hsafe. rewrite Hp in Hsafe. discriminate Hsafe.
Qed.

(* A safe run never stops where attributes wait: inside it `pad_safe`
   and `state_ok` hold, and at its end `blank_safe`. *)
Lemma run_safe_attr_waits : forall A R,
  run_safe (A ++ R)%list (PPara []) = true ->
  attr_waits (snd (run_lines A (PPara []))) = false.
Proof.
  intros A R Hsafe.
  destruct (run_ok A R (PPara []) [] Hsafe I tail_ok_idle_nil) as [Hs _].
  pose proof (run_safe_app A R _ Hsafe) as HR.
  destruct R as [|x R]; cbn [run_safe] in HR.
  - exact (blank_safe_attr_waits _ HR).
  - apply andb_true_iff in HR as [Hp _]. exact (ok_attr_waits _ Hp Hs).
Qed.

(** The parser loosens an item only at a blank the rule counts. *)
Theorem item_loose_separates : forall L,
  run_safe L (PPara []) = true -> is_blank (hd "" L) = false ->
  item_loose L = true -> exists i, separates L i.
Proof.
  intros L Hsafe Hhd Hloose. unfold item_loose in Hloose.
  destruct (loose_witness L (PPara []) false false Hloose)
    as [H|[[H _]|[(A & b & B & l & C & -> & Hb & Hw & Hl & Hf)|(A & R & -> & Hw)]]];
    try discriminate H.
  2: { rewrite (run_safe_attr_waits A R Hsafe) in Hw. discriminate Hw. }
  exists (length A).
  destruct (run_ok A (b :: B ++ l :: C)%list (PPara []) [] Hsafe I tail_ok_idle_nil)
    as [Hs Ht].
  pose proof (run_safe_app A _ _ Hsafe) as HsafeA.
  set (sA := snd (run_lines A (PPara []))) in *.
  assert (Hp : pad_safe sA = true)
    by (cbn [run_safe] in HsafeA; apply andb_true_iff in HsafeA as [Hp _]; exact Hp).
  assert (HsafeB : run_safe (B ++ l :: C)%list (snd (step b sA)) = true)
    by (cbn [run_safe] in HsafeA; apply andb_true_iff in HsafeA as [_ H]; exact H).
  rewrite run_lines_snd_app in Hw, Hf. fold sA in Hw, Hf.
  cbn [run_lines] in Hw. rewrite run_lines_snd_cons in Hf.
  replace (snd (let (bs, st') := step b sA in
                let (more, final) := run_lines [] st' in (bs ++ more, final))%list)
    with (snd (step b sA)) in Hw
    by (destruct (step b sA); reflexivity).
  assert (HA : A <> []) by (intros ->; cbn [hd app] in Hhd; congruence).
  unfold separates.
  rewrite nth_middle, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
  replace (skipn (S (length A)) (A ++ b :: B ++ l :: C))%list with (B ++ l :: C)%list
    by (rewrite skipn_app, skipn_all2 by lia;
        replace (S (length A) - length A) with 1 by lia; reflexivity).
  split; [exact Hb|]. split.
  { destruct A as [|a A']; [congruence|]. cbn [hd app] in Hhd. cbn [existsb].
    unfold nonblank at 1. rewrite Hhd. reflexivity. }
  rewrite (parse_lines_run A (PPara []) _ _ (surjective_pairing _)). fold sA.
  pose proof (classify_blank b Hb) as Eb.
  destruct (holds_blank sA) eqn:Ha.
  - (* the blank lands in a block that holds it: a footnote that does not
       take the next line, which closes before it *)
    destruct (held_blank b sA Eb Hp Hs Ha) as (Hnil & Hp1 & Hs1 & _ & Hfin & Hcl).
    set (s1 := snd (step b sA)) in *.
    assert (HB : B = []).
    { apply (waits_nil B s1 l C); [|apply spec_open_pad_safe, Hp1|exact Hw|exact HsafeB].
      intros x Hx Hk. destruct (Hcl x Hx Hk) as [Hr _]. rewrite Hr. reflexivity. }
    subst B. cbn [run_lines snd] in Hf. fold s1 in Hf.
    destruct (spends_facts l s1 Hf) as (_ & Hk & Hset).
    destruct (Hcl l Hl Hk) as (Hrl & Hne & Hend & Hkx).
    destruct (Hcl _ (is_blank_para (indent_of l)) Hkx) as (Hrx & _).
    assert (Hsplit : forall y, step y s1
                 = ((finish s1 ++ fst (step y (PPara [])))%list, snd (step y (PPara []))) ->
               starts_block A b y).
    { intros y Hy. unfold starts_block.
      rewrite parse_lines_app_run, (parse_lines_run A (PPara []) _ _ (surjective_pairing _)).
      destruct (run_lines A (PPara [])) as [bsA stA] eqn:EA. cbn [fst snd].
      change stA with sA.
      rewrite (parse_lines_step _ _ _ _ _ (surjective_pairing (step b sA))).
      fold s1. rewrite Hnil, app_nil_l, parse_one, Hy, Hfin. cbn [fst snd].
      rewrite parse_one, !app_assoc. reflexivity. }
    split; [rewrite ends_list_app by exact Hne; exact Hend|].
    exists l. split; [exact (find_after_blanks [] l C eq_refl Hl)|].
    split; [exact Hset|]. split; [exact (Hsplit l Hrl)|exact (Hsplit _ Hrx)].
  - (* the blank lands in no block: the item's blocks end there *)
    pose proof (state_ok_blank_safe _ Hs Ha) as Hbs.
    pose proof (blank_settles b sA Eb Hbs Ha) as Hs1.
    set (s1 := snd (step b sA)) in *.
    assert (HB : B = []).
    { apply (waits_nil B s1 l C); [|apply settled_spec, Hs1|exact Hw|exact HsafeB].
      intros x Hx Hk. rewrite (settled_restart x s1 Hs1 Hx Hk). reflexivity. }
    subst B. cbn [run_lines snd] in Hf. fold s1 in Hf.
    destruct (spends_facts l s1 Hf) as (_ & Hk & Hset).
    split; [exact (Ht Ha)|].
    exists l. split; [exact (find_after_blanks [] l C eq_refl Hl)|]. split; [exact Hset|]. split.
    + exact (starts_block_unkept A b l Hbs Ha Hb Hl Hk).
    + exact (starts_block_unkept A b _ Hbs Ha Hb (is_blank_para _) (keeps_line_para l _ Hs1 Hk)).
Qed.

(* The scan's flags at a line, whatever came before it. *)
Lemma lines_loose_reach : forall A lo gap st R,
  exists lo' gap',
    lines_loose lo gap st (A ++ R)%list = lines_loose lo' gap' (snd (run_lines A st)) R.
Proof.
  induction A as [|a A IH]; intros lo gap st R; [exists lo, gap; reflexivity|].
  cbn [app lines_loose]. rewrite run_lines_snd_cons.
  destruct (classify a); try apply IH.
  all: destruct (fate_after st _ (line_fate 0 a _ st)); apply IH.
Qed.

Lemma settled_attr_waits : forall st, settled st -> attr_waits st = false.
Proof.
  intros st H. destruct st as [[|]| | | | | | | | | | |pend specs inner|];
    cbn [settled] in H; try contradiction; try reflexivity.
  destruct H as [_ Hni]. exact Hni.
Qed.

(* Blanks after a settled state only keep the flag armed. *)
Lemma lines_loose_blanks : forall B lo st R,
  forallb is_blank B = true -> settled st ->
  lines_loose lo true st (B ++ R)%list = lines_loose lo true (snd (run_lines B st)) R.
Proof.
  induction B as [|x B IH]; intros lo st R HB Hs; [reflexivity|].
  cbn [forallb] in HB. apply andb_true_iff in HB as [Hx HB].
  cbn [app lines_loose]. rewrite run_lines_snd_cons, (classify_blank x Hx).
  unfold stops_waiting. rewrite (settled_attr_waits st Hs), andb_false_l, orb_false_r.
  destruct (settled_blank x st (classify_blank x Hx) Hs) as (_ & Hs' & _).
  apply IH; assumption.
Qed.

Lemma lines_loose_true : forall R gap st, lines_loose true gap st R = true.
Proof.
  induction R as [|x R IH]; intros gap st; [reflexivity|].
  cbn [lines_loose]. destruct (classify x); try apply IH.
  all: destruct (fate_after st _ (line_fate 0 x _ st)); apply IH.
Qed.

Lemma find_nonblank_split : forall R l,
  find nonblank R = Some l ->
  exists B C, R = (B ++ l :: C)%list /\ forallb is_blank B = true /\ is_blank l = false.
Proof.
  induction R as [|x R IH]; intros l H; [discriminate H|].
  cbn [find] in H. unfold nonblank at 1 in H. destruct (is_blank x) eqn:Hx; cbn [negb] in H.
  - destruct (IH l H) as (B & C & -> & HB & Hl).
    exists (x :: B), C. cbn [forallb]. rewrite Hx, HB. repeat split. exact Hl.
  - injection H as <-. exists [], R. repeat split. exact Hx.
Qed.

Lemma split_at : forall i (L : list string) d,
  skipn (S i) L <> [] -> L = (firstn i L ++ nth i L d :: skipn (S i) L)%list.
Proof.
  induction i as [|i IH]; intros [|x L] d H; try (cbn in H; congruence); [reflexivity|].
  cbn [firstn nth app]. rewrite skipn_cons in H |- *. f_equal. apply IH, H.
Qed.

(** The converse: a blank the rule counts loosens the item, when the
    lines before it leave no code block open. *)
Theorem separates_item_loose : forall L i,
  blank_safe (snd (run_lines (firstn i L) (PPara []))) = true ->
  separates L i -> item_loose L = true.
Proof.
  intros L i Hbs (Hb & _ & Hend & l & Hfind & Hset & Hsl & Hsx).
  destruct (find_nonblank_split _ l Hfind) as (B & C & HR & HB & Hl).
  assert (HL : L = (firstn i L ++ nth i L "" :: B ++ l :: C)%list)
    by (rewrite <- HR; apply split_at; rewrite HR; destruct B; discriminate).
  set (A := firstn i L) in *. set (b := nth i L "") in *.
  destruct (holds_blank (snd (run_lines A (PPara [])))) eqn:Ha.
  { destruct (absorbed_ends_list _ Hbs Ha) as [Hne Hlist].
    rewrite (parse_lines_run A (PPara []) _ _ (surjective_pairing _)),
      ends_list_app in Hend by exact Hne.
    congruence. }
  pose proof (blank_settles b _ (classify_blank b Hb) Hbs Ha) as Hs1.
  assert (Hk : keeps_line 0 l (snd (step b (snd (run_lines A (PPara []))))) = false).
  { destruct (keeps_line 0 l _) eqn:Hk; [exfalso|reflexivity].
    destruct (kept_cases l _ Hs1 Hk) as [Hkx|Hcap].
    - exact (kept_not_starts A b _ Hbs Ha Hb (is_blank_para _) (para_not_attr _) Hkx Hsx).
    - exact (kept_not_starts A b l Hbs Ha Hb Hl
               (fun ap => caption_not_attr l ap Hcap) Hk Hsl). }
  destruct (settled_run_blanks B _ Hs1 HB) as (_ & HsB & _).
  rewrite <- (run_blanks_keeps B l _ HB Hs1) in Hk.
  unfold item_loose. rewrite HL.
  destruct (lines_loose_reach A false false (PPara []) (b :: B ++ l :: C)) as (lo & gap & ->).
  cbn [lines_loose]. rewrite (classify_blank b Hb).
  unfold stops_waiting at 1. rewrite (blank_safe_attr_waits _ Hbs), andb_false_l, orb_false_r.
  rewrite (lines_loose_blanks B lo _ (l :: C) HB Hs1).
  cbn [lines_loose]. unfold fate_after, stops_waiting.
  rewrite (settled_attr_waits _ HsB), andb_false_l. unfold line_fate.
  rewrite (settled_spec _ HsB), Hk.
  unfold settles_blank in Hset.
  destruct (classify l) eqn:E; try (rewrite orb_true_r; apply lines_loose_true).
  - apply classify_kblank_blank in E. congruence.
  - discriminate Hset.
  - destruct (@battrs K); [discriminate Hset|rewrite orb_true_r; apply lines_loose_true].
Qed.

(** A list the parser calls loose has a blank the rule counts: inside an
    item, or, when it was written with blank lines between its items,
    between two of them. *)
Corollary list_spacing_separates : forall sp itemss,
  forallb (fun L => run_safe L (PPara []) && negb (is_blank (hd "" L))) itemss = true ->
  list_spacing_of sp itemss = Loose ->
  (exists L, In L itemss /\ exists i, separates L i)
  \/ (sp = Loose /\ exists pre L M post, itemss = (pre ++ L :: M :: post)%list).
Proof.
  intros sp itemss Hok H. unfold list_spacing_of in H.
  destruct (existsb (fun L => item_loose L) itemss) eqn:Ei.
  - left. apply existsb_exists in Ei as [L [Hin HL]].
    rewrite forallb_forall in Hok. specialize (Hok L Hin).
    apply andb_true_iff in Hok as [Hs Hh]. apply negb_true_iff in Hh.
    exists L. split; [exact Hin|]. exact (item_loose_separates L Hs Hh HL).
  - right. cbn [orb] in H. destruct sp; [discriminate H|].
    split; [reflexivity|]. unfold seps_loosen in H.
    destruct itemss as [|L [|M post]]; try discriminate H.
    exists [], L, M, post. reflexivity.
Qed.

(** And a blank the rule counts inside an item loosens the list. *)
Corollary separates_loosens : forall sp itemss L i,
  In L itemss ->
  blank_safe (snd (run_lines (firstn i L) (PPara []))) = true ->
  separates L i -> list_spacing_of sp itemss = Loose.
Proof.
  intros sp itemss L i Hin Hbs Hsep. unfold list_spacing_of.
  replace (existsb (fun L => item_loose L) itemss) with true; [reflexivity|].
  symmetry. apply existsb_exists. exists L. split; [exact Hin|].
  exact (separates_item_loose L i Hbs Hsep).
Qed.

(** A list written with blank lines between its items is loose: each of
    them is between two items. *)
Corollary blank_between_items_loosens : forall pre L M post,
  list_spacing_of Loose (pre ++ L :: M :: post)%list = Loose.
Proof.
  intros pre L M post. unfold list_spacing_of.
  replace (seps_loosen (pre ++ L :: M :: post)%list) with true;
    [rewrite orb_true_r; reflexivity|].
  destruct pre as [|P [|Q pre']]; reflexivity.
Qed.

End WithTable.
