(* ai-disclosure: autonomous *)

(** * States a run reaches

   `pstate` has inhabitants no input produces: a code block whose fence
   has length zero, pending attributes over a spec.  Some facts about a
   blank line are false of those and true of every state a run from idle
   passes through.  `reached` is the part of that difference the facts
   below need, and `step_reached` says a line keeps it.

   Keys are off throughout: a key that holds a code block or a div open
   claims every line, which is a different statement (keyed-blocks 5). *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast Attributes Inline Marker Step Uniformity.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(* A state pending attributes can wait over: a block is open in it. *)
Definition carried (st : pstate) : bool :=
  match st with
  | PPara [] | PAttr _ _ _ _ _ _ | PPend _ _ _ | PKey _ _ _ _ => false
  | _ => true
  end.

Fixpoint reached (st : pstate) : bool :=
  match st with
  (* A blank never closes it. *)
  | PFence f _ _ _ _ => Nat.ltb 0 (f_len f)
  (* A spec still open holds the lines it took. *)
  | PAttr _ _ _ _ ap slices =>
      (ap_done ap || match slices with [] => false | _ :: _ => true end)%bool
  (* Idle only between a spec closing and the next line. *)
  | PPend _ _ inner => (reached inner && (is_idle inner || carried inner))%bool
  | PKey _ _ _ _ => false
  | PQuote _ _ _ inner | PDiv _ _ _ _ _ inner | PList _ _ inner
  | PFoot _ _ _ _ inner => reached inner
  | _ => true
  end.

Hypothesis Hkeyed : bkeyed = false.

(* What a line may leave: a reached state, and one pending attributes
   can still wait over when the line closed nothing. *)
Local Definition kept (st : pstate) (r : blocks * pstate) : Prop :=
  reached (snd r) = true
  /\ (carried st = true -> fst r = [] -> carried (snd r) = true).

Local Lemma finish_carried : forall st, carried st = true -> finish st <> [].
Proof.
  intros st Hc.
  destruct st as [[|c cur]| | | | | | | | | | | |]; try discriminate Hc;
    cbn [finish]; discriminate.
Qed.

Local Lemma kept_close_reopen : forall st r,
  carried st = true -> reached (snd r) = true -> kept st (close_reopen st r).
Proof.
  intros st [bs st'] Hc Hr. unfold close_reopen. split; [exact Hr|].
  intros _ H. cbn [fst] in H. apply app_eq_nil in H as [H _].
  destruct (finish_carried st Hc H).
Qed.

Local Lemma kept_pend_result : forall st pend specs r,
  reached (snd r) = true ->
  (fst r = [] -> (is_idle (snd r) || carried (snd r))%bool = true) ->
  kept (PPend pend specs st) (pend_result pend specs r).
Proof.
  intros st pend specs [bs st'] Hr Hc. cbn [fst snd] in *. split; [|discriminate].
  destruct bs; cbn [pend_result snd reached]; [|exact Hr].
  rewrite Hr, (Hc eq_refl). reflexivity.
Qed.

Local Lemma open_line_reached : forall descend ind l k,
  classify l = k ->
  (forall rest, reached (snd (descend rest)) = true) ->
  reached (snd (open_line descend ind l k)) = true.
Proof.
  intros descend ind l k E Hd.
  destruct k as [| |f|len cls|rest|lvl rest|sty core chk rest|ap|lbl rest|lbl v|r|];
    cbn [open_line open_kind]; try reflexivity.
  - cbn [open_fence snd reached]. apply Nat.ltb_lt.
    pose proof (classify_fence_len l f E). lia.
  - destruct bdivs; reflexivity.
  - destruct (quote_header rest) as [[[kind fold] title]|]; [reflexivity|].
    unfold open_quote. specialize (Hd rest). destruct (descend rest). exact Hd.
  - unfold open_list.
    match goal with |- context [descend ?x] => specialize (Hd x); destruct (descend x) end.
    exact Hd.
  - unfold open_attr. destruct battrs; cbn [snd reached]; [apply orb_true_r|reflexivity].
  - unfold open_foot. destruct bfootnotes; [|reflexivity].
    specialize (Hd rest). destruct (descend rest). exact Hd.
  - destruct btables; reflexivity.
  - unfold open_text. rewrite Hkeyed. reflexivity.
Qed.

Local Lemma open_line_carried : forall descend ind l k,
  k <> KBlank -> (forall ap, k <> KAttr ap) ->
  fst (open_line descend ind l k) = [] ->
  carried (snd (open_line descend ind l k)) = true.
Proof.
  intros descend ind l k Hb Ha.
  destruct k as [| |f|len cls|rest|lvl rest|sty core chk rest|ap|lbl rest|lbl v|r|];
    cbn [open_line open_kind]; try congruence; try reflexivity.
  - discriminate.
  - destruct bdivs; reflexivity.
  - destruct (quote_header rest) as [[[kind fold] title]|]; [reflexivity|].
    unfold open_quote. destruct (descend rest). reflexivity.
  - unfold open_list.
    match goal with |- context [descend ?x] => destruct (descend x) end. reflexivity.
  - unfold open_foot. destruct bfootnotes; [|reflexivity].
    destruct (descend rest). reflexivity.
  - destruct btables; reflexivity.
  - unfold open_text. rewrite Hkeyed. reflexivity.
Qed.

Local Lemma feed_lazy_reached : forall l st,
  reached st = true ->
  reached (feed_lazy l st) = true
  /\ ((is_idle st || carried st)%bool = true -> carried (feed_lazy l st) = true).
Proof.
  intros l st.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH
    |dlen dcls drng dop ddone dinner IH|ls done inner IH
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH
    |krng klbl ksrc kinner IH];
    intros Hr; cbn [feed_lazy reached] in *;
    try (split; [first [exact Hr | exact (proj1 (IH Hr)) | reflexivity]
                |first [reflexivity | intros H; exact H]]).
  apply andb_true_iff in Hr as [Hr Hc]. destruct (IH Hr) as [H1 H2].
  split; [|intros H; discriminate H].
  rewrite H1, (H2 Hc). apply orb_true_r.
Qed.

(* A nonblank line that is not a spec, met from idle, opens a block or
   closes one. *)
Local Lemma step_fuel_idle_carried : forall n off l k,
  classify l = k -> k <> KBlank -> (forall ap, k <> KAttr ap) ->
  fst (step_fuel n off l (PPara [])) = [] ->
  (is_idle (snd (step_fuel n off l (PPara [])))
   || carried (snd (step_fuel n off l (PPara []))))%bool = true.
Proof.
  intros n off l k E Hb Ha. destruct n as [|n]; [reflexivity|].
  cbn [step_fuel]. rewrite E. intros H.
  rewrite (open_line_carried _ _ l k Hb Ha H). apply orb_true_r.
Qed.

Local Ltac into Hin Hr inner :=
  match goal with
  | |- context [step_fuel ?n ?o ?r inner] =>
      let H := fresh in
      pose proof (Hin inner o r Hr) as H; destruct (step_fuel n o r inner);
      split; [exact H|reflexivity]
  end.

Local Lemma step_fuel_kept : forall n off l st,
  reached st = true -> kept st (step_fuel n off l st).
Proof.
  induction n as [|n IH]; intros off l st Hr; [split; [exact Hr|auto]|].
  assert (Hd : forall off' rest,
            reached (snd (step_fuel n off' rest (PPara []))) = true)
    by (intros; apply IH; reflexivity).
  (* a line the state does not take: it closes, and the line opens *)
  assert (Hcr : forall st0 k,
            carried st0 = true -> classify l = k ->
            kept st0 (close_reopen st0
                        (open_line (fun rest => step_fuel n (off + consumed l rest) rest (PPara []))
                           (off + indent_of l) l k))).
  { intros st0 k Hc E. apply kept_close_reopen; [exact Hc|].
    apply open_line_reached; [exact E|]. intros rest. apply Hd. }
  (* a line handed to what the container holds *)
  assert (Hin : forall inner off' l',
            reached inner = true ->
            reached (snd (step_fuel n off' l' inner)) = true)
    by (intros inner off' l' H; exact (proj1 (IH off' l' inner H))).
  assert (Hfresh : forall b : blocks * pstate,
            reached (snd b) = true -> forall st0 x, kept st0 ((x :: fst b)%list, snd b))
    by (intros b H st0 x; split; [exact H|discriminate]).
  cbn [step_fuel].
  destruct st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner
    |dlen dcls drng dop ddone dinner|ls done inner
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner|trng trows tcap|ppend pspecs pinner
    |krng klbl ksrc kinner].
  - destruct cur as [|c cur].
    + split; [|discriminate].
      apply open_line_reached; [reflexivity|]. intros rest. apply Hd.
    + destruct (bunderline_of l); [split; [reflexivity|discriminate]|].
      destruct (classify l) eqn:E;
        try (apply kept_close_reopen; reflexivity);
        (destruct (binterrupt _);
         [apply Hcr; reflexivity|split; reflexivity]).
  - destruct (classify l) eqn:E;
      try (apply Hcr; reflexivity).
    + destruct bheading_continues; [destruct (Nat.eqb _ _)|];
        first [split; reflexivity | apply kept_close_reopen; reflexivity].
    + destruct bheading_continues; [split; reflexivity|].
      apply kept_close_reopen; [reflexivity|].
      cbn [open_kind]. unfold open_text. rewrite Hkeyed. reflexivity.
  - destruct (fence_close f l); split; try reflexivity; try discriminate. exact Hr.
  - cbn [reached] in Hr.
    destruct (classify l) eqn:E;
      try (destruct (is_lazy _ inner);
           [split; [exact (proj1 (feed_lazy_reached l inner Hr))|reflexivity]
           |apply Hcr; reflexivity]).
    into Hin Hr inner.
  - cbn [reached] in Hr.
    destruct (negb _ && _)%bool; [split; [reflexivity|discriminate]|].
    into Hin Hr dinner.
  - cbn [reached] in Hr.
    destruct (classify l) eqn:E; [into Hin Hr inner|..];
      (destruct (list_takes ls off l inner); [into Hin Hr inner|]);
      try (destruct (is_lazy _ inner);
           [split; [exact (proj1 (feed_lazy_reached l inner Hr))|reflexivity]
           |apply Hcr; reflexivity]).
    destruct (narrow _ _); [apply Hcr; reflexivity|].
    match goal with
    | |- context [step_fuel n ?o ?r (PPara [])] =>
        pose proof (Hd o r) as H; destruct (step_fuel n o r (PPara []))
    end.
    split; [exact H|reflexivity].
  - cbn [reached] in Hr. destruct (ap_done aap) eqn:Hdone.
    { split; [|discriminate]. apply Hin. reflexivity. }
    cbn [orb] in Hr.
    assert (Hpend : forall k,
              kept (PAttr apend aspecs arng aind aap aslices)
                (pend_result apend aspecs
                   (step_fuel n off l (para_recover k aslices)))).
    { intros k. destruct (IH off l (para_recover k aslices) eq_refl) as [H1 H2].
      split; [|discriminate].
      refine (proj1 (kept_pend_result (PPara []) apend aspecs _ H1 _)).
      intros Hnil. apply orb_true_iff. right. exact (H2 eq_refl Hnil). }
    destruct (Nat.ltb aind (off + indent_of l)).
    + destruct (ap_failed _); [apply Hpend|].
      split; [|discriminate]. cbn [snd reached].
      destruct aslices; [discriminate Hr|]. unfold push_text.
      destruct (is_blank l); apply orb_true_r.
    + destruct (is_blank l); [split; [reflexivity|discriminate]|apply Hpend].
  - destruct (bunderline_of l); [split; [reflexivity|discriminate]|].
    destruct (classify l) eqn:E;
      try (apply kept_close_reopen; reflexivity);
      (destruct (binterrupt _);
       [apply Hcr; reflexivity|split; reflexivity]).
  - match goal with
    | |- context [if ?c then ref_cont l else None] =>
        destruct (if c then ref_cont l else None)
    end; [split; reflexivity|].
    pose proof (Hd off l) as H. destruct (step_fuel n off l (PPara [])).
    apply (Hfresh (_, _) H).
  - cbn [reached] in Hr.
    destruct (is_blank l); [into Hin Hr finner|].
    destruct (foot_takes find off l finner); [into Hin Hr finner|].
    destruct (is_lazy _ finner);
      [split; [exact (proj1 (feed_lazy_reached l finner Hr))|reflexivity]|].
    pose proof (Hd off l) as H. destruct (step_fuel n off l (PPara [])).
    apply (Hfresh (_, _) H).
  - pose proof (Hd off l) as H.
    destruct tcap; try (destruct (caption_open l)); try (destruct (is_blank l));
      try (destruct (classify l)); try (destruct (step_fuel n off l (PPara [])));
      first [apply (Hfresh (_, _) H) | split; [reflexivity|first [reflexivity|discriminate]]].
  - cbn [reached] in Hr. apply andb_true_iff in Hr as [Hr Hc].
    assert (Hdown : classify l <> KBlank \/ is_idle pinner = false ->
                    (forall ap, classify l = KAttr ap -> is_idle pinner = false) ->
              kept (PPend ppend pspecs pinner)
                (pend_result ppend pspecs (step_fuel n off l pinner))).
    { intros Hb Ha. destruct (IH off l pinner Hr) as [H1 H2].
      apply kept_pend_result; [exact H1|]. intros Hnil.
      destruct (carried pinner) eqn:Hcp;
        [apply orb_true_iff; right; exact (H2 eq_refl Hnil)|].
      rewrite orb_false_r in Hc.
      destruct pinner as [[|]| | | | | | | | | | | |]; try discriminate Hc.
      apply (step_fuel_idle_carried n off l (classify l) eq_refl); [..|exact Hnil].
      - destruct Hb as [Hb|Hb]; [exact Hb|discriminate Hb].
      - intros ap E. specialize (Ha ap E). discriminate Ha. }
    destruct (classify l) eqn:E;
      try (apply Hdown; [left; discriminate|intros ? ?; discriminate]).
    + destruct (is_idle pinner) eqn:Hi; [split; [reflexivity|discriminate]|].
      apply Hdown; [right; reflexivity|intros ? ?; discriminate].
    + destruct (is_idle pinner) eqn:Hi.
      * split; [|discriminate]. unfold open_attr.
        destruct battrs; cbn [snd reached]; [apply orb_true_r|reflexivity].
      * apply Hdown; [left; discriminate|intros ? _; reflexivity].
  - discriminate Hr.
Qed.

Local Lemma step_kept : forall l st, reached st = true -> kept st (step l st).
Proof. intros l st H. exact (step_fuel_kept _ 0 l st H). Qed.

(** A line keeps a state reached. *)
Lemma step_reached : forall l st,
  reached st = true -> reached (snd (step l st)) = true.
Proof. intros l st H. exact (proj1 (step_kept l st H)). Qed.

Lemma run_lines_reached : forall ls st,
  reached st = true -> reached (snd (run_lines ls st)) = true.
Proof.
  induction ls as [|l ls IH]; intros st H; [exact H|].
  cbn [run_lines]. pose proof (step_reached l st H) as Hs.
  destruct (step l st) as [bs st']. specialize (IH st' Hs).
  destruct (run_lines ls st'). exact IH.
Qed.

Lemma reached_pad_state : forall k st, reached (pad_state k st) = reached st.
Proof.
  intros k st.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH
    |dlen dcls drng dop ddone dinner IH|ls done inner IH
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH
    |krng klbl ksrc kinner IH];
    cbn [pad_state reached]; try reflexivity; try exact IH.
  rewrite IH, pad_state_is_idle.
  destruct pinner as [[|]| | | | | | | | | | | |]; reflexivity.
Qed.

(** No key is open in it, so none claims a line. *)
Lemma reached_key_claims : forall l st,
  reached st = true -> key_claims l st = false.
Proof.
  intros l st.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH
    |dlen dcls drng dop ddone dinner IH|ls done inner IH
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH
    |krng klbl ksrc kinner IH];
    cbn [reached key_claims]; try reflexivity; try exact IH; try discriminate.
  intros H. apply andb_true_iff in H as [H _]. exact (IH H).
Qed.

Local Lemma blank_kblank : classify EmptyString = KBlank.
Proof. exact (classify_blank EmptyString eq_refl). Qed.

(** A blank line leaves no block attributes waiting. *)
Lemma reached_blank_attr_waits : forall st,
  reached st = true -> attr_waits (snd (step "" st)) = false.
Proof.
  pose proof blank_kblank as Hblank.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH
    |dlen dcls drng dop ddone dinner IH|ls done inner IH
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH
    |krng klbl ksrc kinner IH];
    intros Hr.
  - destruct cur as [|c cur'];
      [rewrite (step_idle "" KBlank Hblank eq_refl); reflexivity
      |rewrite (step_para_flush "" c cur' Hblank); reflexivity].
  - rewrite (step_heading_close "" lvl hrng cur Hblank). reflexivity.
  - unfold step. cbn [step_fuel]. destruct (fence_close f ""); reflexivity.
  - rewrite (step_quote_close "" KBlank qrng qhead done inner [] (PPara [])
               Hblank eq_refl eq_refl eq_refl). reflexivity.
  - destruct (step "" dinner) as [bs i] eqn:Hs.
    rewrite (step_div_cont "" dlen dcls drng dop ddone dinner bs i
               (div_stays_open_blank "" dinner dlen eq_refl) Hs).
    reflexivity.
  - destruct (step "" inner) as [bs i] eqn:Hs.
    rewrite (step_list_blank "" ls done inner bs i Hblank Hs). reflexivity.
  - unfold step. cbn [step_fuel pstate_depth String.length Nat.add].
    destruct (ap_done aap).
    + cbn [step_fuel]. rewrite Hblank. reflexivity.
    + replace (Nat.ltb aind (0 + indent_of "")) with false
        by (symmetry; apply Nat.ltb_ge; cbn; lia).
      reflexivity.
  - rewrite (step_para_off_flush "" okoff ocur Hblank). reflexivity.
  - rewrite (step_ref_blank "" rrng rind rlbl rval Hblank). reflexivity.
  - unfold step. cbn [step_fuel]. cbn [is_blank].
    destruct (step_fuel _ 0 "" finner). reflexivity.
  - unfold step. cbn [step_fuel].
    destruct tcap; try destruct (caption_open ""); reflexivity.
  - cbn [reached] in Hr. apply andb_true_iff in Hr as [Hr Hc].
    unfold step. cbn [step_fuel]. rewrite Hblank.
    destruct (is_idle pinner) eqn:Hi; [reflexivity|]. cbn [orb] in Hc.
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    pose proof (step_kept "" pinner Hr) as [_ Hk]. specialize (IH Hr).
    destruct (step "" pinner) as [bs st'] eqn:Hs. cbn [fst snd] in *.
    destruct bs as [|b bs]; cbn [pend_result snd attr_waits]; [|exact IH].
    specialize (Hk Hc eq_refl).
    destruct st' as [[|]| | | | | | | | | | | |]; try discriminate Hk; reflexivity.
  - discriminate Hr.
Qed.

(** A blank line emits and leaves open what the end of input would have
    closed: adding one after the lines changes no block.  An open code
    block drops the blank lines it ends with, and a spec the blank fails
    becomes the paragraph the end of input would have made of it. *)
Lemma reached_blank_finish : forall st,
  reached st = true ->
  (fst (step "" st) ++ finish (snd (step "" st)))%list = finish st.
Proof.
  pose proof blank_kblank as Hl.
  induction st as [cur|lvl hrng cur|f fnd crng cop acc|qrng qhead done inner IH
    |dlen dcls drng dop ddone dinner IH|ls done inner IH
    |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH
    |krng klbl ksrc kinner IH];
    intros Hr.
  - destruct cur as [|c cur'].
    + rewrite (step_idle "" KBlank Hl eq_refl). reflexivity.
    + rewrite (step_para_flush "" c cur' Hl). reflexivity.
  - rewrite (step_heading_close "" lvl hrng cur Hl). reflexivity.
  - cbn [reached] in Hr. unfold step. cbn [step_fuel].
    assert (Hc : fence_close f "" = false).
    { unfold fence_close. cbn. destruct (f_len f); [discriminate Hr|reflexivity]. }
    rewrite Hc. cbn [fst snd app finish].
    replace (drop_ws_upto (fnd - 0) "") with "" by (destruct (fnd - 0); reflexivity).
    reflexivity.
  - rewrite (step_quote_close "" KBlank qrng qhead done inner _ _ Hl eq_refl eq_refl
               (surjective_pairing _)).
    cbn [fst snd open_kind finish app]. reflexivity.
  - cbn [reached] in Hr.
    rewrite (step_div_cont "" dlen dcls drng dop ddone dinner _ _
               (div_stays_open_blank "" dinner dlen eq_refl)
               (surjective_pairing _)).
    cbn [fst snd finish app].
    rewrite rev_app_distr, rev_involutive, <- app_assoc, (IH Hr).
    reflexivity.
  - cbn [reached] in Hr.
    rewrite (step_list_blank "" ls done inner _ _ Hl (surjective_pairing _)).
    cbn [fst snd finish app].
    rewrite rev_app_distr, rev_involutive, <- app_assoc, (IH Hr).
    unfold stops_waiting. rewrite (reached_blank_attr_waits inner Hr).
    rewrite andb_true_r, list_settle_false.
    destruct ls; destruct (attr_waits inner); reflexivity.
  - cbn [reached] in Hr. unfold step.
    cbn [step_fuel pstate_depth String.length Nat.add].
    destruct (ap_done aap) eqn:Hdone.
    + cbn [step_fuel finish]. rewrite Hl, Hdone. reflexivity.
    + replace (Nat.ltb aind (0 + indent_of "")) with false
        by (symmetry; apply Nat.ltb_ge; cbn; lia).
      cbn [orb] in Hr. destruct aslices as [|sl aslices]; [discriminate Hr|].
      cbn [is_blank fst snd app finish]. rewrite Hdone. reflexivity.
  - rewrite (step_para_off_flush "" okoff ocur Hl). reflexivity.
  - rewrite (step_ref_blank "" rrng rind rlbl rval Hl). reflexivity.
  - cbn [reached] in Hr.
    destruct (step "" finner) as [bs inner'] eqn:Hs.
    assert (Hfoot : step "" (PFoot frng find flbl fdone finner) =
              ([], PFoot (touch_extent frng) find flbl (rev bs ++ fdone)%list inner')).
    { unfold step. cbn [step_fuel pstate_depth]. cbn [is_blank].
      rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
      rewrite Hs. reflexivity. }
    rewrite Hfoot. cbn [fst snd finish app].
    specialize (IH Hr). cbn [fst snd] in IH.
    rewrite rev_app_distr, rev_involutive, <- app_assoc, IH.
    reflexivity.
  - unfold step. cbn [step_fuel open_line].
    rewrite (caption_open_blank "" eq_refl).
    destruct tcap; reflexivity.
  - cbn [reached] in Hr. apply andb_true_iff in Hr as [Hr Hc].
    unfold step. cbn [step_fuel open_line]. rewrite Hl.
    destruct (is_idle pinner) eqn:Hi.
    { destruct pinner as [[|]| | | | | | | | | | | |]; try discriminate Hi.
      reflexivity. }
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
    specialize (IH Hr).
    destruct (step "" pinner) as [bs st'] eqn:Hs.
    cbn [fst snd] in IH. cbn [pend_result]; nopos.
    destruct bs as [|b bs'].
    + cbn [fst snd finish app]. rewrite <- IH. reflexivity.
    + cbn [fst snd finish]. rewrite decorate_head_cons_app, <- IH. reflexivity.
  - discriminate Hr.
Qed.

(** A blank line at the end of the input changes no block. *)
Theorem trailing_blank_line : forall L,
  parse_lines (L ++ [EmptyString]) (PPara []) = parse_lines L (PPara []).
Proof.
  intros L. rewrite parse_lines_app_run.
  pose proof (run_lines_reached L (PPara []) eq_refl) as Hr.
  destruct (run_lines L (PPara [])) as [bs st] eqn:Hrun. cbn [snd] in Hr.
  rewrite (parse_lines_run L _ _ _ Hrun).
  pose proof (reached_blank_finish st Hr) as Hfin.
  cbn [parse_lines]. destruct (step "" st) as [b st']. exact (f_equal _ Hfin).
Qed.

End WithTable.
