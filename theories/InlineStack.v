(* ai-disclosure: autonomous *)

(* The candidate stack computes what the specification scanner computes.
   `sabs` rebuilds the chain the specification would hold: the frames
   from the bottom out, each with its depth read off the shared counter
   and its payload joined from the segments above it.  Every step,
   break and finish commutes with it, so the paragraph entry points the
   extraction substitutes (`Extract.v`) are equal to the ones they
   replace. *)

From Stdlib Require Import String Ascii List Bool Lia Arith.
From DjotV Require Import Strings Ast Attributes InlineTable InlineView
  InlineScan InlineLocated InlineBuffer.
Import ListNotations.

Local Open Scope string_scope.

(*
Escapes in a payload
====================
*)

(* Whether a payload ends on a backslash that escapes the next byte. *)
Fixpoint esc_after (e : bool) (s : string) : bool :=
  match s with
  | EmptyString => e
  | String c rest => esc_after (negb e && is_bslash c)%bool rest
  end.

Lemma esc_after_app : forall a b e,
  esc_after e (a ++ b) = esc_after (esc_after e a) b.
Proof. induction a as [|c a IH]; intros b e; [reflexivity|]. apply IH. Qed.

Lemma ddecode_from_app : forall a b e,
  ddecode_from e (a ++ b) = (ddecode_from e a ++ ddecode_from (esc_after e a) b)%string.
Proof.
  induction a as [|c a IH]; intros b e; [reflexivity|].
  cbn [ddecode_from esc_after append].
  destruct e; cbn [negb andb].
  - rewrite IH, append_assoc. reflexivity.
  - destruct (is_bslash c); cbn [andb]; rewrite IH; reflexivity.
Qed.

Lemma ddecode_snoc : forall s c,
  ddecode (s ++ one c) =
  (ddecode s ++
   (if esc_after false s
    then (if is_punct c then one c else String bslash (one c))
    else if is_bslash c then EmptyString else one c))%string.
Proof.
  intros s c. unfold ddecode. rewrite ddecode_from_app. f_equal.
  unfold one; destruct (esc_after false s); cbn [ddecode_from];
    [rewrite append_empty_r; reflexivity|].
  destruct (is_bslash c); reflexivity.
Qed.

Section WithTable.
Context {T : dtable}.

Section Lawful.
Context {Buf : Type} {X : TextOps Buf} {L : TextLaws Buf}.

Ltac laws := rewrite ?tval_push, ?tval_nil, ?tval_of, ?tnonempty_val.

(*
The abstraction
===============
*)

Definition mkframe (p : nat) (esc : bool) (k : ckind) (lvl : nat)
  (pay : string) (inner : iscan) : iscan :=
  match k with
  | CDest kids image open o => IDest kids image open esc (p - lvl) (ddecode pay) inner o
  end.

(* `pay` is the top frame's payload; each frame below adds the segment
   from its opener to the next one's. *)
Fixpoint wrap (p : nat) (esc : bool) (fs : list (cframe (Buf:=Buf)))
  (pay : string) (inner : iscan) : iscan :=
  match fs with
  | [] => inner
  | f :: fs' =>
      wrap p esc fs' (tval (cf_under f) ++ pay)
        (mkframe p esc (cf_kind f) (cf_level f) pay inner)
  end.

Definition sabs (s : sscan (Buf:=Buf)) : iscan :=
  wrap (s_parens s) (s_esc s) (s_frames s) (tval (s_seg s))
    (map_text (s_cur s)).

(*
The invariant
=============
*)

(* The levels, top first, strictly decreasing and below `bound`. *)
Fixpoint lv (bound : nat) (fs : list (cframe (Buf:=Buf))) : Prop :=
  match fs with
  | [] => True
  | f :: fs' => cf_level f < bound /\ lv (cf_level f) fs'
  end.

(* Every open payload ends in the same escape state. *)
Fixpoint esc_ok (esc : bool) (fs : list (cframe (Buf:=Buf))) (pay : string) : Prop :=
  match fs with
  | [] => True
  | f :: fs' => esc_after false pay = esc /\ esc_ok esc fs' (tval (cf_under f) ++ pay)
  end.

Definition wf_parts (fs : list (cframe (Buf:=Buf))) (p : nat) (esc : bool)
  (seg : Buf) : Prop :=
  lv (S p) fs /\ esc_ok esc fs (tval seg).

Definition swf (s : sscan (Buf:=Buf)) : Prop :=
  wf_parts (s_frames s) (s_parens s) (s_esc s) (s_seg s).

Lemma swf_slift : forall st, swf (slift st).
Proof. intros st. repeat split. Qed.

Lemma lv_mono : forall fs b b', lv b fs -> b <= b' -> lv b' fs.
Proof.
  intros [|f fs] b b' H Hle; cbn [lv] in *; [exact I|].
  destruct H; split; [lia|assumption].
Qed.

Lemma lv_below : forall fs b, lv b fs -> Forall (fun f => cf_level f < b) fs.
Proof.
  induction fs as [|f fs IH]; intros b H; [constructor|].
  destruct H as [H1 H2]. constructor; [exact H1|].
  eapply Forall_impl; [|exact (IH _ H2)]. intros g Hg. cbn beta in Hg. lia.
Qed.

Lemma esc_ok_snoc : forall esc fs pay c,
  esc_ok esc fs pay ->
  esc_ok (negb esc && is_bslash c)%bool fs (pay ++ one c).
Proof.
  induction fs as [|f fs IH]; intros pay c H; [exact I|].
  destruct H as [H1 H2]. split.
  - rewrite esc_after_app, H1. reflexivity.
  - rewrite <- append_assoc. apply IH. exact H2.
Qed.

(*
One frame, one byte
===================
*)

Section Cursor.
Context `{PosPolicy} `{InlineCursor}.

(* A frame the byte does not close. *)
Definition quiet (esc : bool) (c : ascii) (p : nat) (f : cframe (Buf:=Buf)) : Prop :=
  cf_level f <= p /\ (esc = false -> c = rparen -> cf_level f <> p).

Lemma mkframe_step : forall a c p esc f pay inner,
  esc_after false pay = esc -> quiet esc c p f ->
  istep_at a c (mkframe p esc (cf_kind f) (cf_level f) pay inner)
  = mkframe (scount esc c lparen rparen p)
      (negb esc && is_bslash c) (cf_kind f) (cf_level f) (pay ++ one c)
      (istep_at a c inner).
Proof.
  intros a c p esc f pay inner He Hq.
  unfold quiet in Hq. destruct f as [k lvl u]; cbn [cf_kind cf_level] in *.
  destruct k as [kids image open o]; cbn [mkframe istep_at]; tred.
  rewrite ddecode_snoc, He. destruct Hq as [Hle Hc].
  destruct esc; cbn [negb andb scount].
  - reflexivity.
  - unfold is_bslash. destruct (Ascii.eqb c bslash) eqn:Eb.
    + apply Ascii.eqb_eq in Eb. subst c. rewrite append_empty_r. reflexivity.
    + destruct (Ascii.eqb c lparen) eqn:Ep.
      { apply Ascii.eqb_eq in Ep. subst c. f_equal. lia. }
      destruct (Ascii.eqb c rparen) eqn:Er.
      { apply Ascii.eqb_eq in Er. subst c.
        assert (lvl <> p) by (apply Hc; reflexivity).
        destruct (p - lvl) as [|d] eqn:Ed; [lia|]. f_equal. lia. }
      reflexivity.
Qed.

Lemma wrap_step : forall a c p esc fs pay inner,
  esc_ok esc fs pay -> Forall (quiet esc c p) fs ->
  istep_at a c (wrap p esc fs pay inner)
  = wrap (scount esc c lparen rparen p)
      (negb esc && is_bslash c) fs (pay ++ one c) (istep_at a c inner).
Proof.
  induction fs as [|f fs IH]; intros pay inner He Hq; [reflexivity|].
  destruct He as [He1 He2]. inversion Hq as [|? ? Hq1 Hq2]; subst.
  cbn [wrap]. rewrite IH by assumption.
  rewrite mkframe_step by first [reflexivity|assumption].
  rewrite append_assoc. reflexivity.
Qed.

(* Every frame below the top is below the top's level, so none of them
   closes. *)
Lemma quiet_below : forall fs p esc c,
  lv p fs -> Forall (quiet esc c p) fs.
Proof.
  intros fs p esc c Hl.
  eapply Forall_impl; [|exact (lv_below _ _ Hl)].
  intros f Hf. cbn beta in Hf. split; [lia|intros _ _; lia].
Qed.

(* The byte closes nothing: every frame is quiet. *)
Lemma quiet_all : forall fs p esc c,
  lv (S p) fs ->
  match fs with
  | [] => true
  | f :: _ => negb (negb esc && Ascii.eqb c rparen && Nat.eqb (cf_level f) p)
  end = true ->
  Forall (quiet esc c p) fs.
Proof.
  intros [|f fs] p esc c Hl Hc; [constructor|].
  destruct Hl as [H1 H2]. constructor.
  - split; [lia|]. intros -> ->. intros Hp. subst p.
    rewrite Ascii.eqb_refl, Nat.eqb_refl in Hc. discriminate Hc.
  - apply (quiet_below fs p). apply (lv_mono _ _ _ H2). lia.
Qed.

(*
The step
========
*)

Lemma speel_sabs : forall fs p esc seg cur,
  sabs (speel fs p esc seg cur)
  = wrap p esc fs (tval seg) (map_text cur).
Proof.
  intros fs p esc seg cur. unfold speel.
  destruct cur; try reflexivity.
  destruct esc0; [reflexivity|]. destruct depth; [|reflexivity].
  destruct (negb (tnonempty dst) && negb esc && sabove (stop_level fs) p)%bool eqn:E;
    [|reflexivity].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply negb_true_iff in E1, E2. rewrite tnonempty_val in E1. subst esc. laws.
  unfold sabs. cbn [s_parens s_esc s_frames s_seg s_cur wrap cf_kind cf_level cf_under].
  laws. rewrite append_empty_r. cbn [mkframe map_text]. rewrite Nat.sub_diag.
  destruct (tval dst) eqn:Ed; [reflexivity|cbn in E1; discriminate E1].
Qed.

Lemma speel_swf : forall fs p esc seg cur,
  wf_parts fs p esc seg ->
  swf (speel fs p esc seg cur).
Proof.
  intros fs p esc seg cur W.
  destruct W as (Ld & He).
  unfold speel. destruct cur; try (repeat split; assumption).
  destruct esc0; [repeat split; assumption|]. destruct depth; [|repeat split; assumption].
  destruct (negb (tnonempty dst) && negb esc && sabove (stop_level fs) p)%bool eqn:E;
    [|repeat split; assumption].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply negb_true_iff in E2. subst esc.
  unfold swf, wf_parts; cbn [s_frames s_parens s_esc s_seg lv esc_ok
    cf_kind cf_level cf_under].
  repeat split; try assumption; try lia.
  - destruct fs as [|g fs]; [exact I|]. cbn [stop_level sabove lv] in *.
    apply Nat.ltb_lt in E3. destruct Ld as [_ Ld]. split; [exact E3|exact Ld].
  - rewrite tval_nil. reflexivity.
  - rewrite tval_nil, append_empty_r. assumption.
Qed.

Lemma scount_bound : forall esc c up down n x,
  x < S n -> (esc = false -> c = down -> x <> n) -> x < S (scount esc c up down n).
Proof.
  intros esc c up down n x H1 H2. unfold scount.
  destruct esc; [lia|].
  destruct (Ascii.eqb c up); [lia|].
  destruct (Ascii.eqb c down) eqn:E; [|lia].
  apply Ascii.eqb_eq in E. specialize (H2 eq_refl E). lia.
Qed.

Lemma wf_quiet : forall fs p esc seg c,
  wf_parts fs p esc seg ->
  Forall (quiet esc c p) fs ->
  wf_parts fs (scount esc c lparen rparen p)
    (negb esc && is_bslash c) (if null fs then seg else tpush seg (one c)).
Proof.
  intros fs p esc seg c W Q.
  destruct W as (Ld & He). split.
  - destruct fs as [|f fs]; [exact I|]. destruct Ld as [L1 L2].
    inversion Q as [|? ? [Q1 Q2] _]; subst.
    split; [apply scount_bound; [exact L1|exact Q2]|exact L2].
  - destruct fs as [|f fs]; [exact I|]. cbn [null]. laws.
    apply esc_ok_snoc. exact He.
Qed.

Lemma sframe_close_map : forall k pay,
  map_text (sframe_close (Buf:=Buf) k pay)
  = match k with
    | CDest kids image open o =>
        IText false EmptyString (Some rparen)
          (oemit (imk (span_start open) cursor_stop
                    (bnode image kids (Direct (drop_nl (ddecode pay))))) o)
    end.
Proof. intros [kids image open o] pay; cbn [sframe_close map_text]; laws; reflexivity. Qed.

Theorem sstep_at_spec : forall a c s, swf s ->
  sabs (sstep_at a c s) = istep_at a c (sabs s) /\ swf (sstep_at a c s).
Proof.
  intros a c [fs p esc seg cur] W.
  pose proof W as W'. destruct W' as (Ld & He).
  cbn [s_frames s_parens s_esc s_seg s_cur] in *.
  unfold sstep_at, sabs. cbn [s_frames s_parens s_esc s_seg s_cur].
  destruct fs as [|f fs'].
  - (* no frame *)
    split.
    + match goal with
      | |- wrap (s_parens ?x) _ _ _ _ = _ =>
          change (wrap (s_parens x) (s_esc x) (s_frames x)
                    (tval (s_seg x)) (map_text (s_cur x))) with (sabs x)
      end.
      rewrite speel_sabs. cbn [wrap]. apply istep_at_map.
    + apply speel_swf. apply (wf_quiet [] p esc seg c W). constructor.
  - destruct (negb esc && Ascii.eqb c rparen && Nat.eqb (cf_level f) p)%bool eqn:Cd.
    + (* the top frame closes *)
      apply andb_prop in Cd as [Cd Cl]. apply andb_prop in Cd as [Ce Cc].
      apply negb_true_iff in Ce. apply Ascii.eqb_eq in Cc.
      apply Nat.eqb_eq in Cl. subst esc c.
      destruct Ld as [Lf Ls]. destruct He as [He1 He2].
      rewrite Cl in Ls.
      assert (Qf : Forall (quiet false rparen p) fs') by (apply quiet_below; exact Ls).
      cbn [wrap].
      split.
      * rewrite wrap_step by assumption.
        cbn [s_frames s_parens s_esc s_seg s_cur].
        assert (Close : istep_at a rparen
                  (mkframe p false (cf_kind f) (cf_level f) (tval seg) (map_text cur))
                = map_text (sframe_close (cf_kind f) (tval seg))).
        { rewrite sframe_close_map. destruct f as [k lvl u].
          cbn [cf_kind cf_level] in *. subst lvl.
          destruct k as [kids image open o].
          cbn [mkframe istep_at]. rewrite Nat.sub_diag. tred. reflexivity. }
        rewrite Close.
        destruct fs' as [|g fs'']; [reflexivity|]. cbn [null]. laws.
        rewrite append_assoc. reflexivity.
      * unfold swf, wf_parts. cbn [s_frames s_parens s_esc s_seg].
        pose proof (wf_quiet fs' p false
          (tof (tval (cf_under f) ++ tval seg)) rparen) as WQ.
        destruct WQ as (L1 & E3).
        { split; [apply (lv_mono _ _ _ Ls); lia|laws; exact He2]. }
        { exact Qf. }
        split; [exact L1|].
        destruct fs' as [|g fs'']; [exact I|]. cbn [null] in *. laws.
        rewrite tval_push, tval_of in E3. rewrite append_assoc in E3. exact E3.
    + (* nothing closes *)
      assert (Q : Forall (quiet esc c p) (f :: fs')).
      { apply quiet_all; [exact Ld|]. cbn beta iota. rewrite Cd. reflexivity. }
      split.
      * match goal with
        | |- wrap (s_parens ?x) _ _ _ _ = _ =>
            change (wrap (s_parens x) (s_esc x) (s_frames x)
                      (tval (s_seg x)) (map_text (s_cur x))) with (sabs x)
        end.
        rewrite speel_sabs, wrap_step by assumption. rewrite istep_at_map.
        laws. reflexivity.
      * apply speel_swf. apply (wf_quiet (f :: fs') p esc seg c W Q).
Qed.

(*
The break and the finish
========================
*)

Lemma wrap_break : forall a p esc fs pay inner,
  esc_ok esc fs pay ->
  ibreak_at a (wrap p esc fs pay inner) = wrap p false fs (pay ++ nl) (ibreak_at a inner).
Proof.
  induction fs as [|f fs IH]; intros pay inner He; [reflexivity|].
  destruct He as [He1 He2]. cbn [wrap]. rewrite IH by exact He2.
  rewrite append_assoc. f_equal.
  destruct (cf_kind f) as [kids image open o]; cbn [mkframe ibreak_at]; tred.
  unfold ddecode. rewrite ddecode_from_app. fold (ddecode pay). rewrite He1.
  destruct esc; reflexivity.
Qed.

Theorem sbreak_at_spec : forall a s, swf s ->
  sabs (sbreak_at a s) = ibreak_at a (sabs s) /\ swf (sbreak_at a s).
Proof.
  intros a [fs p esc seg cur] W.
  destruct W as (Ld & He).
  cbn [s_frames s_parens s_esc s_seg s_cur] in *.
  unfold sbreak_at, sabs. cbn [s_frames s_parens s_esc s_seg s_cur].
  split.
  - rewrite wrap_break by exact He. rewrite ibreak_at_map.
    destruct fs; [reflexivity|]. cbn [null]. laws. reflexivity.
  - split; [exact Ld|]. cbn [s_esc s_seg s_frames].
    destruct fs as [|f fs]; [exact I|]. cbn [null]. laws.
    clear -He. revert He. generalize (tval seg). generalize (f :: fs). clear.
    induction l as [|g l IH]; intros pay Hl; [exact I|]. destruct Hl as [H1 H2].
    split; [rewrite esc_after_app, H1; destruct esc; reflexivity|].
    rewrite <- append_assoc. apply IH. exact H2.
Qed.

Lemma wrap_finish : forall p esc fs pay inner,
  ifinish_ostate (wrap p esc fs pay inner) = ifinish_ostate inner.
Proof.
  induction fs as [|f fs IH]; intros pay inner; [reflexivity|].
  cbn [wrap]. rewrite IH. destruct (cf_kind f); reflexivity.
Qed.

Theorem sfinish_spec : forall s, sfinish s = ifinish (sabs s).
Proof.
  intros s. unfold sfinish, sabs, ifinish, ifinish_rev.
  rewrite wrap_finish, <- ifinish_ostate_map. reflexivity.
Qed.

End Cursor.

(*
Drivers
=======
*)

Lemma sabs_sstart : sabs sstart = istart.
Proof.
  unfold sabs, sstart, slift. cbn [s_frames s_cur s_seg s_parens s_esc wrap].
  apply map_text_lift.
Qed.

Lemma swf_sstart : swf sstart.
Proof. apply swf_slift. Qed.

Theorem sscan_str_spec : forall s st, swf st ->
  sabs (sscan_str s st) = iscan_str s (sabs st) /\ swf (sscan_str s st).
Proof.
  induction s as [|c s IH]; intros st W; [split; [reflexivity|exact W]|].
  destruct (@sstep_at_spec semantic_pos semantic_inline_cursor
              inline_attrs_enabled c st W) as [E W'].
  destruct (IH _ W') as [E2 W2]. split; [|exact W2].
  change (sabs (sscan_str s (@sstep_at T Buf X semantic_pos semantic_inline_cursor
            inline_attrs_enabled c st))
          = iscan_str s (@istep T string _ semantic_pos semantic_inline_cursor c (sabs st))).
  rewrite E2, E. reflexivity.
Qed.

Theorem sscan_str_off_spec : forall s st, swf st ->
  sabs (sscan_str_off s st) = iscan_str_off s (sabs st) /\ swf (sscan_str_off s st).
Proof.
  induction s as [|c s IH]; intros st W; [split; [reflexivity|exact W]|].
  destruct (@sstep_at_spec semantic_pos semantic_inline_cursor false c st W)
    as [E W'].
  destruct (IH _ W') as [E2 W2]. split; [|exact W2].
  change (sabs (sscan_str_off s (@sstep_at T Buf X semantic_pos semantic_inline_cursor
            false c st))
          = iscan_str_off s (@istep_at T string _ semantic_pos semantic_inline_cursor
              false c (sabs st))).
  rewrite E2, E. reflexivity.
Qed.

Theorem sscan_lines_spec : forall l st, swf st ->
  sabs (sscan_lines l st) = iscan_lines l (sabs st) /\ swf (sscan_lines l st).
Proof.
  induction l as [|x l IH]; intros st W; [split; [reflexivity|exact W]|].
  destruct l as [|y l]; [apply sscan_str_spec; exact W|].
  destruct (sscan_str_spec x st W) as [E1 W1].
  destruct (@sbreak_at_spec semantic_pos semantic_inline_cursor
              inline_attrs_enabled _ W1) as [E2 W2].
  destruct (IH _ W2) as [E3 W3]. split; [|exact W3].
  change (sabs (sscan_lines (y :: l)
            (@sbreak_at T Buf X semantic_pos semantic_inline_cursor
               inline_attrs_enabled (sscan_str x st)))
          = iscan_lines (y :: l)
              (@ibreak T string _ semantic_pos semantic_inline_cursor
                 (iscan_str x (sabs st)))).
  rewrite E3, E2, E1. reflexivity.
Qed.

Theorem sscan_lines_off_spec : forall k l st, swf st ->
  sabs (sscan_lines_off k l st) = iscan_lines_off k l (sabs st)
  /\ swf (sscan_lines_off k l st).
Proof.
  induction k as [|k IH]; intros l st W; [apply sscan_lines_spec; exact W|].
  destruct l as [|x [|y l]]; [split; [reflexivity|exact W]| |].
  - apply sscan_str_off_spec. exact W.
  - destruct (sscan_str_off_spec x st W) as [E1 W1].
    destruct (@sbreak_at_spec semantic_pos semantic_inline_cursor false _ W1)
      as [E2 W2].
    destruct (IH (y :: l) _ W2) as [E3 W3]. split; [|exact W3].
    change (sabs (sscan_lines_off k (y :: l)
              (@sbreak_at T Buf X semantic_pos semantic_inline_cursor false
                 (sscan_str_off x st)))
            = iscan_lines_off k (y :: l)
                (@ibreak_at T string _ semantic_pos semantic_inline_cursor false
                   (iscan_str_off x (sabs st)))).
    rewrite E3, E2, E1. reflexivity.
Qed.

Theorem sscan_str_located_spec : forall `{P : PosPolicy} allow k origin rem s st,
  swf st ->
  sabs (sscan_str_located allow k origin rem s st)
  = InlineLocated.iscan_str_located allow k origin rem s (sabs st)
  /\ swf (sscan_str_located allow k origin rem s st).
Proof.
  intros P allow k origin rem s. revert rem.
  induction s as [|c s IH]; intros rem st W; [split; [reflexivity|exact W]|].
  destruct (@sstep_at_spec P (InlineLocated.cursor_in k rem origin) allow c st W)
    as [E W'].
  destruct (IH (pred rem) _ W') as [E2 W2]. split; [|exact W2].
  change (sabs (sscan_str_located allow k origin (pred rem) s
            (@sstep_at T Buf X P (InlineLocated.cursor_in k rem origin) allow c st))
          = InlineLocated.iscan_str_located allow k origin (pred rem) s
              (@istep_at T string _ P (InlineLocated.cursor_in k rem origin)
                 allow c (sabs st))).
  rewrite E2, E. reflexivity.
Qed.

Theorem sscan_lines_located_spec : forall `{P : PosPolicy} off origin l st,
  swf st ->
  sabs (sscan_lines_located off origin l st)
  = InlineLocated.iscan_lines_located off origin l (sabs st)
  /\ swf (sscan_lines_located off origin l st).
Proof.
  intros P off origin l. revert off.
  induction l as [|[k x] l IH]; intros off st W; [split; [reflexivity|exact W]|].
  destruct l as [|[k' y] l]; [apply sscan_str_located_spec; exact W|].
  destruct (sscan_str_located_spec (InlineLocated.allow_attrs off) k origin
              (String.length x) x st W) as [E1 W1].
  destruct (@sbreak_at_spec P
              (CursorAt (Spot k 0) (InlineLocated.lines_start ((k', y) :: l))
                 (Spot k (String.length x)))
              (InlineLocated.allow_attrs off) _ W1) as [E2 W2].
  destruct (IH (pred off) _ W2) as [E3 W3]. split; [|exact W3].
  change (sabs (sscan_lines_located (pred off) origin ((k', y) :: l)
            (@sbreak_at T Buf X P
               (CursorAt (Spot k 0) (InlineLocated.lines_start ((k', y) :: l))
                  (Spot k (String.length x)))
               (InlineLocated.allow_attrs off)
               (sscan_str_located (InlineLocated.allow_attrs off) k origin
                  (String.length x) x st)))
          = InlineLocated.iscan_lines_located (pred off) origin ((k', y) :: l)
              (@ibreak_at T string _ P
                 (CursorAt (Spot k 0) (InlineLocated.lines_start ((k', y) :: l))
                    (Spot k (String.length x)))
                 (InlineLocated.allow_attrs off)
                 (InlineLocated.iscan_str_located (InlineLocated.allow_attrs off) k
                    origin (String.length x) x (sabs st)))).
  rewrite E3, E2, E1. reflexivity.
Qed.

End Lawful.

(*
The entry points
================

Each is equal to the one the extraction substitutes it for.
*)

Theorem parse_inline_line_stk_spec : forall s,
  parse_inline_line_stk s = parse_inline_line s.
Proof.
  intros s. unfold parse_inline_line_stk, parse_inline_line.
  rewrite sfinish_spec. f_equal.
  destruct (sscan_str_spec s sstart swf_sstart) as [E _].
  rewrite E, sabs_sstart. reflexivity.
Qed.

Theorem para_inlines_off_stk_spec : forall k l,
  para_inlines_off_stk k l = para_inlines_off k l.
Proof.
  intros k l. unfold para_inlines_off_stk, para_inlines_off.
  rewrite sfinish_spec. f_equal.
  destruct (sscan_lines_off_spec k l sstart swf_sstart) as [E _].
  rewrite E, sabs_sstart. reflexivity.
Qed.

Theorem para_inlines_stk_spec : forall l,
  para_inlines_off_stk 0 l = para_inlines l.
Proof. intros l. apply para_inlines_off_stk_spec. Qed.

Theorem para_inlines_located_stk_spec : forall `{PosPolicy} off l,
  para_inlines_located_stk off l = InlineLocated.para_inlines_located off l.
Proof.
  intros P off l.
  unfold para_inlines_located_stk, InlineLocated.para_inlines_located,
    InlineLocated.ifinish_located.
  rewrite sfinish_spec. f_equal.
  destruct (sscan_lines_located_spec off (InlineLocated.lines_start l) l sstart
              swf_sstart) as [E _].
  rewrite E, sabs_sstart. reflexivity.
Qed.

Theorem parse_inline_line_located_stk_spec : forall `{PosPolicy} k rem s,
  parse_inline_line_located_stk k rem s = parse_inline_line_located k rem s.
Proof.
  intros P k rem s.
  unfold parse_inline_line_located_stk, parse_inline_line_located.
  rewrite sfinish_spec. f_equal.
  destruct (sscan_str_located_spec inline_attrs_enabled k (Spot k rem) rem s
              sstart swf_sstart) as [E _].
  rewrite E, sabs_sstart. reflexivity.
Qed.

End WithTable.
