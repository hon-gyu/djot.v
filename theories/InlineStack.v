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

Lemma concat_cons_empty : forall u acc,
  String.concat EmptyString (u :: acc) = (u ++ String.concat EmptyString acc)%string.
Proof.
  intros u [|x acc]; cbn [String.concat]; [rewrite append_empty_r|]; reflexivity.
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

Definition mkframe (p b : nat) (esc : bool) (k : ckind (Buf:=Buf)) (lvl : nat)
  (pay : string) (inner : iscan) : iscan :=
  match k with
  | CDest kids image open o => IDest kids image open esc (p - lvl) (ddecode pay) inner o
  | CHole txt o => IHole (b - lvl) esc pay (tval txt) inner o
  end.

(* `pay` is the top frame's payload; each frame below adds the segment
   from its opener to the next one's. *)
Fixpoint wrap (p b : nat) (esc : bool) (fs : list (cframe (Buf:=Buf)))
  (pay : string) (inner : iscan) : iscan :=
  match fs with
  | [] => inner
  | f :: fs' =>
      wrap p b esc fs' (tval (cf_under f) ++ pay)
        (mkframe p b esc (cf_kind f) (cf_level f) pay inner)
  end.

Definition sabs (s : sscan (Buf:=Buf)) : iscan :=
  wrap (s_parens s) (s_braces s) (s_esc s) (s_frames s) (tval (s_seg s))
    (map_text (s_cur s)).

Fixpoint payload_after (fs : list (cframe (Buf:=Buf))) (pay : string) : string :=
  match fs with
  | [] => pay
  | f :: fs' => payload_after fs' (tval (cf_under f) ++ pay)
  end.

Lemma wrap_app : forall p b esc xs ys pay inner,
  wrap p b esc (xs ++ ys)%list pay inner
  = wrap p b esc ys (payload_after xs pay) (wrap p b esc xs pay inner).
Proof.
  induction xs as [|f xs IH]; intros ys pay inner; [reflexivity|].
  cbn [app wrap payload_after]. apply IH.
Qed.

(*
The invariant
=============
*)

Definition is_dest (f : cframe (Buf:=Buf)) : bool :=
  match cf_kind f with CDest _ _ _ _ => true | CHole _ _ => false end.

Fixpoint dtop_of (fs : list (cframe (Buf:=Buf))) : option nat :=
  match fs with
  | [] => None
  | f :: fs' => if is_dest f then Some (cf_level f) else dtop_of fs'
  end.

Fixpoint htop_of (fs : list (cframe (Buf:=Buf))) : option nat :=
  match fs with
  | [] => None
  | f :: fs' => if is_dest f then htop_of fs' else Some (cf_level f)
  end.

Fixpoint saved_ok (fs : list (cframe (Buf:=Buf))) : Prop :=
  match fs with
  | [] => True
  | f :: fs' => cf_dtop f = dtop_of fs' /\ cf_htop f = htop_of fs' /\ saved_ok fs'
  end.

(* The levels of one kind, top first, strictly decreasing and below
   `bound`. *)
Fixpoint lv (dest : bool) (bound : nat) (fs : list (cframe (Buf:=Buf))) : Prop :=
  match fs with
  | [] => True
  | f :: fs' =>
      if Bool.eqb (is_dest f) dest
      then cf_level f < bound /\ lv dest (cf_level f) fs'
      else lv dest bound fs'
  end.

(* Every open payload ends in the same escape state. *)
Fixpoint esc_ok (esc : bool) (fs : list (cframe (Buf:=Buf))) (pay : string) : Prop :=
  match fs with
  | [] => True
  | f :: fs' => esc_after false pay = esc /\ esc_ok esc fs' (tval (cf_under f) ++ pay)
  end.

Definition wf_parts (fs : list (cframe (Buf:=Buf))) (dtop htop : option nat)
  (p b : nat) (esc : bool) (seg : Buf) : Prop :=
  saved_ok fs /\ dtop = dtop_of fs /\ htop = htop_of fs
  /\ lv true (S p) fs /\ lv false (S b) fs /\ esc_ok esc fs (tval seg).

Definition swf (s : sscan (Buf:=Buf)) : Prop :=
  wf_parts (s_frames s) (s_dtop s) (s_htop s) (s_parens s) (s_braces s)
    (s_esc s) (s_seg s).

Lemma swf_slift : forall st, swf (slift st).
Proof. intros st. repeat split. Qed.

Lemma lv_mono : forall dest fs b b', lv dest b fs -> b <= b' -> lv dest b' fs.
Proof.
  induction fs as [|f fs IH]; intros b b' H Hle; cbn [lv] in *; [exact I|].
  destruct (Bool.eqb (is_dest f) dest); [destruct H; split; [lia|assumption]|].
  eapply IH; eassumption.
Qed.

Definition top_of (dest : bool) (fs : list (cframe (Buf:=Buf))) : option nat :=
  if dest then dtop_of fs else htop_of fs.

Lemma lv_tighten : forall dest fs b x,
  lv dest b fs -> sabove (top_of dest fs) x = true -> lv dest x fs.
Proof.
  induction fs as [|f fs IH]; intros b x H Ha; cbn [lv] in *; [exact I|].
  unfold top_of in Ha; cbn [dtop_of htop_of] in Ha.
  destruct (is_dest f), dest; cbn [Bool.eqb] in *;
    try (destruct H as [H1 H2]; split; [cbn [sabove] in Ha; apply Nat.ltb_lt in Ha; exact Ha|exact H2]);
    eapply IH; try eassumption; exact Ha.
Qed.

Lemma lv_app : forall dest xs ys b, lv dest b (xs ++ ys)%list -> exists b', lv dest b' ys /\ b' <= b.
Proof.
  induction xs as [|f xs IH]; intros ys b H; [exists b; split; [exact H|lia]|].
  cbn [app lv] in H. destruct (Bool.eqb (is_dest f) dest).
  - destruct H as [H1 H2]. destruct (IH _ _ H2) as [b' [Hb Hle]].
    exists b'. split; [exact Hb|lia].
  - exact (IH _ _ H).
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

Lemma esc_ok_payload : forall esc xs ys pay,
  esc_ok esc (xs ++ ys)%list pay -> esc_ok esc ys (payload_after xs pay).
Proof.
  induction xs as [|f xs IH]; intros ys pay H; [exact H|].
  destruct H as [_ H]. apply IH. exact H.
Qed.

Lemma saved_ok_app : forall xs ys, saved_ok (xs ++ ys)%list -> saved_ok ys.
Proof. induction xs as [|f xs IH]; intros ys H; [exact H|]. apply IH, H. Qed.

(*
Popping
=======
*)

Lemma spop_spec : forall dest fs acc f fs' pay,
  spop dest fs acc = Some (f, fs', pay) ->
  exists above, fs = (above ++ f :: fs')%list
    /\ is_dest f = dest
    /\ Forall (fun g => is_dest g = negb dest) above
    /\ pay = payload_after above (String.concat EmptyString acc).
Proof.
  induction fs as [|g fs IH]; intros acc f fs' pay H; [discriminate H|].
  cbn [spop] in H.
  destruct (match cf_kind g with CDest _ _ _ _ => dest | CHole _ _ => negb dest end) eqn:E.
  - injection H as <- <- <-. exists []. repeat split; [|constructor].
    unfold is_dest. destruct (cf_kind g), dest; cbn in *; congruence.
  - destruct (IH _ _ _ _ H) as [above [-> [Hk [Ha Hp]]]].
    exists (g :: above). split; [reflexivity|]. split; [exact Hk|]. split.
    + constructor; [|exact Ha]. unfold is_dest.
      destruct (cf_kind g), dest; cbn in *; congruence.
    + rewrite Hp. cbn [payload_after]. rewrite concat_cons_empty. reflexivity.
Qed.

Lemma spop_some : forall dest fs acc l,
  top_of dest fs = Some l ->
  exists f fs' pay, spop dest fs acc = Some (f, fs', pay) /\ cf_level f = l.
Proof.
  induction fs as [|g fs IH]; intros acc l H;
    [destruct dest; discriminate H|].
  unfold top_of in H. cbn [dtop_of htop_of spop] in *.
  unfold is_dest in H.
  destruct (cf_kind g), dest; cbn [negb] in *;
    try (injection H as <-; eexists _, _, _; split; reflexivity);
    apply IH; exact H.
Qed.

(*
One frame, one byte
===================
*)

Section Cursor.
Context `{PosPolicy} `{InlineCursor}.

(* A frame the byte does not close. *)
Definition quiet (esc : bool) (c : ascii) (p b : nat) (f : cframe (Buf:=Buf)) : Prop :=
  if is_dest f
  then cf_level f <= p /\ (esc = false -> c = rparen -> cf_level f <> p)
  else cf_level f <= b /\ (esc = false -> c = rbrace -> cf_level f <> b).

Lemma eqb_refl_char : forall c, Ascii.eqb c c = true.
Proof. intros c. apply Ascii.eqb_refl. Qed.

Lemma mkframe_step : forall a c p b esc f pay inner,
  esc_after false pay = esc -> quiet esc c p b f ->
  istep_at a c (mkframe p b esc (cf_kind f) (cf_level f) pay inner)
  = mkframe (scount esc c lparen rparen p) (scount esc c lbrace rbrace b)
      (negb esc && is_bslash c) (cf_kind f) (cf_level f) (pay ++ one c)
      (istep_at a c inner).
Proof.
  intros a c p b esc f pay inner He Hq.
  unfold quiet, is_dest in Hq. destruct f as [k lvl u dt ht]; cbn [cf_kind cf_level] in *.
  destruct k as [kids image open o|txt o]; cbn [mkframe istep_at]; tred.
  - rewrite ddecode_snoc, He. destruct Hq as [Hle Hc].
    destruct esc; cbn [negb andb scount].
    + reflexivity.
    + unfold is_bslash. destruct (Ascii.eqb c bslash) eqn:Eb.
      * apply Ascii.eqb_eq in Eb. subst c. rewrite append_empty_r. reflexivity.
      * destruct (Ascii.eqb c lparen) eqn:Ep.
        { apply Ascii.eqb_eq in Ep. subst c. f_equal. lia. }
        destruct (Ascii.eqb c rparen) eqn:Er.
        { apply Ascii.eqb_eq in Er. subst c.
          assert (lvl <> p) by (apply Hc; reflexivity).
          destruct (p - lvl) as [|d] eqn:Ed; [lia|]. f_equal. lia. }
        reflexivity.
  - destruct Hq as [Hle Hc]. unfold ihole_step.
    destruct esc; cbn [negb andb scount]; [reflexivity|].
    unfold is_bslash. destruct (Ascii.eqb c bslash) eqn:Eb;
      [apply Ascii.eqb_eq in Eb; subst c; reflexivity|].
    destruct (Ascii.eqb c lbrace) eqn:Ep.
    { apply Ascii.eqb_eq in Ep. subst c. f_equal. lia. }
    destruct (Ascii.eqb c rbrace) eqn:Er.
    { apply Ascii.eqb_eq in Er. subst c.
      assert (lvl <> b) by (apply Hc; reflexivity).
      destruct (b - lvl) as [|d] eqn:Ed; [lia|]. f_equal. lia. }
    reflexivity.
Qed.

Lemma wrap_step : forall a c p b esc fs pay inner,
  esc_ok esc fs pay -> Forall (quiet esc c p b) fs ->
  istep_at a c (wrap p b esc fs pay inner)
  = wrap (scount esc c lparen rparen p) (scount esc c lbrace rbrace b)
      (negb esc && is_bslash c) fs (pay ++ one c) (istep_at a c inner).
Proof.
  induction fs as [|f fs IH]; intros pay inner He Hq; [reflexivity|].
  destruct He as [He1 He2]. inversion Hq as [|? ? Hq1 Hq2]; subst.
  cbn [wrap]. rewrite IH by assumption.
  rewrite mkframe_step by first [reflexivity|assumption].
  rewrite append_assoc. reflexivity.
Qed.

Lemma lv_quiet_d : forall fs bnd (P : cframe (Buf:=Buf) -> Prop),
  lv true bnd fs ->
  (forall f, is_dest f = true -> cf_level f < bnd -> P f) ->
  (forall f, is_dest f = false -> P f) ->
  Forall P fs.
Proof.
  induction fs as [|f fs IH]; intros bnd Q Hl Hd Hh; constructor.
  - cbn [lv] in Hl. destruct (is_dest f) eqn:E; cbn [Bool.eqb] in Hl;
      [apply Hd; [exact E|apply Hl]|apply Hh; exact E].
  - cbn [lv] in Hl. destruct (is_dest f) eqn:E; cbn [Bool.eqb] in Hl.
    + destruct Hl as [H1 H2]. apply (IH (cf_level f)); [exact H2| |exact Hh].
      intros g Eg Lg. apply Hd; [exact Eg|lia].
    + exact (IH bnd Q Hl Hd Hh).
Qed.

Lemma lv_quiet_h : forall fs bnd (P : cframe (Buf:=Buf) -> Prop),
  lv false bnd fs ->
  (forall f, is_dest f = false -> cf_level f < bnd -> P f) ->
  (forall f, is_dest f = true -> P f) ->
  Forall P fs.
Proof.
  induction fs as [|f fs IH]; intros bnd Q Hl Hh Hd; constructor.
  - cbn [lv] in Hl. destruct (is_dest f) eqn:E; cbn [Bool.eqb] in Hl;
      [apply Hd; exact E|apply Hh; [exact E|apply Hl]].
  - cbn [lv] in Hl. destruct (is_dest f) eqn:E; cbn [Bool.eqb] in Hl.
    + exact (IH bnd Q Hl Hh Hd).
    + destruct Hl as [H1 H2]. apply (IH (cf_level f)); [exact H2| |exact Hd].
      intros g Eg Lg. apply Hh; [exact Eg|lia].
Qed.

Lemma sat_level_false : forall top x, sat_level top x = false -> sabove top x = true \/ exists l, top = Some l /\ x < l.
Proof.
  intros [l|] x Hl; cbn [sat_level sabove] in *; [|left; reflexivity].
  apply Nat.eqb_neq in Hl. destruct (Nat.ltb l x) eqn:E; [left; reflexivity|].
  right. exists l. split; [reflexivity|]. apply Nat.ltb_ge in E. lia.
Qed.

(* The byte closes nothing: every frame is quiet. *)
Lemma quiet_all : forall fs p b esc c,
  lv true (S p) fs -> lv false (S b) fs ->
  (negb esc && Ascii.eqb c rparen && sat_level (dtop_of fs) p)%bool = false ->
  (negb esc && Ascii.eqb c rbrace && sat_level (htop_of fs) b)%bool = false ->
  Forall (quiet esc c p b) fs.
Proof.
  intros fs p b esc c Hd Hh Cd Ch.
  assert (Fd : Forall (fun f => is_dest f = true ->
            cf_level f <= p /\ (esc = false -> c = rparen -> cf_level f <> p)) fs).
  { destruct esc; [|destruct (Ascii.eqb c rparen) eqn:Ec].
    - apply (lv_quiet_d fs (S p)); [exact Hd| |intros f E E'; congruence].
      intros f _ Lf _. split; [lia|discriminate].
    - cbn [negb andb] in Cd.
      destruct (sat_level_false _ _ Cd) as [Ha|[l [El Ll]]].
      + apply (lv_quiet_d fs p); [apply (lv_tighten true fs (S p)); assumption| |intros f E E'; congruence].
        intros f _ Lf _. split; [lia|intros _ _; lia].
      + (* the top destination is above the counter: impossible *)
        exfalso. clear -Hd El Ll.
        induction fs as [|f fs IH]; [discriminate El|].
        cbn [dtop_of lv] in *. destruct (is_dest f); cbn [Bool.eqb] in Hd.
        * injection El as <-. lia.
        * exact (IH Hd El).
    - apply (lv_quiet_d fs (S p)); [exact Hd| |intros f E E'; congruence].
      intros f _ Lf _. split; [lia|]. intros _ ->. rewrite eqb_refl_char in Ec. discriminate. }
  assert (Fh : Forall (fun f => is_dest f = false ->
            cf_level f <= b /\ (esc = false -> c = rbrace -> cf_level f <> b)) fs).
  { destruct esc; [|destruct (Ascii.eqb c rbrace) eqn:Ec].
    - apply (lv_quiet_h fs (S b)); [exact Hh| |intros f E E'; congruence].
      intros f _ Lf _. split; [lia|discriminate].
    - cbn [negb andb] in Ch.
      destruct (sat_level_false _ _ Ch) as [Ha|[l [El Ll]]].
      + apply (lv_quiet_h fs b); [apply (lv_tighten false fs (S b)); assumption| |intros f E E'; congruence].
        intros f _ Lf _. split; [lia|intros _ _; lia].
      + exfalso. clear -Hh El Ll.
        induction fs as [|f fs IH]; [discriminate El|].
        cbn [htop_of lv] in *. destruct (is_dest f); cbn [Bool.eqb] in Hh.
        * exact (IH Hh El).
        * injection El as <-. lia.
    - apply (lv_quiet_h fs (S b)); [exact Hh| |intros f E E'; congruence].
      intros f _ Lf _. split; [lia|]. intros _ ->. rewrite eqb_refl_char in Ec. discriminate. }
  clear -Fd Fh. induction fs as [|f fs IH]; [constructor|].
  inversion Fd; inversion Fh; subst. constructor; [|apply IH; assumption].
  unfold quiet. destruct (is_dest f); auto.
Qed.

(*
The step
========
*)

Lemma speel_sabs : forall fs dtop htop p b esc seg cur,
  sabs (speel fs dtop htop p b esc seg cur)
  = wrap p b esc fs (tval seg) (map_text cur).
Proof.
  intros fs dtop htop p b esc seg cur. unfold speel.
  destruct cur; try reflexivity.
  - destruct esc0; [reflexivity|]. destruct depth; [|reflexivity].
    destruct (negb (tnonempty dst) && negb esc && sabove dtop p)%bool eqn:E;
      [|reflexivity].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply negb_true_iff in E1, E2. rewrite tnonempty_val in E1. subst esc. laws.
    unfold sabs. cbn [s_parens s_braces s_esc s_frames s_seg s_cur wrap cf_kind cf_level cf_under].
    laws. rewrite append_empty_r. cbn [mkframe map_text]. rewrite Nat.sub_diag.
    destruct (tval dst) eqn:Ed; [reflexivity|cbn in E1; discriminate E1].
  - destruct depth; [|reflexivity]. destruct esc0; [reflexivity|].
    destruct (negb (tnonempty src) && negb esc && sabove htop b)%bool eqn:E;
      [|reflexivity].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply negb_true_iff in E1, E2. rewrite tnonempty_val in E1. subst esc. laws.
    unfold sabs. cbn [s_parens s_braces s_esc s_frames s_seg s_cur wrap cf_kind cf_level cf_under].
    laws. rewrite append_empty_r. cbn [mkframe map_text]. rewrite Nat.sub_diag.
    destruct (tval src) eqn:Ed; [reflexivity|cbn in E1; discriminate E1].
Qed.

Lemma speel_swf : forall fs dtop htop p b esc seg cur,
  wf_parts fs dtop htop p b esc seg ->
  swf (speel fs dtop htop p b esc seg cur).
Proof.
  intros fs dtop htop p b esc seg cur W.
  destruct W as (Hs & Hd & Hh & Ld & Lh & He).
  unfold speel. destruct cur; try (repeat split; assumption).
  - destruct esc0; [repeat split; assumption|]. destruct depth; [|repeat split; assumption].
    destruct (negb (tnonempty dst) && negb esc && sabove dtop p)%bool eqn:E;
      [|repeat split; assumption].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply negb_true_iff in E2. subst esc dtop htop.
    unfold swf, wf_parts; cbn [s_frames s_dtop s_htop s_parens s_braces s_esc s_seg
      saved_ok dtop_of htop_of lv esc_ok is_dest cf_kind cf_level cf_dtop cf_htop cf_under Bool.eqb].
    repeat split; try assumption; try lia.
    + apply (lv_tighten true fs (S p)); assumption.
    + rewrite tval_nil. reflexivity.
    + rewrite tval_nil, append_empty_r. assumption.
  - destruct depth; [|repeat split; assumption]. destruct esc0; [repeat split; assumption|].
    destruct (negb (tnonempty src) && negb esc && sabove htop b)%bool eqn:E;
      [|repeat split; assumption].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply negb_true_iff in E2. subst esc dtop htop.
    unfold swf, wf_parts; cbn [s_frames s_dtop s_htop s_parens s_braces s_esc s_seg
      saved_ok dtop_of htop_of lv esc_ok is_dest cf_kind cf_level cf_dtop cf_htop cf_under Bool.eqb].
    repeat split; try assumption; try lia.
    + apply (lv_tighten false fs (S b)); assumption.
    + rewrite tval_nil. reflexivity.
    + rewrite tval_nil, append_empty_r. assumption.
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

Lemma lv_count : forall dest fs bnd n esc c up down,
  lv dest bnd fs -> bnd <= S n ->
  Forall (fun f => is_dest f = dest -> cf_level f < S n /\
            (esc = false -> c = down -> cf_level f <> n)) fs ->
  lv dest (S (scount esc c up down n)) fs.
Proof.
  induction fs as [|f fs IH]; intros bnd n esc c up down Hx Hb Q; [exact I|].
  inversion Q as [|? ? Q1 Q2]; subst. cbn [lv] in *.
  destruct (Bool.eqb (is_dest f) dest) eqn:E.
  - apply Bool.eqb_prop in E. destruct Hx as [H1 H2].
    destruct (Q1 E) as [Q3 Q4]. split; [apply scount_bound; assumption|].
    exact H2.
  - eapply IH; eassumption.
Qed.

Lemma wf_quiet : forall fs dtop htop p b esc seg c,
  wf_parts fs dtop htop p b esc seg ->
  Forall (quiet esc c p b) fs ->
  wf_parts fs dtop htop (scount esc c lparen rparen p) (scount esc c lbrace rbrace b)
    (negb esc && is_bslash c) (if null fs then seg else tpush seg (one c)).
Proof.
  intros fs dtop htop p b esc seg c W Q.
  destruct W as (Hs & Hd & Hh & Ld & Lh & He).
  repeat split; try assumption.
  - apply (lv_count true fs (S p)); [exact Ld|lia|].
    eapply Forall_impl; [|exact Q]. intros f Hq E. unfold quiet in Hq.
    rewrite E in Hq. destruct Hq. split; [lia|assumption].
  - apply (lv_count false fs (S b)); [exact Lh|lia|].
    eapply Forall_impl; [|exact Q]. intros f Hq E. unfold quiet in Hq.
    rewrite E in Hq. destruct Hq. split; [lia|assumption].
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
    | CHole txt o => ihole_close pay (tval txt) o
    end.
Proof.
  intros [kids image open o|txt o] pay; cbn [sframe_close map_text]; laws;
    [reflexivity|]. unfold ihole_close. cbn [map_text]. laws. reflexivity.
Qed.

Theorem sstep_at_spec : forall a c s, swf s ->
  sabs (sstep_at a c s) = istep_at a c (sabs s) /\ swf (sstep_at a c s).
Proof.
  intros a c [fs dtop htop p b esc seg cur] W.
  pose proof W as W'. destruct W' as (Hs & Hd & Hh & Ld & Lh & He).
  cbn [s_frames s_dtop s_htop s_parens s_braces s_esc s_seg s_cur] in *.
  unfold sstep_at, sabs. cbn [s_frames s_dtop s_htop s_parens s_braces s_esc s_seg s_cur].
  destruct (negb esc && Ascii.eqb c rparen && sat_level dtop p)%bool eqn:Cd;
  [|destruct (negb esc && Ascii.eqb c rbrace && sat_level htop b)%bool eqn:Ch].
  - (* a destination closes *)
    apply andb_prop in Cd as [Cd Cl]. apply andb_prop in Cd as [Ce Cc].
    apply negb_true_iff in Ce. apply Ascii.eqb_eq in Cc. subst esc c.
    destruct dtop as [l|]; [|discriminate Cl]. cbn [sat_level] in Cl.
    apply Nat.eqb_eq in Cl. subst l.
    destruct (spop_some true fs [tval seg] p (eq_sym Hd)) as (f & fs' & pay & Hp & Hl).
    cbn [orb]. rewrite Hp.
    destruct (spop_spec _ _ _ _ _ _ Hp) as (above & -> & Hk & Ha & Hpay).
    cbn [String.concat] in Hpay. subst pay.
    rewrite wrap_app. cbn [wrap].
    assert (Qf : Forall (quiet false rparen p b) fs').
    { apply quiet_all.
      - destruct (lv_app true above (f :: fs') (S p) Ld) as [b' [Lb Lle]].
        cbn [lv] in Lb. rewrite Hk in Lb. cbn [Bool.eqb] in Lb. destruct Lb as [_ Lb].
        apply (lv_mono _ _ _ _ Lb). lia.
      - destruct (lv_app false above (f :: fs') (S b) Lh) as [b' [Lb Lle]].
        cbn [lv] in Lb. rewrite Hk in Lb. cbn [Bool.eqb] in Lb.
        apply (lv_mono _ _ _ _ Lb). lia.
      - (* the next destination is below `p` *)
        destruct (lv_app true above (f :: fs') (S p) Ld) as [b' [Lb Lle]].
        cbn [lv] in Lb. rewrite Hk in Lb. cbn [Bool.eqb] in Lb. destruct Lb as [Lf Lb].
        rewrite Hl in Lb. clear -Lb.
        destruct (sat_level (dtop_of fs') p) eqn:E; [|apply andb_false_r].
        exfalso. induction fs' as [|g fs' IH]; [discriminate E|].
        cbn [dtop_of lv] in *. destruct (is_dest g); cbn [Bool.eqb] in Lb.
        + cbn [sat_level] in E. apply Nat.eqb_eq in E. lia.
        + exact (IH Lb E).
      - reflexivity. }
    assert (Ef : esc_ok false fs' (tval (cf_under f) ++ payload_after above (tval seg))).
    { pose proof (esc_ok_payload _ _ _ _ He) as E1. exact (proj2 E1). }
    assert (Ep : esc_after false (payload_after above (tval seg)) = false).
    { exact (proj1 (esc_ok_payload _ _ _ _ He)). }
    split.
    + rewrite wrap_step by assumption.
      cbn [s_frames s_parens s_braces s_esc s_seg s_cur].
      assert (Cl : forall inner, istep_at a rparen
                (mkframe p b false (cf_kind f) (cf_level f)
                   (payload_after above (tval seg)) inner)
              = map_text (sframe_close (cf_kind f) (payload_after above (tval seg)))).
      { intros inner. rewrite sframe_close_map. destruct f as [k lvl u dt ht].
        cbn [cf_kind cf_level is_dest] in *. subst lvl.
        destruct k as [kids image open o|txt o]; [|discriminate Hk].
        cbn [mkframe istep_at]. rewrite Nat.sub_diag. tred. reflexivity. }
      rewrite Cl.
      destruct fs' as [|g fs'']; [reflexivity|]. cbn [null]. laws.
      rewrite append_assoc. reflexivity.
    + pose proof (saved_ok_app _ _ Hs) as Sf. destruct Sf as (Sd & Sh & Sf).
      unfold swf, wf_parts. cbn [s_frames s_dtop s_htop s_parens s_braces s_esc s_seg].
      split; [exact Sf|]. split; [exact Sd|]. split; [exact Sh|].
      pose proof (wf_quiet fs' (dtop_of fs') (htop_of fs') p b false
        (tof (tval (cf_under f) ++ payload_after above (tval seg))) rparen) as WQ.
      destruct WQ as (_ & _ & _ & L1 & L2 & E3).
      { repeat split; try assumption.
        - destruct (lv_app true above (f :: fs') (S p) Ld) as [b' [Lb Lle]].
          cbn [lv] in Lb. rewrite Hk in Lb. cbn [Bool.eqb] in Lb. destruct Lb as [_ Lb].
          apply (lv_mono _ _ _ _ Lb). lia.
        - destruct (lv_app false above (f :: fs') (S b) Lh) as [b' [Lb Lle]].
          cbn [lv] in Lb. rewrite Hk in Lb. cbn [Bool.eqb] in Lb.
          apply (lv_mono _ _ _ _ Lb). lia.
        - laws. exact Ef. }
      { exact Qf. }
      split; [exact L1|]. split; [exact L2|].
      destruct fs' as [|g fs'']; [exact I|]. cbn [null] in *. laws.
      rewrite tval_push, tval_of in E3. rewrite append_assoc in E3. exact E3.
  - (* a hole closes *)
    apply andb_prop in Ch as [Ch Cl]. apply andb_prop in Ch as [Ce Cc].
    apply negb_true_iff in Ce. apply Ascii.eqb_eq in Cc. subst esc c.
    destruct htop as [l|]; [|discriminate Cl]. cbn [sat_level] in Cl.
    apply Nat.eqb_eq in Cl. subst l.
    destruct (spop_some false fs [tval seg] b (eq_sym Hh)) as (f & fs' & pay & Hp & Hl).
    cbn [orb]. rewrite Hp.
    destruct (spop_spec _ _ _ _ _ _ Hp) as (above & -> & Hk & Ha & Hpay).
    cbn [String.concat] in Hpay. subst pay.
    rewrite wrap_app. cbn [wrap].
    assert (Qf : Forall (quiet false rbrace p b) fs').
    { apply quiet_all.
      - destruct (lv_app true above (f :: fs') (S p) Ld) as [b' [Lb Lle]].
        cbn [lv] in Lb. rewrite Hk in Lb. cbn [Bool.eqb] in Lb.
        apply (lv_mono _ _ _ _ Lb). lia.
      - destruct (lv_app false above (f :: fs') (S b) Lh) as [b' [Lb Lle]].
        cbn [lv] in Lb. rewrite Hk in Lb. cbn [Bool.eqb] in Lb. destruct Lb as [_ Lb].
        apply (lv_mono _ _ _ _ Lb). lia.
      - reflexivity.
      - destruct (lv_app false above (f :: fs') (S b) Lh) as [b' [Lb Lle]].
        cbn [lv] in Lb. rewrite Hk in Lb. cbn [Bool.eqb] in Lb. destruct Lb as [Lf Lb].
        rewrite Hl in Lb. clear -Lb.
        destruct (sat_level (htop_of fs') b) eqn:E; [|apply andb_false_r].
        exfalso. induction fs' as [|g fs' IH]; [discriminate E|].
        cbn [htop_of lv] in *. destruct (is_dest g); cbn [Bool.eqb] in Lb.
        + exact (IH Lb E).
        + cbn [sat_level] in E. apply Nat.eqb_eq in E. lia. }
    assert (Ef : esc_ok false fs' (tval (cf_under f) ++ payload_after above (tval seg))).
    { pose proof (esc_ok_payload _ _ _ _ He) as E1. exact (proj2 E1). }
    split.
    + rewrite wrap_step by assumption.
      cbn [s_frames s_parens s_braces s_esc s_seg s_cur].
      assert (Cl : forall inner, istep_at a rbrace
                (mkframe p b false (cf_kind f) (cf_level f)
                   (payload_after above (tval seg)) inner)
              = map_text (sframe_close (cf_kind f) (payload_after above (tval seg)))).
      { intros inner. rewrite sframe_close_map. destruct f as [k lvl u dt ht].
        cbn [cf_kind cf_level is_dest] in *. subst lvl.
        destruct k as [kids image open o|txt o]; [discriminate Hk|].
        cbn [mkframe istep_at]. rewrite Nat.sub_diag. unfold ihole_step. tred.
        reflexivity. }
      rewrite Cl.
      destruct fs' as [|g fs'']; [reflexivity|]. cbn [null]. laws.
      rewrite append_assoc. reflexivity.
    + pose proof (saved_ok_app _ _ Hs) as Sf. destruct Sf as (Sd & Sh & Sf).
      unfold swf, wf_parts. cbn [s_frames s_dtop s_htop s_parens s_braces s_esc s_seg].
      split; [exact Sf|]. split; [exact Sd|]. split; [exact Sh|].
      pose proof (wf_quiet fs' (dtop_of fs') (htop_of fs') p b false
        (tof (tval (cf_under f) ++ payload_after above (tval seg))) rbrace) as WQ.
      destruct WQ as (_ & _ & _ & L1 & L2 & E3).
      { repeat split; try assumption.
        - destruct (lv_app true above (f :: fs') (S p) Ld) as [b' [Lb Lle]].
          cbn [lv] in Lb. rewrite Hk in Lb. cbn [Bool.eqb] in Lb.
          apply (lv_mono _ _ _ _ Lb). lia.
        - destruct (lv_app false above (f :: fs') (S b) Lh) as [b' [Lb Lle]].
          cbn [lv] in Lb. rewrite Hk in Lb. cbn [Bool.eqb] in Lb. destruct Lb as [_ Lb].
          apply (lv_mono _ _ _ _ Lb). lia.
        - laws. exact Ef. }
      { exact Qf. }
      split; [exact L1|]. split; [exact L2|].
      destruct fs' as [|g fs'']; [exact I|]. cbn [null] in *. laws.
      rewrite tval_push, tval_of in E3. rewrite append_assoc in E3. exact E3.
  - (* nothing closes *)
    cbn [orb]. subst dtop htop.
    pose proof (quiet_all fs p b esc c Ld Lh Cd Ch) as Q.
    split.
    + match goal with
      | |- wrap (s_parens ?x) _ _ _ _ _ = _ =>
          change (wrap (s_parens x) (s_braces x) (s_esc x) (s_frames x)
                    (tval (s_seg x)) (map_text (s_cur x))) with (sabs x)
      end.
      rewrite speel_sabs, wrap_step by assumption. rewrite istep_at_map.
      destruct fs as [|f fs]; [reflexivity|]. cbn [null]. laws. reflexivity.
    + apply speel_swf. apply wf_quiet; [exact W|exact Q].
Qed.

(*
The break and the finish
========================
*)

Lemma wrap_break : forall a p b esc fs pay inner,
  esc_ok esc fs pay ->
  ibreak_at a (wrap p b esc fs pay inner) = wrap p b false fs (pay ++ nl) (ibreak_at a inner).
Proof.
  induction fs as [|f fs IH]; intros pay inner He; [reflexivity|].
  destruct He as [He1 He2]. cbn [wrap]. rewrite IH by exact He2.
  rewrite append_assoc. f_equal.
  destruct (cf_kind f) as [kids image open o|txt o]; cbn [mkframe ibreak_at]; tred;
    [|reflexivity].
  unfold ddecode. rewrite ddecode_from_app. fold (ddecode pay). rewrite He1.
  destruct esc; reflexivity.
Qed.

Theorem sbreak_at_spec : forall a s, swf s ->
  sabs (sbreak_at a s) = ibreak_at a (sabs s) /\ swf (sbreak_at a s).
Proof.
  intros a [fs dtop htop p b esc seg cur] W.
  destruct W as (Hs & Hd & Hh & Ld & Lh & He).
  cbn [s_frames s_dtop s_htop s_parens s_braces s_esc s_seg s_cur] in *.
  unfold sbreak_at, sabs. cbn [s_frames s_parens s_braces s_esc s_seg s_cur].
  split.
  - rewrite wrap_break by exact He. rewrite ibreak_at_map.
    destruct fs; [reflexivity|]. cbn [null]. laws. reflexivity.
  - repeat split; try assumption. cbn [s_esc s_seg s_frames].
    destruct fs as [|f fs]; [exact I|]. cbn [null]. laws.
    clear -He. revert He. generalize (tval seg). generalize (f :: fs). clear.
    induction l as [|g l IH]; intros pay Hl; [exact I|]. destruct Hl as [H1 H2].
    split; [rewrite esc_after_app, H1; destruct esc; reflexivity|].
    rewrite <- append_assoc. apply IH. exact H2.
Qed.

Lemma wrap_finish : forall p b esc fs pay inner,
  ifinish_ostate (wrap p b esc fs pay inner) = ifinish_ostate inner.
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
  unfold sabs, sstart, slift. cbn [s_frames s_cur s_seg s_parens s_braces s_esc wrap].
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
