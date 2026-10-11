(* ai-disclosure: autonomous *)

(* The grammar of `PrecedenceGrammar.v` against the readings of
   `Precedence.v`: a paragraph has exactly one parse, its valid reading.

   Both directions go through `ref_read`, the stack machine that computes
   the reading.  A derivation is followed by the machine, rule by rule.
   A run of the machine is a derivation being built: each opener on the
   stack heads a level whose tokens so far are settled, and whether the
   opener is left unmatched (R3) or pairs (R4 to R7) is decided when a
   closer takes it or the paragraph ends. *)

From Stdlib Require Import String Ascii List Bool Lia Arith.
From DjotV Require Import Strings InlineTable Precedence PrecedenceFacts PrecedenceGrammar.
Import ListNotations.

Section WithTable.
Context {T : dtable}.

(*
The machine, run to its end
===========================
*)

Definition run (s : string) (p : nat) (st : rstate) : rstate :=
  rgo s (S (String.length s - p)) p st.

Local Lemma rgo_fuel : forall s f f' p st,
  String.length s - p < f -> String.length s - p < f' -> rgo s f p st = rgo s f' p st.
Proof.
  intros s f. induction f as [|f IH]; intros f' p st H H'; [lia|].
  destruct f' as [|f']; [lia|]. cbn [rgo].
  destruct (tok_of s p) as [t|]; [|reflexivity].
  destruct (chain_next s (rs_pairs (rstep s p t st)) p) as [q|] eqn:Hq; [|reflexivity].
  pose proof (chain_next_bound s _ p q Hq). apply IH; lia.
Qed.

Local Lemma run_step : forall s p t l st q,
  tok_at s p = Some (t, l) -> chain_next s (rs_pairs (rstep s p t st)) p = Some q ->
  run s p st = run s q (rstep s p t st).
Proof.
  intros s p t l st q Ht Hq. unfold run.
  pose proof (chain_next_bound s _ p q Hq).
  replace (rgo s (S (String.length s - p)) p st)
    with (rgo s (String.length s - p) q (rstep s p t st)).
  - apply rgo_fuel; lia.
  - cbn [rgo]. unfold tok_of. rewrite Ht. cbn [option_map fst]. rewrite Hq. reflexivity.
Qed.

Local Lemma run_last : forall s p t l st,
  tok_at s p = Some (t, l) -> chain_next s (rs_pairs (rstep s p t st)) p = None ->
  run s p st = rstep s p t st.
Proof.
  intros s p t l st Ht Hq. unfold run. cbn [rgo]. unfold tok_of. rewrite Ht.
  cbn [option_map fst]. rewrite Hq. reflexivity.
Qed.

Local Lemma run_end : forall s p st, tok_at s p = None -> run s p st = st.
Proof.
  intros s p st Ht. unfold run. cbn [rgo]. unfold tok_of. rewrite Ht. reflexivity.
Qed.

Local Lemma sdrop_all : forall s, sdrop (String.length s) s = EmptyString.
Proof. induction s as [|c s IH]; [reflexivity|exact IH]. Qed.

Local Lemma tok_at_length : forall s, tok_at s (String.length s) = None.
Proof. intros s. unfold tok_at. rewrite sdrop_all. reflexivity. Qed.

Local Lemma tok_end_at : forall s p t l, tok_at s p = Some (t, l) -> tok_end s p = p + l.
Proof. intros s p t l H. unfold tok_end. rewrite H. reflexivity. Qed.

(*
The stack, as the grammar's parameters
======================================

`L` is the keys above every marker and `B` the keys below one. *)

Fixpoint live_keys (lv : list litem) : list key :=
  match lv with
  | LOpen _ k :: rest => k :: live_keys rest
  | _ => []
  end.

Fixpoint barred_keys (lv : list litem) : list key :=
  match lv with
  | [] => []
  | LOpen _ _ :: rest => barred_keys rest
  | LBar _ :: rest => live_keys rest ++ barred_keys rest
  end.

Local Lemma has_key_keys : forall k lv,
  has_key k lv = true <-> In k (live_keys lv ++ barred_keys lv).
Proof.
  intros k. induction lv as [|[x k'|d] lv IH]; cbn [has_key live_keys barred_keys app].
  - split; [discriminate|intros []].
  - rewrite orb_true_iff, key_eq_iff, IH. cbn [In].
    split; (intros [E|H]; [left; symmetry; exact E|right; exact H]).
  - exact IH.
Qed.

Local Lemma pick_cases : forall k lv,
  match pick k lv with
  | PFound _ _ => In k (live_keys lv)
  | PBarred => ~ In k (live_keys lv) /\ In k (barred_keys lv)
  | PNone => ~ In k (live_keys lv) /\ ~ In k (barred_keys lv)
  end.
Proof.
  intros k. induction lv as [|[x k'|d] lv IH]; cbn [pick live_keys barred_keys].
  - split; intros [].
  - destruct (key_eq k k') eqn:E.
    + apply key_eq_iff in E. left. symmetry. exact E.
    + assert (N : k' <> k) by (intros ->; rewrite key_eq_refl in E; discriminate).
      destruct (pick k lv); [right; exact IH| |];
        (split; [intros [H|H]; [exact (N H)|exact (proj1 IH H)]|exact (proj2 IH)]).
  - destruct (has_key k lv) eqn:E.
    + split; [intros []|apply has_key_keys, E].
    + split; [intros []|]. intros H. apply has_key_keys in H. congruence.
Qed.

Local Lemma pick_in : forall k lv x below,
  pick k lv = PFound x below -> In (LOpen x k) lv.
Proof.
  intros k. induction lv as [|[y k'|d] lv IH]; intros x below H; cbn [pick] in H.
  - discriminate.
  - destruct (key_eq k k') eqn:E.
    + apply key_eq_iff in E. injection H as <- _. left. rewrite E. reflexivity.
    + right. exact (IH x below H).
  - destruct (has_key k lv); discriminate.
Qed.

(* The opener right before `p`, if `pv` names one. *)
Definition adjacent (s : string) (lv : list litem) (p : nat) (pv : option key) : Prop :=
  forall k, pv = Some k -> exists x rest, lv = LOpen x k :: rest /\ tok_end s x = p.

(*
A step of the machine, by the rule that reads the token
=======================================================
*)

Local Lemma rstep_text : forall s p t st pv,
  adjacent s (rs_live st) p pv ->
  (opens_as t = None /\ free (live_keys (rs_live st)) pv (barred_keys (rs_live st)) t)
  \/ barred_tok (live_keys (rs_live st)) (barred_keys (rs_live st)) t ->
  rstep s p t st = st.
Proof.
  intros s p t [lv m os] pv Ha H. cbn [rs_live] in *.
  destruct t as [c| |k mr op cl|im|b|c|ws|ws|pre n body cl raw|k|src ok|a|b a|b a|l|n|n];
    try reflexivity.
  - cbn [rstep rs_live]. destruct cl.
    + pose proof (pick_cases (KDelim k mr) lv) as P.
      destruct (pick (KDelim k mr) lv) as [x below| |] eqn:E.
      * destruct H as [[Ho Hf]|(k' & Hc & Hn & _)].
        -- destruct (Hf _ eq_refl) as [(_ & _ & Hpv)|[Hn _]]; [|contradiction].
           destruct (Ha _ Hpv) as (x' & rest & -> & He). cbn [pick] in E.
           rewrite key_eq_refl in E. injection E as <- <-.
           rewrite He, Nat.ltb_irrefl. destruct op; [discriminate Ho|reflexivity].
        -- cbn [closes_as] in Hc. injection Hc as <-. contradiction.
      * reflexivity.
      * destruct H as [[Ho Hf]|(k' & Hc & Hn & Hb)].
        -- destruct op; [discriminate Ho|reflexivity].
        -- cbn [closes_as] in Hc. injection Hc as <-. destruct P as [_ P]. contradiction.
    + destruct H as [[Ho _]|(k' & Hc & _)]; [|discriminate Hc].
      destruct op; [discriminate Ho|reflexivity].
  - destruct H as [[Ho _]|(k' & Hc & _)]; [discriminate Ho|discriminate Hc].
  - cbn [rstep rs_live]. pose proof (pick_cases KBracket lv) as P.
    destruct (pick KBracket lv) as [x below| |]; [|reflexivity|reflexivity].
    destruct H as [[_ Hf]|(k' & Hc & Hn & _)].
    + destruct (Hf _ eq_refl) as [(_ & Hn & _)|[Hn _]]; [discriminate Hn|contradiction].
    + cbn [closes_as] in Hc. injection Hc as <-. contradiction.
  - cbn [rstep rs_live]. pose proof (pick_cases KBracket lv) as P.
    destruct (pick KBracket lv) as [x below| |]; [|reflexivity|reflexivity].
    destruct H as [[_ Hf]|(k' & Hc & Hn & _)].
    + destruct (Hf _ eq_refl) as [(_ & Hn & _)|[Hn _]]; [discriminate Hn|contradiction].
    + cbn [closes_as] in Hc. injection Hc as <-. contradiction.
Qed.

Local Lemma rstep_open : forall s p t st pv k,
  adjacent s (rs_live st) p pv -> opens_as t = Some k ->
  free (live_keys (rs_live st)) pv (barred_keys (rs_live st)) t ->
  rstep s p t st = RState (LOpen p k :: rs_live st) (rs_pairs st) (p :: rs_os st).
Proof.
  intros s p t [lv m os] pv k Ha Ho Hf. cbn [rs_live rs_pairs rs_os] in *.
  destruct t as [c| |k0 mr op cl|im|b|c|ws|ws|pre n body cl raw|k0|src ok|a|b a|b a|l|n|n];
    try discriminate Ho.
  - destruct op; [|discriminate Ho]. cbn [opens_as] in Ho. injection Ho as <-.
    cbn [rstep rs_live]. destruct cl; [|reflexivity].
    pose proof (pick_cases (KDelim k0 mr) lv) as P.
    destruct (pick (KDelim k0 mr) lv) as [x below| |] eqn:E.
    + destruct (Hf _ eq_refl) as [(_ & _ & Hpv)|[Hn _]]; [|contradiction].
      destruct (Ha _ Hpv) as (x' & rest & -> & He). cbn [pick] in E.
      rewrite key_eq_refl in E. injection E as <- <-.
      rewrite He, Nat.ltb_irrefl. reflexivity.
    + destruct P as [Pn Pb]. destruct (Hf _ eq_refl) as [(Hl & _)|[_ Hb]]; contradiction.
    + reflexivity.
  - cbn [opens_as] in Ho. injection Ho as <-. reflexivity.
Qed.

Local Lemma rstep_close : forall s e tc st k x below,
  closes_as tc = Some k -> pick k (rs_live st) = PFound x below ->
  (needs_content k = true -> tok_end s x < e) ->
  rstep s e tc st
  = RState (match tc with
            | TClose true =>
                match region_end s e true with None => LBar e :: below | Some _ => below end
            | _ => below
            end) ((x, e) :: rs_pairs st) (rs_os st).
Proof.
  intros s e tc [lv m os] k x below Hc P Hn. cbn [rs_live rs_pairs rs_os] in *.
  destruct tc as [c| |k0 mr op cl|im|b|c|ws|ws|pre n body cl raw|k0|src ok|a|b a|b a|l|n|n];
    try discriminate Hc.
  - destruct cl; [|discriminate Hc]. cbn [closes_as] in Hc. injection Hc as <-.
    cbn [rstep rs_live rs_pairs rs_os]. rewrite P.
    specialize (Hn eq_refl). apply Nat.ltb_lt in Hn. rewrite Hn. reflexivity.
  - cbn [closes_as] in Hc. injection Hc as <-. cbn [rstep rs_live rs_pairs rs_os]. rewrite P.
    destruct b; destruct (region_end s e _); reflexivity.
  - cbn [closes_as] in Hc. injection Hc as <-. cbn [rstep rs_live rs_pairs rs_os]. rewrite P.
    reflexivity.
Qed.

(* The chain after a token that does not pair, and after one that does. *)
Local Lemma chain_keep : forall s m p t l,
  tok_at s p = Some (t, l) -> (forall i j, In (i, j) m -> j < p) ->
  chain_next s m p = Some (p + l).
Proof.
  intros s m p t l Ht J. unfold chain_next. rewrite Ht.
  assert (C : is_closer m p = false).
  { destruct (is_closer m p) eqn:E; [|reflexivity].
    apply is_closer_iff in E as [i Hi]. specialize (J i p Hi). lia. }
  destruct t; rewrite ?C; reflexivity.
Qed.

Local Lemma is_closer_head : forall x e m, is_closer ((x, e) :: m) e = true.
Proof. intros x e m. cbn [is_closer existsb snd]. rewrite Nat.eqb_refl. reflexivity. Qed.

Local Lemma chain_past : forall s m x e tc le k q,
  tok_at s e = Some (tc, le) -> closes_as tc = Some k -> past s e tc le = Some q ->
  chain_next s ((x, e) :: m) e = Some q.
Proof.
  intros s m x e tc le k q Ht Hc Hp. unfold chain_next. rewrite Ht, is_closer_head.
  destruct tc; try discriminate Hc; try exact Hp.
  cbn [past] in Hp. unfold resume. destruct (region_end s e dest); [exact Hp|discriminate Hp].
Qed.

Local Lemma past_gt : forall s e tc le q,
  tok_at s e = Some (tc, le) -> past s e tc le = Some q -> e < q.
Proof.
  intros s e tc le q Ht Hp. pose proof (tok_at_len s e tc le Ht) as [Hl _].
  destruct tc; cbn [past] in Hp; try (injection Hp as <-; lia).
  destruct (region_end s e dest) as [z|] eqn:R; [|discriminate Hp].
  injection Hp as <-. pose proof (region_end_bound s e dest z R). lia.
Qed.

(* A pair that a level goes on after leaves the stack below its opener. *)
Local Lemma past_below : forall s e tc le q below,
  past s e tc le = Some q ->
  match tc with
  | TClose true =>
      match region_end s e true with None => LBar e :: below | Some _ => below end
  | _ => below
  end = below.
Proof.
  intros s e tc le q below Hp. destruct tc; try reflexivity.
  destruct dest; [|reflexivity]. cbn [past] in Hp.
  destruct (region_end s e true); [reflexivity|discriminate Hp].
Qed.

Local Lemma past_none : forall s e tc le k,
  closes_as tc = Some k -> past s e tc le = None ->
  exists b, tc = TClose b /\ region_end s e b = None.
Proof.
  intros s e tc le k Hc Hp. destruct tc; try discriminate Hc; try discriminate Hp.
  exists dest. split; [reflexivity|]. cbn [past] in Hp.
  destruct (region_end s e dest); [discriminate Hp|reflexivity].
Qed.

(*
A derivation is a run
=====================

The machine follows a level from `p` to where it stops, adding the
level's pairs and openers.  What the level leaves on the stack is not a
closer's to take: an opener left unmatched is not of the kind `F`. *)

Local Lemma seq_run : forall s L F pv B p r, seq s L F pv B p r ->
  forall st, L = live_keys (rs_live st) -> B = barred_keys (rs_live st) ->
    adjacent s (rs_live st) p pv -> (forall i j, In (i, j) (rs_pairs st) -> j < p) ->
    exists lv',
      run s p st
      = run s (snd r) (RState lv' (fst (fst r) ++ rs_pairs st) (snd (fst r) ++ rs_os st))
      /\ (forall i j, In (i, j) (fst (fst r) ++ rs_pairs st) -> j < snd r)
      /\ (forall K tc le, tok_at s (snd r) = Some (tc, le) -> F = Some K ->
            pick K lv' = pick K (rs_live st)).
Proof.
  intros s L F pv B p r D.
  induction D as
    [L F pv B p Ht
    |L pv B p t l k Ht Hc
    |L F pv B p t l r Ht Hx D IH
    |L F pv B p t l k m os e Ht Ho Hf HF D IH
    |L F pv B p t l k m1 os1 e tc le q m2 os2 e2 Ht Ho Hf D1 IH1 Hte Hc Hn Hp D2 IH2
    |L F pv B p t l m1 os1 e le m2 os2 e2 Ht Ho Hf D1 IH1 Hte Hr D2 IH2 He2
    |L F pv B p t l m1 os1 e le Ht Ho Hf D1 IH1 Hte Hr];
    intros [lv m0 os0] EL EB Ha J; cbn [rs_live rs_pairs rs_os fst snd app] in *; subst L B.
  - exists lv. split; [reflexivity|]. split; [exact J|reflexivity].
  - exists lv. split; [reflexivity|]. split; [exact J|reflexivity].
  - pose proof (rstep_text s p t (RState lv m0 os0) pv Ha Hx) as E.
    pose proof (chain_keep s m0 p t l Ht J) as Hq.
    rewrite (run_step s p t l _ (p + l) Ht ltac:(rewrite E; exact Hq)), E.
    apply (IH (RState lv m0 os0)); [reflexivity|reflexivity|intros k0 E0; discriminate E0|].
    intros i j H. specialize (J i j H). lia.
  - pose proof (rstep_open s p t (RState lv m0 os0) pv k Ha Ho Hf) as E.
    cbn [rs_live rs_pairs rs_os] in E.
    pose proof (chain_keep s m0 p t l Ht J) as Hq.
    rewrite (run_step s p t l _ (p + l) Ht ltac:(rewrite E; exact Hq)), E.
    destruct (IH (RState (LOpen p k :: lv) m0 (p :: os0))) as (lv' & Er & J' & Pk);
      [reflexivity|reflexivity| |intros i j H; specialize (J i j H); lia|].
    { intros k0 E0. injection E0 as <-. exists p, lv. split; [reflexivity|].
      exact (tok_end_at s p t l Ht). }
    cbn [rs_live rs_pairs rs_os fst snd] in Er, J', Pk.
    exists lv'. split; [rewrite Er, <- app_assoc; reflexivity|]. split; [exact J'|].
    intros K tc le Hte EF. rewrite (Pk K tc le Hte EF). cbn [pick].
    destruct (key_eq K k) eqn:E0; [|reflexivity].
    apply key_eq_iff in E0. subst K. contradiction.
  - pose proof (rstep_open s p t (RState lv m0 os0) pv k Ha Ho Hf) as E.
    cbn [rs_live rs_pairs rs_os] in E.
    pose proof (chain_keep s m0 p t l Ht J) as Hq.
    rewrite (run_step s p t l _ (p + l) Ht ltac:(rewrite E; exact Hq)), E.
    destruct (IH1 (RState (LOpen p k :: lv) m0 (p :: os0))) as (lv1 & Er1 & J1 & Pk1);
      [reflexivity|reflexivity| |intros i j H; specialize (J i j H); lia|].
    { intros k0 E0. injection E0 as <-. exists p, lv. split; [reflexivity|].
      exact (tok_end_at s p t l Ht). }
    cbn [rs_live rs_pairs rs_os fst snd] in Er1, J1, Pk1.
    specialize (Pk1 k tc le Hte eq_refl). cbn [pick] in Pk1. rewrite key_eq_refl in Pk1.
    pose proof (rstep_close s e tc (RState lv1 (m1 ++ m0) (os1 ++ p :: os0)) k p lv Hc Pk1
                  ltac:(intros H; rewrite (tok_end_at s p t l Ht); exact (Hn H))) as E2.
    cbn [rs_pairs rs_os] in E2. rewrite (past_below s e tc le q lv Hp) in E2.
    pose proof (chain_past s (m1 ++ m0) p e tc le k q Hte Hc Hp) as Hq2.
    pose proof (past_gt s e tc le q Hte Hp) as Hlt.
    rewrite Er1, (run_step s e tc le _ q Hte ltac:(rewrite E2; exact Hq2)), E2.
    destruct (IH2 (RState lv ((p, e) :: m1 ++ m0) (os1 ++ p :: os0))) as (lv2 & Er2 & J2 & Pk2);
      [reflexivity|reflexivity|intros k0 E0; discriminate E0| |].
    { intros i j [H|H]; [injection H as _ <-; exact Hlt|specialize (J1 i j H); lia]. }
    cbn [rs_live rs_pairs rs_os fst snd] in Er2, J2, Pk2.
    exists lv2. split; [|split; [|exact Pk2]].
    + rewrite Er2. rewrite <- !app_assoc. reflexivity.
    + intros i j H. apply (J2 i j). rewrite <- app_assoc in H. exact H.
  - pose proof (rstep_open s p t (RState lv m0 os0) pv KBracket Ha Ho Hf) as E.
    cbn [rs_live rs_pairs rs_os] in E.
    pose proof (chain_keep s m0 p t l Ht J) as Hq.
    rewrite (run_step s p t l _ (p + l) Ht ltac:(rewrite E; exact Hq)), E.
    destruct (IH1 (RState (LOpen p KBracket :: lv) m0 (p :: os0))) as (lv1 & Er1 & J1 & Pk1);
      [reflexivity|reflexivity| |intros i j H; specialize (J i j H); lia|].
    { intros k0 E0. injection E0 as <-. exists p, lv. split; [reflexivity|].
      exact (tok_end_at s p t l Ht). }
    cbn [rs_live rs_pairs rs_os fst snd] in Er1, J1, Pk1.
    specialize (Pk1 KBracket _ le Hte eq_refl). cbn [pick key_eq] in Pk1.
    pose proof (rstep_close s e (TClose true) (RState lv1 (m1 ++ m0) (os1 ++ p :: os0))
                  KBracket p lv eq_refl Pk1 ltac:(discriminate)) as E2.
    cbn [rs_pairs rs_os] in E2. rewrite Hr in E2.
    assert (Hq2 : chain_next s ((p, e) :: m1 ++ m0) e = Some (S e))
      by (unfold chain_next, resume; rewrite Hte, is_closer_head, Hr; reflexivity).
    rewrite Er1, (run_step s e _ le _ (S e) Hte ltac:(rewrite E2; exact Hq2)), E2.
    destruct (IH2 (RState (LBar e :: lv) ((p, e) :: m1 ++ m0) (os1 ++ p :: os0)))
      as (lv2 & Er2 & J2 & _);
      [reflexivity|reflexivity|intros k0 E0; discriminate E0| |].
    { intros i j [H|H]; [injection H as _ <-; lia|specialize (J1 i j H); lia]. }
    cbn [rs_live rs_pairs rs_os fst snd] in Er2, J2.
    exists lv2. split; [|split].
    + rewrite Er2. rewrite <- !app_assoc. reflexivity.
    + intros i j H. apply (J2 i j). rewrite <- app_assoc in H. exact H.
    + intros K tc le' H. rewrite He2 in H. discriminate H.
  - pose proof (rstep_open s p t (RState lv m0 os0) pv KBracket Ha Ho Hf) as E.
    cbn [rs_live rs_pairs rs_os] in E.
    pose proof (chain_keep s m0 p t l Ht J) as Hq.
    rewrite (run_step s p t l _ (p + l) Ht ltac:(rewrite E; exact Hq)), E.
    destruct (IH1 (RState (LOpen p KBracket :: lv) m0 (p :: os0))) as (lv1 & Er1 & J1 & Pk1);
      [reflexivity|reflexivity| |intros i j H; specialize (J i j H); lia|].
    { intros k0 E0. injection E0 as <-. exists p, lv. split; [reflexivity|].
      exact (tok_end_at s p t l Ht). }
    cbn [rs_live rs_pairs rs_os fst snd] in Er1, J1, Pk1.
    specialize (Pk1 KBracket _ le Hte eq_refl). cbn [pick key_eq] in Pk1.
    pose proof (rstep_close s e (TClose false) (RState lv1 (m1 ++ m0) (os1 ++ p :: os0))
                  KBracket p lv eq_refl Pk1 ltac:(discriminate)) as E2.
    cbn [rs_pairs rs_os] in E2.
    assert (Hq2 : chain_next s ((p, e) :: m1 ++ m0) e = None)
      by (unfold chain_next, resume; rewrite Hte, is_closer_head, Hr; reflexivity).
    rewrite Er1, (run_last s e _ le _ Hte ltac:(rewrite E2; exact Hq2)), E2.
    exists lv. split; [|split].
    + rewrite run_end by apply tok_at_length. rewrite <- app_assoc. reflexivity.
    + pose proof (tok_at_len s e _ le Hte) as [Hl Hb].
      intros i j [H|H]; [injection H as _ <-; lia|specialize (J1 i j H); lia].
    + intros K tc le' H. rewrite tok_at_length in H. discriminate H.
Qed.

Lemma parses_read : forall s r, parses s r -> ref_read s = r.
Proof.
  intros s [m os] (e & He & D). cbn [fst snd] in D.
  destruct (seq_run s _ _ _ _ _ _ D rstart eq_refl eq_refl) as (lv' & Er & _).
  - intros k E. discriminate E.
  - intros i j [].
  - cbn [fst snd rstart rs_pairs rs_os] in Er. rewrite !app_nil_r in Er.
    rewrite (run_end s e _ He) in Er. unfold run in Er. rewrite Nat.sub_0_r in Er.
    unfold ref_read. rewrite Er. reflexivity.
Qed.

(*
A run is a derivation
=====================

A stretch is part of a level, read left to right from `p0`, where `pr0`
is the opener right before: its tokens are text or whole pairs, so the
kinds live and barred do not change along it. *)

Definition pvat (p0 : nat) (pr0 : option key) (p : nat) : option key :=
  if Nat.eqb p p0 then pr0 else None.

Inductive stretch (s : string) (L B : list key) (p0 : nat) (pr0 : option key)
  : nat -> matching -> list nat -> Prop :=
  | stretch_nil : stretch s L B p0 pr0 p0 [] []
  | stretch_text : forall p t l m os,
      stretch s L B p0 pr0 p m os -> tok_at s p = Some (t, l) ->
      (opens_as t = None /\ free L (pvat p0 pr0 p) B t) \/ barred_tok L B t ->
      stretch s L B p0 pr0 (p + l) m os
  | stretch_pair : forall p t l k m os m1 os1 e tc le q,
      stretch s L B p0 pr0 p m os -> tok_at s p = Some (t, l) -> opens_as t = Some k ->
      free L (pvat p0 pr0 p) B t ->
      seq s (k :: L) (Some k) (Some k) B (p + l) (m1, os1, e) ->
      tok_at s e = Some (tc, le) -> closes_as tc = Some k ->
      (needs_content k = true -> p + l < e) -> past s e tc le = Some q ->
      stretch s L B p0 pr0 q ((p, e) :: m1 ++ m) (os1 ++ p :: os).

Local Lemma seq_le : forall s L F pv B p r, seq s L F pv B p r -> p <= snd r.
Proof.
  intros s L F pv B p r D.
  induction D as
    [L F pv B p Ht
    |L pv B p t l k Ht Hc
    |L F pv B p t l r Ht Hx D IH
    |L F pv B p t l k m os e Ht Ho Hf HF D IH
    |L F pv B p t l k m1 os1 e tc le q m2 os2 e2 Ht Ho Hf D1 IH1 Hte Hc Hn Hp D2 IH2
    |L F pv B p t l m1 os1 e le m2 os2 e2 Ht Ho Hf D1 IH1 Hte Hr D2 IH2 He2
    |L F pv B p t l m1 os1 e le Ht Ho Hf D1 IH1 Hte Hr]; cbn [snd] in *; try lia.
  - pose proof (past_gt s e tc le q Hte Hp). lia.
  - pose proof (tok_at_len s p t l Ht). lia.
Qed.

Local Lemma stretch_le : forall s L B p0 pr0 p m os, stretch s L B p0 pr0 p m os -> p0 <= p.
Proof.
  intros s L B p0 pr0 p m os H.
  induction H as [|p t l m os H IH Ht Hx|p t l k m os m1 os1 e tc le q H IH Ht Ho Hf D Hte Hc Hn Hp];
    [lia|lia|].
  pose proof (seq_le _ _ _ _ _ _ _ D) as H1. cbn [snd] in H1.
  pose proof (past_gt s e tc le q Hte Hp). lia.
Qed.

Local Lemma pvat_start : forall p0 pr0, pvat p0 pr0 p0 = pr0.
Proof. intros p0 pr0. unfold pvat. rewrite Nat.eqb_refl. reflexivity. Qed.

Local Lemma pvat_past : forall p0 pr0 p, p0 < p -> pvat p0 pr0 p = None.
Proof.
  intros p0 pr0 p H. unfold pvat. destruct (Nat.eqb p p0) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. lia.
Qed.

(* A stretch, then the rest of its level. *)
Local Lemma stretch_seq : forall s L B p0 pr0 p m os, stretch s L B p0 pr0 p m os ->
  forall F m' os' e, seq s L F (pvat p0 pr0 p) B p (m', os', e) ->
    seq s L F pr0 B p0 (m' ++ m, os' ++ os, e).
Proof.
  intros s L B p0 pr0 p m os H.
  induction H as [|p t l m os H IH Ht Hx|p t l k m os m1 os1 e tc le q H IH Ht Ho Hf D Hte Hc Hn Hp];
    intros F m' os' e' D'.
  - rewrite pvat_start in D'. rewrite !app_nil_r. exact D'.
  - pose proof (stretch_le _ _ _ _ _ _ _ _ H) as Hle.
    pose proof (tok_at_len s p t l Ht) as [Hl _].
    rewrite pvat_past in D' by lia.
    apply IH. exact (seq_text s L F _ B p t l _ Ht Hx D').
  - pose proof (stretch_le _ _ _ _ _ _ _ _ H) as Hle.
    pose proof (seq_le _ _ _ _ _ _ _ D) as H1. cbn [snd] in H1.
    pose proof (past_gt s e tc le q Hte Hp) as H2.
    rewrite pvat_past in D' by lia.
    pose proof (seq_pair s L F _ B p t l k m1 os1 e tc le q m' os' e' Ht Ho Hf D Hte Hc Hn Hp D')
      as D2.
    specialize (IH F _ _ _ D2). rewrite <- !app_assoc in IH. exact IH.
Qed.

(* What the stack stands for: under each opener, the level it was read
   in, up to it, and under each marker the bracket pair whose destination
   did not close.  `p0` and `pr0` are where the level on top begins;
   the pairs and openers are those of everything below it. *)
Inductive base (s : string) : list litem -> nat -> option key -> matching -> list nat -> Prop :=
  | base_top : base s [] 0 None [] []
  | base_open : forall rest p0 pr0 m0 os0 x m1 os1 t l k,
      base s rest p0 pr0 m0 os0 ->
      stretch s (live_keys rest) (barred_keys rest) p0 pr0 x m1 os1 ->
      tok_at s x = Some (t, l) -> opens_as t = Some k ->
      free (live_keys rest) (pvat p0 pr0 x) (barred_keys rest) t ->
      base s (LOpen x k :: rest) (x + l) (Some k) (m1 ++ m0) (x :: os1 ++ os0)
  | base_bar : forall rest p0 pr0 m0 os0 x m1 os1 t l mc osc d ld,
      base s rest p0 pr0 m0 os0 ->
      stretch s (live_keys rest) (barred_keys rest) p0 pr0 x m1 os1 ->
      tok_at s x = Some (t, l) -> opens_as t = Some KBracket ->
      free (live_keys rest) (pvat p0 pr0 x) (barred_keys rest) t ->
      seq s (KBracket :: live_keys rest) (Some KBracket) (Some KBracket) (barred_keys rest)
        (x + l) (mc, osc, d) ->
      tok_at s d = Some (TClose true, ld) -> region_end s d true = None ->
      base s (LBar d :: rest) (S d) None ((x, d) :: mc ++ m1 ++ m0) (osc ++ x :: os1 ++ os0).

(* The paragraph ends: every opener left on the stack is unmatched. *)
Local Lemma base_close : forall s lv p0 pr0 m0 os0, base s lv p0 pr0 m0 os0 ->
  forall m os e, seq s (live_keys lv) None pr0 (barred_keys lv) p0 (m, os, e) ->
    tok_at s e = None ->
    seq s [] None None [] 0 (m ++ m0, os ++ os0, e).
Proof.
  intros s lv p0 pr0 m0 os0 H.
  induction H as
    [|rest p0 pr0 m0 os0 x m1 os1 t l k H IH Sr Ht Ho Hf
     |rest p0 pr0 m0 os0 x m1 os1 t l mc osc d ld H IH Sr Ht Ho Hf Dc Htd Hr];
    intros m os e D He; cbn [live_keys barred_keys] in D.
  - rewrite !app_nil_r. exact D.
  - pose proof (seq_open s _ None _ _ x t l k m os e Ht Ho Hf ltac:(discriminate) D) as D1.
    pose proof (stretch_seq _ _ _ _ _ _ _ _ Sr _ _ _ _ D1) as D2.
    specialize (IH _ _ _ D2 He). rewrite <- !app_assoc in IH. exact IH.
  - pose proof (seq_dest s _ None _ _ x t l mc osc d ld m os e Ht Ho Hf Dc Htd Hr D He) as D1.
    pose proof (stretch_seq _ _ _ _ _ _ _ _ Sr _ _ _ _ D1) as D2.
    specialize (IH _ _ _ D2 He). rewrite <- !app_assoc in IH. exact IH.
Qed.

(* A closer takes an opener: the openers above it are left unmatched in
   its content. *)
Local Lemma base_pick : forall s lv p0 pr0 m0 os0, base s lv p0 pr0 m0 os0 ->
  forall K x below m os e, pick K lv = PFound x below ->
    seq s (live_keys lv) (Some K) pr0 (barred_keys lv) p0 (m, os, e) ->
    exists pb prb mb osb m1 os1 t l mc osc,
      base s below pb prb mb osb
      /\ stretch s (live_keys below) (barred_keys below) pb prb x m1 os1
      /\ tok_at s x = Some (t, l) /\ opens_as t = Some K
      /\ free (live_keys below) (pvat pb prb x) (barred_keys below) t
      /\ seq s (K :: live_keys below) (Some K) (Some K) (barred_keys below) (x + l) (mc, osc, e)
      /\ m ++ m0 = mc ++ m1 ++ mb /\ os ++ os0 = osc ++ x :: os1 ++ osb.
Proof.
  intros s lv p0 pr0 m0 os0 H.
  induction H as
    [|rest p0 pr0 m0 os0 x0 m1 os1 t l k H IH Sr Ht Ho Hf
     |rest p0 pr0 m0 os0 x0 m1 os1 t l mc osc d ld H IH Sr Ht Ho Hf Dc Htd Hr];
    intros K x below m os e P D; cbn [pick live_keys barred_keys] in P, D.
  - discriminate P.
  - destruct (key_eq K k) eqn:E.
    + apply key_eq_iff in E. subst k. injection P as <- <-.
      exists p0, pr0, m0, os0, m1, os1, t, l, m, os. repeat split; try assumption.
    + assert (N : Some K <> Some k)
        by (intros E0; injection E0 as ->; rewrite key_eq_refl in E; discriminate).
      pose proof (seq_open s _ (Some K) _ _ x0 t l k m os e Ht Ho Hf N D) as D1.
      pose proof (stretch_seq _ _ _ _ _ _ _ _ Sr _ _ _ _ D1) as D2.
      destruct (IH K x below _ _ e P D2)
        as (pb & prb & mb & osb & m1b & os1b & tb & lb & mc & osc & Bb & Sb & Hx & Hox & Hfx
            & Dc & Em & Eo).
      exists pb, prb, mb, osb, m1b, os1b, tb, lb, mc, osc.
      repeat split; try assumption.
      * rewrite <- Em, <- app_assoc. reflexivity.
      * rewrite <- Eo, <- !app_assoc. reflexivity.
  - destruct (has_key K rest); discriminate P.
Qed.

(* An opener's token ends by where the level on top begins, and only the
   top one's ends there. *)
Local Lemma base_bound : forall s lv p0 pr0 m0 os0, base s lv p0 pr0 m0 os0 ->
  forall y k, In (LOpen y k) lv -> tok_end s y <= p0.
Proof.
  intros s lv p0 pr0 m0 os0 H.
  induction H as
    [|rest p0 pr0 m0 os0 x0 m1 os1 t l k H IH Sr Ht Ho Hf
     |rest p0 pr0 m0 os0 x0 m1 os1 t l mc osc d ld H IH Sr Ht Ho Hf Dc Htd Hr];
    intros y k' Hy.
  - destruct Hy.
  - pose proof (stretch_le _ _ _ _ _ _ _ _ Sr) as Hle.
    destruct Hy as [E|Hy]; [injection E as <- _; rewrite (tok_end_at s x0 t l Ht); lia|].
    specialize (IH y k' Hy). lia.
  - pose proof (stretch_le _ _ _ _ _ _ _ _ Sr) as Hle.
    pose proof (seq_le _ _ _ _ _ _ _ Dc) as H1. cbn [snd] in H1.
    destruct Hy as [E|Hy]; [discriminate E|].
    specialize (IH y k' Hy). lia.
Qed.

Local Lemma base_adj : forall s lv p0 pr0 m0 os0, base s lv p0 pr0 m0 os0 ->
  forall K x below, pick K lv = PFound x below -> p0 <= tok_end s x -> pr0 = Some K.
Proof.
  intros s lv p0 pr0 m0 os0 H K x below P Hx.
  destruct H as
    [|rest p0 pr0 m0 os0 x0 m1 os1 t l k H Sr Ht Ho Hf
     |rest p0 pr0 m0 os0 x0 m1 os1 t l mc osc d ld H Sr Ht Ho Hf Dc Htd Hr];
    cbn [pick] in P.
  - discriminate P.
  - destruct (key_eq K k) eqn:E; [apply key_eq_iff in E; rewrite E; reflexivity|].
    pose proof (base_bound _ _ _ _ _ _ H x K (pick_in K rest x below P)) as Hb.
    pose proof (stretch_le _ _ _ _ _ _ _ _ Sr) as Hle.
    pose proof (tok_at_len s x0 t l Ht) as [Hl _]. lia.
  - destruct (has_key K rest); discriminate P.
Qed.

(* A step of the machine, read as a rule. *)
Local Lemma rstep_cases : forall s p t st pv,
  (forall K x below, pick K (rs_live st) = PFound x below -> p <= tok_end s x -> pv = Some K) ->
  (rstep s p t st = st
   /\ ((opens_as t = None /\ free (live_keys (rs_live st)) pv (barred_keys (rs_live st)) t)
       \/ barred_tok (live_keys (rs_live st)) (barred_keys (rs_live st)) t))
  \/ (exists k, rstep s p t st = RState (LOpen p k :: rs_live st) (rs_pairs st) (p :: rs_os st)
        /\ opens_as t = Some k
        /\ free (live_keys (rs_live st)) pv (barred_keys (rs_live st)) t)
  \/ (exists k x below, closes_as t = Some k /\ pick k (rs_live st) = PFound x below
        /\ (needs_content k = true -> tok_end s x < p)).
Proof.
  intros s p t [lv m os] pv Hadj. cbn [rs_live rs_pairs rs_os] in *.
  assert (Plain : closes_as t = None -> opens_as t = None -> rstep s p t (RState lv m os) = RState lv m os ->
                  (rstep s p t (RState lv m os) = RState lv m os
                   /\ ((opens_as t = None /\ free (live_keys lv) pv (barred_keys lv) t)
                       \/ barred_tok (live_keys lv) (barred_keys lv) t))).
  { intros Hc Ho E. split; [exact E|]. left. split; [exact Ho|].
    intros k Hk. rewrite Hc in Hk. discriminate Hk. }
  destruct t as [c| |k mr op cl|im|b|c|ws|ws|pre n body cl raw|k|src ok|a|b a|b a|l|n|n];
    try (left; apply Plain; reflexivity).
  - cbn [rstep rs_live]. destruct cl.
    + pose proof (pick_cases (KDelim k mr) lv) as P.
      destruct (pick (KDelim k mr) lv) as [x below| |] eqn:E.
      * destruct (Nat.ltb (tok_end s x) p) eqn:Hlt.
        -- right. right. exists (KDelim k mr), x, below. split; [reflexivity|].
           split; [exact E|]. intros _. apply Nat.ltb_lt. exact Hlt.
        -- apply Nat.ltb_ge in Hlt.
           assert (Hf : free (live_keys lv) pv (barred_keys lv) (TDelim k mr op true)).
           { intros k' Hc. cbn [closes_as] in Hc. injection Hc as <-. left.
             split; [exact P|]. split; [reflexivity|exact (Hadj _ _ _ E Hlt)]. }
           destruct op; [right; left; exists (KDelim k mr); auto|left; auto].
      * left. split; [reflexivity|]. right. exists (KDelim k mr). destruct P. auto.
      * assert (Hf : free (live_keys lv) pv (barred_keys lv) (TDelim k mr op true)).
        { intros k' Hc. cbn [closes_as] in Hc. injection Hc as <-. right. exact P. }
        destruct op; [right; left; exists (KDelim k mr); auto|left; auto].
    + assert (Hf : free (live_keys lv) pv (barred_keys lv) (TDelim k mr op false))
        by (intros k' Hc; discriminate Hc).
      destruct op; [right; left; exists (KDelim k mr); auto|left; auto].
  - right. left. exists KBracket. split; [reflexivity|]. split; [reflexivity|].
    intros k' Hc. discriminate Hc.
  - cbn [rstep rs_live]. pose proof (pick_cases KBracket lv) as P.
    destruct (pick KBracket lv) as [x below| |] eqn:E.
    + right. right. exists KBracket, x, below. split; [reflexivity|]. split; [exact E|].
      intros H. discriminate H.
    + left. split; [reflexivity|]. right. exists KBracket. destruct P. auto.
    + left. split; [reflexivity|]. left. split; [reflexivity|].
      intros k' Hc. cbn [closes_as] in Hc. injection Hc as <-. right. exact P.
  - cbn [rstep rs_live]. pose proof (pick_cases KBracket lv) as P.
    destruct (pick KBracket lv) as [x below| |] eqn:E.
    + right. right. exists KBracket, x, below. split; [reflexivity|]. split; [exact E|].
      intros H. discriminate H.
    + left. split; [reflexivity|]. right. exists KBracket. destruct P. auto.
    + left. split; [reflexivity|]. left. split; [reflexivity|].
      intros k' Hc. cbn [closes_as] in Hc. injection Hc as <-. right. exact P.
Qed.

(* The machine at `p`: its stack stands for the levels open there, and
   the level on top has been read up to `p`. *)
Definition ginv (s : string) (p : nat) (st : rstate) : Prop :=
  exists p0 pr0 m0 os0 m1 os1,
    base s (rs_live st) p0 pr0 m0 os0
    /\ stretch s (live_keys (rs_live st)) (barred_keys (rs_live st)) p0 pr0 p m1 os1
    /\ rs_pairs st = m1 ++ m0 /\ rs_os st = os1 ++ os0.

Local Lemma ginv_end : forall s p st,
  ginv s p st -> tok_at s p = None -> seq s [] None None [] 0 (rs_pairs st, rs_os st, p).
Proof.
  intros s p st (p0 & pr0 & m0 & os0 & m1 & os1 & Bs & Sr & -> & ->) Ht.
  pose proof (seq_end s (live_keys (rs_live st)) None (pvat p0 pr0 p) (barred_keys (rs_live st))
                p Ht) as D.
  pose proof (stretch_seq _ _ _ _ _ _ _ _ Sr _ _ _ _ D) as D1.
  exact (base_close _ _ _ _ _ _ Bs _ _ _ D1 Ht).
Qed.

Local Lemma ginv_step : forall s p t l st,
  ginv s p st -> (forall i j, In (i, j) (rs_pairs st) -> j < p) -> tok_at s p = Some (t, l) ->
  match chain_next s (rs_pairs (rstep s p t st)) p with
  | Some q =>
      ginv s q (rstep s p t st) /\ (forall i j, In (i, j) (rs_pairs (rstep s p t st)) -> j < q)
  | None =>
      exists e, tok_at s e = None
        /\ seq s [] None None [] 0 (rs_pairs (rstep s p t st), rs_os (rstep s p t st), e)
  end.
Proof.
  intros s p t l [lv m os] (p0 & pr0 & m0 & os0 & m1 & os1 & Bs & Sr & Em & Eo) J Ht.
  cbn [rs_live rs_pairs rs_os] in *. subst m os.
  pose proof (stretch_le _ _ _ _ _ _ _ _ Sr) as Hle.
  pose proof (tok_at_len s p t l Ht) as [Hl _].
  assert (Hadj : forall K x below, pick K lv = PFound x below -> p <= tok_end s x ->
                   pvat p0 pr0 p = Some K).
  { intros K x below P Hx.
    pose proof (base_bound _ _ _ _ _ _ Bs x K (pick_in K lv x below P)) as Hb.
    assert (p = p0) by lia. subst p. rewrite pvat_start.
    exact (base_adj _ _ _ _ _ _ Bs K x below P Hx). }
  destruct (rstep_cases s p t (RState lv (m1 ++ m0) (os1 ++ os0)) _ Hadj)
    as [[E Hx]|[(k & E & Ho & Hf)|(k & x & below & Hc & P & Hn)]];
    cbn [rs_live rs_pairs rs_os] in *.
  - rewrite E. cbn [rs_pairs]. rewrite (chain_keep s _ p t l Ht J).
    split; [|intros i j H; specialize (J i j H); lia].
    exists p0, pr0, m0, os0, m1, os1. cbn [rs_live rs_pairs rs_os].
    split; [exact Bs|]. split; [exact (stretch_text s _ _ p0 pr0 p t l m1 os1 Sr Ht Hx)|].
    split; reflexivity.
  - rewrite E. cbn [rs_pairs]. rewrite (chain_keep s _ p t l Ht J).
    split; [|intros i j H; specialize (J i j H); lia].
    exists (p + l), (Some k), (m1 ++ m0), (p :: os1 ++ os0), [], [].
    cbn [rs_live rs_pairs rs_os live_keys barred_keys].
    split; [exact (base_open s lv p0 pr0 m0 os0 p m1 os1 t l k Bs Sr Ht Ho Hf)|].
    split; [apply stretch_nil|]. split; reflexivity.
  - rewrite (rstep_close s p t (RState lv (m1 ++ m0) (os1 ++ os0)) k x below Hc P Hn). cbn [rs_live rs_pairs rs_os].
    pose proof (seq_stop s (live_keys lv) (pvat p0 pr0 p) (barred_keys lv) p t l k Ht Hc) as D0.
    pose proof (stretch_seq _ _ _ _ _ _ _ _ Sr _ _ _ _ D0) as D1. cbn [app] in D1.
    destruct (base_pick _ _ _ _ _ _ Bs k x below _ _ p P D1)
      as (pb & prb & mb & osb & m1b & os1b & tb & lb & mc & osc & Bb & Sb & Hxt & Hox & Hfx
          & Dc & Emm & Eoo).
    assert (Hn' : needs_content k = true -> x + lb < p)
      by (intros H; rewrite <- (tok_end_at s x tb lb Hxt); exact (Hn H)).
    destruct (past s p t l) as [q|] eqn:Hp.
    + rewrite (past_below s p t l q below Hp), (chain_past s _ x p t l k q Ht Hc Hp).
      pose proof (past_gt s p t l q Ht Hp) as Hlt.
      split; [|intros i j [H|H]; [injection H as _ <-; exact Hlt|specialize (J i j H); lia]].
      exists pb, prb, mb, osb, ((x, p) :: mc ++ m1b), (osc ++ x :: os1b).
      cbn [rs_live rs_pairs rs_os].
      split; [exact Bb|].
      split; [exact (stretch_pair s _ _ pb prb x tb lb k m1b os1b mc osc p t l q
                       Sb Hxt Hox Hfx Dc Ht Hc Hn' Hp)|].
      split; [rewrite Emm; cbn [app]; rewrite <- app_assoc; reflexivity|].
      rewrite Eoo, <- app_assoc. reflexivity.
    + destruct (past_none s p t l k Hc Hp) as (b & -> & Hr).
      cbn [closes_as] in Hc. injection Hc as <-.
      destruct b.
      * rewrite Hr.
        assert (Hq : chain_next s ((x, p) :: m1 ++ m0) p = Some (S p))
          by (unfold chain_next, resume; rewrite Ht, is_closer_head, Hr; reflexivity).
        rewrite Hq.
        split; [|intros i j [H|H]; [injection H as _ <-; lia|specialize (J i j H); lia]].
        exists (S p), None, ((x, p) :: mc ++ m1b ++ mb), (osc ++ x :: os1b ++ osb), [], [].
        cbn [rs_live rs_pairs rs_os live_keys barred_keys].
        split; [exact (base_bar s below pb prb mb osb x m1b os1b tb lb mc osc p l
                         Bb Sb Hxt Hox Hfx Dc Ht Hr)|].
        split; [apply stretch_nil|].
        split; [rewrite Emm; reflexivity|rewrite Eoo; reflexivity].
      * assert (Hq : chain_next s ((x, p) :: m1 ++ m0) p = None)
          by (unfold chain_next, resume; rewrite Ht, is_closer_head, Hr; reflexivity).
        rewrite Hq. exists (String.length s). split; [apply tok_at_length|].
        pose proof (seq_label s _ None _ _ x tb lb mc osc p l Hxt Hox Hfx Dc Ht Hr) as D2.
        pose proof (stretch_seq _ _ _ _ _ _ _ _ Sb _ _ _ _ D2) as D3.
        pose proof (base_close _ _ _ _ _ _ Bb _ _ _ D3 (tok_at_length s)) as D4.
        rewrite Emm, Eoo. rewrite <- !app_assoc in D4. exact D4.
Qed.

Local Lemma rgo_parses : forall s f p st,
  ginv s p st -> (forall i j, In (i, j) (rs_pairs st) -> j < p) -> String.length s - p < f ->
  exists e, tok_at s e = None
    /\ seq s [] None None [] 0 (rs_pairs (rgo s f p st), rs_os (rgo s f p st), e).
Proof.
  intros s f. induction f as [|f IH]; intros p st G J Hf; [lia|].
  cbn [rgo]. unfold tok_of. destruct (tok_at s p) as [[t l]|] eqn:Ht; cbn [option_map fst].
  - pose proof (ginv_step s p t l st G J Ht) as N.
    destruct (chain_next s (rs_pairs (rstep s p t st)) p) as [q|] eqn:Hq; [|exact N].
    destruct N as [G' J']. pose proof (chain_next_bound s _ p q Hq).
    apply IH; [exact G'|exact J'|lia].
  - exists p. split; [exact Ht|exact (ginv_end s p st G Ht)].
Qed.

Lemma read_parses : forall s, parses s (ref_read s).
Proof.
  intros s. unfold parses, ref_read. cbn [fst snd].
  apply rgo_parses; [|intros i j []|lia].
  exists 0, None, [], [], [], []. cbn [rstart rs_live rs_pairs rs_os live_keys barred_keys].
  split; [apply base_top|]. split; [apply stretch_nil|]. split; reflexivity.
Qed.

(*
The theorems
============
*)

(* A paragraph's parses are the reading the machine computes: there is
   one, and no other. *)
Theorem parses_ref_read : forall s r, parses s r <-> r = ref_read s.
Proof.
  intros s r. split.
  - intros H. symmetry. exact (parses_read s r H).
  - intros ->. apply read_parses.
Qed.

(* A parse is a valid reading. *)
Theorem parses_valid : forall s r, parses s r -> valid s r.
Proof. intros s r H. rewrite <- (parses_read s r H). apply ref_read_valid. Qed.

(* The valid reading has a parse: one with its pairs and its openers. *)
Theorem valid_parses : forall s m os,
  valid s (m, os) ->
  exists m' os', parses s (m', os')
    /\ (forall i j, In (i, j) m <-> In (i, j) m') /\ (forall q, In q os <-> In q os').
Proof.
  intros s m os V. destruct (ref_read s) as [m' os'] eqn:E.
  exists m', os'. split; [rewrite <- E; apply read_parses|].
  apply (valid_unique s m os m' os' V). rewrite <- E. apply ref_read_valid.
Qed.

(* The grammar is unambiguous. *)
Theorem parses_unique : forall s r r', parses s r -> parses s r' -> r = r'.
Proof.
  intros s r r' H H'. rewrite <- (parses_read s r H). exact (parses_read s r' H').
Qed.

End WithTable.
