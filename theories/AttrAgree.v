(* ai-disclosure: autonomous *)

(* The attribute machine (`Attributes.v`) accepts exactly the grammar of
   `AttrSyntax.v`, with the attributes the grammar gives.

   - `machine_accepts`: fed a body of the grammar and then `}`, the
     machine is done after the `}`, with `attrs_of` of the body's items,
     and the rest unread.
   - `machine_sound`: a run that ends done has read such a body and `}`.
   - `body_attrs_unique`: so a body has one meaning, however its items are
     read. *)

From Stdlib Require Import String Ascii Bool List Lia.
From DjotV Require Import Strings Ast Attributes AttrSyntax.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope char_scope.

(*
Characters
==========

The grammar's classes are the machine's, byte for byte.
*)

Local Ltac all_bytes c := destruct c as [[] [] [] [] [] [] [] []]; reflexivity.

Local Lemma attr_space_ws : forall c, attr_space c = attr_ws c.
Proof. intros c. all_bytes c. Qed.

Local Lemma key_char_eq : forall c, key_char c = Attributes.is_key_char c.
Proof. intros c. all_bytes c. Qed.

Local Lemma id_char_eq : forall c, id_char c = is_id_char c.
Proof. intros c. all_bytes c. Qed.

Local Lemma escapable_eq : forall c, escapable c = Attributes.is_escapable c.
Proof. intros c. all_bytes c. Qed.

Local Lemma run_char_eq : forall c, AttrSyntax.run_char c = Attributes.collapse_char c.
Proof. intros c. all_bytes c. Qed.

(*
Tokens
======
*)

(* A string pushed onto a reversed token. *)
Local Fixpoint push_str (s : string) (t : list ascii) : list ascii :=
  match s with
  | EmptyString => t
  | String c s' => push_str s' (c :: t)
  end.

Local Lemma rev_chars_push : forall s t,
  rev_chars (push_str s t) = rev_chars t ++ s.
Proof.
  induction s as [|c s IH]; intros t; cbn [push_str].
  - rewrite append_empty_r. reflexivity.
  - rewrite IH. cbn [rev_chars]. rewrite append_assoc. reflexivity.
Qed.

Local Lemma token_push : forall s, rev_chars (push_str s []) = s.
Proof. intros s. rewrite rev_chars_push. reflexivity. Qed.

(*
Runs
====

Each scanning state reads a run of its characters without leaving the
state, pushing them onto its token.
*)

Local Lemma all_cons : forall p c s, all p (String c s) = true ->
  p c = true /\ all p s = true.
Proof. intros p c s H. cbn [all] in H. apply andb_true_iff in H. exact H. Qed.

Local Lemma run_id : forall n r t k a, all id_char n = true ->
  afeed (n ++ r) (AP AId t k a) = afeed r (AP AId (push_str n t) k a).
Proof.
  induction n as [|c n IH]; intros r t k a H; [reflexivity|].
  apply all_cons in H as [Hc H]. cbn [append afeed ap_st push_str].
  unfold astep. cbn [ap_st]. rewrite <- id_char_eq, Hc. apply IH, H.
Qed.

Local Lemma run_class : forall n r t k a, all class_char n = true ->
  afeed (n ++ r) (AP AClass t k a) = afeed r (AP AClass (push_str n t) k a).
Proof.
  induction n as [|c n IH]; intros r t k a H; [reflexivity|].
  apply all_cons in H as [Hc H]. cbn [append afeed ap_st push_str].
  unfold astep. cbn [ap_st]. unfold Attributes.is_attr_class_char.
  unfold class_char in Hc. rewrite <- key_char_eq. unfold key_char. rewrite Hc.
  apply IH, H.
Qed.

Local Lemma run_key : forall n r t k a, all key_char n = true ->
  afeed (n ++ r) (AP AKey t k a) = afeed r (AP AKey (push_str n t) k a).
Proof.
  induction n as [|c n IH]; intros r t k a H; [reflexivity|].
  apply all_cons in H as [Hc H]. cbn [append afeed ap_st push_str].
  unfold astep. cbn [ap_st]. rewrite <- key_char_eq, Hc.
  destruct (Ascii.eqb c "=") eqn:E;
    [apply Ascii.eqb_eq in E; subst c; discriminate|].
  apply IH, H.
Qed.

Local Lemma run_bare : forall n r t k a, all bare_char n = true ->
  afeed (n ++ r) (AP ABare t k a) = afeed r (AP ABare (push_str n t) k a).
Proof.
  induction n as [|c n IH]; intros r t k a H; [reflexivity|].
  apply all_cons in H as [Hc H]. cbn [append afeed ap_st push_str].
  unfold astep. cbn [ap_st]. rewrite <- key_char_eq. unfold key_char. rewrite Hc.
  apply IH, H.
Qed.

Local Lemma run_comment : forall n r k a, all comment_char n = true ->
  afeed (n ++ r) (AP AComment [] k a) = afeed r (AP AComment [] k a).
Proof.
  induction n as [|c n IH]; intros r k a H; [reflexivity|].
  apply all_cons in H as [Hc H]. cbn [append afeed ap_st].
  unfold astep. cbn [ap_st].
  destruct (Ascii.eqb c "%") eqn:E1;
    [apply Ascii.eqb_eq in E1; subst c; discriminate|].
  destruct (Ascii.eqb c "}") eqn:E2;
    [apply Ascii.eqb_eq in E2; subst c; discriminate|].
  apply IH, H.
Qed.

Local Lemma run_quoted : forall q v r t k a, quoted q v ->
  afeed (q ++ r) (AP AQuot t k a) = afeed r (AP AQuot (push_str q t) k a).
Proof.
  intros q v r t k a H. revert r t. induction H as [|c q v Hq Hb H IH|c q v H IH];
    intros r t; [reflexivity| |].
  - cbn [append afeed ap_st push_str]. unfold astep. cbn [ap_st].
    destruct (Ascii.eqb c """") eqn:E1; [apply Ascii.eqb_eq in E1; contradiction|].
    destruct (Ascii.eqb c bslash) eqn:E2; [apply Ascii.eqb_eq in E2; contradiction|].
    unfold Attributes.dquote. rewrite E1. apply IH.
  - cbn [append afeed ap_st push_str]. unfold astep. cbn [ap_st]. apply IH.
Qed.

(*
Values
======

The machine collapses whitespace, then resolves escapes; the grammar
resolves escapes, then collapses.  The two agree because no escapable
character is whitespace and a backslash is neither.
*)

Local Ltac bytes_imp c := destruct c as [[] [] [] [] [] [] [] []]; vm_compute;
  first [intros; reflexivity | intros H; discriminate H].

Local Lemma bare_not_run : forall c, bare_char c = true -> Attributes.collapse_char c = false.
Proof. intros c. bytes_imp c. Qed.

Local Lemma bare_not_bslash : forall c, bare_char c = true -> Ascii.eqb c bslash = false.
Proof. intros c. bytes_imp c. Qed.

Local Lemma run_not_escapable : forall c,
  Attributes.collapse_char c = true -> Attributes.is_escapable c = false.
Proof. intros c. bytes_imp c. Qed.

Local Lemma unescape_cons : forall c s, Ascii.eqb c bslash = false ->
  Attributes.unescape (String c s) = String c (Attributes.unescape s).
Proof. intros c s H. cbn [Attributes.unescape]. rewrite H. reflexivity. Qed.

Local Lemma norm_bare : forall v, all bare_char v = true -> Attributes.norm_value v = v.
Proof.
  intros v H. unfold Attributes.norm_value, Attributes.collapse_ws.
  generalize false. induction v as [|c v IH]; intros b; [reflexivity|].
  apply all_cons in H as [Hc H]. cbn [Attributes.collapse_from].
  rewrite (bare_not_run c Hc), unescape_cons by (apply bare_not_bslash, Hc).
  rewrite IH by exact H. reflexivity.
Qed.

Local Lemma collapse_quoted : forall q v, quoted q v -> forall b,
  Attributes.unescape (Attributes.collapse_from b q) = AttrSyntax.collapse_from b v.
Proof.
  intros q v H. induction H as [|c q v Hq Hb H IH|c q v H IH]; intros b.
  - reflexivity.
  - cbn [Attributes.collapse_from AttrSyntax.collapse_from].
    rewrite run_char_eq.
    assert (Hb' : Ascii.eqb c bslash = false) by (apply Ascii.eqb_neq; exact Hb).
    destruct (Attributes.collapse_char c); [destruct b|].
    + apply IH.
    + rewrite unescape_cons by reflexivity. rewrite IH. reflexivity.
    + rewrite unescape_cons by exact Hb'. rewrite IH. reflexivity.
  - cbn [Attributes.collapse_from].
    replace (Attributes.collapse_char "092") with false by reflexivity. cbn iota.
    unfold escape. rewrite escapable_eq.
    destruct (Attributes.collapse_char c) eqn:Hr.
    + rewrite (run_not_escapable c Hr). cbn [append AttrSyntax.collapse_from].
      replace (AttrSyntax.run_char "092") with false by reflexivity. cbn iota.
      rewrite run_char_eq, Hr.
      cbn [Attributes.unescape]. replace (Ascii.eqb "092" "092") with true by reflexivity. cbn iota.
      replace (Attributes.is_escapable " ") with false by reflexivity. cbn iota.
      replace (Ascii.eqb " " "092") with false by reflexivity. cbn iota.
      rewrite IH. reflexivity.
    + cbn [Attributes.unescape]. replace (Ascii.eqb "092" "092") with true by reflexivity. cbn iota.
      destruct (Attributes.is_escapable c) eqn:He.
      * cbn [append AttrSyntax.collapse_from]. rewrite run_char_eq, Hr, IH. reflexivity.
      * assert (Hc : Ascii.eqb c "092" = false) by (apply Ascii.eqb_neq; intros ->; discriminate).
        unfold bslash. rewrite Hc. replace (Ascii.eqb "092" "092") with true by reflexivity. cbn iota.
        cbn [append AttrSyntax.collapse_from].
        replace (AttrSyntax.run_char "092") with false by reflexivity. cbn iota.
        rewrite run_char_eq, Hr, IH. reflexivity.
Qed.

Local Lemma norm_quoted : forall q v, quoted q v -> Attributes.norm_value q = collapse v.
Proof. intros q v H. apply (collapse_quoted q v H false). Qed.

(*
Items
=====

From between attributes, a closed item returns to between attributes
with the item's attributes added; an open item waits for whitespace,
which does the same, or for `}`, which ends the spec.
*)

Local Notation scan k a := (AP AScan [] k a).
Local Notation done k a := (AP ADone [] k a).

Local Lemma afeed_done : forall r t k a, afeed r (AP ADone t k a) = (AP ADone t k a, r).
Proof. intros [|c r] t k a; reflexivity. Qed.

Local Lemma scan_key : forall c t k a, key_char c = true ->
  astep (AP AScan t k a) c = AP AKey [c] k a.
Proof.
  intros c t k a. destruct c as [[] [] [] [] [] [] [] []]; vm_compute;
    first [intros; reflexivity | intros H; discriminate H].
Qed.

Local Lemma val_bare : forall c t k a, key_char c = true ->
  astep (AP AVal t k a) c = AP ABare [c] k a.
Proof.
  intros c t k a. destruct c as [[] [] [] [] [] [] [] []]; vm_compute;
    first [intros; reflexivity | intros H; discriminate H].
Qed.

Local Lemma ws_not_id : forall c, attr_ws c = true -> is_id_char c = false.
Proof. intros c. bytes_imp c. Qed.

Local Lemma ws_not_key : forall c, attr_ws c = true -> Attributes.is_key_char c = false.
Proof. intros c. bytes_imp c. Qed.

Local Lemma ws_not_brace : forall c, attr_ws c = true -> Ascii.eqb c "}" = false.
Proof. intros c. bytes_imp c. Qed.

Local Lemma key_split : forall s, key s -> exists c s', s = String c s' /\
  key_char c = true /\ all key_char s' = true.
Proof.
  intros [|c s'] [Hne H]; [contradiction|]. apply all_cons in H as [Hc H].
  exists c, s'. auto.
Qed.

(* The steps on the bytes with a role. *)
Local Lemma step_scan_close : forall t k a, astep (AP AScan t k a) "}" = AP ADone t k a.
Proof. reflexivity. Qed.
Local Lemma step_scan_hash : forall t k a, astep (AP AScan t k a) "#" = AP AId [] k a.
Proof. reflexivity. Qed.
Local Lemma step_scan_dot : forall t k a, astep (AP AScan t k a) "." = AP AClass [] k a.
Proof. reflexivity. Qed.
Local Lemma step_scan_pct : forall t k a, astep (AP AScan t k a) "%" = AP AComment [] k a.
Proof. reflexivity. Qed.
Local Lemma step_comment_pct : forall t k a, astep (AP AComment t k a) "%" = AP AScan [] k a.
Proof. reflexivity. Qed.
Local Lemma step_comment_close : forall t k a,
  astep (AP AComment t k a) "}" = AP ADone t k a.
Proof. reflexivity. Qed.
Local Lemma step_key_eq : forall t k a,
  astep (AP AKey t k a) "=" = AP AVal [] (rev_chars t) a.
Proof. reflexivity. Qed.
Local Lemma step_val_quote : forall t k a, astep (AP AVal t k a) """" = AP AQuot [] k a.
Proof. reflexivity. Qed.
Local Lemma step_quot_close : forall t k a,
  astep (AP AQuot t k a) """" = AP AScan [] k (Attr.set k (Attributes.norm_value (rev_chars t)) a).
Proof. reflexivity. Qed.
Local Lemma step_id_close : forall t k a, astep (AP AId t k a) "}" =
  AP ADone [] k (if String.eqb (rev_chars t) "" then a else Attr.set "id" (rev_chars t) a).
Proof. reflexivity. Qed.
Local Lemma step_class_close : forall t k a, astep (AP AClass t k a) "}" =
  AP ADone [] k (if String.eqb (rev_chars t) "" then a else Attr.add_class (rev_chars t) a).
Proof. reflexivity. Qed.
Local Lemma step_bare_close : forall t k a, astep (AP ABare t k a) "}" =
  AP ADone [] k (Attr.set k (Attributes.norm_value (rev_chars t)) a).
Proof. reflexivity. Qed.

Local Lemma step_id_ws : forall c t k a, attr_ws c = true -> astep (AP AId t k a) c =
  AP AScan [] k (if String.eqb (rev_chars t) "" then a else Attr.set "id" (rev_chars t) a).
Proof.
  intros c t k a Hc. unfold astep. cbn [ap_st].
  rewrite (ws_not_id c Hc), (ws_not_brace c Hc), Hc. reflexivity.
Qed.
Local Lemma step_class_ws : forall c t k a, attr_ws c = true -> astep (AP AClass t k a) c =
  AP AScan [] k (if String.eqb (rev_chars t) "" then a else Attr.add_class (rev_chars t) a).
Proof.
  intros c t k a Hc. unfold astep. cbn [ap_st]. unfold Attributes.is_attr_class_char.
  rewrite (ws_not_key c Hc), (ws_not_brace c Hc), Hc. reflexivity.
Qed.
Local Lemma step_bare_ws : forall c t k a, attr_ws c = true -> astep (AP ABare t k a) c =
  AP AScan [] k (Attr.set k (Attributes.norm_value (rev_chars t)) a).
Proof.
  intros c t k a Hc. unfold astep. cbn [ap_st].
  rewrite (ws_not_key c Hc), (ws_not_brace c Hc), Hc. reflexivity.
Qed.
Local Lemma step_scan_ws : forall c t k a, attr_ws c = true ->
  astep (AP AScan t k a) c = AP AScan t k a.
Proof. intros c t k a Hc. unfold astep. cbn [ap_st]. rewrite Hc. reflexivity. Qed.

(* One byte into a live state. *)
Local Lemma afeed_cons : forall c r st t k a, st <> ADone -> st <> AFail ->
  afeed (String c r) (AP st t k a) = afeed r (astep (AP st t k a) c).
Proof. intros c r [] t k a H1 H2; try reflexivity; contradiction. Qed.

Local Ltac feed := rewrite afeed_cons by discriminate.

Local Lemma run_key_eq : forall n r k a, key n ->
  afeed (n ++ String "=" r) (scan k a) = afeed r (AP AVal [] n a).
Proof.
  intros n r k a Hn. destruct (key_split n Hn) as (c & n' & -> & Hc & Hn').
  cbn [append]. feed. rewrite (scan_key c [] k a Hc).
  rewrite run_key by exact Hn'. feed. rewrite step_key_eq, rev_chars_push. reflexivity.
Qed.

Local Lemma closed_run : forall s i, closed_item s i -> forall r k a,
  exists k', afeed (s ++ r) (scan k a) = afeed r (scan k' (add_item a i)).
Proof.
  intros s i H r k0 a. destruct H as [k q v Hk Hq|t Ht].
  - exists k. rewrite !append_assoc. unfold AttrSyntax.dq. cbn [append].
    rewrite run_key_eq by exact Hk. feed. rewrite step_val_quote.
    rewrite (run_quoted q v) by exact Hq. feed.
    rewrite step_quot_close, token_push, (norm_quoted q v Hq). reflexivity.
  - exists k0. rewrite !append_assoc. cbn [append]. feed. rewrite step_scan_pct.
    rewrite run_comment by exact Ht. cbn [append]. feed. rewrite step_comment_pct. reflexivity.
Qed.

(* The state an open item leaves the machine in, before what follows. *)
Local Lemma open_run : forall s i, open_item s i -> forall k a,
  exists x k', (forall r, afeed (s ++ r) (scan k a) = afeed r x) /\
    (forall c r, attr_ws c = true -> afeed (String c r) x = afeed r (scan k' (add_item a i))) /\
    (forall r, afeed (String "}" r) x = (done k' (add_item a i), r)).
Proof.
  intros s i H k a. destruct H as [n Hn|n Hn|k' v Hk Hv Hb].
  - exists (AP AId (push_str n []) k a), k. split; [|split].
    + intros r. cbn [append]. feed. rewrite step_scan_hash. apply run_id, Hn.
    + intros c r Hc. feed. rewrite (step_id_ws c _ _ _ Hc), token_push. reflexivity.
    + intros r. feed. rewrite step_id_close, token_push. apply afeed_done.
  - exists (AP AClass (push_str n []) k a), k. split; [|split].
    + intros r. cbn [append]. feed. rewrite step_scan_dot. apply run_class, Hn.
    + intros c r Hc. feed. rewrite (step_class_ws c _ _ _ Hc), token_push. reflexivity.
    + intros r. feed. rewrite step_class_close, token_push. apply afeed_done.
  - destruct v as [|d v]; [contradiction|].
    assert (Hb' := Hb). apply all_cons in Hb' as [Hd Hv'].
    exists (AP ABare (push_str v [d]) k' a), k'. split; [|split].
    + intros r. rewrite append_assoc. cbn [append].
      rewrite run_key_eq by exact Hk. feed. rewrite (val_bare d [] k' a Hd).
      apply run_bare, Hv'.
    + intros c r Hc. feed. rewrite (step_bare_ws c _ _ _ Hc), rev_chars_push.
      cbn [add_item]. rewrite norm_bare by exact Hb. reflexivity.
    + intros r. feed. rewrite step_bare_close, rev_chars_push.
      cbn [add_item]. rewrite norm_bare by exact Hb. apply afeed_done.
Qed.

(*
Every body is accepted
======================
*)

Local Lemma body_run : forall b is, body b is -> forall k a r,
  exists k', afeed (b ++ String "}" r) (scan k a) = (done k' (fold_left add_item is a), r).
Proof.
  intros b is H. induction H as [|c b is Hc H IH|s i b is Hs H IH|s i Hs
                                 |s i c b is Hs Hc H IH|t Ht]; intros k a r.
  - exists k. cbn [append]. feed. rewrite step_scan_close. apply afeed_done.
  - cbn [append]. feed. rewrite attr_space_ws in Hc. rewrite (step_scan_ws c _ _ _ Hc).
    apply IH.
  - destruct (closed_run s i Hs (b ++ String "}" r) k a) as [k1 E].
    rewrite append_assoc, E. apply IH.
  - destruct (open_run s i Hs k a) as (x & k1 & H1 & _ & H3).
    exists k1. rewrite H1, H3. reflexivity.
  - destruct (open_run s i Hs k a) as (x & k1 & H1 & H2 & _).
    rewrite attr_space_ws in Hc.
    rewrite append_assoc. cbn [append]. rewrite H1, (H2 c _ Hc). apply IH.
  - exists k. rewrite append_assoc. cbn [append]. feed. rewrite step_scan_pct.
    rewrite run_comment by exact Ht. feed. rewrite step_comment_close. apply afeed_done.
Qed.

(* Fed a body and `}`, the machine is done after the `}`, with the body's
   attributes, and has left the rest unread. *)
Theorem machine_accepts : forall b is r, body b is ->
  exists p, afeed (b ++ String "}" r) ap_init = (p, r) /\
    ap_done p = true /\ ap_attrs p = attrs_of is.
Proof.
  intros b is r H. destruct (body_run b is H "" [] r) as [k E].
  exists (done k (attrs_of is)). split; [exact E|split; reflexivity].
Qed.

(*
Inversions
==========

What a scanning state must read to end done: a run of its characters,
then the byte that commits it.
*)

Local Lemma afeed_fail : forall r t k a, afeed r (AP AFail t k a) = (AP AFail t k a, r).
Proof. intros [|c r] t k a; reflexivity. Qed.

Local Lemma afeed_nil_live : forall st t k a p rest,
  afeed EmptyString (AP st t k a) = (p, rest) -> p = AP st t k a.
Proof. intros st t k a p rest H. cbn in H. congruence. Qed.

(* A failed or unfinished run is not done. *)
Local Ltac not_done H Hd :=
  try unfold Attributes.ap_goto in H;
  first [ rewrite afeed_fail in H; injection H as <- _; discriminate Hd
        | apply afeed_nil_live in H; subst; discriminate Hd ].

Local Definition id_add (t : list ascii) (a : attr) : attr :=
  if String.eqb (rev_chars t) "" then a else Attr.set "id" (rev_chars t) a.
Local Definition class_add (t : list ascii) (a : attr) : attr :=
  if String.eqb (rev_chars t) "" then a else Attr.add_class (rev_chars t) a.
Local Definition value_add (t : list ascii) (k : string) (a : attr) : attr :=
  Attr.set k (Attributes.norm_value (rev_chars t)) a.

Local Lemma inv_id : forall s t k a p rest,
  afeed s (AP AId t k a) = (p, rest) -> ap_done p = true ->
  exists n, all id_char n = true /\
    ((s = n ++ String "}" rest /\ p = done k (id_add (push_str n t) a)) \/
     (exists c s', attr_ws c = true /\ s = n ++ String c s' /\
        afeed s' (scan k (id_add (push_str n t) a)) = (p, rest))).
Proof.
  induction s as [|c s IH]; intros t k a p rest H Hd; [not_done H Hd|].
  rewrite afeed_cons in H by discriminate.
  destruct (is_id_char c) eqn:Hi.
  - unfold astep in H. cbn [ap_st] in H. rewrite Hi in H.
    destruct (IH _ _ _ _ _ H Hd) as (n & Hn & HH).
    exists (String c n). split; [cbn [all]; rewrite id_char_eq, Hi, Hn; reflexivity|].
    cbn [ap_key ap_tok ap_attrs] in HH.
    destruct HH as [[-> ->]|(c0 & s' & Hw & -> & Hf)];
      [left; split; reflexivity|right; exists c0, s'; auto].
  - destruct (Ascii.eqb c "}") eqn:Hb.
    + apply Ascii.eqb_eq in Hb. subst c. rewrite step_id_close, afeed_done in H.
      injection H as <- <-. exists EmptyString. split; [reflexivity|left; split; reflexivity].
    + destruct (attr_ws c) eqn:Hw.
      * rewrite (step_id_ws c _ _ _ Hw) in H. exists EmptyString.
        split; [reflexivity|right]. exists c, s. auto.
      * unfold astep in H. cbn [ap_st] in H. rewrite Hi, Hb, Hw in H. not_done H Hd.
Qed.

Local Lemma inv_class : forall s t k a p rest,
  afeed s (AP AClass t k a) = (p, rest) -> ap_done p = true ->
  exists n, all class_char n = true /\
    ((s = n ++ String "}" rest /\ p = done k (class_add (push_str n t) a)) \/
     (exists c s', attr_ws c = true /\ s = n ++ String c s' /\
        afeed s' (scan k (class_add (push_str n t) a)) = (p, rest))).
Proof.
  induction s as [|c s IH]; intros t k a p rest H Hd; [not_done H Hd|].
  rewrite afeed_cons in H by discriminate.
  destruct (Attributes.is_key_char c) eqn:Hi.
  - unfold astep in H. cbn [ap_st] in H. unfold Attributes.is_attr_class_char in H.
    rewrite Hi in H.
    destruct (IH _ _ _ _ _ H Hd) as (n & Hn & HH).
    exists (String c n).
    split; [cbn [all]; rewrite Hn, andb_true_r; unfold class_char; rewrite <- Hi, <- key_char_eq; reflexivity|].
    cbn [ap_key ap_tok ap_attrs] in HH.
    destruct HH as [[-> ->]|(c0 & s' & Hw & -> & Hf)];
      [left; split; reflexivity|right; exists c0, s'; auto].
  - destruct (Ascii.eqb c "}") eqn:Hb.
    + apply Ascii.eqb_eq in Hb. subst c. rewrite step_class_close, afeed_done in H.
      injection H as <- <-. exists EmptyString. split; [reflexivity|left; split; reflexivity].
    + destruct (attr_ws c) eqn:Hw.
      * rewrite (step_class_ws c _ _ _ Hw) in H. exists EmptyString.
        split; [reflexivity|right]. exists c, s. auto.
      * unfold astep in H. cbn [ap_st] in H. unfold Attributes.is_attr_class_char in H.
        rewrite Hi, Hb, Hw in H. not_done H Hd.
Qed.

Local Lemma inv_bare : forall s t k a p rest,
  afeed s (AP ABare t k a) = (p, rest) -> ap_done p = true ->
  exists n, all bare_char n = true /\
    ((s = n ++ String "}" rest /\ p = done k (value_add (push_str n t) k a)) \/
     (exists c s', attr_ws c = true /\ s = n ++ String c s' /\
        afeed s' (scan k (value_add (push_str n t) k a)) = (p, rest))).
Proof.
  induction s as [|c s IH]; intros t k a p rest H Hd; [not_done H Hd|].
  rewrite afeed_cons in H by discriminate.
  destruct (Attributes.is_key_char c) eqn:Hi.
  - unfold astep in H. cbn [ap_st] in H. rewrite Hi in H.
    destruct (IH _ _ _ _ _ H Hd) as (n & Hn & HH).
    exists (String c n).
    split; [cbn [all]; rewrite Hn, andb_true_r; rewrite <- Hi, <- key_char_eq; reflexivity|].
    cbn [ap_key ap_tok ap_attrs] in HH.
    destruct HH as [[-> ->]|(c0 & s' & Hw & -> & Hf)];
      [left; split; reflexivity|right; exists c0, s'; auto].
  - destruct (Ascii.eqb c "}") eqn:Hb.
    + apply Ascii.eqb_eq in Hb. subst c. rewrite step_bare_close, afeed_done in H.
      injection H as <- <-. exists EmptyString. split; [reflexivity|left; split; reflexivity].
    + destruct (attr_ws c) eqn:Hw.
      * rewrite (step_bare_ws c _ _ _ Hw) in H. exists EmptyString.
        split; [reflexivity|right]. exists c, s. auto.
      * unfold astep in H. cbn [ap_st] in H. rewrite Hi, Hb, Hw in H. not_done H Hd.
Qed.

Local Lemma inv_comment : forall s t k a p rest,
  afeed s (AP AComment t k a) = (p, rest) -> ap_done p = true ->
  exists n, all comment_char n = true /\
    ((s = n ++ String "}" rest /\ p = AP ADone t k a) \/
     (exists s', s = n ++ String "%" s' /\ afeed s' (scan k a) = (p, rest))).
Proof.
  induction s as [|c s IH]; intros t k a p rest H Hd; [not_done H Hd|].
  rewrite afeed_cons in H by discriminate.
  destruct (Ascii.eqb c "%") eqn:Hp; [|destruct (Ascii.eqb c "}") eqn:Hb].
  - apply Ascii.eqb_eq in Hp. subst c. rewrite step_comment_pct in H.
    exists EmptyString. split; [reflexivity|right]. exists s. auto.
  - apply Ascii.eqb_eq in Hb. subst c. rewrite step_comment_close, afeed_done in H.
    injection H as <- <-. exists EmptyString. split; [reflexivity|left; split; reflexivity].
  - unfold astep in H. cbn [ap_st] in H. rewrite Hp, Hb in H.
    destruct (IH _ _ _ _ _ H Hd) as (n & Hn & HH).
    exists (String c n).
    split; [cbn [all]; rewrite Hn, andb_true_r; unfold comment_char, AttrSyntax.one_of;
           cbn [list_ascii_of_string existsb]; rewrite Hp, Hb; reflexivity|].
    destruct HH as [[-> ->]|(s' & -> & Hf)];
      [left; split; reflexivity|right; exists s'; auto].
Qed.

Local Lemma inv_key : forall s t k a p rest,
  afeed s (AP AKey t k a) = (p, rest) -> ap_done p = true ->
  exists n s', all key_char n = true /\ s = n ++ String "=" s' /\
    afeed s' (AP AVal [] (rev_chars (push_str n t)) a) = (p, rest).
Proof.
  induction s as [|c s IH]; intros t k a p rest H Hd; [not_done H Hd|].
  rewrite afeed_cons in H by discriminate.
  destruct (Ascii.eqb c "=") eqn:He; [|destruct (Attributes.is_key_char c) eqn:Hi].
  - apply Ascii.eqb_eq in He. subst c. rewrite step_key_eq in H.
    exists EmptyString, s. auto.
  - unfold astep in H. cbn [ap_st] in H. rewrite He, Hi in H.
    destruct (IH _ _ _ _ _ H Hd) as (n & s' & Hn & -> & Hf).
    exists (String c n), s'.
    split; [cbn [all]; rewrite key_char_eq, Hi, Hn; reflexivity|auto].
  - unfold astep in H. cbn [ap_st] in H. rewrite He, Hi in H. not_done H Hd.
Qed.

Local Lemma inv_quot : forall s,
  (forall t k a p rest, afeed s (AP AQuot t k a) = (p, rest) -> ap_done p = true ->
   exists q v s', quoted q v /\ s = q ++ String """" s' /\
     afeed s' (scan k (Attr.set k (Attributes.norm_value (rev_chars t ++ q)) a)) = (p, rest)) /\
  (forall t k a p rest, afeed s (AP AEsc t k a) = (p, rest) -> ap_done p = true ->
   exists c q v s', quoted q v /\ s = String c (q ++ String """" s') /\
     afeed s' (scan k (Attr.set k (Attributes.norm_value (rev_chars t ++ String c q)) a))
       = (p, rest)).
Proof.
  induction s as [|c s [IHq IHe]]; split; intros t k a p rest H Hd; try not_done H Hd.
  - rewrite afeed_cons in H by discriminate.
    destruct (Ascii.eqb c """") eqn:Hq; [|destruct (Ascii.eqb c bslash) eqn:Hb].
    + apply Ascii.eqb_eq in Hq. subst c. rewrite step_quot_close in H.
      exists EmptyString, EmptyString, s. rewrite append_empty_r. split; [constructor|auto].
    + apply Ascii.eqb_eq in Hb. subst c.
      unfold astep in H. cbn [ap_st] in H.
      replace (Ascii.eqb bslash Attributes.dquote) with false in H by reflexivity.
      rewrite Ascii.eqb_refl in H.
      destruct (IHe _ _ _ _ _ H Hd) as (c & q & v & s' & Hqv & -> & Hf).
      exists (String bslash (String c q)), (escape c ++ v), s'.
      split; [constructor; exact Hqv|split; [reflexivity|]].
      unfold ap_push, Attributes.ap_goto in Hf. cbn [ap_key ap_tok ap_attrs rev_chars] in Hf.
      rewrite append_assoc in Hf. exact Hf.
    + unfold astep in H. cbn [ap_st] in H. unfold Attributes.dquote in H. rewrite Hq, Hb in H.
      destruct (IHq _ _ _ _ _ H Hd) as (q & v & s' & Hqv & -> & Hf).
      exists (String c q), (String c v), s'.
      split; [constructor; [apply Ascii.eqb_neq, Hq|apply Ascii.eqb_neq, Hb|exact Hqv]|].
      split; [reflexivity|].
      unfold ap_push, Attributes.ap_goto in Hf. cbn [ap_key ap_tok ap_attrs rev_chars] in Hf.
      rewrite append_assoc in Hf. exact Hf.
  - rewrite afeed_cons in H by discriminate. unfold astep in H. cbn [ap_st] in H.
    destruct (IHq _ _ _ _ _ H Hd) as (q & v & s' & Hqv & -> & Hf).
    exists c, q, v, s'. split; [exact Hqv|split; [reflexivity|]].
    unfold ap_push, Attributes.ap_goto in Hf. cbn [ap_key ap_tok ap_attrs rev_chars] in Hf.
      rewrite append_assoc in Hf. exact Hf.
Qed.

(*
Every accepted run is a body
============================
*)

Local Lemma id_add_item : forall n a, id_add (push_str n []) a = add_item a (IId n).
Proof. intros n a. unfold id_add. rewrite token_push. reflexivity. Qed.

Local Lemma class_add_item : forall n a, class_add (push_str n []) a = add_item a (IClass n).
Proof. intros n a. unfold class_add. rewrite token_push. reflexivity. Qed.

Local Lemma length_lt : forall a c b, String.length b < String.length (a ++ String c b).
Proof. intros a c b. rewrite length_append. cbn [String.length]. lia. Qed.

Local Lemma key_cons : forall c n, key_char c = true -> all key_char n = true ->
  key (String c n).
Proof. intros c n Hc Hn. split; [discriminate|cbn [all]; rewrite Hc, Hn; reflexivity]. Qed.

Local Lemma body_sound : forall m s, String.length s < m -> forall k a p rest,
  afeed s (scan k a) = (p, rest) -> ap_done p = true ->
  exists b is, s = b ++ String "}" rest /\ body b is /\
    ap_attrs p = fold_left add_item is a.
Proof.
  induction m as [|m IH]; intros s Hl k a p rest H Hd; [lia|].
  destruct s as [|c s]; [not_done H Hd|].
  rewrite afeed_cons in H by discriminate. cbn [String.length] in Hl.
  unfold astep in H. cbn [ap_st] in H.
  destruct (attr_ws c) eqn:Hw.
  { destruct (IH s ltac:(lia) k a p rest H Hd) as (b & is & -> & Hb & Ha).
    exists (String c b), is. split; [reflexivity|split; [|exact Ha]].
    apply BSpace; [rewrite attr_space_ws; exact Hw|exact Hb]. }
  destruct (Ascii.eqb c "}") eqn:Hc1.
  { apply Ascii.eqb_eq in Hc1. subst c. unfold Attributes.ap_goto in H.
    rewrite afeed_done in H. injection H as <- <-.
    exists EmptyString, []. split; [reflexivity|split; [constructor|reflexivity]]. }
  destruct (Ascii.eqb c "#") eqn:Hc2.
  { apply Ascii.eqb_eq in Hc2. subst c. unfold ap_begin in H. cbn [ap_key ap_attrs] in H.
    destruct (inv_id _ _ _ _ _ _ H Hd) as (n & Hn & [[-> ->]|(c & s' & Hc & -> & Hf)]).
    - exists (String "#" n), [IId n]. split; [reflexivity|split].
      + apply BLast. exact (OId n Hn).
      + cbn [ap_attrs fold_left]. apply id_add_item.
    - rewrite id_add_item in Hf.
      pose proof (length_lt n c s') as Hlt.
      destruct (IH s' ltac:(lia) _ _ _ _ Hf Hd) as (b & is & -> & Hb & Ha).
      exists (String "#" n ++ String c b), (IId n :: is).
      split; [cbn [append]; rewrite append_assoc; reflexivity|split; [|exact Ha]].
      apply BOpen; [exact (OId n Hn)|rewrite attr_space_ws; exact Hc|exact Hb]. }
  destruct (Ascii.eqb c "%") eqn:Hc3.
  { apply Ascii.eqb_eq in Hc3. subst c. unfold ap_begin in H. cbn [ap_key ap_attrs] in H.
    destruct (inv_comment _ _ _ _ _ _ H Hd) as (n & Hn & [[-> ->]|(s' & -> & Hf)]).
    - exists (String "%" n), [IComment]. split; [reflexivity|split; [|reflexivity]].
      exact (BOpenComment n Hn).
    - pose proof (length_lt n "%" s') as Hlt.
      destruct (IH s' ltac:(lia) _ _ _ _ Hf Hd) as (b & is & -> & Hb & Ha).
      exists (("%" ++ n ++ "%") ++ b), (IComment :: is).
      split; [cbn [append]; rewrite !append_assoc; reflexivity|split; [|exact Ha]].
      apply BClosed; [exact (CComment n Hn)|exact Hb]. }
  destruct (Ascii.eqb c ".") eqn:Hc4.
  { apply Ascii.eqb_eq in Hc4. subst c. unfold ap_begin in H. cbn [ap_key ap_attrs] in H.
    destruct (inv_class _ _ _ _ _ _ H Hd) as (n & Hn & [[-> ->]|(c & s' & Hc & -> & Hf)]).
    - exists (String "." n), [IClass n]. split; [reflexivity|split].
      + apply BLast. exact (OClass n Hn).
      + cbn [ap_attrs fold_left]. apply class_add_item.
    - rewrite class_add_item in Hf.
      pose proof (length_lt n c s') as Hlt.
      destruct (IH s' ltac:(lia) _ _ _ _ Hf Hd) as (b & is & -> & Hb & Ha).
      exists (String "." n ++ String c b), (IClass n :: is).
      split; [cbn [append]; rewrite append_assoc; reflexivity|split; [|exact Ha]].
      apply BOpen; [exact (OClass n Hn)|rewrite attr_space_ws; exact Hc|exact Hb]. }
  destruct (Attributes.is_key_char c) eqn:Hk; [|not_done H Hd].
  unfold ap_begin, ap_push in H. cbn [ap_key ap_attrs ap_tok] in H.
  destruct (inv_key _ _ _ _ _ _ H Hd) as (n & s1 & Hn & -> & H1).
  rewrite rev_chars_push in H1. cbn [rev_chars append] in H1.
  rewrite <- key_char_eq in Hk. pose proof (key_cons c n Hk Hn) as HK.
  set (K := String c n) in *.
  pose proof (length_lt n "=" s1) as Hlt1.
  destruct s1 as [|d s2]; [not_done H1 Hd|].
  rewrite afeed_cons in H1 by discriminate. unfold astep in H1. cbn [ap_st] in H1.
  destruct (Ascii.eqb d Attributes.dquote) eqn:Hq.
  { apply Ascii.eqb_eq in Hq. subst d. unfold ap_begin in H1. cbn [ap_key ap_attrs] in H1.
    destruct (proj1 (inv_quot s2) _ _ _ _ _ H1 Hd) as (q & v & s3 & Hqv & -> & Hf).
    cbn [rev_chars append] in Hf. rewrite (norm_quoted q v Hqv) in Hf.
    assert (Hlt : String.length s3 < m).
    { pose proof (length_lt q """" s3). cbn [String.length] in Hlt1 |- *. lia. }
    destruct (IH s3 Hlt _ _ _ _ Hf Hd) as (b & is & -> & Hb & Ha).
    exists ((K ++ "=" ++ String """" EmptyString ++ q ++ String """" EmptyString) ++ b),
           (IPair K (collapse v) :: is).
    split.
    - subst K. cbn [append]. rewrite !append_assoc.
      f_equal. f_equal. cbn [append]. rewrite append_assoc. reflexivity.
    - split; [|exact Ha]. apply BClosed; [exact (CQuoted K q v HK Hqv)|exact Hb]. }
  destruct (Attributes.is_key_char d) eqn:Hd'; [|not_done H1 Hd].
  unfold ap_begin, ap_push in H1. cbn [ap_key ap_attrs ap_tok] in H1.
  rewrite <- key_char_eq in Hd'.
  destruct (inv_bare _ _ _ _ _ _ H1 Hd) as (v & Hv & [[-> ->]|(c' & s' & Hc & -> & Hf)]).
  - assert (Hdv : all bare_char (String d v) = true)
      by (cbn [all]; unfold key_char in Hd'; rewrite Hd', Hv; reflexivity).
    exists (K ++ "=" ++ String d v), [IPair K (String d v)].
    split; [subst K; cbn [append]; rewrite !append_assoc; reflexivity|split].
    + apply BLast. apply OBare; [exact HK|discriminate|exact Hdv].
    + cbn [ap_attrs fold_left add_item]. unfold value_add.
      rewrite rev_chars_push. cbn [rev_chars append]. rewrite (norm_bare _ Hdv). reflexivity.
  - assert (Hdv : all bare_char (String d v) = true)
      by (cbn [all]; unfold key_char in Hd'; rewrite Hd', Hv; reflexivity).
    unfold value_add in Hf. rewrite rev_chars_push in Hf. cbn [rev_chars append] in Hf.
    rewrite (norm_bare _ Hdv) in Hf.
    assert (Hlt : String.length s' < m).
    { pose proof (length_lt v c' s'). cbn [String.length] in Hlt1 |- *. lia. }
    destruct (IH s' Hlt _ _ _ _ Hf Hd) as (b & is & -> & Hb & Ha).
    exists ((K ++ "=" ++ String d v) ++ String c' b), (IPair K (String d v) :: is).
    split; [subst K; cbn [append]; rewrite !append_assoc; reflexivity|split; [|exact Ha]].
    apply BOpen; [apply OBare; [exact HK|discriminate|exact Hdv]
                 |rewrite attr_space_ws; exact Hc|exact Hb].
Qed.

(* A run that ends done has read a body and its `}`, and holds the body's
   attributes. *)
Theorem machine_sound : forall s p rest,
  afeed s ap_init = (p, rest) -> ap_done p = true ->
  exists b is, s = b ++ String "}" rest /\ body b is /\ ap_attrs p = attrs_of is.
Proof.
  intros s p rest H Hd. exact (body_sound (S (String.length s)) s ltac:(lia) _ _ _ _ H Hd).
Qed.

(*
Unambiguity
===========
*)

(* However a body is split into items, it gives the same attributes. *)
Theorem body_attrs_unique : forall b is1 is2, body b is1 -> body b is2 ->
  attrs_of is1 = attrs_of is2.
Proof.
  intros b is1 is2 H1 H2.
  destruct (machine_accepts b is1 EmptyString H1) as (p1 & E1 & _ & A1).
  destruct (machine_accepts b is2 EmptyString H2) as (p2 & E2 & _ & A2).
  rewrite E1 in E2. injection E2 as ->. congruence.
Qed.

Local Lemma append_same_length : forall a b x y,
  String.length a = String.length b -> a ++ x = b ++ y -> a = b /\ x = y.
Proof.
  induction a as [|c a IH]; intros [|d b] x y Hl H; try discriminate; [auto|].
  cbn in Hl, H. injection H as -> H. injection Hl as Hl.
  destruct (IH b x y Hl H) as [-> ->]. auto.
Qed.

(* A spec ends at one `}`: two bodies that both read a text end at the
   same place. *)
Theorem body_extent_unique : forall b1 b2 is1 is2 r1 r2,
  body b1 is1 -> body b2 is2 ->
  b1 ++ String "}" r1 = b2 ++ String "}" r2 -> b1 = b2 /\ r1 = r2.
Proof.
  intros b1 b2 is1 is2 r1 r2 H1 H2 E.
  destruct (machine_accepts b1 is1 r1 H1) as (p1 & E1 & _).
  destruct (machine_accepts b2 is2 r2 H2) as (p2 & E2 & _).
  rewrite E, E2 in E1. injection E1 as _ <-.
  assert (Hl : String.length b1 = String.length b2).
  { apply (f_equal String.length) in E. rewrite !length_append in E. cbn in E. lia. }
  destruct (append_same_length _ _ _ _ Hl E) as [-> _]. auto.
Qed.

(*
Block attributes
================

A line opens a block attribute spec that closes on it exactly when, past
its indentation, it is `{`, a body, `}` and whitespace.
*)

Local Lemma astep_nl_not_done : forall p, ap_done p = false -> ap_done (astep p "010") = false.
Proof. intros [[] t k a] H; try discriminate; reflexivity. Qed.

Theorem attr_open_closes : forall l b is r,
  drop_leading_ws l = String "{" (b ++ String "}" r) -> body b is -> blank_to_eol r = true ->
  exists p, attr_open l = Some p /\ ap_done p = true /\ ap_attrs p = attrs_of is.
Proof.
  intros l b is r E H Hr. unfold attr_open. rewrite E.
  rewrite append_assoc. cbn [append].
  destruct (machine_accepts b is (r ++ attr_nl) H) as (p & Ep & Hd & Ha).
  rewrite Ep, Hd. exists p.
  assert (Hf : ap_failed p = false)
    by (unfold ap_done in Hd; unfold ap_failed; destruct (ap_st p); congruence).
  rewrite Hf, Attributes.blank_to_eol_app, Hr. auto.
Qed.

Theorem attr_open_closed : forall l p, attr_open l = Some p -> ap_done p = true ->
  exists b is r, drop_leading_ws l = String "{" (b ++ String "}" r) /\ body b is /\
    blank_to_eol r = true /\ ap_attrs p = attrs_of is.
Proof.
  intros l p H Hd.
  destruct (attr_open_inv l p H) as (b0 & r0 & E & Hf & _ & Hb).
  rewrite Attributes.afeed_app in Hf.
  destruct (afeed b0 ap_init) as [p0 r1] eqn:E0. cbn [fst snd] in Hf.
  unfold Attributes.ap_live in Hf.
  destruct (ap_st p0) eqn:Hs.
  all: try (exfalso; cbn [attr_nl afeed] in Hf; rewrite Hs in Hf; injection Hf as <- _;
            assert (Hnd : ap_done p0 = false) by (unfold ap_done; rewrite Hs; reflexivity);
            pose proof (astep_nl_not_done p0 Hnd) as Hn;
            destruct (ap_st (astep p0 "010")) eqn:Hs'; cbn [afeed] in *;
            unfold ap_done in Hd, Hn; congruence).
  all: injection Hf as <- <-.
  - exfalso. unfold ap_done in Hd. rewrite Hs in Hd. discriminate.
  - destruct (machine_sound b0 p0 r1 E0 Hd) as (b & is & -> & Hbody & Ha).
    exists b, is, r1. split; [exact E|split; [exact Hbody|split; [|exact Ha]]].
    specialize (Hb Hd). rewrite Attributes.blank_to_eol_app in Hb.
    apply andb_true_iff in Hb as [Hb _]. exact Hb.
Qed.
