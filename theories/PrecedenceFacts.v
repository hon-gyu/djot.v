(* ai-disclosure: autonomous *)

(* Facts about the readings of `Precedence.v`: at most one is valid, and
   `ref_read` computes it. *)

From Stdlib Require Import String Ascii List Bool Lia Arith Sorted.
From DjotV Require Import Strings Ast Attributes InlineTable InlineView Precedence.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

(*
Uniqueness
==========

At most one reading is valid, so the rules determine it and `valid`, not
`ref_read`, is the specification.  The roles are settled in the
order of the bytes: whether a token is on the chain, closes or opens
reads only the pairs that closed before it and the openers before it. *)

Lemma key_eq_iff : forall a b, key_eq a b = true <-> a = b.
Proof.
  intros [k m|] [k' m'|]; cbn; split; intros H; try discriminate; try reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    destruct k, k'; try discriminate H1; apply Bool.eqb_prop in H2; subst; reflexivity.
  - injection H as -> ->. destruct k'; cbn; apply Bool.eqb_reflx.
Qed.

Lemma key_eq_refl : forall a, key_eq a a = true.
Proof. intros a. apply key_eq_iff. reflexivity. Qed.

Lemma close_key_fun : forall s j k k',
  close_key s j = Some k -> close_key s j = Some k' -> k = k'.
Proof. intros s j k k' H1 H2. rewrite H1 in H2. injection H2 as E. exact E. Qed.

Lemma closest_live_fun : forall s m os j k p q,
  closest_live s m os j k p -> closest_live s m os j k q -> p = q.
Proof.
  intros s m os j k p q [Hp Mp] [Hq Mq].
  specialize (Mp q Hq). specialize (Mq p Hp). lia.
Qed.

Lemma is_opener_iff : forall m i, is_opener m i = true <-> exists j, In (i, j) m.
Proof.
  intros m i. unfold is_opener. rewrite existsb_exists. split.
  - intros ([a b] & Hin & E). apply Nat.eqb_eq in E. cbn in E. subst a.
    exists b. exact Hin.
  - intros [j Hin]. exists (i, j). split; [exact Hin|apply Nat.eqb_refl].
Qed.

Lemma is_closer_iff : forall m j, is_closer m j = true <-> closes m j.
Proof.
  intros m j. unfold is_closer, closes. rewrite existsb_exists. split.
  - intros ([a b] & Hin & E). apply Nat.eqb_eq in E. cbn in E. subst b.
    exists a. exact Hin.
  - intros [i Hin]. exists (i, j). split; [exact Hin|apply Nat.eqb_refl].
Qed.

Lemma closes_dec : forall m j, {closes m j} + {~ closes m j}.
Proof.
  intros m j. destruct (is_closer m j) eqn:D.
  - left. apply is_closer_iff, D.
  - right. intros H. apply is_closer_iff in H. congruence.
Qed.

(* Two readings that agree before `n`. *)
Definition agree (m1 : matching) (os1 : list nat) (m2 : matching) (os2 : list nat)
  (n : nat) : Prop :=
  (forall i j, j < n -> In (i, j) m1 <-> In (i, j) m2)
  /\ (forall q, q < n -> In q os1 <-> In q os2).

Lemma agree_sym : forall m1 os1 m2 os2 n,
  agree m1 os1 m2 os2 n -> agree m2 os2 m1 os1 n.
Proof.
  intros m1 os1 m2 os2 n [Hm Ho]. split.
  - intros i j Hj. symmetry. apply Hm, Hj.
  - intros q Hq. symmetry. apply Ho, Hq.
Qed.

(*
Bounds
------
*)

Lemma length_chars : forall c n, String.length (chars c n) = n.
Proof. intros c n. induction n as [|n IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma prefix_length : forall a s, prefix a s = true -> String.length a <= String.length s.
Proof.
  induction a as [|x a IH]; intros s H; cbn; [lia|].
  destruct s as [|y s]; [discriminate|]. cbn [prefix] in H.
  destruct (ascii_dec x y); [|discriminate]. cbn. specialize (IH s H). lia.
Qed.

Lemma get_lt : forall n s c, get n s = Some c -> n < String.length s.
Proof.
  induction n as [|n IH]; intros [|d s] c H; cbn in *; try discriminate; [lia|].
  specialize (IH s c H). lia.
Qed.

Lemma ws_run_length : forall s, String.length (ws_run s) <= String.length s.
Proof.
  induction s as [|c s IH]; cbn; [lia|]. destruct (is_ws c); cbn; lia.
Qed.

Lemma line_rest_length : forall s, String.length (line_rest s) <= String.length s.
Proof.
  induction s as [|c s IH]; cbn; [lia|]. destruct (Ascii.eqb c nl_char); cbn; lia.
Qed.

Lemma verb_go_len : forall s n run, snd (fst (verb_go n run s)) <= String.length s.
Proof.
  induction s as [|c s IH]; intros n run; cbn [verb_go String.length].
  - destruct (Nat.eqb run n); cbn; lia.
  - destruct (is_tick c).
    + specialize (IH n (S run)). destruct (verb_go n (S run) s) as [[b l] cl]. cbn in *. lia.
    + destruct (Nat.eqb run n); [cbn; lia|].
      specialize (IH n 0). destruct (verb_go n 0 s) as [[b l] cl]. cbn in *. lia.
Qed.

Lemma tick_run_le : forall s, tick_run s <= String.length s.
Proof. induction s as [|c s IH]; cbn; [lia|]. destruct (is_tick c); cbn; lia. Qed.

Lemma fmt_go_len : forall s f, fmt_go s = Some f -> S (String.length f) <= String.length s.
Proof.
  induction s as [|c s IH]; intros f H; [discriminate|]. cbn [fmt_go] in H.
  destruct (Ascii.eqb c rbrace); [injection H as <-; cbn; lia|].
  destruct (raw_stop c || Ascii.eqb c nl_char)%bool; [discriminate|].
  destruct (fmt_go s) as [f'|] eqn:E; [|discriminate]. injection H as <-.
  specialize (IH f' eq_refl). cbn. lia.
Qed.

Lemma raw_spec_len : forall s f, raw_spec s = Some f -> S (S (S (String.length f))) <= String.length s.
Proof.
  intros [|b [|e r]] f H; try discriminate. cbn [raw_spec] in H.
  destruct (Ascii.eqb b lbrace && Ascii.eqb e eqchar)%bool; [|discriminate].
  destruct (fmt_go r) as [[|c f']|] eqn:E; try discriminate. injection H as <-.
  pose proof (fmt_go_len r _ E). cbn in *. lia.
Qed.

Lemma verb_tok_len : forall pre s t l,
  starts_with tick s = true -> verb_tok pre s = (t, l) -> 0 < l <= String.length s.
Proof.
  intros pre s t l Hc H. unfold verb_tok in H.
  pose proof (verb_go_len (sdrop (tick_run s) s) (tick_run s) 0) as G.
  rewrite sdrop_length in G.
  pose proof (tick_run_le s) as Tr.
  assert (Ht : tick_run s <> 0)
    by (destruct s as [|c rest]; [discriminate|]; cbn in Hc |- *; unfold is_tick; rewrite Hc;
        discriminate).
  destruct (verb_go _ 0 _) as [[b u] cl]. cbn [fst snd] in G.
  destruct (if (cl && Nat.eqb pre 0 && raw_inline_enabled)%bool
            then raw_spec (sdrop (tick_run s + u) s) else None) as [f|] eqn:Er.
  - injection H as <- <-.
    destruct (cl && Nat.eqb pre 0 && raw_inline_enabled)%bool; [|discriminate].
    pose proof (raw_spec_len _ _ Er) as Lr. rewrite sdrop_length in Lr. lia.
  - injection H as <- <-. lia.
Qed.

Lemma verb_tok_shape : forall pre s,
  exists n b cl r l, verb_tok pre s = (TVerb pre n b cl r, l).
Proof.
  intros pre s. unfold verb_tok. destruct (verb_go _ _ _) as [[b u] cl].
  destruct (if (cl && Nat.eqb pre 0 && raw_inline_enabled)%bool
            then raw_spec (sdrop (tick_run s + u) s) else None) as [f|];
    do 5 eexists; reflexivity.
Qed.

Lemma dollar_run_le : forall s, dollar_run s <= String.length s.
Proof. induction s as [|c s IH]; cbn; [lia|]. destruct (Ascii.eqb c dollar); cbn; lia. Qed.

Lemma run_of_le : forall c s, run_of c s <= String.length s.
Proof. induction s as [|d s IH]; cbn; [lia|]. destruct (Ascii.eqb d c); cbn; lia. Qed.

Lemma dash_tok_len : forall c rest t l,
  Ascii.eqb c hyphen = true -> dash_tok (String c rest) = (t, l) ->
  0 < l <= S (String.length rest).
Proof.
  intros c rest t l Hc H. unfold dash_tok in H. pose proof (run_of_le hyphen rest) as Le.
  pose proof (sdrop_length (run_of hyphen (String c rest)) (String c rest)) as Ls.
  cbn [run_of String.length] in *. rewrite Hc in *.
  destruct (dstyle_of hyphen) as [k|]; [|injection H as <- <-; lia].
  pose proof (dwidth_nonzero k) as Wn.
  destruct (dwidth k) as [|w]; [destruct (Wn eq_refl)|].
  destruct (starts_with rbrace (sdrop (S (run_of hyphen rest)) (String c rest))
            && Nat.leb (S w) (S (run_of hyphen rest)))%bool eqn:E;
    [|injection H as <- <-; lia].
  apply andb_true_iff in E as [Er Ew]. apply Nat.leb_le in Ew.
  destruct (sdrop (S (run_of hyphen rest)) (String c rest)) as [|d r]; [discriminate Er|].
  cbn [String.length] in Ls.
  destruct (Nat.eqb (S (run_of hyphen rest)) (S w)) eqn:En;
    [|apply Nat.eqb_neq in En]; injection H as <- <-; lia.
Qed.

Lemma dollar_tok_len : forall c rest t l,
  Ascii.eqb c dollar = true -> dollar_tok (String c rest) = (t, l) ->
  0 < l <= S (String.length rest).
Proof.
  intros c rest t l Hc H. unfold dollar_tok in H.
  pose proof (dollar_run_le (String c rest)) as Dr.
  pose proof (sdrop_length (dollar_run (String c rest)) (String c rest)) as Ls.
  cbn [dollar_run String.length] in *. rewrite Hc in *.
  destruct (math_enabled && starts_with tick (sdrop (S (dollar_run rest)) (String c rest)))%bool
    eqn:E.
  - apply andb_true_iff in E as [_ E].
    destruct (verb_tok (S (dollar_run rest)) (sdrop (S (dollar_run rest)) (String c rest)))
      as [t0 l0] eqn:Ev.
    pose proof (verb_tok_len _ _ _ _ E Ev) as L0. injection H as <- <-. lia.
  - injection H as <- <-. lia.
Qed.

Lemma auto_go_len : forall r src stop, auto_go r = (src, stop) ->
  String.length src + (match stop with Some _ => 1 | None => 0 end) <= String.length r.
Proof.
  induction r as [|c r IH]; intros src stop H; cbn [auto_go] in H.
  - injection H as <- <-. reflexivity.
  - destruct (auto_stop c); [injection H as <- <-; cbn; lia|].
    destruct (auto_go r) as [src' stop'] eqn:E. injection H as <- <-.
    specialize (IH _ _ eq_refl). cbn. lia.
Qed.

Lemma auto_tok_len : forall r t l, auto_tok r = (t, l) -> 0 < l <= S (String.length r).
Proof.
  intros r t l H. unfold auto_tok in H. destruct (auto_go r) as [src stop] eqn:E.
  pose proof (auto_go_len r src stop E) as L.
  destruct (match stop with Some c => Ascii.eqb c gt | None => false end
            && auto_body_ok src && auto_kind_ok src)%bool eqn:Ok; injection H as <- <-.
  - destruct stop; [|discriminate]. lia.
  - lia.
Qed.

Lemma auto_tok_shape : forall r,
  (exists src l, auto_tok r = (TAuto src, l)) \/ auto_tok r = (TText lt, 1).
Proof.
  intros r. unfold auto_tok. destruct (auto_go r) as [src stop].
  destruct (_ && _)%bool; [left; eauto|right; reflexivity].
Qed.

Lemma symbol_run_le : forall s, symbol_run s <= String.length s.
Proof. induction s as [|c s IH]; cbn; [lia|]. destruct (symbol_char c); cbn; lia. Qed.

Lemma sym_tok_len : forall r t l, sym_tok r = (t, l) -> 0 < l <= S (String.length r).
Proof.
  intros r t l H. unfold sym_tok in H. pose proof (symbol_run_le r) as Le.
  destruct (Nat.ltb 0 (symbol_run r) && starts_with ":"%char (sdrop (symbol_run r) r))%bool
    eqn:E; injection H as <- <-; [|lia].
  apply andb_true_iff in E as [_ E].
  destruct (sdrop (symbol_run r) r) as [|c r'] eqn:Es; [discriminate|].
  pose proof (sdrop_length (symbol_run r) r) as L. rewrite Es in L. cbn in L. lia.
Qed.

Lemma sym_tok_shape : forall r,
  (exists a l, sym_tok r = (TSymbol a, l)) \/ sym_tok r = (TText ":"%char, 1).
Proof.
  intros r. unfold sym_tok. destruct (_ && _)%bool; [left; eauto|right; reflexivity].
Qed.

(* The machine is done only at a `}`. *)
Lemma astep_done : forall p c,
  ap_done p = false -> ap_done (astep p c) = true -> c = rbrace.
Proof.
  intros p c Hp H. apply Ascii.eqb_eq. unfold ap_done, astep in *.
  destruct p as [st tok key at_]. cbn [ap_st] in *.
  destruct st; try discriminate Hp;
    repeat match type of H with
           | context [if ?b then _ else _] =>
               let E := fresh "E" in destruct b eqn:E; try exact E
           end; cbn in H; try discriminate H.
Qed.

Lemma spec_go_split : forall s p b a,
  ap_done p = false -> spec_go p s = Some (b, a) ->
  exists r, s = (b ++ String rbrace r)%string.
Proof.
  induction s as [|c s IH]; intros p b a Hp H; [discriminate|]. cbn [spec_go] in H.
  destruct (ap_failed (astep p c)); [discriminate|].
  destruct (ap_done (astep p c)) eqn:Ed.
  - injection H as <- _. rewrite (astep_done p c Hp Ed). exists s. reflexivity.
  - destruct (spec_go (astep p c) s) as [[b' a']|] eqn:E; [|discriminate].
    injection H as <- _. destruct (IH _ _ _ Ed E) as [r ->]. exists r. reflexivity.
Qed.

Lemma spec_at_split : forall s b a,
  spec_at s = Some (b, a) -> exists r, s = (b ++ String rbrace r)%string.
Proof.
  intros s b a H. unfold spec_at in H. destruct inline_attrs_enabled; [|discriminate].
  exact (spec_go_split s ap_init b a eq_refl H).
Qed.

Lemma spec_at_len : forall s b a,
  spec_at s = Some (b, a) -> S (String.length b) <= String.length s.
Proof.
  intros s b a H. destruct (spec_at_split s b a H) as [r ->].
  rewrite length_append. cbn [String.length]. lia.
Qed.

Lemma note_go_split : forall s esc l,
  note_go esc s = Some l -> exists r, s = (l ++ String rbrack r)%string.
Proof.
  induction s as [|c s IH]; intros esc l H; [discriminate|]. cbn [note_go] in H.
  assert (K : forall e, option_map (String c) (note_go e s) = Some l ->
              exists r, String c s = (l ++ String rbrack r)%string).
  { intros e He. destruct (note_go e s) as [l'|] eqn:E; [|discriminate]. injection He as <-.
    destruct (IH e l' E) as [r ->]. exists r. reflexivity. }
  destruct esc; [exact (K _ H)|]. destruct (is_bslash c); [exact (K _ H)|].
  destruct (Ascii.eqb c rbrack) eqn:Er; [|exact (K _ H)].
  injection H as <-. apply Ascii.eqb_eq in Er. subst c. exists s. reflexivity.
Qed.

(* A footnote reference's label is right after its `[^`, before a `]`. *)
Lemma note_at_split : forall s l,
  note_at s = Some l -> exists r, s = String hat (l ++ String rbrack r).
Proof.
  intros [|c s] l H; [discriminate|]. cbn [note_at] in H.
  destruct (notes_enabled && Ascii.eqb c hat)%bool eqn:E; [|discriminate].
  apply andb_true_iff in E as [_ E]. apply Ascii.eqb_eq in E. subst c.
  destruct (note_go_split s false l H) as [r ->]. exists r. reflexivity.
Qed.

Lemma next_tok_len : forall prev s t l,
  next_tok prev s = Some (t, l) -> 0 < l <= String.length s.
Proof.
  intros prev s t l H. destruct s as [|c rest] eqn:Es; [discriminate|].
  pose proof dwidth_nonzero as Wn.
  assert (P1 : forall k, prefix (dtoken k) rest = true -> dwidth k <= String.length rest).
  { intros k Hp. apply prefix_length in Hp. unfold dtoken in Hp. rewrite length_chars in Hp.
    exact Hp. }
  assert (P2 : forall k, prefix (dtoken k) s = true -> dwidth k <= String.length s).
  { intros k Hp. apply prefix_length in Hp. unfold dtoken in Hp. rewrite length_chars in Hp.
    exact Hp. }
  assert (G : forall k, at_rbrace (get (dwidth k) s) = true -> dwidth k < String.length s).
  { intros k Hg. unfold at_rbrace in Hg. destruct (get (dwidth k) s) eqn:E; [|discriminate].
    exact (get_lt _ _ _ E). }
  rewrite <- Es in H. unfold next_tok, esc_tok, bang_tok, lbrack_tok, rbrack_tok, lbrace_tok, delim_tok in H. rewrite Es in H at 1.
  injection H as H. rewrite <- Es. subst s. cbn [String.length] in *.
  pose proof (line_rest_length rest). pose proof (ws_run_length rest).
  repeat match type of H with
  | (if ?b then _ else _) = _ => destruct b eqn:?
  | (match ?x with _ => _ end) = _ => destruct x eqn:?
  end;
    try (injection H as <- <-); try lia.
  all: first
    [ match goal with Hw : is_ws ?a = true |- _ =>
        cbn [ws_run] in H1; rewrite Hw in H1 |- *; cbn [String.length] in *; lia end
    | cbn [String.length]; lia
    | match goal with Hp : prefix (dtoken ?k) _ = true |- _ =>
        specialize (P1 k Hp); specialize (Wn k); lia end
    | match goal with Hg : at_rbrace (get (dwidth ?k) _) = true |- _ =>
        specialize (G k Hg); specialize (Wn k); lia end
    | match goal with Hp : prefix (dtoken ?k) _ = true |- _ =>
        specialize (P2 k Hp); specialize (Wn k); lia end
    | match goal with Ht : is_tick ?x = true |- _ =>
        pose proof (verb_tok_len 0 (String x rest) t l Ht H); cbn [String.length] in *; lia end
    | match goal with Hd : Ascii.eqb ?x dollar = true |- _ =>
        exact (dollar_tok_len _ _ t l Hd H) end
    | match goal with Hd : Ascii.eqb ?x period = true |- _ =>
        rewrite Hd; pose proof (run_of_le period rest); lia end
    | match goal with Hd : Ascii.eqb ?x hyphen = true |- _ =>
        exact (dash_tok_len _ _ t l Hd H) end
    | match goal with Hd : Ascii.eqb ?x lt = true |- _ =>
        exact (auto_tok_len _ t l H) end
    | match goal with Hd : Ascii.eqb ?x ":"%char = true |- _ =>
        exact (sym_tok_len _ t l H) end
    | match goal with Hs : spec_at _ = Some _ |- _ =>
        pose proof (spec_at_len _ _ _ Hs); cbn [String.length]; lia end
    | match goal with Hs : starts_with lbrack ?r = true |- _ =>
        destruct r; [discriminate Hs|cbn [String.length]; lia] end
    | match goal with Hs : note_at _ = Some _ |- _ =>
        destruct (note_at_split _ _ Hs) as [? ->]; cbn [String.length];
        rewrite length_append; cbn [String.length]; lia end ].
Qed.

Lemma tok_at_len : forall s p t l,
  tok_at s p = Some (t, l) -> 0 < l /\ p + l <= String.length s.
Proof.
  intros s p t l H. unfold tok_at in H. pose proof (next_tok_len _ _ _ _ H) as Hl.
  rewrite sdrop_length in Hl. lia.
Qed.

Lemma dest_close_bound : forall s esc depth i e,
  dest_close esc depth i s = Some e -> i <= e < i + String.length s.
Proof.
  induction s as [|c s IH]; intros esc depth i e H; [discriminate|].
  cbn [dest_close] in H. cbn [String.length].
  destruct esc; [apply IH in H; lia|].
  destruct (is_bslash c); [apply IH in H; lia|].
  destruct (Ascii.eqb c lparen); [apply IH in H; lia|].
  destruct (Ascii.eqb c rparen); [|apply IH in H; lia].
  destruct depth; [injection H as <-; lia|apply IH in H; lia].
Qed.

Lemma label_close_bound : forall s esc i e,
  label_close esc i s = Some e -> i <= e < i + String.length s.
Proof.
  induction s as [|c s IH]; intros esc i e H; [discriminate|].
  cbn [label_close] in H. cbn [String.length].
  destruct esc; [apply IH in H; lia|].
  destruct (is_bslash c); [apply IH in H; lia|].
  destruct (Ascii.eqb c rbrack); [injection H as <-; lia|apply IH in H; lia].
Qed.

Lemma dest_close_split : forall s esc depth i e,
  dest_close esc depth i s = Some e ->
  exists r, s = (substring 0 (e - i) s ++ String rparen r)%string.
Proof.
  induction s as [|c s IH]; intros esc depth i e H; [discriminate|].
  pose proof (dest_close_bound _ _ _ _ _ H) as B. cbn [dest_close] in H.
  assert (K : forall esc' depth', dest_close esc' depth' (S i) s = Some e ->
              exists r, String c s = (substring 0 (e - i) (String c s) ++ String rparen r)%string).
  { intros esc' depth' He. pose proof (dest_close_bound _ _ _ _ _ He) as B'.
    destruct (IH _ _ _ _ He) as [r Er]. exists r.
    replace (e - i) with (S (e - S i)) by lia. cbn [substring append].
    rewrite <- Er. reflexivity. }
  destruct esc; [exact (K _ _ H)|]. destruct (is_bslash c); [exact (K _ _ H)|].
  destruct (Ascii.eqb c lparen); [exact (K _ _ H)|].
  destruct (Ascii.eqb c rparen) eqn:Er; [|exact (K _ _ H)].
  destruct depth; [|exact (K _ _ H)].
  injection H as <-. apply Ascii.eqb_eq in Er. subst c.
  exists s. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma label_close_split : forall s esc i e,
  label_close esc i s = Some e ->
  exists r, s = (substring 0 (e - i) s ++ String rbrack r)%string.
Proof.
  induction s as [|c s IH]; intros esc i e H; [discriminate|].
  pose proof (label_close_bound _ _ _ _ H) as B. cbn [label_close] in H.
  assert (K : forall esc', label_close esc' (S i) s = Some e ->
              exists r, String c s = (substring 0 (e - i) (String c s) ++ String rbrack r)%string).
  { intros esc' He. pose proof (label_close_bound _ _ _ _ He) as B'.
    destruct (IH _ _ _ He) as [r Er]. exists r.
    replace (e - i) with (S (e - S i)) by lia. cbn [substring append].
    rewrite <- Er. reflexivity. }
  destruct esc; [exact (K _ H)|]. destruct (is_bslash c); [exact (K _ H)|].
  destruct (Ascii.eqb c rbrack) eqn:Er; [|exact (K _ H)].
  injection H as <-. apply Ascii.eqb_eq in Er. subst c.
  exists s. rewrite Nat.sub_diag. reflexivity.
Qed.

(* The byte that opens a region after a `]`, and the byte that closes
   it. *)
Definition region_open (dest : bool) : ascii := if dest then lparen else lbrack.
Definition region_close (dest : bool) : ascii := if dest then rparen else rbrack.

(* A closing `]` is followed by its region: the byte that opens it, its
   bytes, and the byte that closes it. *)
Lemma tok_at_close : forall s p b reg l,
  tok_at s p = Some (TClose b reg, l) ->
  l = 1 /\ exists r, sdrop p s
                     = String rbrack (String (region_open b) (reg ++ String (region_close b) r)).
Proof.
  intros s p b reg l H. unfold tok_at, next_tok, esc_tok, dots_tok, dash_tok, bang_tok, lbrack_tok, rbrack_tok, lbrace_tok, delim_tok, dollar_tok in H.
  destruct (sdrop p s) as [|c rest]; [discriminate|]. injection H as H.
  repeat match type of H with
  | context [sym_tok ?a] =>
      let E := fresh in destruct (sym_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [auto_tok ?a] =>
      let E := fresh in destruct (auto_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [verb_tok ?a ?b] =>
      let E := fresh in destruct (verb_tok_shape a b) as (? & ? & ? & ? & ? & E); rewrite E in H;
      cbn iota beta in H
  | (if ?b then _ else _) = _ => destruct b eqn:?
  | (match ?x with _ => _ end) = _ => destruct x eqn:?
  | context [if ?b then _ else _] => destruct b eqn:?
  | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
  | context [match ?x with EmptyString => _ | String _ _ => _ end] => destruct x eqn:?
  | context [match ?x with pair _ _ => _ end] => destruct x eqn:?
  end; try congruence.
  all: injection H as <- <- <-; split; [reflexivity|].
  all: repeat match goal with E : (?x =? ?y)%char = true |- _ => apply Ascii.eqb_eq in E; subst x end.
  all: first
    [ match goal with E : dest_close _ _ _ _ = Some _ |- _ =>
        destruct (dest_close_split _ _ _ _ _ E) as [r Er] end
    | match goal with E : label_close _ _ _ = Some _ |- _ =>
        destruct (label_close_split _ _ _ _ E) as [r Er] end ];
    exists r; cbn [region_open region_close]; rewrite Nat.sub_0_r in Er; rewrite <- Er; reflexivity.
Qed.

(* A span's closer is the `]`, and its spec is right after it. *)
Lemma tok_at_span : forall s p b a l,
  tok_at s p = Some (TSpan b a, l) ->
  l = 1 /\ exists r, sdrop p s = String rbrack (String lbrace (b ++ String rbrace r)).
Proof.
  intros s p b a l H. unfold tok_at, next_tok, esc_tok, dots_tok, dash_tok, bang_tok, lbrack_tok, rbrack_tok, lbrace_tok, delim_tok, dollar_tok in H.
  destruct (sdrop p s) as [|c rest]; [discriminate|]. injection H as H.
  repeat match type of H with
  | context [sym_tok ?a] =>
      let E := fresh in destruct (sym_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [auto_tok ?a] =>
      let E := fresh in destruct (auto_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [verb_tok ?a ?b] =>
      let E := fresh in destruct (verb_tok_shape a b) as (? & ? & ? & ? & ? & E); rewrite E in H;
      cbn iota beta in H
  | (if ?b then _ else _) = _ => destruct b eqn:?
  | (match ?x with _ => _ end) = _ => destruct x eqn:?
  | context [if ?b then _ else _] => destruct b eqn:?
  | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
  | context [match ?x with EmptyString => _ | String _ _ => _ end] => destruct x eqn:?
  | context [match ?x with pair _ _ => _ end] => destruct x eqn:?
  end; try congruence.
  all: injection H as <- <- <-; split; [reflexivity|];
    repeat match goal with E : (?x =? ?y)%char = true |- _ => apply Ascii.eqb_eq in E; subst x end;
    match goal with E : spec_at _ = Some _ |- _ =>
      destruct (spec_at_split _ _ _ E) as [r ->] end;
    exists r; reflexivity.
Qed.

(* An attribute spec is a `{`, its bytes and the `}`, before a byte that
   is no row's character. *)
Lemma tok_at_attr : forall s p b a l,
  tok_at s p = Some (TAttr b a, l) ->
  l = S (S (String.length b))
  /\ exists d r, sdrop p s = String lbrace (String d r) /\ dstyle_of d = None
                 /\ spec_at (String d r) = Some (b, a).
Proof.
  intros s p b a l H. unfold tok_at, next_tok, esc_tok, dots_tok, dash_tok, bang_tok, lbrack_tok, rbrack_tok, lbrace_tok, delim_tok, dollar_tok in H.
  destruct (sdrop p s) as [|c rest]; [discriminate|]. injection H as H.
  repeat match type of H with
  | context [sym_tok ?a] =>
      let E := fresh in destruct (sym_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [auto_tok ?a] =>
      let E := fresh in destruct (auto_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [verb_tok ?a ?b] =>
      let E := fresh in destruct (verb_tok_shape a b) as (? & ? & ? & ? & ? & E); rewrite E in H;
      cbn iota beta in H
  | (if ?b then _ else _) = _ => destruct b eqn:?
  | (match ?x with _ => _ end) = _ => destruct x eqn:?
  | context [if ?b then _ else _] => destruct b eqn:?
  | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
  | context [match ?x with EmptyString => _ | String _ _ => _ end] => destruct x eqn:?
  | context [match ?x with pair _ _ => _ end] => destruct x eqn:?
  end; try congruence.
  all: injection H as <- <- <-; split; [reflexivity|].
  all: match goal with E : (?x =? lbrace)%char = true |- _ => apply Ascii.eqb_eq in E; subst x end.
  all: match goal with E : spec_at ?rr = Some _, D : match ?rr with _ => _ end = None |- _ =>
         destruct rr as [|d r];
         [unfold spec_at in E; destruct inline_attrs_enabled; discriminate E|exists d, r; auto] end.
Qed.

(* A footnote reference is a `[`, a `^`, its label and the `]`. *)
Lemma tok_at_note : forall s p lab l,
  tok_at s p = Some (TNote lab, l) ->
  l = S (S (S (String.length lab)))
  /\ exists r, notes_enabled = true /\ sdrop p s = String lbrack (String hat r)
               /\ note_go false r = Some lab.
Proof.
  intros s p lab l H. unfold tok_at, next_tok, esc_tok, dots_tok, dash_tok, bang_tok, lbrack_tok, rbrack_tok, lbrace_tok, delim_tok, dollar_tok in H.
  destruct (sdrop p s) as [|c rest]; [discriminate|]. injection H as H.
  repeat match type of H with
  | context [sym_tok ?a] =>
      let E := fresh in destruct (sym_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [auto_tok ?a] =>
      let E := fresh in destruct (auto_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [verb_tok ?a ?b] =>
      let E := fresh in destruct (verb_tok_shape a b) as (? & ? & ? & ? & ? & E); rewrite E in H;
      cbn iota beta in H
  | (if ?b then _ else _) = _ => destruct b eqn:?
  | (match ?x with _ => _ end) = _ => destruct x eqn:?
  | context [if ?b then _ else _] => destruct b eqn:?
  | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
  | context [match ?x with EmptyString => _ | String _ _ => _ end] => destruct x eqn:?
  | context [match ?x with pair _ _ => _ end] => destruct x eqn:?
  end; try congruence.
  all: injection H as <- <-; split; [reflexivity|].
  all: match goal with E : (?x =? lbrack)%char = true |- _ => apply Ascii.eqb_eq in E; subst x end;
    match goal with E : note_at ?rr = Some _ |- _ =>
      destruct rr as [|d r0]; [discriminate E|]; cbn [note_at] in E;
      destruct (notes_enabled && Ascii.eqb d hat)%bool eqn:Eh; [|discriminate E];
      apply andb_true_iff in Eh as [Hen Eh]; apply Ascii.eqb_eq in Eh; subst d;
      exists r0; auto end.
Qed.

Lemma tok_at_dollars : forall s p k l, tok_at s p = Some (TDollars k, l) -> l = k.
Proof.
  intros s p k l H. unfold tok_at, next_tok, esc_tok, dots_tok, dash_tok, bang_tok, lbrack_tok, rbrack_tok, lbrace_tok, delim_tok, dollar_tok in H.
  destruct (sdrop p s) as [|c rest]; [discriminate|]. injection H as H.
  repeat match type of H with
  | context [sym_tok ?a] =>
      let E := fresh in destruct (sym_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [auto_tok ?a] =>
      let E := fresh in destruct (auto_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [verb_tok ?a ?b] =>
      let E := fresh in destruct (verb_tok_shape a b) as (? & ? & ? & ? & ? & E); rewrite E in H;
      cbn iota beta in H
  | (if ?b then _ else _) = _ => destruct b
  | (match ?x with _ => _ end) = _ => destruct x
  | context [if ?b then _ else _] => destruct b
  | context [match ?x with Some _ => _ | None => _ end] => destruct x
  | context [match ?x with EmptyString => _ | String _ _ => _ end] => destruct x
  | context [match ?x with pair _ _ => _ end] => destruct x
  end; congruence.
Qed.

Lemma tok_at_dots : forall s p k l, tok_at s p = Some (TDots k, l) -> l = k.
Proof.
  intros s p k l H. unfold tok_at, next_tok, esc_tok, dots_tok, dash_tok, bang_tok, lbrack_tok, rbrack_tok, lbrace_tok, delim_tok, dollar_tok in H.
  destruct (sdrop p s) as [|c rest]; [discriminate|]. injection H as H.
  repeat match type of H with
  | context [sym_tok ?a] =>
      let E := fresh in destruct (sym_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [auto_tok ?a] =>
      let E := fresh in destruct (auto_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [verb_tok ?a ?b] =>
      let E := fresh in destruct (verb_tok_shape a b) as (? & ? & ? & ? & ? & E); rewrite E in H;
      cbn iota beta in H
  | (if ?b then _ else _) = _ => destruct b
  | (match ?x with _ => _ end) = _ => destruct x
  | context [if ?b then _ else _] => destruct b
  | context [match ?x with Some _ => _ | None => _ end] => destruct x
  | context [match ?x with EmptyString => _ | String _ _ => _ end] => destruct x
  | context [match ?x with pair _ _ => _ end] => destruct x
  end; congruence.
Qed.

Lemma tok_at_dash : forall s p k l, tok_at s p = Some (TDash k, l) -> l = k.
Proof.
  intros s p k l H. unfold tok_at, next_tok, esc_tok, dots_tok, dash_tok, bang_tok, lbrack_tok, rbrack_tok, lbrace_tok, delim_tok, dollar_tok in H.
  destruct (sdrop p s) as [|c rest]; [discriminate|]. injection H as H.
  repeat match type of H with
  | context [sym_tok ?a] =>
      let E := fresh in destruct (sym_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [auto_tok ?a] =>
      let E := fresh in destruct (auto_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [verb_tok ?a ?b] =>
      let E := fresh in destruct (verb_tok_shape a b) as (? & ? & ? & ? & ? & E); rewrite E in H;
      cbn iota beta in H
  | (if ?b then _ else _) = _ => destruct b
  | (match ?x with _ => _ end) = _ => destruct x
  | context [if ?b then _ else _] => destruct b
  | context [match ?x with Some _ => _ | None => _ end] => destruct x
  | context [match ?x with EmptyString => _ | String _ _ => _ end] => destruct x
  | context [match ?x with pair _ _ => _ end] => destruct x
  end; congruence.
Qed.

Lemma chain_next_bound : forall s m p q,
  chain_next s m p = Some q -> p < q <= String.length s.
Proof.
  intros s m p q H. unfold chain_next in H.
  destruct (tok_at s p) as [[t l]|] eqn:E; [|discriminate].
  pose proof (tok_at_len s p t l E) as Hl.
  destruct t; try (injection H as <-; lia).
  - destruct (is_closer m p); [|injection H as <-; lia]. injection H as <-.
    destruct (tok_at_close s p dest region l E) as [_ [r Er]].
    pose proof (sdrop_length p s) as L. rewrite Er in L. cbn [String.length] in L.
    rewrite length_append in L. cbn [String.length] in L. lia.
  - destruct (is_closer m p); [|injection H as <-; lia]. injection H as <-.
    destruct (tok_at_span s p body a l E) as [_ [r Er]].
    pose proof (sdrop_length p s) as L. rewrite Er in L. cbn [String.length] in L.
    rewrite length_append in L. cbn [String.length] in L. lia.
Qed.

(* The chain is one sequence: between two of its points, the next point
   after the first. *)
Lemma chain_between : forall s m a p,
  chain s m p -> chain s m a -> p < a ->
  exists q, chain_next s m p = Some q /\ q <= a.
Proof.
  intros s m a. induction a as [a IH] using lt_wf_ind. intros p Hp Ha Hlt.
  inversion Ha as [E|p' a' Hp' Hn E]; [lia|subst a'].
  pose proof (chain_next_bound s m p' a Hn) as Hb.
  destruct (lt_eq_lt_dec p p') as [[Hl|<-]|Hl].
  - destruct (IH p' ltac:(lia) p Hp Hp' Hl) as (q & Hq & Hqa).
    exists q. split; [exact Hq|lia].
  - exists a. split; [exact Hn|lia].
  - destruct (IH p ltac:(lia) p' Hp' Hp Hl) as (q & Hq & Hqa).
    rewrite Hn in Hq. injection Hq as <-. lia.
Qed.

Lemma chain_none : forall s m p a,
  chain s m p -> chain_next s m p = None -> chain s m a -> a <= p.
Proof.
  intros s m p a Hp Hn Ha. destruct (le_lt_dec a p) as [H|H]; [exact H|].
  destruct (chain_between s m a p Hp Ha H) as (q & Hq & _). congruence.
Qed.

Lemma chain_gap : forall s m p q a,
  chain s m p -> chain_next s m p = Some q -> p < a < q -> ~ chain s m a.
Proof.
  intros s m p q a Hp Hn Ha Hc.
  destruct (chain_between s m a p Hp Hc ltac:(lia)) as (q' & Hq & Hle).
  rewrite Hn in Hq. injection Hq as <-. lia.
Qed.

Section Agree.
Variables (s : string) (m1 m2 : matching) (os1 os2 : list nat) (n : nat).
Hypothesis A : agree m1 os1 m2 os2 n.

Lemma dead_agree : forall j p, j <= n -> dead m1 j p -> dead m2 j p.
Proof.
  destruct A as [Hm _]. intros j p Hj [(j' & Hj' & H)|(i' & j' & Hj' & H & Hb)].
  - left. exists j'. split; [exact Hj'|]. apply Hm; [lia|exact H].
  - right. exists i', j'. split; [exact Hj'|]. split; [apply Hm; [lia|exact H]|exact Hb].
Qed.

Lemma closes_agree : forall q, q < n -> closes m1 q -> closes m2 q.
Proof.
  destruct A as [Hm _]. intros q Hq [i H]. exists i. apply Hm; [exact Hq|exact H].
Qed.

End Agree.

Lemma closer_agree : forall m1 os1 m2 os2 n q,
  agree m1 os1 m2 os2 n -> q < n -> is_closer m1 q = is_closer m2 q.
Proof.
  intros m1 os1 m2 os2 n q A Hq. apply Bool.eq_true_iff_eq. rewrite !is_closer_iff.
  split; [apply (closes_agree m1 m2 os1 os2 n A q Hq)|].
  apply (closes_agree m2 m1 os2 os1 n (agree_sym _ _ _ _ _ A) q Hq).
Qed.

Lemma chain_agree : forall s m1 os1 m2 os2 n t,
  agree m1 os1 m2 os2 n -> t <= n -> chain s m1 t -> chain s m2 t.
Proof.
  intros s m1 os1 m2 os2 n t A Ht H. induction H as [|p q Hp IH Hn]; [constructor|].
  pose proof (chain_next_bound s m1 p q Hn) as Hb.
  apply (chain_step s m2 p q); [apply IH; lia|].
  rewrite <- Hn. unfold chain_next.
  rewrite (closer_agree m1 os1 m2 os2 n p A ltac:(lia)). reflexivity.
Qed.

Lemma live_agree : forall s m1 os1 m2 os2 n j q k,
  agree m1 os1 m2 os2 n -> j <= n ->
  live s m1 os1 j q k -> live s m2 os2 j q k.
Proof.
  intros s m1 os1 m2 os2 n j q k A Hj (Hin & Hq & Ho & Hc & Hd).
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  split; [apply (proj2 A); [lia|exact Hin]|]. split; [exact Hq|].
  split; [exact Ho|]. split.
  - intros H. apply Hc. apply (closes_agree m2 m1 os2 os1 n A'); [lia|exact H].
  - intros H. apply Hd. apply (dead_agree m2 m1 os2 os1 n A' j q Hj H).
Qed.

Lemma closest_live_agree : forall s m1 os1 m2 os2 n j k p,
  agree m1 os1 m2 os2 n -> j <= n ->
  closest_live s m1 os1 j k p -> closest_live s m2 os2 j k p.
Proof.
  intros s m1 os1 m2 os2 n j k p A Hj [Hp Mp].
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  split; [exact (live_agree s m1 os1 m2 os2 n j p k A Hj Hp)|].
  intros q Hq. apply Mp. exact (live_agree s m2 os2 m1 os1 n j q k A' Hj Hq).
Qed.

Local Lemma valid_pairs_at : forall s m1 os1 m2 os2 n,
  valid s (m1, os1) -> valid s (m2, os2) -> agree m1 os1 m2 os2 n ->
  forall i, In (i, n) m1 -> In (i, n) m2.
Proof.
  intros s m1 os1 m2 os2 n [P1 _] [P2 [U2 _]] A i H.
  destruct (P1 i n H) as (k & Hk & Hch & Hcl & Hne).
  apply (closest_live_agree s m1 os1 m2 os2 n n k i A (le_n n)) in Hcl.
  pose proof (chain_agree s m1 os1 m2 os2 n n A (le_n n) Hch) as Hch2.
  destruct (closes_dec m2 n) as [[i' Hi']|Hn].
  - destruct (P2 i' n Hi') as (k' & Hk' & _ & Hcl' & _).
    rewrite <- (close_key_fun s n k k' Hk Hk') in Hcl'.
    rewrite (closest_live_fun s m2 os2 n k i i' Hcl Hcl'). exact Hi'.
  - destruct (U2 n k Hk Hch2 Hn i Hcl) as [Hc E].
    specialize (Hne Hc). lia.
Qed.

Local Lemma valid_os_at : forall s m1 os1 m2 os2 n,
  valid s (m1, os1) -> valid s (m2, os2) -> agree m1 os1 m2 os2 n ->
  (forall i, In (i, n) m1 <-> In (i, n) m2) ->
  In n os1 -> In n os2.
Proof.
  intros s m1 os1 m2 os2 n [_ [_ O1]] [_ [_ O2]] A Hn H.
  apply O1 in H as (Ho & Hch & Hc). apply O2.
  split; [exact Ho|]. split.
  - exact (chain_agree s m1 os1 m2 os2 n n A (le_n n) Hch).
  - intros [i Hi]. apply Hc. exists i. apply Hn, Hi.
Qed.

Theorem valid_unique : forall s m1 os1 m2 os2,
  valid s (m1, os1) -> valid s (m2, os2) ->
  (forall i j, In (i, j) m1 <-> In (i, j) m2) /\ (forall q, In q os1 <-> In q os2).
Proof.
  intros s m1 os1 m2 os2 V1 V2.
  assert (Step : forall n, agree m1 os1 m2 os2 n ->
            (forall i, In (i, n) m1 <-> In (i, n) m2) /\ (In n os1 <-> In n os2)).
  { intros n A.
    assert (Hp : forall i, In (i, n) m1 <-> In (i, n) m2).
    { intros i. split.
      - apply (valid_pairs_at s m1 os1 m2 os2 n V1 V2 A).
      - apply (valid_pairs_at s m2 os2 m1 os1 n V2 V1 (agree_sym _ _ _ _ _ A)). }
    split; [exact Hp|]. split.
    - apply (valid_os_at s m1 os1 m2 os2 n V1 V2 A Hp).
    - apply (valid_os_at s m2 os2 m1 os1 n V2 V1 (agree_sym _ _ _ _ _ A)).
      intros i. symmetry. apply Hp. }
  assert (All : forall n, agree m1 os1 m2 os2 n).
  { induction n as [|n IH]; [split; intros; lia|].
    destruct (Step n IH) as [Hp Ho]. split.
    - intros i j Hj. destruct (Nat.eq_dec j n) as [->|Hne]; [apply Hp|].
      apply (proj1 IH). lia.
    - intros q Hq. destruct (Nat.eq_dec q n) as [->|Hne]; [exact Ho|].
      apply (proj2 IH). lia. }
  split.
  - intros i j. apply (proj1 (All (S j))). lia.
  - intros q. apply (proj2 (All (S q))). lia.
Qed.

(* "Containers can't overlap": a pair that opens inside another closes
   inside it. *)
Theorem valid_nested : forall s m os i j i' j',
  valid s (m, os) -> In (i, j) m -> In (i', j') m -> i < i' < j -> j' < j.
Proof.
  intros s m os i j i' j' [P _] H H' Hb.
  destruct (P i j H) as (k & Hk & _ & Hcl & _).
  destruct (P i' j' H') as (k' & Hk' & _ & Hcl' & _).
  destruct (lt_eq_lt_dec j' j) as [[Hlt|Heq]|Hgt]; [exact Hlt| |].
  - subst j'. pose proof (close_key_fun s j k k' Hk Hk') as <-.
    pose proof (closest_live_fun s m os j k i i' Hcl Hcl'). lia.
  - exfalso. destruct Hcl' as [(_ & _ & _ & _ & Hd) _].
    apply Hd. right. exists i, j. split; [exact Hgt|]. split; [exact H|exact Hb].
Qed.

(*
The computed reading is valid
=============================

At a byte `n` the stack holds exactly the openers still open at `n`,
innermost first, and every role before `n` obeys the rules.  A token's
role reads only what came before it, so extending the reading past `n`
keeps the rules for the tokens before `n` (`agree`). *)

Lemma pick_found : forall k lv p below,
  ldesc lv -> pick k lv = PFound p below ->
  In (p, k) lv
  /\ (forall q, In (q, k) lv -> q <= p)
  /\ (forall x, In x below <-> In x lv /\ fst x < p)
  /\ ldesc below.
Proof.
  intros k lv. induction lv as [|[q k'] rest IH]; intros p below D H; [discriminate|].
  apply StronglySorted_inv in D as [D F]. rewrite Forall_forall in F.
  cbn [pick] in H. destruct (key_eq k k') eqn:E.
  - injection H as <- <-. apply key_eq_iff in E. subst k'.
    split; [left; reflexivity|]. split; [|split].
    + intros q0 [Hq|Hq]; [injection Hq as ->; lia|]. specialize (F _ Hq). cbn in F. lia.
    + intros x. split.
      * intros Hx. split; [right; exact Hx|]. exact (F x Hx).
      * intros [[<-|Hx] Hlt]; [cbn in Hlt; lia|exact Hx].
    + exact D.
  - destruct (IH p below D H) as (Hin & Hmax & Hb & Db).
    split; [right; exact Hin|]. split; [|split].
    + intros q' [Hq'|Hq'].
      * injection Hq' as <- E'. subst k'. rewrite key_eq_refl in E. discriminate.
      * exact (Hmax q' Hq').
    + intros x. rewrite Hb. split.
      * intros [Hx Hlt]. split; [right; exact Hx|exact Hlt].
      * intros [[<-|Hx] Hlt]; [|split; [exact Hx|exact Hlt]].
        specialize (F _ Hin). cbn in F, Hlt. lia.
    + exact Db.
Qed.

Lemma pick_none : forall k lv,
  pick k lv = PNone -> forall q, ~ In (q, k) lv.
Proof.
  intros k lv. induction lv as [|[q' k'] rest IH]; intros H q Hq; [exact Hq|].
  cbn [pick] in H. destruct (key_eq k k') eqn:E; [discriminate|].
  destruct Hq as [Hq|Hq]; [|exact (IH H q Hq)].
  injection Hq as <- E'. subst k'. rewrite key_eq_refl in E. discriminate.
Qed.

(* The three rules of `valid`, one token at a time. *)
Definition pair_ok (s : string) (m : matching) (os : list nat) (i j : nat) : Prop :=
  exists k, close_key s j = Some k /\ chain s m j
    /\ closest_live s m os j k i /\ (needs_content k = true -> tok_end s i < j).

Definition unmatched_ok (s : string) (m : matching) (os : list nat) (j : nat) : Prop :=
  forall k, close_key s j = Some k -> chain s m j -> ~ closes m j ->
    forall p, closest_live s m os j k p -> needs_content k = true /\ tok_end s p = j.

Definition opener_ok (s : string) (m : matching) (os : list nat) (q : nat) : Prop :=
  In q os <-> (exists k, open_key s q = Some k) /\ chain s m q /\ ~ closes m q.

Record rinv (s : string) (n : nat) (st : rstate) : Prop := RInv {
  ri_bound_pairs : forall i j, In (i, j) (rs_pairs st) -> j < n;
  ri_bound_os : forall q, In q (rs_os st) -> q < n;
  ri_live : forall q k,
    In (q, k) (rs_live st) <-> live s (rs_pairs st) (rs_os st) n q k;
  ri_desc : ldesc (rs_live st);
  ri_pairs : forall i j, In (i, j) (rs_pairs st) -> pair_ok s (rs_pairs st) (rs_os st) i j;
  ri_unmatched : forall j, j < n -> unmatched_ok s (rs_pairs st) (rs_os st) j;
  ri_os : forall q, q < n -> opener_ok s (rs_pairs st) (rs_os st) q
}.

(* What a token's rules read is settled before it. *)
Lemma pair_ok_agree : forall s m os m' os' n i j,
  agree m os m' os' n -> j <= n -> pair_ok s m os i j -> pair_ok s m' os' i j.
Proof.
  intros s m os m' os' n i j A Hj (k & Hk & Hc & Hl & Hn).
  exists k. split; [exact Hk|]. split; [|split; [|exact Hn]].
  - exact (chain_agree s m os m' os' n j A Hj Hc).
  - exact (closest_live_agree s m os m' os' n j k i A Hj Hl).
Qed.

Lemma unmatched_ok_agree : forall s m os m' os' n j,
  agree m os m' os' n -> j < n -> unmatched_ok s m os j -> unmatched_ok s m' os' j.
Proof.
  intros s m os m' os' n j A Hj U k Hk Hc Hnc p Hp.
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  apply (U k Hk).
  - exact (chain_agree s m' os' m os n j A' ltac:(lia) Hc).
  - intros H. apply Hnc. exact (closes_agree m m' os os' n A j Hj H).
  - exact (closest_live_agree s m' os' m os n j k p A' ltac:(lia) Hp).
Qed.

Lemma opener_ok_agree : forall s m os m' os' n q,
  agree m os m' os' n -> q < n -> opener_ok s m os q -> opener_ok s m' os' q.
Proof.
  intros s m os m' os' n q A Hq O.
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  unfold opener_ok in *. split.
  - intros H. apply (proj2 A q Hq) in H. apply O in H as (Ho & Hc & Hnc).
    split; [exact Ho|]. split.
    + exact (chain_agree s m os m' os' n q A ltac:(lia) Hc).
    + intros H. apply Hnc. exact (closes_agree m' m os' os n A' q Hq H).
  - intros (Ho & Hc & Hnc). apply (proj2 A q Hq). apply O.
    split; [exact Ho|]. split.
    + exact (chain_agree s m' os' m os n q A' ltac:(lia) Hc).
    + intros H. apply Hnc. exact (closes_agree m m' os os' n A q Hq H).
Qed.

Local Lemma pairs_lt : forall s n st i j,
  rinv s n st -> In (i, j) (rs_pairs st) -> i < j.
Proof.
  intros s n st i j I H. destruct (ri_pairs s n st I i j H) as (_ & _ & _ & [(_ & Hq & _) _] & _).
  exact Hq.
Qed.

Local Lemma dead_succ : forall m n q,
  (forall i j, In (i, j) m -> j < n) -> (dead m (S n) q <-> dead m n q).
Proof.
  intros m n q B. split.
  - intros [(j' & Hj & H)|(i' & j' & Hj & H & Hb)].
    + left. exists j'. split; [exact (B _ _ H)|exact H].
    + right. exists i', j'. split; [exact (B _ _ H)|]. split; assumption.
  - intros [(j' & Hj & H)|(i' & j' & Hj & H & Hb)].
    + left. exists j'. split; [lia|exact H].
    + right. exists i', j'. split; [lia|]. split; assumption.
Qed.

(* No pair closes at `n`. *)
Local Lemma live_succ : forall s n st os' q k,
  rinv s n st -> (forall q', q' < n -> In q' os' <-> In q' (rs_os st)) ->
  live s (rs_pairs st) os' (S n) q k
  <-> live s (rs_pairs st) (rs_os st) n q k
      \/ (q = n /\ In n os' /\ open_key s n = Some k).
Proof.
  intros s n st os' q k I Hos.
  pose proof (ri_bound_pairs s n st I) as B. pose proof (ri_bound_os s n st I) as Bo. split.
  - intros (Hin & Hq & Ho & Hc & Hd). destruct (Nat.eq_dec q n) as [->|Hne].
    + right. split; [reflexivity|]. split; assumption.
    + left. split; [apply Hos; [lia|exact Hin]|]. split; [lia|]. split; [exact Ho|].
      split; [exact Hc|]. intros H. apply Hd. apply dead_succ; assumption.
  - intros [(Hin & Hq & Ho & Hc & Hd)|(-> & Hin & Ho)].
    + split; [apply Hos; [exact Hq|exact Hin]|]. split; [lia|]. split; [exact Ho|].
      split; [exact Hc|]. intros H. apply Hd. apply (dead_succ _ n q B), H.
    + split; [exact Hin|]. split; [lia|]. split; [exact Ho|]. split.
      * intros [i Hi]. specialize (B _ _ Hi). lia.
      * intros [(j' & Hj & H)|(i' & j' & Hj & H & Hb)].
        -- specialize (B _ _ H). pose proof (pairs_lt s n st _ _ I H). lia.
        -- specialize (B _ _ H). lia.
Qed.

(* A pair closes at `n` with its opener `p` live. *)
Local Lemma live_pair : forall s n st p q k,
  rinv s n st -> p < n ->
  live s ((p, n) :: rs_pairs st) (rs_os st) (S n) q k
  <-> live s (rs_pairs st) (rs_os st) n q k /\ q < p.
Proof.
  intros s n st p q k I Hpn.
  pose proof (ri_bound_pairs s n st I) as B. pose proof (ri_bound_os s n st I) as Bo.
  assert (Dead : dead ((p, n) :: rs_pairs st) (S n) q
                 <-> dead (rs_pairs st) n q \/ q = p \/ p < q < n).
  { split.
    - intros [(j' & Hj & [E|H])|(i' & j' & Hj & [E|H] & Hb)].
      + injection E as -> ->. right. left. reflexivity.
      + left. left. exists j'. split; [exact (B _ _ H)|exact H].
      + injection E as -> ->. right. right. exact Hb.
      + left. right. exists i', j'. split; [exact (B _ _ H)|]. split; assumption.
    - intros [[(j' & Hj & H)|(i' & j' & Hj & H & Hb)]|[->|Hb]].
      + left. exists j'. split; [lia|right; exact H].
      + right. exists i', j'. split; [lia|]. split; [right; exact H|exact Hb].
      + left. exists n. split; [lia|left; reflexivity].
      + right. exists p, n. split; [lia|]. split; [left; reflexivity|exact Hb]. }
  split.
  - intros (Hin & Hq & Ho & Hc & Hd).
    assert (Hqn : q < n) by (specialize (Bo q Hin); lia).
    rewrite Dead in Hd.
    split; [|destruct (lt_eq_lt_dec q p) as [[H|H]|H]; [exact H|tauto|]; exfalso; apply Hd; right; right; lia].
    split; [exact Hin|]. split; [exact Hqn|]. split; [exact Ho|]. split.
    + intros [i Hi]. apply Hc. exists i. right. exact Hi.
    + intros H. apply Hd. left. exact H.
  - intros [(Hin & Hq & Ho & Hc & Hd) Hqp].
    split; [exact Hin|]. split; [lia|]. split; [exact Ho|]. split.
    + intros [i [E|Hi]]; [injection E as _ ->; lia|]. apply Hc. exists i. exact Hi.
    + rewrite Dead. intros [H|[H|H]]; [exact (Hd H)|lia|lia].
Qed.

(* A byte off the chain: nothing changes. *)
Local Lemma rinv_skip : forall s n st,
  rinv s n st -> ~ chain s (rs_pairs st) n -> rinv s (S n) st.
Proof.
  intros s n st I Hc.
  constructor.
  - intros i j H. specialize (ri_bound_pairs s n st I i j H). lia.
  - intros q H. specialize (ri_bound_os s n st I q H). lia.
  - intros q k. rewrite (ri_live s n st I), (live_succ s n st (rs_os st) q k I (fun _ _ => iff_refl _)).
    split; [intros H; left; exact H|intros [H|(_ & H & _)]; [exact H|]].
    specialize (ri_bound_os s n st I n H). lia.
  - exact (ri_desc s n st I).
  - exact (ri_pairs s n st I).
  - intros j Hj. destruct (Nat.eq_dec j n) as [->|Hne];
      [|apply (ri_unmatched s n st I); lia].
    intros k _ Hch. contradiction.
  - intros q Hq. destruct (Nat.eq_dec q n) as [->|Hne];
      [|apply (ri_os s n st I); lia].
    split; [intros H; specialize (ri_bound_os s n st I n H); lia|intros (_ & Hch & _); contradiction].
Qed.

Local Lemma rinv_skip_to : forall s a b st,
  rinv s a st -> a <= b -> (forall j, a <= j < b -> ~ chain s (rs_pairs st) j) ->
  rinv s b st.
Proof.
  intros s a b st I Hab. induction Hab as [|b Hab IH]; intros Hoff; [exact I|].
  apply rinv_skip; [apply IH; intros j Hj; apply Hoff; lia|apply Hoff; lia].
Qed.

(* A token that closes nothing: it opens or it is text. *)
Local Lemma rinv_noclose : forall s n st op K,
  rinv s n st ->
  (op = true -> open_key s n = Some K) ->
  opener_ok s (rs_pairs st) (if op then n :: rs_os st else rs_os st) n ->
  unmatched_ok s (rs_pairs st) (if op then n :: rs_os st else rs_os st) n ->
  rinv s (S n)
    (RState (if op then (n, K) :: rs_live st else rs_live st) (rs_pairs st)
       (if op then n :: rs_os st else rs_os st)).
Proof.
  intros s n st op K I HK Ho Hu.
  set (os' := if op then n :: rs_os st else rs_os st).
  assert (Hos : forall q, q < n -> In q os' <-> In q (rs_os st)).
  { intros q Hq. unfold os'. destruct op; [|reflexivity]. cbn.
    split; [intros [E|H]; [lia|exact H]|intros H; right; exact H]. }
  assert (A : agree (rs_pairs st) (rs_os st) (rs_pairs st) os' n).
  { split; [intros; reflexivity|]. intros q Hq. symmetry. apply Hos, Hq. }
  constructor; cbn [rs_live rs_pairs rs_os]; fold os'.
  - intros i j H. specialize (ri_bound_pairs s n st I i j H). lia.
  - intros q H. unfold os' in H. destruct op; [destruct H as [<-|H]; [lia|]|];
      specialize (ri_bound_os s n st I q H); lia.
  - intros q k. rewrite (live_succ s n st os' q k I Hos), <- (ri_live s n st I).
    unfold os'. destruct op.
    + specialize (HK eq_refl). cbn. split.
      * intros [E|H]; [injection E as <- <-; right; auto|left; exact H].
      * intros [H|(-> & _ & Ho')]; [right; exact H|].
        rewrite HK in Ho'. injection Ho' as <-. left. reflexivity.
    + split; [intros H; left; exact H|].
      intros [H|(-> & Hin & _)]; [exact H|].
      exfalso. specialize (ri_bound_os s n st I n Hin). lia.
  - destruct op; [|exact (ri_desc s n st I)]. constructor; [exact (ri_desc s n st I)|].
    apply Forall_forall. intros [q k] Hx; cbn.
    apply (ri_live s n st I) in Hx as (_ & Hq & _). exact Hq.
  - intros i j H. apply (pair_ok_agree s (rs_pairs st) (rs_os st) _ os' n i j A).
    + exact (Nat.lt_le_incl _ _ (ri_bound_pairs s n st I i j H)).
    + exact (ri_pairs s n st I i j H).
  - intros j Hj. destruct (Nat.eq_dec j n) as [->|Hne]; [exact Hu|].
    apply (unmatched_ok_agree s (rs_pairs st) (rs_os st) _ os' n j A); [lia|].
    apply (ri_unmatched s n st I). lia.
  - intros q Hq. destruct (Nat.eq_dec q n) as [->|Hne]; [exact Ho|].
    apply (opener_ok_agree s (rs_pairs st) (rs_os st) _ os' n q A); [lia|].
    apply (ri_os s n st I). lia.
Qed.

(* A token that closes a pair with `p`. *)
Local Lemma rinv_pair : forall s n st p K lv',
  rinv s n st -> chain s (rs_pairs st) n ->
  close_key s n = Some K ->
  closest_live s (rs_pairs st) (rs_os st) n K p ->
  (needs_content K = true -> tok_end s p < n) ->
  (forall q k, In (q, k) lv' <-> In (q, k) (rs_live st) /\ q < p) ->
  ldesc lv' ->
  rinv s (S n) (RState lv' ((p, n) :: rs_pairs st) (rs_os st)).
Proof.
  intros s n st p K lv' I Hch HK Hcl Hne Hlv Hdesc.
  set (m' := (p, n) :: rs_pairs st).
  pose proof (ri_bound_pairs s n st I) as B.
  assert (Hpn : p < n) by (destruct Hcl as [(_ & Hp & _) _]; exact Hp).
  assert (A : agree (rs_pairs st) (rs_os st) m' (rs_os st) n).
  { split; [|intros; reflexivity]. intros i j Hj. unfold m'. cbn. split.
    - intros H. right. exact H.
    - intros [E|H]; [injection E as _ ->; lia|exact H]. }
  constructor; cbn [rs_live rs_pairs rs_os]; fold m'.
  - intros i j [E|H]; [injection E as _ <-; lia|specialize (B i j H); lia].
  - intros q H. specialize (ri_bound_os s n st I q H). lia.
  - intros q k. unfold m'. rewrite Hlv, (live_pair s n st p q k I Hpn), (ri_live s n st I).
    reflexivity.
  - exact Hdesc.
  - intros i j [E|H].
    + injection E as <- <-. exists K. split; [exact HK|]. split.
      * exact (chain_agree s (rs_pairs st) (rs_os st) m' (rs_os st) n n A (le_n n) Hch).
      * split; [|exact Hne].
        exact (closest_live_agree s (rs_pairs st) (rs_os st) m' (rs_os st) n n K p A (le_n n) Hcl).
    + apply (pair_ok_agree s (rs_pairs st) (rs_os st) m' (rs_os st) n i j A).
      * exact (Nat.lt_le_incl _ _ (B i j H)).
      * exact (ri_pairs s n st I i j H).
  - intros j Hj. destruct (Nat.eq_dec j n) as [->|Hne'].
    + intros k _ _ Hc. exfalso. apply Hc. exists p. left. reflexivity.
    + apply (unmatched_ok_agree s (rs_pairs st) (rs_os st) m' (rs_os st) n j A); [lia|].
      apply (ri_unmatched s n st I). lia.
  - intros q Hq. destruct (Nat.eq_dec q n) as [->|Hne'].
    + split.
      * intros H. specialize (ri_bound_os s n st I n H). lia.
      * intros (_ & _ & Hc). exfalso. apply Hc. exists p. left. reflexivity.
    + apply (opener_ok_agree s (rs_pairs st) (rs_os st) m' (rs_os st) n q A); [lia|].
      apply (ri_os s n st I). lia.
Qed.

(* What a found opener leaves below it. *)
Local Lemma pick_below : forall s n st K p below,
  rinv s n st -> pick K (rs_live st) = PFound p below ->
  closest_live s (rs_pairs st) (rs_os st) n K p
  /\ (forall q k, In (q, k) below <-> In (q, k) (rs_live st) /\ q < p)
  /\ ldesc below.
Proof.
  intros s n st K p below I P.
  destruct (pick_found K _ p below (ri_desc s n st I) P) as (Hin & Hmax & Hb & Db).
  split; [|split; [|exact Db]].
  - split; [apply (ri_live s n st I); exact Hin|].
    intros q Hq. apply (ri_live s n st I) in Hq. exact (Hmax q Hq).
  - intros q k. rewrite Hb. reflexivity.
Qed.

Local Lemma pick_not_live : forall s n st K p,
  rinv s n st -> pick K (rs_live st) = PNone ->
  ~ closest_live s (rs_pairs st) (rs_os st) n K p.
Proof.
  intros s n st K p I P [Hp _]. apply (ri_live s n st I) in Hp.
  exact (pick_none K _ P p Hp).
Qed.

Lemma rinv_step : forall s n st t,
  tok_of s n = Some t -> rinv s n st -> chain s (rs_pairs st) n ->
  rinv s (S n) (rstep s n t st).
Proof.
  intros s n [lv m os] t Hn I Hch.
  assert (Hok : open_key s n = opens_as t) by (unfold open_key; rewrite Hn; reflexivity).
  assert (Hck : close_key s n = closes_as t) by (unfold close_key; rewrite Hn; reflexivity).
  assert (Hnc : ~ closes m n)
    by (intros [i Hi]; specialize (ri_bound_pairs s n _ I i n Hi); cbn in *; lia).
  cbn [rs_pairs] in Hch.
  unfold rstep; cbn [rs_live rs_pairs rs_os].
  pose (st := RState lv m os).
  assert (NC : forall op K,
            (op = true -> open_key s n = Some K) ->
            opener_ok s m (if op then n :: os else os) n ->
            unmatched_ok s m (if op then n :: os else os) n ->
            rinv s (S n) (RState (if op then (n, K) :: lv else lv) m
                             (if op then n :: os else os)))
    by (intros op K; exact (rinv_noclose s n st op K I)).
  assert (Aos : forall op : bool, agree m os m (if op then n :: os else os) n).
  { intros op. split; [intros; reflexivity|]. intros q Hq. destruct op; [|reflexivity]. cbn.
    split; [intros H; right; exact H|intros [E|H]; [lia|exact H]]. }
  assert (OO : forall (op : bool) (K : key), open_key s n = (if op then Some K else None) ->
            opener_ok s m (if op then n :: os else os) n).
  { intros [|] K Ho.
    - split; [intros _|intros _; left; reflexivity].
      split; [exists K; exact Ho|]. split; [exact Hch|exact Hnc].
    - split; [intros H; specialize (ri_bound_os s n _ I n H); cbn in *; lia|].
      intros [[k Hk] _]; congruence. }
  assert (UN : forall (op : bool) K,
            (forall p, ~ closest_live s m os n K p) -> close_key s n = Some K ->
            unmatched_ok s m (if op then n :: os else os) n).
  { intros op K Hn' HK k Hk _ _ p Hp. rewrite HK in Hk. injection Hk as <-.
    exfalso. apply (Hn' p).
    exact (closest_live_agree s m _ m os n n K p (agree_sym _ _ _ _ _ (Aos op)) (le_n n) Hp). }
  assert (Text : opens_as t = None -> closes_as t = None -> rinv s (S n) st).
  { intros Ho Hc. apply (NC false KBracket); [discriminate| |].
    - apply (OO false KBracket). rewrite Hok. exact Ho.
    - intros k Hk. congruence. }
  (* a `]` that may close a link or a span: it pairs with the closest
     open bracket, or is text *)
  assert (Close : close_key s n = Some KBracket -> open_key s n = None ->
            rinv s (S n)
              (match pick KBracket lv with
               | PFound p below => RState below ((p, n) :: m) os
               | PNone => st
               end)).
  { intros HK Ho. destruct (pick KBracket lv) as [p below|] eqn:P.
    - destruct (pick_below s n st KBracket p below I P) as (Hcl & Hlv & Db).
      exact (rinv_pair s n st p KBracket below I Hch HK Hcl
               (fun H => ltac:(discriminate H)) Hlv Db).
    - apply (NC false KBracket); [discriminate|apply (OO false KBracket Ho)|].
      exact (UN false KBracket (fun p => pick_not_live s n st KBracket p I P) HK). }
  (* text, a break and the escapes neither open nor close *)
  destruct t as [c| |k mr op cl| |b rg|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn]; try (apply Text; reflexivity).
  - (* a delimiter *)
    set (K := KDelim k mr).
    assert (Hop : open_key s n = if op then Some K else None)
      by (rewrite Hok; destruct op; reflexivity).
    assert (Ropen : (forall op' : bool, unmatched_ok s m (if op' then n :: os else os) n) ->
              rinv s (S n) (ropen n K op st)).
    { intros Hu. unfold ropen. destruct op; cbn [rs_live rs_pairs rs_os].
      - apply (NC true K); [intros _; exact Hop|apply (OO true K Hop)|apply (Hu true)].
      - apply (NC false K); [discriminate|apply (OO false K Hop)|apply (Hu false)]. }
    destruct cl.
    2: { cbn. apply Ropen. intros op' k' Hk'. rewrite Hck in Hk'. discriminate. }
    assert (HK : close_key s n = Some K) by (rewrite Hck; reflexivity).
    destruct (pick K lv) as [p below|] eqn:P.
    + destruct (pick_below s n st K p below I P) as (Hcl & Hlv & Db).
      unfold st in Hcl, Hlv; cbn [rs_live rs_pairs rs_os] in Hcl, Hlv.
      destruct (Nat.ltb (tok_end s p) n) eqn:L.
      * apply Nat.ltb_lt in L.
        exact (rinv_pair s n st p K below I Hch HK Hcl (fun _ => L) Hlv Db).
      * apply Nat.ltb_ge in L. apply Ropen.
        intros op' k' Hk' _ _ p' Hp'. rewrite HK in Hk'. injection Hk' as <-.
        pose proof (closest_live_agree s m _ m os n n K p'
                      (agree_sym _ _ _ _ _ (Aos op')) (le_n n) Hp') as Hp''.
        rewrite <- (closest_live_fun s m os n K p p' Hcl Hp'').
        split; [reflexivity|].
        destruct Hcl as [(Hin & Hpn & Hop' & _) _].
        pose proof (proj1 (ri_os s n st I p Hpn) Hin) as (_ & Hchp & _).
        destruct (chain_between s m n p Hchp Hch Hpn) as (q & Hq & Hqn).
        unfold open_key, tok_of in Hop'. unfold tok_end in *. unfold chain_next in Hq.
        destruct (tok_at s p) as [[tp lp]|]; [|discriminate].
        destruct tp; try (injection Hq as <-; lia); discriminate Hop'.
    + apply Ropen. intros op'.
      exact (UN op' K (fun p => pick_not_live s n st K p I P) HK).
  - (* a `[` *)
    apply (NC true KBracket); [intros _; rewrite Hok; reflexivity|apply (OO true KBracket)|].
    + rewrite Hok. reflexivity.
    + intros k Hk. rewrite Hck in Hk. discriminate.
  - (* a `]` before a region that closes *)
    exact (Close ltac:(rewrite Hck; reflexivity) ltac:(rewrite Hok; reflexivity)).
  - (* a `]` that may close a span *)
    exact (Close ltac:(rewrite Hck; reflexivity) ltac:(rewrite Hok; reflexivity)).
Qed.

(* A step adds at most a pair closing at the token and the token as an
   opener. *)
Lemma rstep_grows : forall s i t st,
  (rs_pairs (rstep s i t st) = rs_pairs st
   \/ exists p, rs_pairs (rstep s i t st) = (p, i) :: rs_pairs st)
  /\ (rs_os (rstep s i t st) = rs_os st \/ rs_os (rstep s i t st) = i :: rs_os st).
Proof.
  intros s i t [lv m os]. unfold rstep. cbn [rs_live rs_pairs rs_os].
  assert (Ro : forall k op st',
            rs_pairs st' = m -> rs_os st' = os ->
            (rs_pairs (ropen i k op st') = m
             \/ exists p, rs_pairs (ropen i k op st') = (p, i) :: m)
            /\ (rs_os (ropen i k op st') = os \/ rs_os (ropen i k op st') = i :: os)).
  { intros k [|] st' E1 E2; unfold ropen; cbn [rs_pairs rs_os]; rewrite E1, E2;
      split; [left|right|left|left]; reflexivity. }
  destruct t as [c| |k mr op cl| |b rg|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn]; try (split; left; reflexivity).
  - destruct (if cl then pick (KDelim k mr) lv else PNone) as [p below|];
      [destruct (Nat.ltb (tok_end s p) i)|];
      try (apply Ro; reflexivity).
    cbn. split; [right; exists p; reflexivity|left; reflexivity].
  - apply Ro; reflexivity.
  - destruct (pick KBracket lv) as [p below|]; try (split; left; reflexivity).
    cbn. split; [right; exists p; reflexivity|left; reflexivity].
  - destruct (pick KBracket lv) as [p below|]; try (split; left; reflexivity).
    cbn. split; [right; exists p; reflexivity|left; reflexivity].
Qed.

(* Past the last token of the chain the invariant is the rules. *)
Local Lemma rinv_valid : forall s n st,
  rinv s n st ->
  (forall j, n <= j -> chain s (rs_pairs st) j -> tok_of s j = None) ->
  valid s (rs_pairs st, rs_os st).
Proof.
  intros s n st I Hend.
  split; [|split].
  - exact (ri_pairs s n st I).
  - intros j k Hk Hc. destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
    + exact (ri_unmatched s n st I j Hj k Hk Hc).
    + unfold close_key in Hk. rewrite (Hend j Hj Hc) in Hk. discriminate.
  - intros q. destruct (Nat.lt_ge_cases q n) as [Hq|Hq].
    + exact (ri_os s n st I q Hq).
    + split.
      * intros H. specialize (ri_bound_os s n st I q H). lia.
      * intros ([k Hk] & Hc & _). unfold open_key in Hk.
        rewrite (Hend q Hq Hc) in Hk. discriminate.
Qed.

(* A step keeps the token on the chain; the invariant then holds at the
   next token, or the rules hold if there is none. *)
Lemma rinv_next : forall s n st t,
  rinv s n st -> chain s (rs_pairs st) n -> tok_of s n = Some t ->
  chain s (rs_pairs (rstep s n t st)) n
  /\ match chain_next s (rs_pairs (rstep s n t st)) n with
     | Some q => rinv s q (rstep s n t st) /\ chain s (rs_pairs (rstep s n t st)) q
     | None => valid s (rs_pairs (rstep s n t st), rs_os (rstep s n t st))
     end.
Proof.
  intros s n st t I Hch Ht.
  set (st' := rstep s n t st).
  pose proof (rinv_step s n st t Ht I Hch) as I'.
  destruct (rstep_grows s n t st) as [Gp Go]; fold st' in Gp, Go.
  assert (A : agree (rs_pairs st) (rs_os st) (rs_pairs st') (rs_os st') n).
  { split.
    - intros i j Hj. destruct Gp as [-> | [p ->]]; [reflexivity|]. cbn.
      split; [intros H0; right; exact H0|intros [E|H0]; [injection E as _ ->; lia|exact H0]].
    - intros q Hq. destruct Go as [-> | ->]; [reflexivity|]. cbn.
      split; [intros H0; right; exact H0|intros [E|H0]; [lia|exact H0]]. }
  assert (Hch' : chain s (rs_pairs st') n) by exact (chain_agree s _ _ _ _ n n A (le_n n) Hch).
  split; [exact Hch'|].
  destruct (chain_next s (rs_pairs st') n) as [q|] eqn:Hq.
  - pose proof (chain_next_bound s _ n q Hq) as Hb. split.
    + apply (rinv_skip_to s (S n) q st' I'); [lia|].
      intros j Hj. exact (chain_gap s _ n q j Hch' Hq ltac:(lia)).
    + exact (chain_step s _ n q Hch' Hq).
  - apply (rinv_valid s (S n) st' I'). intros j Hj Hc.
    pose proof (chain_none s _ n j Hch' Hq Hc). lia.
Qed.

(* Past the end of the paragraph. *)
Lemma rinv_end : forall s n st,
  rinv s n st -> chain s (rs_pairs st) n -> tok_of s n = None ->
  valid s (rs_pairs st, rs_os st).
Proof.
  intros s n st I Hch Ht. apply (rinv_valid s n st I). intros j Hj Hc.
  destruct (Nat.eq_dec j n) as [->|Hne]; [exact Ht|].
  destruct (chain_between s _ j n Hch Hc ltac:(lia)) as (q & Hq & _).
  unfold chain_next, tok_of in Hq, Ht. destruct (tok_at s n); [discriminate|].
  discriminate.
Qed.

Local Lemma rgo_valid : forall s f n st,
  rinv s n st -> chain s (rs_pairs st) n -> String.length s - n < f ->
  valid s (rs_pairs (rgo s f n st), rs_os (rgo s f n st)).
Proof.
  intros s f. induction f as [|f IH]; intros n st I Hch Hf; [lia|].
  cbn [rgo]. destruct (tok_of s n) as [t|] eqn:Ht; [|exact (rinv_end s n st I Hch Ht)].
  destruct (rinv_next s n st t I Hch Ht) as [_ N].
  destruct (chain_next s (rs_pairs (rstep s n t st)) n) as [q|] eqn:Hq; [|exact N].
  pose proof (chain_next_bound s _ n q Hq). destruct N as [I' Hq'].
  apply IH; [exact I'|exact Hq'|lia].
Qed.

Lemma rinv_start : forall s, rinv s 0 rstart.
Proof.
  intros s. constructor; cbn [rs_live rs_pairs rs_os rstart].
  - intros i j [].
  - intros q [].
  - intros q k. split; [intros []|intros ([] & _)].
  - constructor.
  - intros i j [].
  - intros j H. lia.
  - intros q H. lia.
Qed.

Theorem ref_read_valid : forall s, valid s (ref_read s).
Proof.
  intros s. unfold ref_read.
  apply rgo_valid; [apply rinv_start|constructor|lia].
Qed.

(*
Lines over the alphabet
=======================

With no option claiming a byte the alphabet leaves out, every line is
over it.  A backslash pairs with the byte after it, and the rest are
bytes the alphabet admits one by one. *)

Lemma alphabet_total_byte : alphabet_total = true ->
  forall c, Ascii.eqb c nl_char = false -> is_bslash c = false -> in_alphabet c = true.
Proof.
  intros H c Hn Hb. unfold alphabet_total in H.
  repeat rewrite andb_true_iff in H.
  destruct H as ((((((Hw & Hd) & Ht) & Hh) & Hy) & Hl) & Hr).
  apply negb_true_iff in Hw, Hd, Ht, Hh, Hl, Hr. unfold is_delim in Hl, Hr.
  unfold in_alphabet. rewrite Hd, Ht, Hh, Hy, Hn. cbn [negb andb orb].
  destruct c as [[] [] [] [] [] [] [] []]; try discriminate Hn; try discriminate Hb; cbn;
    match goal with |- context [match ?m with Some _ => _ | None => _ end] =>
      destruct m eqn:E end;
    try reflexivity.
  all: change rparen with ")"%char in Hr; change lparen with "("%char in Hl;
    first [rewrite E in Hr; discriminate Hr | rewrite E in Hl; discriminate Hl].
Qed.

Lemma alphabet_total_line : alphabet_total = true ->
  forall x, no_char nl_char x = true -> over_alphabet x = true.
Proof.
  intros H x. remember (String.length x) as m eqn:Em. revert x Em.
  induction m as [m IH] using lt_wf_ind. intros x Em Hn.
  destruct x as [|c x]; [reflexivity|].
  cbn [no_char] in Hn. apply andb_true_iff in Hn as [Hc Hn]. apply negb_true_iff in Hc.
  cbn [over_alphabet]. destruct (is_bslash c) eqn:Eb.
  - destruct x as [|d x]; [reflexivity|].
    cbn [no_char] in Hn. apply andb_true_iff in Hn as [Hd Hn]. rewrite Hd. cbn [andb].
    apply (IH (String.length x)); [cbn in Em; lia|reflexivity|exact Hn].
  - rewrite (alphabet_total_byte H c Hc Eb).
    assert (Hf : follow_ok c x = true).
    { unfold alphabet_total in H. unfold follow_ok.
      destruct wikilinks_enabled; [rewrite andb_false_l in H; discriminate H|].
      rewrite andb_false_r. reflexivity. }
    rewrite Hf. apply (IH (String.length x)); [cbn in Em; lia|reflexivity|exact Hn].
Qed.

End WithTable.
