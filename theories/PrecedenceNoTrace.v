(* ai-disclosure: autonomous *)

(* A token the reading takes as text leaves no trace: escaping its first
   byte gives the same tree.  Stated for `<`, `[`, `]` and `!`, the bytes
   whose token reads past them, and proved of the specification of
   `Precedence.v`. *)

From Stdlib Require Import String Ascii List Bool Lia Arith.
From DjotV Require Import Strings Ast Attributes InlineTable InlineView Precedence
  PrecedenceFacts.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

Definition text_byte (c : ascii) : bool :=
  (Ascii.eqb c lt || Ascii.eqb c lbrack || Ascii.eqb c rbrack || Ascii.eqb c bang)%bool.

(* Whether a backslash escapes the byte after `x`, reading `x` from `e`. *)
Fixpoint esc_after (e : bool) (x : string) : bool :=
  match x with
  | EmptyString => e
  | String a r => esc_after (if e then false else is_bslash a) r
  end.

(*
Lookaheads
==========

Every lookahead past a byte `c` of the four reads `x ++ c :: y` and
`x ++ \ :: c :: y` alike: the two fail together, and a result found
inside `x` is found in both.  A label scan is the exception: it closes
at a `]` that no backslash escapes, so it needs the `]` unescaped.
*)

Section Insert.
Variable c : ascii.
Hypothesis Hc : text_byte c = true.

Local Ltac bytes :=
  let H := fresh in
  pose proof Hc as H; unfold text_byte in H;
  repeat (apply orb_true_iff in H as [H|H]); apply Ascii.eqb_eq in H; subst c.

Local Lemma c_not_bslash : is_bslash c = false.
Proof. bytes; reflexivity. Qed.

Local Lemma c_not_ws : is_ws c = false.
Proof. bytes; reflexivity. Qed.

Local Lemma c_not_nl : Ascii.eqb c nl_char = false.
Proof. bytes; reflexivity. Qed.

Local Lemma c_not_paren : Ascii.eqb c lparen = false /\ Ascii.eqb c rparen = false.
Proof. bytes; split; reflexivity. Qed.

Local Lemma c_punct : is_punct c = true.
Proof. bytes; reflexivity. Qed.

Local Lemma c_style : dstyle_of c = None.
Proof.
  destruct (dstyle_of c) as [k|] eqn:E; [|reflexivity].
  pose proof (dstyle_of_char c k E) as Ek. pose proof (dchar_free k) as F.
  rewrite Ek in F. pose proof Hc as H; unfold text_byte in H.
  unfold dreserved in F; apply orb_false_iff in F as [F1 F2];
    repeat (apply orb_false_iff in F1 as [F1 ?]); repeat (apply orb_true_iff in H as [H|H]);
    congruence.
Qed.

Local Lemma bslash_style : dstyle_of bslash = None.
Proof.
  destruct (dstyle_of bslash) as [k|] eqn:E; [|reflexivity].
  pose proof (dstyle_of_char bslash k E) as Ek. pose proof (dchar_free k) as F.
  rewrite Ek in F. unfold dreserved, is_bslash in F. rewrite Ascii.eqb_refl in F. discriminate F.
Qed.

Local Notation orig x y := (x ++ String c y)%string.
Local Notation ins x y := (x ++ String bslash (String c y))%string.

(* A destination: past the inserted byte the two scans are in the same
   state, one byte apart. *)
Lemma dest_close_ins : forall y x e d i,
  dest_close e d i (ins x y)
  = option_map (fun j => if Nat.ltb j (i + String.length x) then j else S j)
      (dest_close e d i (orig x y)).
Proof.
  intros y x. induction x as [|a x IH]; intros e d i.
  - cbn [append dest_close String.length]. rewrite Nat.add_0_r.
    destruct c_not_paren as [P1 P2].
    assert (E : forall j, dest_close false d (S j) y = option_map S (dest_close false d j y)).
    { intros j. replace (S j) with (j + 1) by lia. rewrite dest_close_shift.
      destruct (dest_close false d j y); cbn; [f_equal; lia|reflexivity]. }
    rewrite c_not_bslash, P1, P2. change (is_bslash bslash) with true. cbn iota.
    assert (B : forall o, (forall j, o = Some j -> S i <= j) ->
               option_map S o = option_map (fun j => if (j <? i)%nat then j else S j) o).
    { intros [j|] H; [|reflexivity]. specialize (H j eq_refl). cbn [option_map].
      replace (j <? i)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity. }
    rewrite E. destruct e; apply B; intros j Hj; exact (proj1 (dest_close_bound _ _ _ _ _ Hj)).
  - cbn [append dest_close String.length].
    replace (i + S (String.length x)) with (S i + String.length x) by lia.
    destruct e; [apply IH|]. destruct (is_bslash a); [apply IH|].
    destruct (Ascii.eqb a lparen); [apply IH|]. destruct (Ascii.eqb a rparen); [|apply IH].
    destruct d; [cbn [option_map]; destruct (Nat.ltb i (S i + String.length x)) eqn:L;
                 [reflexivity|apply Nat.ltb_ge in L; lia]|apply IH].
Qed.

(* A reference label, with the `]` unescaped. *)
Lemma label_close_ins : forall y x e i,
  (c = rbrack -> esc_after e x = false) ->
  match label_close e i (orig x y) with
  | None => label_close e i (ins x y) = None
  | Some j => j < i + String.length x -> label_close e i (ins x y) = Some j
  end.
Proof.
  intros y x. induction x as [|a x IH]; intros e i Hp.
  - cbn [append label_close String.length esc_after] in *. rewrite Nat.add_0_r.
    rewrite c_not_bslash. change (is_bslash bslash) with true. cbn iota.
    assert (E : label_close false (S (S i)) y = option_map S (label_close false (S i) y)).
    { replace (S (S i)) with (S i + 1) by lia. rewrite label_close_shift.
      destruct (label_close false (S i) y); cbn; [f_equal; lia|reflexivity]. }
    destruct e.
    + destruct (Ascii.eqb c rbrack) eqn:R.
      { apply Ascii.eqb_eq in R. specialize (Hp R). discriminate Hp. }
      destruct (label_close false (S i) y) as [j|] eqn:J.
      * intros L. pose proof (label_close_bound _ _ _ _ J). lia.
      * rewrite E. reflexivity.
    + destruct (Ascii.eqb c rbrack); [intros L; lia|].
      destruct (label_close false (S i) y) as [j|] eqn:J.
      * intros L. pose proof (label_close_bound _ _ _ _ J). lia.
      * rewrite E. reflexivity.
  - cbn [append label_close String.length esc_after] in *.
    replace (i + S (String.length x)) with (S i + String.length x) by lia.
    destruct e; [apply IH, Hp|]. destruct (is_bslash a); [apply IH, Hp|].
    destruct (Ascii.eqb a rbrack); [intros L; reflexivity|apply IH, Hp].
Qed.

(* A footnote label: the same scan. *)
Lemma note_go_ins : forall y x e,
  (c = rbrack -> esc_after e x = false) ->
  match note_go e (orig x y) with
  | None => note_go e (ins x y) = None
  | Some l => String.length l < String.length x -> note_go e (ins x y) = Some l
  end.
Proof.
  intros y x. induction x as [|a x IH]; intros e Hp.
  - cbn [append note_go String.length esc_after] in *.
    rewrite c_not_bslash. change (is_bslash bslash) with true. cbn iota.
    destruct e.
    + destruct (Ascii.eqb c rbrack) eqn:R.
      { apply Ascii.eqb_eq in R. specialize (Hp R). discriminate Hp. }
      destruct (note_go false y); cbn [option_map]; [intros L; lia|reflexivity].
    + destruct (Ascii.eqb c rbrack); [intros L; cbn in L; lia|].
      destruct (note_go false y); cbn [option_map]; [intros L; lia|reflexivity].
  - cbn [append note_go String.length esc_after] in *.
    assert (G : forall b, match note_go b (orig x y) with
                          | None => note_go b (ins x y) = None
                          | Some l => String.length l < String.length x ->
                                      note_go b (ins x y) = Some l
                          end ->
                match option_map (String a) (note_go b (orig x y)) with
                | None => option_map (String a) (note_go b (ins x y)) = None
                | Some l => String.length l < S (String.length x) ->
                            option_map (String a) (note_go b (ins x y)) = Some l
                end).
    { intros b H. destruct (note_go b (orig x y)) as [l|]; cbn [option_map] in *.
      - intros L. cbn [String.length] in L. rewrite H by lia. reflexivity.
      - rewrite H. reflexivity. }
    destruct e; [apply G, IH, Hp|]. destruct (is_bslash a); [apply G, IH, Hp|].
    destruct (Ascii.eqb a rbrack); [intros L; reflexivity|apply G, IH, Hp].
Qed.

(* What the attribute machine does next depends only on its state. *)
Local Lemma astep_st : forall p q a,
  ap_st p = ap_st q -> ap_st (astep p a) = ap_st (astep q a).
Proof.
  intros [sp tp kp ap] [sq tq kq aq] a E. cbn [ap_st] in E. subst sq.
  unfold astep. cbn [ap_st].
  destruct sp; repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    reflexivity.
Qed.

Local Lemma spec_go_st : forall s p q,
  ap_st p = ap_st q -> spec_go p s = None -> spec_go q s = None.
Proof.
  induction s as [|a s IH]; intros p q E H; [reflexivity|]. cbn [spec_go] in *.
  pose proof (astep_st p q a E) as E'.
  unfold ap_failed, ap_done in *. rewrite <- E'.
  destruct (spec_go (astep p a) s) as [[b0 a0]|] eqn:G.
  - destruct (ap_st (astep p a)); try discriminate H; reflexivity.
  - rewrite (IH _ _ E' G). destruct (ap_st (astep p a)); try discriminate H; reflexivity.
Qed.

(* One byte of an attribute spec: outside a quoted value or a comment the
   byte fails the machine, as the backslash does, and inside one the
   backslash and the byte leave it where the byte alone does. *)
Local Lemma astep_ins : forall p, ap_st p <> ADone -> ap_st p <> AFail ->
  (ap_failed (astep p c) = true /\ ap_failed (astep p bslash) = true)
  \/ (ap_failed (astep p bslash) = false /\ ap_done (astep p bslash) = false
      /\ ap_failed (astep p c) = false /\ ap_done (astep p c) = false
      /\ ap_st (astep (astep p bslash) c) = ap_st (astep p c)).
Proof.
  intros [st tk ky at'] H1 H2. cbn [ap_st] in H1, H2.
  destruct st; try contradiction; bytes; first [left; split; reflexivity | right; repeat split].
Qed.

Lemma spec_go_ins : forall y x p,
  match spec_go p (orig x y) with
  | None => spec_go p (ins x y) = None
  | Some (b, a) => String.length b < String.length x -> spec_go p (ins x y) = Some (b, a)
  end.
Proof.
  intros y x. induction x as [|a x IH]; intros p.
  - cbn [append String.length].
    destruct (spec_go p (String c y)) as [[b a]|] eqn:G; [intros L; lia|].
    destruct (ap_st p) eqn:Sp.
    all: try (cbn [spec_go]; unfold astep at 1; rewrite Sp; cbn [spec_go] in G; unfold astep in G;
              rewrite Sp in G; unfold ap_failed, ap_done in *; rewrite Sp in *;
              first [reflexivity|discriminate G]).
    all: destruct (astep_ins p ltac:(congruence) ltac:(congruence))
      as [[F1 F2]|(F1 & D1 & F2 & D2 & E)].
    all: cbn [spec_go] in G |- *.
    all: try (rewrite F2; reflexivity).
    all: rewrite F1, D1; cbn iota; rewrite F2, D2 in G; cbn iota in G.
    all: unfold ap_failed, ap_done in *; rewrite E.
    all: destruct (ap_st (astep p c)) eqn:Sc; try discriminate F2; try discriminate D2.
    all: destruct (spec_go (astep p c) y) as [[? ?]|] eqn:G'; try discriminate G.
    all: erewrite spec_go_st; [reflexivity| |exact G']; rewrite E, Sc; reflexivity.
  - cbn [append String.length spec_go].
    destruct (ap_failed (astep p a)); [reflexivity|].
    destruct (ap_done (astep p a)); [intros _; reflexivity|].
    specialize (IH (astep p a)).
    destruct (spec_go (astep p a) (orig x y)) as [[b a0]|].
    + intros L. cbn [String.length] in L. rewrite IH by lia. reflexivity.
    + rewrite IH. reflexivity.
Qed.

(* Runs that neither byte continues. *)
Lemma symbol_run_ins : forall y x,
  symbol_run (ins x y) = symbol_run (orig x y) /\ symbol_run (orig x y) <= String.length x.
Proof.
  intros y x. induction x as [|a x IH]; cbn [append symbol_run String.length].
  - bytes; split; reflexivity.
  - destruct (symbol_char a); [destruct IH as [-> L]; split; [reflexivity|lia]|split; [reflexivity|lia]].
Qed.

Lemma run_of_ins : forall d y x,
  Ascii.eqb c d = false -> Ascii.eqb bslash d = false ->
  run_of d (ins x y) = run_of d (orig x y) /\ run_of d (orig x y) <= String.length x.
Proof.
  intros d y x H1 H2. induction x as [|a x IH]; cbn [append run_of String.length].
  - rewrite H1, H2. split; reflexivity.
  - destruct (Ascii.eqb a d); [destruct IH as [-> L]; split; [reflexivity|lia]|split; [reflexivity|lia]].
Qed.

Lemma dollar_run_ins : forall y x,
  dollar_run (ins x y) = dollar_run (orig x y) /\ dollar_run (orig x y) <= String.length x.
Proof.
  intros y x. induction x as [|a x IH]; cbn [append dollar_run String.length].
  - bytes; split; reflexivity.
  - destruct (Ascii.eqb a dollar); [destruct IH as [-> L]; split; [reflexivity|lia]|split; [reflexivity|lia]].
Qed.

Lemma tick_run_ins : forall y x,
  tick_run (ins x y) = tick_run (orig x y) /\ tick_run (orig x y) <= String.length x.
Proof.
  intros y x. induction x as [|a x IH]; cbn [append tick_run String.length].
  - bytes; split; reflexivity.
  - destruct (is_tick a); [destruct IH as [-> L]; split; [reflexivity|lia]|split; [reflexivity|lia]].
Qed.

Lemma ws_run_ins : forall y x, ws_run (ins x y) = ws_run (orig x y).
Proof.
  intros y x. induction x as [|a x IH]; cbn [append ws_run].
  - rewrite c_not_ws. reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* The rest of the line: the same, or blank in neither. *)
Lemma line_rest_ins : forall y x,
  line_rest (ins x y) = line_rest (orig x y)
  \/ (is_blank (line_rest (orig x y)) = false /\ is_blank (line_rest (ins x y)) = false).
Proof.
  intros y x. induction x as [|a x IH]; cbn [append line_rest].
  - right. rewrite c_not_nl. cbn [is_blank]. rewrite c_not_ws. split; reflexivity.
  - destruct (Ascii.eqb a nl_char); [left; reflexivity|].
    destruct IH as [->|[B1 B2]]; [left; reflexivity|right].
    cbn [is_blank]. rewrite B1, B2, !andb_false_r. split; reflexivity.
Qed.

Lemma get_ins : forall y x n, n < String.length x -> get n (ins x y) = get n (orig x y).
Proof.
  intros y x. induction x as [|a x IH]; intros n L; cbn [String.length] in L; [lia|].
  destruct n; [reflexivity|]. cbn [append get]. apply IH. lia.
Qed.

Lemma prefix_ins : forall d w y x,
  Ascii.eqb d c = false -> Ascii.eqb d bslash = false ->
  prefix (chars d w) (ins x y) = prefix (chars d w) (orig x y).
Proof.
  intros d w y. induction w as [|w IH]; intros x H1 H2; [destruct x; reflexivity|].
  destruct x as [|a x]; cbn [chars append prefix].
  - destruct (ascii_dec d bslash) as [E|_]; [subst; rewrite Ascii.eqb_refl in H2; discriminate|].
    destruct (ascii_dec d c) as [E|_]; [subst; rewrite Ascii.eqb_refl in H1; discriminate|].
    reflexivity.
  - destruct (ascii_dec d a); [apply IH; assumption|reflexivity].
Qed.

(* An autolink candidate: what its scan reads past the byte. *)
Local Lemma auto_go_ins : forall y x,
  (exists src st, auto_go (orig x y) = (src, st) /\ String.length src < String.length x
                  /\ auto_go (ins x y) = (src, st))
  \/ (exists z st, auto_go (orig x y) = ((x ++ z)%string, st)
      /\ auto_go (ins x y) = ((x ++ String bslash z)%string, st)
      /\ (z = EmptyString -> st = Some c)
      /\ (forall a z', z = String a z' -> a = c)).
Proof.
  intros y x. induction x as [|a x IH]; cbn [append auto_go].
  - right. assert (Hb : auto_stop bslash = false) by reflexivity. rewrite Hb.
    destruct (auto_stop c) eqn:S.
    + exists EmptyString, (Some c). repeat split; [intros; discriminate].
    + destruct (auto_go y) as [src st]. exists (String c src), st.
      repeat split; [intros E; discriminate E|intros a z' E; injection E as -> _; reflexivity].
  - destruct (auto_stop a).
    + left. exists EmptyString, (Some a). repeat split. cbn [String.length]. lia.
    + destruct IH as [(src & st & E1 & L & E2)|(z & st & E1 & E2 & Z1 & Z2)].
      * left. exists (String a src), st. rewrite E1, E2. repeat split. cbn [String.length]. lia.
      * right. exists z, st. rewrite E1, E2. repeat split; assumption.
Qed.

Local Lemma no_ws_bslash : forall x w, no_ws (x ++ String bslash w) = no_ws (x ++ w).
Proof.
  induction x as [|a x IH]; intros w; [reflexivity|]. cbn [append no_ws]. rewrite IH. reflexivity.
Qed.

Local Lemma no_char_bslash : forall d x w, Ascii.eqb bslash d = false ->
  no_char d (x ++ String bslash w) = no_char d (x ++ w).
Proof.
  intros d x w H. induction x as [|a x IH]; [cbn [append no_char]; rewrite H; reflexivity|].
  cbn [append no_char]. rewrite IH. reflexivity.
Qed.

Local Lemma auto_kind_ins : forall z x,
  auto_kind_ok (ins x z) = auto_kind_ok (orig x z).
Proof.
  intros z x. unfold auto_kind_ok, auto_email. f_equal.
  - generalize (@None ascii) as pv. induction x as [|a x IH]; intros pv.
    + cbn [append]. destruct pv as [p|]; cbn; bytes; reflexivity.
    + cbn [append]. destruct pv as [p|]; cbn - [append]; rewrite ?IH;
        [destruct (_ && _)%bool|]; rewrite ?IH; reflexivity.
  - induction x as [|a x IH].
    + reflexivity.
    + destruct x as [|b x]; cbn [append] in *.
      * bytes; reflexivity.
      * cbn. destruct (_ && _)%bool; [reflexivity|exact IH].
Qed.

Lemma auto_tok_ins : forall y x,
  auto_tok (ins x y) = auto_tok (orig x y) \/ S (String.length x) < snd (auto_tok (orig x y)).
Proof.
  intros y x. unfold auto_tok.
  destruct (auto_go_ins y x) as [(src & st & E1 & L & E2)|(z & st & E1 & E2 & Z1 & Z2)].
  - left. rewrite E1, E2. reflexivity.
  - rewrite E1, E2.
    destruct st as [g|]; [|left; reflexivity].
    destruct (Ascii.eqb g gt) eqn:G; [|left; reflexivity].
    destruct z as [|a z].
    { specialize (Z1 eq_refl). injection Z1 as ->. bytes; discriminate G. }
    rewrite (Z2 a z eq_refl) in *.
    destruct (auto_body_ok (x ++ String c z) && auto_kind_ok (x ++ String c z))%bool eqn:Ok.
    + right. cbn [andb]. rewrite Ok. cbn [snd]. rewrite length_append. cbn [String.length]. lia.
    + left.
      assert (Bd : auto_body_ok (ins x z) = auto_body_ok (orig x z)).
      { unfold auto_body_ok, auto_region.
        rewrite no_ws_bslash, !no_char_bslash by reflexivity. destruct x; reflexivity. }
      rewrite Bd, auto_kind_ins. cbn [andb]. rewrite Ok. reflexivity.
Qed.

(* A verbatim: its closing run is found in both, or it reads past the
   byte. *)
Lemma verb_go_ins : forall n y x run,
  verb_go n run (ins x y) = verb_go n run (orig x y)
  \/ String.length x < snd (fst (verb_go n run (orig x y))).
Proof.
  intros n y x. induction x as [|a x IH]; intros run; cbn [append verb_go].
  - assert (Hb : is_tick bslash = false) by reflexivity. rewrite Hb.
    assert (Ht : is_tick c = false) by (bytes; reflexivity). rewrite Ht.
    destruct (Nat.eqb run n); [left; reflexivity|right].
    destruct (verb_go n 0 y) as [[b l] cl]. cbn [String.length fst snd]. lia.
  - destruct (is_tick a).
    + destruct (IH (S run)) as [E|L].
      * left. rewrite E. reflexivity.
      * right. destruct (verb_go n (S run) (orig x y)) as [[b l] cl]. cbn [String.length fst snd] in *. lia.
    + destruct (Nat.eqb run n); [left; reflexivity|].
      destruct (IH 0) as [E|L].
      * left. rewrite E. reflexivity.
      * right. destruct (verb_go n 0 (orig x y)) as [[b l] cl]. cbn [String.length fst snd] in *. lia.
Qed.

Lemma fmt_go_ins : forall y x,
  fmt_go (ins x y) = fmt_go (orig x y)
  \/ exists f, fmt_go (orig x y) = Some f /\ String.length x <= String.length f.
Proof.
  intros y x. induction x as [|a x IH]; cbn [append fmt_go].
  - assert (R1 : Ascii.eqb c rbrace = false) by (bytes; reflexivity).
    assert (R2 : (raw_stop c || Ascii.eqb c nl_char)%bool = false) by (bytes; reflexivity).
    assert (B1 : Ascii.eqb bslash rbrace = false) by reflexivity.
    assert (B2 : (raw_stop bslash || Ascii.eqb bslash nl_char)%bool = false) by reflexivity.
    rewrite R1, R2, B1, B2.
    destruct (fmt_go y) as [f|]; cbn [option_map].
    + right. exists (String c f). split; [reflexivity|cbn [String.length]; lia].
    + left. reflexivity.
  - destruct (Ascii.eqb a rbrace); [left; reflexivity|].
    destruct (raw_stop a || Ascii.eqb a nl_char)%bool; [left; reflexivity|].
    destruct IH as [E|(f & E & L)].
    + left. rewrite E. reflexivity.
    + right. rewrite E. exists (String a f). split; [reflexivity|cbn [String.length]; lia].
Qed.

Lemma raw_spec_ins : forall y x,
  raw_spec (ins x y) = raw_spec (orig x y)
  \/ exists f, raw_spec (orig x y) = Some f /\ String.length x < S (S (S (String.length f))).
Proof.
  intros y x. destruct x as [|b [|e x]]; cbn [append raw_spec].
  - left. assert (L1 : Ascii.eqb c lbrace = false) by (bytes; reflexivity).
    rewrite L1. destruct y; reflexivity.
  - left. destruct (Ascii.eqb b lbrace); [|reflexivity].
    assert (Hc' : Ascii.eqb c eqchar = false) by (bytes; reflexivity). rewrite Hc'. reflexivity.
  - destruct (Ascii.eqb b lbrace && Ascii.eqb e eqchar)%bool; [|left; reflexivity].
    destruct (fmt_go_ins y x) as [E|(f & E & L)].
    + left. rewrite E. reflexivity.
    + right. rewrite E.
      destruct f as [|a f];
        [cbn [String.length] in L; destruct x; [|cbn [String.length] in L; lia]|].
      * cbn [append fmt_go] in E. exfalso. revert E.
        bytes; cbn; destruct (fmt_go y); discriminate.
      * exists (String a f). split; [reflexivity|cbn [String.length] in *; lia].
Qed.

Lemma sdrop_app_le : forall n x w, n <= String.length x -> sdrop n (x ++ w) = (sdrop n x ++ w)%string.
Proof.
  induction n as [|n IH]; intros x w L; [reflexivity|].
  destruct x as [|a x]; cbn [String.length] in L; [lia|]. cbn [append sdrop]. apply IH. lia.
Qed.

Lemma sdrop_len_app : forall x w, sdrop (String.length x) (x ++ w) = w.
Proof. induction x as [|a x IH]; intros w; [reflexivity|]. exact (IH w). Qed.

Lemma verb_tok_ins : forall pre y x,
  verb_tok pre (ins x y) = verb_tok pre (orig x y)
  \/ String.length x < snd (verb_tok pre (orig x y)).
Proof.
  intros pre y x. unfold verb_tok.
  destruct (tick_run_ins y x) as [-> Ln].
  set (n := tick_run (orig x y)) in *.
  rewrite !sdrop_app_le by exact Ln.
  destruct (verb_go_ins n y (sdrop n x) 0) as [E|L].
  - rewrite E. destruct (verb_go n 0 (orig (sdrop n x) y)) as [[b u] cl] eqn:G.
    destruct (cl && Nat.eqb pre 0 && raw_inline_enabled)%bool; [|left; reflexivity].
    destruct (Nat.le_gt_cases (n + u) (String.length x)) as [Lu|Lu].
    + rewrite !sdrop_app_le by exact Lu.
      destruct (raw_spec_ins y (sdrop (n + u) x)) as [R|(f & R & Lf)].
      * left. rewrite R. reflexivity.
      * right. rewrite R. cbn [snd]. rewrite sdrop_length in Lf. lia.
    + right. destruct (raw_spec (sdrop (n + u) (orig x y))); cbn [snd]; lia.
  - right. rewrite sdrop_length in L.
    destruct (verb_go n 0 (orig (sdrop n x) y)) as [[b u] cl]. cbn [fst snd] in L.
    destruct (if (cl && Nat.eqb pre 0 && raw_inline_enabled)%bool
              then raw_spec (sdrop (n + u) (orig x y)) else None); cbn [snd]; lia.
Qed.

Lemma dollar_tok_ins : forall y x,
  dollar_tok (ins x y) = dollar_tok (orig x y)
  \/ String.length x < snd (dollar_tok (orig x y)).
Proof.
  intros y x. unfold dollar_tok.
  destruct (dollar_run_ins y x) as [-> Lk].
  set (k := dollar_run (orig x y)) in *.
  destruct (Nat.eq_dec k (String.length x)) as [Ek|Ek].
  - left. rewrite Ek, !sdrop_len_app. cbn [starts_with].
    assert (Ht : Ascii.eqb c tick = false) by (bytes; reflexivity).
    rewrite Ht. destruct math_enabled; reflexivity.
  - rewrite !sdrop_app_le by lia.
    destruct (math_enabled && starts_with tick (orig (sdrop k x) y))%bool eqn:M.
    + assert (Ms : starts_with tick (ins (sdrop k x) y) = starts_with tick (orig (sdrop k x) y)).
      { destruct (sdrop k x) eqn:D; [|reflexivity].
        apply (f_equal String.length) in D. rewrite sdrop_length in D. cbn in D. lia. }
      rewrite Ms, M.
      destruct (verb_tok_ins k y (sdrop k x)) as [E|L].
      * left. rewrite E. reflexivity.
      * right. rewrite sdrop_length in L.
        destruct (verb_tok k (orig (sdrop k x) y)) as [t l]. cbn [snd] in *. lia.
    + left.
      assert (Ms : starts_with tick (ins (sdrop k x) y) = starts_with tick (orig (sdrop k x) y)).
      { destruct (sdrop k x) eqn:D; [|reflexivity].
        apply (f_equal String.length) in D. rewrite sdrop_length in D. cbn in D. lia. }
      rewrite Ms, M. reflexivity.
Qed.

Local Lemma dchar_ne_c : forall k, Ascii.eqb (dchar k) c = false.
Proof.
  intros k. destruct (Ascii.eqb (dchar k) c) eqn:E; [|reflexivity]. apply Ascii.eqb_eq in E.
  pose proof (dreserved_false _ (dchar_free k)) as R. rewrite E in R.
  destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  pose proof Hc as Hb; unfold text_byte in Hb.
  repeat (apply orb_true_iff in Hb as [Hb|Hb]); congruence.
Qed.

Lemma substring_app_le : forall k x w,
  k <= String.length x -> substring 0 k (x ++ w) = substring 0 k x.
Proof.
  induction k as [|k IH]; intros x w L; [destruct x, w; reflexivity|].
  destruct x as [|a x]; cbn [String.length] in L; [lia|].
  cbn [append substring]. f_equal. apply IH. lia.
Qed.

Lemma substring_length0 : forall s k,
  k <= String.length s -> String.length (substring 0 k s) = k.
Proof.
  induction s as [|a s IH]; intros [|k] H; cbn [String.length substring] in *; try lia;
    try reflexivity.
  f_equal. apply IH. lia.
Qed.

Lemma sym_tok_ins : forall y x, sym_tok (ins x y) = sym_tok (orig x y).
Proof.
  intros y x. unfold sym_tok.
  destruct (symbol_run_ins y x) as [-> L]. set (k := symbol_run (orig x y)) in *.
  destruct (Nat.eq_dec k (String.length x)) as [E|E].
  - rewrite E, !sdrop_len_app. cbn [starts_with].
    assert (H1 : Ascii.eqb c ":"%char = false) by (bytes; reflexivity).
    change (Ascii.eqb bslash ":"%char) with false. rewrite H1, !andb_false_r. reflexivity.
  - rewrite !sdrop_app_le, !substring_app_le by lia.
    destruct (sdrop k x) eqn:D; [|reflexivity].
    apply (f_equal String.length) in D. rewrite sdrop_length in D. cbn in D. lia.
Qed.

Lemma dots_tok_ins : forall y x, dots_tok (ins x y) = dots_tok (orig x y).
Proof.
  intros y x. unfold dots_tok.
  rewrite (proj1 (run_of_ins period y x ltac:(bytes; reflexivity) eq_refl)). reflexivity.
Qed.

Lemma dash_tok_ins : forall y x, dash_tok (ins x y) = dash_tok (orig x y).
Proof.
  intros y x. unfold dash_tok.
  destruct (run_of_ins hyphen y x ltac:(bytes; reflexivity) eq_refl) as [-> L].
  set (n := run_of hyphen (orig x y)) in *.
  assert (Sw : starts_with rbrace (sdrop n (ins x y)) = starts_with rbrace (sdrop n (orig x y))).
  { destruct (Nat.eq_dec n (String.length x)) as [E|E].
    - rewrite E, !sdrop_len_app. cbn [starts_with].
      assert (H1 : Ascii.eqb c rbrace = false) by (bytes; reflexivity). rewrite H1. reflexivity.
    - rewrite !sdrop_app_le by lia.
      destruct (sdrop n x) eqn:D; [|reflexivity].
      apply (f_equal String.length) in D. rewrite sdrop_length in D. cbn in D. lia. }
  rewrite Sw. reflexivity.
Qed.

Local Lemma prefix_chars_len : forall d w y x,
  Ascii.eqb d c = false -> prefix (chars d w) (orig x y) = true -> w <= String.length x.
Proof.
  intros d w y. induction w as [|w IH]; intros x H P; [lia|].
  destruct x as [|a x]; cbn [chars append prefix String.length] in *.
  - destruct (ascii_dec d c) as [E|_]; [subst; rewrite Ascii.eqb_refl in H; discriminate|].
    discriminate P.
  - destruct (ascii_dec d a); [|discriminate P]. specialize (IH x H P). lia.
Qed.

Lemma delim_tok_ins : forall prev a y x,
  delim_tok prev a (ins (String a x) y) = delim_tok prev a (orig (String a x) y).
Proof.
  intros prev a y x. unfold delim_tok.
  destruct (dstyle_of a) as [k|]; [|reflexivity].
  pose proof (dchar_ne_c k) as H1.
  assert (H2 : Ascii.eqb (dchar k) bslash = false) by exact (proj1 (dreserved_false _ (dchar_free k))).
  unfold dtoken. rewrite (prefix_ins (dchar k) (dwidth k) y (String a x) H1 H2).
  destruct (prefix (chars (dchar k) (dwidth k)) (orig (String a x) y)) eqn:P; [|reflexivity].
  pose proof (prefix_chars_len _ _ _ _ H1 P) as Lw.
  destruct (Nat.eq_dec (dwidth k) (String.length (String a x))) as [E|E].
  - assert (G1 : get (dwidth k) (orig (String a x) y) = Some c)
      by (rewrite E; clear; generalize (String a x); induction s; [reflexivity|exact IHs]).
    assert (G2 : get (dwidth k) (ins (String a x) y) = Some bslash)
      by (rewrite E; clear; generalize (String a x); induction s; [reflexivity|exact IHs]).
    rewrite G1, G2. bytes; reflexivity.
  - rewrite get_ins by lia. reflexivity.
Qed.

Lemma lbrace_tok_ins : forall y x,
  lbrace_tok (ins x y) = lbrace_tok (orig x y) \/ S (String.length x) < snd (lbrace_tok (orig x y)).
Proof.
  intros y x. unfold lbrace_tok.
  assert (Sty : match ins x y with String d _ => dstyle_of d | EmptyString => None end
                = match orig x y with String d _ => dstyle_of d | EmptyString => None end).
  { destruct x as [|d x]; [|reflexivity]. cbn [append]. rewrite c_style, bslash_style. reflexivity. }
  rewrite Sty.
  destruct (match orig x y with String d _ => dstyle_of d | EmptyString => None end) as [k|] eqn:K.
  - left. destruct x as [|d x]; [cbn in K; rewrite c_style in K; discriminate K|].
    unfold dtoken.
    rewrite (prefix_ins (dchar k) (dwidth k) y (String d x) (dchar_ne_c k)
               (proj1 (dreserved_false _ (dchar_free k)))).
    reflexivity.
  - unfold spec_at. destruct inline_attrs_enabled; [|left; reflexivity].
    pose proof (spec_go_ins y x ap_init) as G.
    destruct (spec_go ap_init (orig x y)) as [[b a]|].
    + destruct (Nat.lt_ge_cases (String.length b) (String.length x)) as [L|L].
      * left. rewrite (G L). reflexivity.
      * right. cbn [snd]. lia.
    + left. rewrite G. reflexivity.
Qed.

(* A footnote reference after a `[`. *)
Lemma note_at_ins : forall y x,
  (c = rbrack -> esc_after false x = false) ->
  note_at (ins x y) = note_at (orig x y)
  \/ exists l, note_at (orig x y) = Some l /\ String.length x < S (S (String.length l)).
Proof.
  intros y x Hp. destruct x as [|d x]; cbn [append note_at].
  - left. assert (H1 : Ascii.eqb c hat = false) by (bytes; reflexivity).
    rewrite H1. destruct notes_enabled; reflexivity.
  - destruct (notes_enabled && Ascii.eqb d hat)%bool eqn:N; [|left; reflexivity].
    apply andb_true_iff in N as [_ N]. apply Ascii.eqb_eq in N. subst d.
    assert (Hp' : c = rbrack -> esc_after false x = false) by exact Hp.
    pose proof (note_go_ins y x false Hp') as G.
    destruct (note_go false (orig x y)) as [l|].
    + destruct (Nat.lt_ge_cases (String.length l) (String.length x)) as [L|L].
      * left. exact (G L).
      * right. exists l. split; [reflexivity|cbn [String.length]; lia].
    + left. exact G.
Qed.

Lemma lbrack_tok_ins : forall y x,
  (c = rbrack -> esc_after false x = false) ->
  lbrack_tok (ins x y) = lbrack_tok (orig x y) \/ S (String.length x) < snd (lbrack_tok (orig x y)).
Proof.
  intros y x Hp. unfold lbrack_tok.
  destruct (note_at_ins y x Hp) as [E|(l & E & L)].
  - left. rewrite E. reflexivity.
  - right. rewrite E. cbn [snd]. lia.
Qed.

Lemma esc_tok_ins : forall y x,
  esc_tok (ins x y) = esc_tok (orig x y) \/ S (String.length x) < snd (esc_tok (orig x y)).
Proof.
  intros y x. destruct x as [|d x].
  - right. unfold esc_tok. cbn [append line_rest]. rewrite c_not_nl. cbn [is_blank].
    rewrite c_not_ws. cbn [andb snd]. cbn [String.length]. lia.
  - left. unfold esc_tok.
    destruct (line_rest_ins y (String d x)) as [E|[B1 B2]].
    + rewrite E, (ws_run_ins y (String d x)). reflexivity.
    + rewrite B1, B2, (ws_run_ins y (String d x)). reflexivity.
Qed.

(* A `]` whose region reaches past `n` bytes. *)
Definition closer_over (t : token) (n : nat) : Prop :=
  match t with
  | TClose _ r | TSpan r _ => n < S (S (S (String.length r)))
  | _ => False
  end.

(* A `]` read alone: a closer, or text. *)
Definition text_closer (o : option (token * nat)) : Prop :=
  match o with
  | Some ((TClose _ _ | TSpan _ _), 1) => True
  | Some (TText d, 1) => d = rbrack
  | _ => False
  end.

Lemma bang_tok_ins : forall y x,
  (c = rbrack -> esc_after false x = false) ->
  bang_tok (ins x y) = bang_tok (orig x y)
  \/ S (String.length x) < snd (bang_tok (orig x y))
  \/ (bang_tok (orig x y) = (TText bang, 1)
      /\ exists x' lab l2, x = String lbrack x' /\ lbrack_tok (orig x' y) = (TNote lab, l2)
                           /\ String.length x < l2).
Proof.
  intros y x Hp. unfold bang_tok. destruct x as [|d x]; cbn [append starts_with].
  - change (Ascii.eqb bslash lbrack) with false.
    destruct (Ascii.eqb c lbrack); [|left; reflexivity].
    cbn [sdrop]. destruct (note_at y); [left; reflexivity|right; left; cbn [snd String.length]; lia].
  - destruct (Ascii.eqb d lbrack) eqn:D; [|left; reflexivity].
    apply Ascii.eqb_eq in D. subst d. cbn [sdrop].
    assert (Hp' : c = rbrack -> esc_after false x = false) by exact Hp.
    destruct (note_at_ins y x Hp') as [E|(l & E & L)].
    + left. rewrite E. reflexivity.
    + right; right. rewrite E. split; [reflexivity|].
      exists x, l, (S (S (S (String.length l)))). split; [reflexivity|].
      split; [unfold lbrack_tok; rewrite E; reflexivity|cbn [String.length]; lia].
Qed.

Lemma rbrack_tok_ins : forall y x,
  (c = rbrack -> esc_after false x = false) ->
  rbrack_tok (ins x y) = rbrack_tok (orig x y)
  \/ (closer_over (fst (rbrack_tok (orig x y))) (S (String.length x))
      /\ text_closer (Some (rbrack_tok (ins x y)))).
Proof.
  intros y x Hp. unfold rbrack_tok. cbv zeta. destruct x as [|d x]; cbn [append].
  - change (Ascii.eqb bslash lparen) with false. change (Ascii.eqb bslash lbrack) with false.
    change (Ascii.eqb bslash lbrace) with false. cbn iota.
    rewrite (proj1 c_not_paren).
    assert (H2 : Ascii.eqb c lbrace = false) by (bytes; reflexivity). rewrite H2.
    destruct (Ascii.eqb c lbrack); [|left; reflexivity].
    destruct (label_close false 0 y); [right|left; reflexivity].
    cbn [fst closer_over text_closer String.length]. split; [lia|reflexivity].
  - destruct (Ascii.eqb d lparen) eqn:D1.
    { pose proof (dest_close_ins y x false 0 0) as E. cbn [Nat.add] in E. rewrite E.
      destruct (dest_close false 0 0 (orig x y)) as [j|] eqn:J; [|left; reflexivity].
      pose proof (dest_close_bound _ _ _ _ _ J) as Bj. rewrite length_append in Bj.
      cbn [String.length] in Bj.
      cbn [option_map]. destruct (Nat.ltb j (String.length x)) eqn:L.
      - left. apply Nat.ltb_lt in L. rewrite !substring_app_le by lia. reflexivity.
      - right. apply Nat.ltb_ge in L. cbn [fst closer_over text_closer String.length].
        split; [|exact I]. rewrite substring_length0 by (rewrite length_append; cbn [String.length]; lia).
        lia. }
    destruct (Ascii.eqb d lbrack) eqn:D2.
    { apply Ascii.eqb_eq in D2. subst d.
      assert (Hp' : c = rbrack -> esc_after false x = false) by exact Hp.
      pose proof (label_close_ins y x false 0 Hp') as E.
      destruct (label_close false 0 (orig x y)) as [j|] eqn:J; [|rewrite E; left; reflexivity].
      pose proof (label_close_bound _ _ _ _ J) as Bj. rewrite length_append in Bj.
      cbn [String.length] in Bj.
      destruct (Nat.lt_ge_cases j (String.length x)) as [L|L].
      - left. rewrite (E L), !substring_app_le by lia. reflexivity.
      - right. cbn [fst closer_over String.length].
        split; [rewrite substring_length0 by (rewrite length_append; cbn [String.length]; lia); lia|].
        destruct (label_close false 0 (ins x y)); exact I + reflexivity. }
    destruct (Ascii.eqb d lbrace) eqn:D3; [|left; reflexivity].
    unfold spec_at. destruct inline_attrs_enabled; [|left; reflexivity].
    pose proof (spec_go_ins y x ap_init) as G.
    destruct (spec_go ap_init (orig x y)) as [[b a]|]; [|rewrite G; left; reflexivity].
    destruct (Nat.lt_ge_cases (String.length b) (String.length x)) as [L|L].
    + left. rewrite (G L). reflexivity.
    + right. cbn [fst closer_over String.length]. split; [lia|].
      destruct (spec_go ap_init (ins x y)) as [[? ?]|]; [exact I|reflexivity].
Qed.

(* A token that begins before the byte: the same in both strings, or it
   reads past the byte, as a token, as a `]` whose region does, or as a
   `!` whose `[` begins a footnote reference that does. *)
Lemma next_tok_ins : forall prev a x y,
  (c = rbrack -> esc_after false (String a x) = false) ->
  next_tok prev (ins (String a x) y) = next_tok prev (orig (String a x) y)
  \/ (exists t l, next_tok prev (orig (String a x) y) = Some (t, l) /\ S (String.length x) < l)
  \/ (exists t, next_tok prev (orig (String a x) y) = Some (t, 1)
      /\ closer_over t (S (String.length x)) /\ text_closer (next_tok prev (ins (String a x) y)))
  \/ (a = bang /\ next_tok prev (orig (String a x) y) = Some (TText bang, 1)
      /\ exists lab l2, next_tok (Some bang) (orig x y) = Some (TNote lab, l2)
                        /\ String.length x < l2).
Proof.
  intros prev a x y Hp.
  set (N := next_tok prev (orig (String a x) y)).
  set (N' := next_tok prev (ins (String a x) y)).
  assert (W : forall o o', N' = Some o' -> N = Some o ->
            o' = o \/ S (String.length x) < snd o ->
            N' = N \/ (exists t l, N = Some (t, l) /\ S (String.length x) < l)
            \/ (exists t, N = Some (t, 1) /\ closer_over t (S (String.length x)) /\ text_closer N')
            \/ (a = bang /\ N = Some (TText bang, 1) /\ exists lab l2,
                 next_tok (Some bang) (orig x y) = Some (TNote lab, l2)
                 /\ String.length x < l2)).
  { intros o o' -> -> [->|L]; [left; reflexivity|].
    right; left. destruct o as [t l]. exists t, l. split; [reflexivity|exact L]. }
  Local Ltac nt := unfold next_tok; cbn [append];
    repeat match goal with H : _ = _ |- _ => rewrite H end; reflexivity.
  destruct (Ascii.eqb a nl_char) eqn:G1; [left; unfold N, N'; nt|].
  destruct (is_bslash a) eqn:G2.
  { apply (W (esc_tok (orig x y)) (esc_tok (ins x y))); [unfold N'; nt|unfold N; nt|].
    destruct (esc_tok_ins y x) as [E|L]; [left; exact E|right; exact L]. }
  destruct (is_tick a) eqn:G3.
  { apply (W (verb_tok 0 (orig (String a x) y)) (verb_tok 0 (ins (String a x) y)));
      [unfold N'; nt|unfold N; nt|].
    destruct (verb_tok_ins 0 y (String a x)) as [E|L];
      [left; exact E|right; cbn [String.length] in L; exact L]. }
  destruct (Ascii.eqb a dollar) eqn:G4.
  { apply (W (dollar_tok (orig (String a x) y)) (dollar_tok (ins (String a x) y)));
      [unfold N'; nt|unfold N; nt|].
    destruct (dollar_tok_ins y (String a x)) as [E|L];
      [left; exact E|right; cbn [String.length] in L; exact L]. }
  destruct (Ascii.eqb a lt) eqn:G5.
  { apply (W (auto_tok (orig x y)) (auto_tok (ins x y))); [unfold N'; nt|unfold N; nt|].
    destruct (auto_tok_ins y x) as [E|L]; [left; exact E|right; exact L]. }
  destruct (Ascii.eqb a ":"%char) eqn:G6.
  { apply (W (sym_tok (orig x y)) (sym_tok (ins x y)));
      [unfold N'; nt|unfold N; nt|left; apply sym_tok_ins]. }
  destruct (Ascii.eqb a period) eqn:G7.
  { apply (W (dots_tok (orig (String a x) y)) (dots_tok (ins (String a x) y)));
      [unfold N'; nt|unfold N; nt|left; apply dots_tok_ins]. }
  destruct (Ascii.eqb a hyphen) eqn:G8.
  { apply (W (dash_tok (orig (String a x) y)) (dash_tok (ins (String a x) y)));
      [unfold N'; nt|unfold N; nt|left; apply dash_tok_ins]. }
  destruct (Ascii.eqb a bang) eqn:G9.
  { apply Ascii.eqb_eq in G9. subst a.
    assert (Hp' : c = rbrack -> esc_after false x = false) by exact Hp.
    destruct (bang_tok_ins y x Hp') as [E|[L|(E & x' & lab & l2 & -> & Lb & L)]].
    - apply (W (bang_tok (orig x y)) (bang_tok (ins x y))); [unfold N'; nt|unfold N; nt|left; exact E].
    - apply (W (bang_tok (orig x y)) (bang_tok (ins x y)));
        [unfold N'; nt|unfold N; nt|right; exact L].
    - right; right; right. split; [reflexivity|].
      split; [unfold N; unfold next_tok; cbn [append]; rewrite <- E; reflexivity|].
      exists lab, l2. split; [|exact L].
      cbn [append]. unfold next_tok. cbn - [lbrack_tok]. rewrite Lb. reflexivity. }
  destruct (Ascii.eqb a lbrack) eqn:G10.
  { apply Ascii.eqb_eq in G10. subst a.
    assert (Hp' : c = rbrack -> esc_after false x = false) by exact Hp.
    apply (W (lbrack_tok (orig x y)) (lbrack_tok (ins x y))); [unfold N'; nt|unfold N; nt|].
    destruct (lbrack_tok_ins y x Hp') as [E|L]; [left; exact E|right; exact L]. }
  destruct (Ascii.eqb a rbrack) eqn:G11.
  { apply Ascii.eqb_eq in G11. subst a.
    assert (Hp' : c = rbrack -> esc_after false x = false) by exact Hp.
    assert (E1 : N = Some (rbrack_tok (orig x y))) by (unfold N; nt).
    assert (E2 : N' = Some (rbrack_tok (ins x y))) by (unfold N'; nt).
    destruct (rbrack_tok_ins y x Hp') as [E|[C T']].
    - left. rewrite E1, E2, E. reflexivity.
    - right; right; left. exists (fst (rbrack_tok (orig x y))). rewrite E2.
      split; [rewrite E1; reflexivity|split; assumption]. }
  destruct (Ascii.eqb a lbrace) eqn:G12.
  { apply (W (lbrace_tok (orig x y)) (lbrace_tok (ins x y))); [unfold N'; nt|unfold N; nt|].
    destruct (lbrace_tok_ins y x) as [E|L]; [left; exact E|right; exact L]. }
  left. unfold N, N'. unfold next_tok. cbn [append].
  rewrite G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12.
  exact (f_equal Some (delim_tok_ins prev a y x)).
Qed.

End Insert.
(*
Where a token ends
==================

A token never ends in a backslash that escapes the byte after it, but a
hard break written as a lone backslash, which a newline or the end
follows.  So a byte the chain reaches is not escaped.
*)

Lemma esc_after_app : forall e u v, esc_after e (u ++ v) = esc_after (esc_after e u) v.
Proof. intros e u. revert e. induction u as [|a u IH]; intros e v; [reflexivity|]. apply IH. Qed.

Local Lemma esc_after_last : forall e u d v,
  is_bslash d = false -> esc_after e (substring 0 (S (String.length u)) (u ++ String d v)) = false.
Proof.
  intros e u d v H. replace (substring 0 (S (String.length u)) (u ++ String d v))
    with (u ++ String d EmptyString)%string.
  - rewrite esc_after_app. cbn [esc_after]. rewrite H. destruct (esc_after e u); reflexivity.
  - clear. induction u as [|a u IH]; [destruct v; reflexivity|]. cbn [append String.length substring].
    rewrite <- IH. reflexivity.
Qed.

(* What a token at the start of `w`, `l` bytes long, leaves. *)
Definition ends_ok (w : string) (l : nat) : Prop :=
  esc_after false (substring 0 l w) = false \/ get l w = Some nl_char \/ get l w = None.

Local Lemma ends_last : forall u d v l,
  is_bslash d = false -> l = S (String.length u) -> ends_ok (u ++ String d v) l.
Proof. intros u d v l H ->. left. apply esc_after_last, H. Qed.

Local Lemma run_of_split : forall d w n, n < run_of d w ->
  exists u v, w = (u ++ String d v)%string /\ String.length u = n.
Proof.
  intros d w. induction w as [|a w IH]; intros n H; cbn [run_of] in H; [lia|].
  destruct (Ascii.eqb a d) eqn:E; [|lia]. apply Ascii.eqb_eq in E. subst a.
  destruct n as [|n].
  - exists EmptyString, w. split; reflexivity.
  - destruct (IH n ltac:(lia)) as (u & v & -> & L). exists (String d u), v.
    split; [reflexivity|cbn [String.length]; lia].
Qed.

Local Lemma dollar_run_split : forall w n, n < dollar_run w ->
  exists u v, w = (u ++ String dollar v)%string /\ String.length u = n.
Proof.
  intros w. induction w as [|a w IH]; intros n H; cbn [dollar_run] in H; [lia|].
  destruct (Ascii.eqb a dollar) eqn:E; [|lia]. apply Ascii.eqb_eq in E. subst a.
  destruct n as [|n].
  - exists EmptyString, w. split; reflexivity.
  - destruct (IH n ltac:(lia)) as (u & v & -> & L). exists (String dollar u), v.
    split; [reflexivity|cbn [String.length]; lia].
Qed.

Local Lemma sdrop_split : forall k w d v, sdrop k w = String d v ->
  exists u, w = (u ++ String d v)%string /\ String.length u = k.
Proof.
  induction k as [|k IH]; intros w d v H.
  - exists EmptyString. split; [exact H|reflexivity].
  - destruct w as [|a w]; [discriminate H|]. destruct (IH w d v H) as (u & -> & L).
    exists (String a u). split; [reflexivity|cbn [String.length]; lia].
Qed.

Local Lemma prefix_chars_split : forall d n w, prefix (chars d (S n)) w = true ->
  exists u v, w = (u ++ String d v)%string /\ String.length u = n.
Proof.
  intros d n. induction n as [|n IH]; intros w H; destruct w as [|a w]; try discriminate H;
    cbn [chars prefix] in H; destruct (ascii_dec d a) as [<-|]; try discriminate H.
  - exists EmptyString, w. split; reflexivity.
  - destruct (IH w H) as (u & v & -> & L). exists (String d u), v.
    split; [reflexivity|cbn [String.length]; lia].
Qed.

Local Lemma verb_go_end : forall n s run, 0 < n ->
  match verb_go n run s with
  | (_, u, true) => (u = 0 /\ run = n)
                    \/ exists x v, s = (x ++ String tick v)%string /\ S (String.length x) = u
  | (_, u, false) => u = String.length s
  end.
Proof.
  intros n. induction s as [|a s IH]; intros run Hn; cbn [verb_go].
  - destruct (Nat.eqb run n) eqn:E; [left; split; [reflexivity|apply Nat.eqb_eq, E]|reflexivity].
  - destruct (is_tick a) eqn:Ta.
    + specialize (IH (S run) Hn). destruct (verb_go n (S run) s) as [[b u] [|]].
      * right. unfold is_tick in Ta. apply Ascii.eqb_eq in Ta. subst a.
        destruct IH as [[-> _]|(x & v & -> & L)].
        -- exists EmptyString, s. split; reflexivity.
        -- exists (String tick x), v. split; [reflexivity|cbn [String.length]; lia].
      * cbn [String.length]. lia.
    + destruct (Nat.eqb run n) eqn:E; [left; split; [reflexivity|apply Nat.eqb_eq, E]|].
      specialize (IH 0 Hn). destruct (verb_go n 0 s) as [[b u] [|]].
      * right. destruct IH as [[-> E0]|(x & v & -> & L)].
        -- lia.
        -- exists (String a x), v. split; [reflexivity|cbn [String.length]; lia].
      * cbn [String.length]. lia.
Qed.

Local Lemma tick_run_split : forall w, 0 < tick_run w ->
  exists u v, w = (u ++ String tick v)%string /\ S (String.length u) = tick_run w.
Proof.
  induction w as [|a w IH]; intros H; cbn [tick_run] in *; [lia|].
  destruct (is_tick a) eqn:Ta; [|lia]. unfold is_tick in Ta. apply Ascii.eqb_eq in Ta. subst a.
  destruct (tick_run w) eqn:E.
  - exists EmptyString, w. split; reflexivity.
  - destruct (IH ltac:(lia)) as (u & v & -> & L). exists (String tick u), v.
    split; [reflexivity|cbn [String.length]; lia].
Qed.

Lemma substring_sdrop_app : forall n w, (substring 0 n w ++ sdrop n w)%string = w.
Proof.
  induction n as [|n IH]; intros [|a w]; try reflexivity.
  cbn [substring sdrop append]. f_equal. apply IH.
Qed.

Lemma get_length : forall w, get (String.length w) w = None.
Proof. induction w as [|a w IH]; [reflexivity|exact IH]. Qed.

Local Lemma verb_tok_end : forall pre w t l, starts_with tick w = true ->
  verb_tok pre w = (t, l) -> ends_ok w l.
Proof.
  intros pre w t l Hs H. unfold verb_tok in H.
  set (n := tick_run w) in *.
  assert (Hn : 0 < n).
  { unfold n. destruct w as [|a w]; [discriminate|]. cbn in Hs |- *. unfold is_tick.
    rewrite Hs. lia. }
  pose proof (verb_go_end n (sdrop n w) 0 Hn) as V.
  destruct (verb_go n 0 (sdrop n w)) as [[b u] cl].
  destruct (if (cl && Nat.eqb pre 0 && raw_inline_enabled)%bool
            then raw_spec (sdrop (n + u) w) else None) as [f|] eqn:R.
  - injection H as <- <-.
    destruct (cl && Nat.eqb pre 0 && raw_inline_enabled)%bool; [|discriminate R].
    destruct (raw_spec_split _ _ R) as (_ & _ & rest & E).
    pose proof (sdrop_split (n + u) w lbrace _ E) as (u0 & Ew & Lu).
    rewrite Ew.
    replace (u0 ++ String lbrace (String eqchar (f ++ String rbrace rest)))%string
      with ((u0 ++ String lbrace (String eqchar f)) ++ String rbrace rest)%string
      by (rewrite append_assoc; reflexivity).
    apply ends_last; [reflexivity|]. rewrite length_append. cbn [String.length]. lia.
  - injection H as <- <-. destruct cl.
    + destruct V as [[_ E0]|(x & v & E & L)]; [lia|].
      destruct (tick_run_split w Hn) as (u1 & v1 & Ew1 & L1). fold n in L1.
      pose proof (eq_sym (substring_sdrop_app n w)) as Ew.
      rewrite Ew, E, <- append_assoc. apply ends_last; [reflexivity|].
      rewrite length_append, substring_length0; [lia|].
      rewrite Ew1, length_append. cbn [String.length]. lia.
    + right; right. rewrite V, sdrop_length.
      assert (n <= String.length w).
      { destruct (tick_run_split w Hn) as (u1 & v1 & -> & L1). fold n in L1.
        rewrite length_append. cbn [String.length]. lia. }
      replace (n + (String.length w - n)) with (String.length w) by lia.
      apply get_length.
Qed.

Local Lemma line_rest_split : forall r, exists v, r = (line_rest r ++ v)%string
  /\ (v = EmptyString \/ exists v', v = String nl_char v').
Proof.
  induction r as [|a r IH]; [exists EmptyString; split; [reflexivity|left; reflexivity]|].
  cbn [line_rest]. destruct (Ascii.eqb a nl_char) eqn:E.
  - apply Ascii.eqb_eq in E. subst a. exists (String nl_char r).
    split; [reflexivity|right; exists r; reflexivity].
  - destruct IH as (v & Ev & Hv). exists v. split; [cbn [append]; f_equal; exact Ev|exact Hv].
Qed.

Local Lemma ws_run_split : forall r, exists v, r = (ws_run r ++ v)%string.
Proof.
  induction r as [|a r IH]; [exists EmptyString; reflexivity|]. cbn [ws_run].
  destruct (is_ws a); [destruct IH as [v Ev]; exists v; cbn [append]; f_equal; exact Ev|].
  exists (String a r). reflexivity.
Qed.

Local Lemma ws_run_blank : forall r, is_blank (ws_run r) = true.
Proof.
  induction r as [|a r IH]; [reflexivity|]. cbn [ws_run].
  destruct (is_ws a) eqn:E; [cbn [is_blank]; rewrite E, IH; reflexivity|reflexivity].
Qed.

Local Lemma esc_after_blank : forall z, is_blank z = true -> esc_after false z = false.
Proof.
  induction z as [|a z IH]; intros H; [reflexivity|]. cbn [is_blank] in H.
  apply andb_true_iff in H as [Ha Hz]. cbn [esc_after].
  assert (B : is_bslash a = false).
  { unfold is_ws in Ha. unfold is_bslash.
    repeat (apply orb_true_iff in Ha as [Ha|Ha]); apply Ascii.eqb_eq in Ha; subst a; reflexivity. }
  rewrite B. exact (IH Hz).
Qed.

Local Lemma substring_self : forall u v, substring 0 (String.length u) (u ++ v) = u.
Proof.
  induction u as [|a u IH]; intros v; [destruct v; reflexivity|].
  cbn [String.length append substring]. f_equal. apply IH.
Qed.

Local Lemma esc_end : forall z v, is_blank z = true ->
  (z <> EmptyString \/ v = EmptyString \/ exists v', v = String nl_char v') ->
  ends_ok (String bslash (z ++ v)) (S (String.length z)).
Proof.
  intros z v Hb Hv. unfold ends_ok. cbn [substring]. rewrite substring_self.
  cbn [esc_after]. change (is_bslash bslash) with true.
  destruct z as [|d z].
  - right. destruct Hv as [N|[->|[v' ->]]]; [contradiction|right; reflexivity|left; reflexivity].
  - left. cbn [esc_after]. cbn [is_blank] in Hb. apply andb_true_iff in Hb as [_ Hz].
    exact (esc_after_blank z Hz).
Qed.

Local Lemma ends_ok_shift : forall u w l,
  esc_after false u = false -> ends_ok w l -> ends_ok (u ++ w) (String.length u + l).
Proof.
  intros u w l Hu H.
  assert (S1 : substring 0 (String.length u + l) (u ++ w) = (u ++ substring 0 l w)%string).
  { clear. induction u as [|a u IH]; [reflexivity|]. cbn [String.length append Nat.add substring].
    f_equal. exact IH. }
  assert (G : get (String.length u + l) (u ++ w) = get l w).
  { clear. induction u as [|a u IH]; [reflexivity|]. exact IH. }
  unfold ends_ok in *. rewrite S1, G, esc_after_app, Hu. exact H.
Qed.

Local Lemma ends_one : forall a r, is_bslash a = false -> ends_ok (String a r) 1.
Proof. intros a r B. exact (ends_last EmptyString a r 1 B eq_refl). Qed.

Local Lemma dollar_tok_end : forall w t l, starts_with dollar w = true ->
  dollar_tok w = (t, l) -> ends_ok w l.
Proof.
  intros w t l Hs H. unfold dollar_tok in H.
  remember (dollar_run w) as k eqn:Ek.
  assert (Hk : 0 < k).
  { subst k. destruct w as [|a w]; [discriminate|]. cbn in Hs |- *. rewrite Hs. lia. }
  destruct (dollar_run_split w (k - 1) ltac:(lia)) as (u & v & Ew & Lu).
  destruct (math_enabled && starts_with tick (sdrop k w))%bool eqn:M.
  - destruct (verb_tok k (sdrop k w)) as [t0 l0] eqn:V. injection H as <- <-.
    apply andb_true_iff in M as [_ M].
    pose proof (verb_tok_end k _ t0 l0 M V) as E0.
    assert (Lk : String.length (substring 0 k w) = k).
    { apply substring_length0. rewrite Ew, length_append. cbn [String.length]. lia. }
    assert (D : forall n z, n <= dollar_run z -> esc_after false (substring 0 n z) = false).
    { clear. intros n z. revert n. induction z as [|a z IH]; intros [|n] H; try reflexivity.
      cbn [dollar_run] in H. destruct (Ascii.eqb a dollar) eqn:E; [|cbn in H; lia].
      apply Ascii.eqb_eq in E. subst a. cbn [substring esc_after].
      change (is_bslash dollar) with false. apply IH. lia. }
    pose proof (ends_ok_shift (substring 0 k w) (sdrop k w) l0 (D k w ltac:(lia)) E0) as X.
    rewrite substring_sdrop_app, Lk in X. exact X.
  - injection H as <- <-. rewrite Ew. apply ends_last; [reflexivity|lia].
Qed.

Local Lemma auto_tok_end : forall r t l, auto_tok r = (t, l) -> ends_ok (String lt r) l.
Proof.
  intros r t l H. unfold auto_tok in H.
  destruct (auto_go r) as [src st] eqn:G.
  destruct (match st with Some c0 => Ascii.eqb c0 gt | None => false end
            && auto_body_ok src && auto_kind_ok src)%bool eqn:Ok.
  - injection H as <- <-. destruct st as [g|]; [|discriminate Ok].
    apply andb_true_iff in Ok as [Ok _]. apply andb_true_iff in Ok as [Eg _].
    apply Ascii.eqb_eq in Eg. subst g.
    destruct (auto_go_split r src (Some gt) G) as (_ & rest & Er & [[D _]|(c0 & r0 & D & -> & _)]);
      [discriminate D|]. injection D as <-.
    rewrite Er. change (String lt (src ++ String gt r0)) with ((String lt src) ++ String gt r0)%string.
    apply ends_last; reflexivity.
  - injection H as <- <-. apply ends_one. reflexivity.
Qed.

Local Lemma sym_tok_end : forall r t l, sym_tok r = (t, l) -> ends_ok (String ":"%char r) l.
Proof.
  intros r t l H. unfold sym_tok in H.
  destruct (Nat.ltb 0 (symbol_run r) && starts_with ":"%char (sdrop (symbol_run r) r))%bool eqn:Ok.
  - injection H as <- <-. apply andb_true_iff in Ok as [_ Ok].
    destruct (sdrop (symbol_run r) r) as [|d v] eqn:D; [discriminate Ok|].
    cbn [starts_with] in Ok. apply Ascii.eqb_eq in Ok. subst d.
    destruct (sdrop_split _ _ _ _ D) as (u & -> & Lu).
    change (String ":"%char (u ++ String ":"%char v)) with ((String ":"%char u) ++ String ":"%char v)%string.
    apply ends_last; [reflexivity|cbn [String.length]; lia].
  - injection H as <- <-. apply ends_one. reflexivity.
Qed.

Local Lemma run_tok_end : forall d w n, is_bslash d = false -> 0 < n -> n <= run_of d w ->
  ends_ok w n.
Proof.
  intros d w n B H1 H2. destruct (run_of_split d w (n - 1) ltac:(lia)) as (u & v & -> & L).
  apply ends_last; [exact B|lia].
Qed.

Local Lemma dots_tok_end : forall w t l, starts_with period w = true ->
  dots_tok w = (t, l) -> ends_ok w l.
Proof.
  intros w t l Hs H. unfold dots_tok in H. injection H as <- <-.
  apply (run_tok_end period); [reflexivity| |lia].
  destruct w as [|a w]; [discriminate|]. cbn in Hs |- *. rewrite Hs. lia.
Qed.

Local Lemma dash_tok_end : forall w t l, starts_with hyphen w = true ->
  dash_tok w = (t, l) -> ends_ok w l.
Proof.
  intros w t l Hs H. unfold dash_tok in H.
  remember (run_of hyphen w) as n eqn:En.
  assert (Hn : 0 < n).
  { subst n. destruct w as [|a w]; [discriminate|]. cbn in Hs |- *. rewrite Hs. lia. }
  destruct (dstyle_of hyphen) as [k|];
    [|injection H as <- <-; apply (run_tok_end hyphen); [reflexivity|lia|lia]].
  destruct (starts_with rbrace (sdrop n w) && Nat.leb (dwidth k) n)%bool eqn:Ok;
    [|injection H as <- <-; apply (run_tok_end hyphen); [reflexivity|lia|lia]].
  apply andb_true_iff in Ok as [Sb Le]. apply Nat.leb_le in Le.
  destruct (Nat.eqb n (dwidth k)) eqn:E.
  - injection H as <- <-.
    destruct (sdrop n w) as [|d v] eqn:D; [discriminate Sb|].
    cbn [starts_with] in Sb. apply Ascii.eqb_eq in Sb. subst d.
    destruct (sdrop_split _ _ _ _ D) as (u & -> & Lu). apply ends_last; [reflexivity|lia].
  - injection H as <- <-. apply Nat.eqb_neq in E.
    apply (run_tok_end hyphen); [reflexivity|lia|lia].
Qed.

Local Lemma bang_tok_end : forall r t l, bang_tok r = (t, l) -> ends_ok (String bang r) l.
Proof.
  intros r t l H. unfold bang_tok in H.
  destruct (starts_with lbrack r) eqn:S.
  - destruct (note_at (sdrop 1 r)); injection H as <- <-; [apply ends_one; reflexivity|].
    destruct r as [|d r]; [discriminate|]. cbn in S. apply Ascii.eqb_eq in S. subst d.
    exact (ends_last (String bang EmptyString) lbrack r 2 eq_refl eq_refl).
  - injection H as <- <-. apply ends_one. reflexivity.
Qed.

Local Lemma lbrack_tok_end : forall r t l, lbrack_tok r = (t, l) -> ends_ok (String lbrack r) l.
Proof.
  intros r t l H. unfold lbrack_tok in H.
  destruct (note_at r) as [lab|] eqn:N; injection H as <- <-; [|apply ends_one; reflexivity].
  destruct (note_at_split r lab N) as [v ->].
  change (String lbrack (String hat (lab ++ String rbrack v)))
    with ((String lbrack (String hat lab)) ++ String rbrack v)%string.
  apply ends_last; reflexivity.
Qed.

Local Lemma lbrace_tok_end : forall r t l, lbrace_tok r = (t, l) -> ends_ok (String lbrace r) l.
Proof.
  intros r t l H. unfold lbrace_tok in H.
  destruct (match r with String d _ => dstyle_of d | EmptyString => None end) as [k|] eqn:K.
  - destruct (prefix (dtoken k) r) eqn:P; injection H as <- <-; [|apply ends_one; reflexivity].
    unfold dtoken in P. destruct (dwidth k) as [|w] eqn:Wk; [destruct (dwidth_nonzero k Wk)|].
    destruct (prefix_chars_split _ _ _ P) as (u & v & -> & Lu).
    change (String lbrace (u ++ String (dchar k) v)) with ((String lbrace u) ++ String (dchar k) v)%string.
    apply ends_last; [exact (proj1 (dreserved_false _ (dchar_free k)))|cbn [String.length]; lia].
  - destruct (spec_at r) as [[b a]|] eqn:Sa; injection H as <- <-; [|apply ends_one; reflexivity].
    destruct (spec_at_split r b a Sa) as [v ->].
    change (String lbrace (b ++ String rbrace v)) with ((String lbrace b) ++ String rbrace v)%string.
    apply ends_last; reflexivity.
Qed.

Local Lemma delim_tok_end : forall prev a r t l, is_bslash a = false ->
  delim_tok prev a (String a r) = (t, l) -> ends_ok (String a r) l.
Proof.
  intros prev a r t l B H. unfold delim_tok in H.
  destruct (dstyle_of a) as [k|]; [|injection H as <- <-; apply ends_one, B].
  destruct (prefix (dtoken k) (String a r)) eqn:P; [|injection H as <- <-; apply ends_one, B].
  unfold dtoken in P. destruct (dwidth k) as [|w] eqn:Wk; [destruct (dwidth_nonzero k Wk)|].
  destruct (at_rbrace (get (S w) (String a r))) eqn:Rb.
  - injection H as <- <-.
    destruct (get (S w) (String a r)) as [g|] eqn:G; [|discriminate Rb].
    unfold at_rbrace in Rb. apply Ascii.eqb_eq in Rb. subst g.
    assert (Sd : sdrop (S w) (String a r) = String rbrace (sdrop (S (S w)) (String a r))).
    { clear -G. revert G. generalize (String a r). generalize (S w). clear.
      induction n as [|n IH]; intros [|x s] G; try discriminate G.
      - injection G as ->. reflexivity.
      - exact (IH s G). }
    destruct (sdrop_split _ _ _ _ Sd) as (u & Ew & Lu). rewrite Ew.
    apply ends_last; [reflexivity|lia].
  - injection H as <- <-.
    destruct (prefix_chars_split _ _ _ P) as (u & v & Ew & Lu). rewrite Ew.
    apply ends_last; [exact (proj1 (dreserved_false _ (dchar_free k)))|lia].
Qed.

Lemma next_tok_end : forall prev w t l, next_tok prev w = Some (t, l) -> ends_ok w l.
Proof.
  intros prev [|a r] t l H; [discriminate H|]. cbn [next_tok] in H. injection H as H.
  destruct (Ascii.eqb a nl_char) eqn:G1.
  { injection H as <- <-. apply ends_one. apply Ascii.eqb_eq in G1. subst a. reflexivity. }
  destruct (is_bslash a) eqn:G2.
  { unfold is_bslash in G2. apply Ascii.eqb_eq in G2. subst a. unfold esc_tok in H.
    destruct (line_rest_split r) as (v & Ev & Hv).
    destruct (is_blank (line_rest r)) eqn:B.
    { injection H as <- <-. rewrite Ev at 1. apply esc_end; [exact B|].
      destruct (line_rest r); [right; exact Hv|left; discriminate]. }
    destruct r as [|d r]; [discriminate B|].
    destruct (is_ws d) eqn:Wd.
    - injection H as <- <-. destruct (ws_run_split (String d r)) as [v' Ev'].
      rewrite Ev' at 1.
      change (if is_ws d then String d (ws_run r) else EmptyString) with (ws_run (String d r)).
      apply esc_end; [apply ws_run_blank|left; cbn [ws_run]; rewrite Wd; discriminate].
    - injection H as <- <-. left. destruct r; reflexivity. }
  destruct (is_tick a) eqn:G3.
  { exact (verb_tok_end 0 (String a r) t l ltac:(cbn [starts_with]; exact G3) H). }
  destruct (Ascii.eqb a dollar) eqn:G4.
  { exact (dollar_tok_end (String a r) t l ltac:(cbn [starts_with]; exact G4) H). }
  destruct (Ascii.eqb a lt) eqn:G5.
  { apply Ascii.eqb_eq in G5. subst a. exact (auto_tok_end r t l H). }
  destruct (Ascii.eqb a ":"%char) eqn:G6.
  { apply Ascii.eqb_eq in G6. subst a. exact (sym_tok_end r t l H). }
  destruct (Ascii.eqb a period) eqn:G7.
  { exact (dots_tok_end (String a r) t l ltac:(cbn [starts_with]; exact G7) H). }
  destruct (Ascii.eqb a hyphen) eqn:G8.
  { exact (dash_tok_end (String a r) t l ltac:(cbn [starts_with]; exact G8) H). }
  destruct (Ascii.eqb a bang) eqn:G9.
  { apply Ascii.eqb_eq in G9. subst a. exact (bang_tok_end r t l H). }
  destruct (Ascii.eqb a lbrack) eqn:G10.
  { apply Ascii.eqb_eq in G10. subst a. exact (lbrack_tok_end r t l H). }
  destruct (Ascii.eqb a rbrack) eqn:G11.
  { unfold rbrack_tok in H. injection H as _ <-. apply ends_one. exact G2. }
  destruct (Ascii.eqb a lbrace) eqn:G12.
  { apply Ascii.eqb_eq in G12. subst a. exact (lbrace_tok_end r t l H). }
  exact (delim_tok_end prev a r t l G2 H).
Qed.

Lemma get_sdrop : forall p s,
  get p s = match sdrop p s with String d _ => Some d | EmptyString => None end.
Proof. induction p as [|p IH]; intros [|a s]; try reflexivity. apply IH. Qed.

(* No backslash escapes a byte the chain reaches, but a newline or the
   end after a hard break. *)
Lemma chain_unescaped : forall s m p, chain s m p -> ends_ok s p.
Proof.
  intros s m p Hc. induction Hc as [|p q Hc IH Hn].
  - left. destruct s; reflexivity.
  - unfold chain_next in Hn.
    destruct (tok_at s p) as [[t l]|] eqn:Ht; [|discriminate Hn].
    pose proof (tok_at_len s p t l Ht) as [Hl Hb].
    set (pre := substring 0 p s).
    assert (Es : s = (pre ++ sdrop p s)%string) by (symmetry; apply substring_sdrop_app).
    assert (Lp : String.length pre = p) by (apply substring_length0; lia).
    assert (Region : forall o cl reg r, is_bslash cl = false ->
              sdrop p s = String rbrack (String o (reg ++ String cl r)) ->
              q = p + S (S (S (String.length reg))) -> ends_ok s q).
    { intros o cl reg r B E ->. left. rewrite Es, E.
      replace (pre ++ String rbrack (String o (reg ++ String cl r)))%string
        with ((pre ++ String rbrack (String o reg)) ++ String cl r)%string
        by (rewrite append_assoc; reflexivity).
      replace (p + S (S (S (String.length reg))))
        with (S (String.length (pre ++ String rbrack (String o reg))))
        by (rewrite length_append; cbn [String.length]; lia).
      apply esc_after_last, B. }
    assert (Plain : q = p + l -> ends_ok s q).
    { intros ->. unfold tok_at in Ht. pose proof (next_tok_end _ _ _ _ Ht) as E.
      destruct IH as [I|[I|I]].
      - pose proof (ends_ok_shift pre (sdrop p s) l I E) as X.
        rewrite <- Es, Lp in X. exact X.
      - rewrite get_sdrop in I. destruct (sdrop p s) as [|d v] eqn:D; [discriminate Ht|].
        injection I as ->. cbn [next_tok] in Ht. rewrite Ascii.eqb_refl in Ht. injection Ht as <- <-.
        left. rewrite Es. replace (p + 1) with (S (String.length pre)) by lia.
        apply esc_after_last. reflexivity.
      - rewrite get_sdrop in I. destruct (sdrop p s); [discriminate Ht|discriminate I]. }
    destruct t; try (injection Hn as <-; apply Plain; reflexivity).
    + destruct (is_closer m p); injection Hn as <-; [|apply Plain; reflexivity].
      destruct (tok_at_close s p dest region l Ht) as [_ [r E]]. eapply Region; [|exact E|reflexivity]. destruct dest; reflexivity.
    + destruct (is_closer m p); injection Hn as <-; [|apply Plain; reflexivity].
      destruct (tok_at_span s p body a l Ht) as [_ [r E]].
      eapply Region; [|exact E|reflexivity]. reflexivity.
Qed.

(*
The reading, run to the end
===========================
*)

Local Lemma agree_weaken : forall m1 os1 m2 os2 n k,
  agree m1 os1 m2 os2 n -> k <= n -> agree m1 os1 m2 os2 k.
Proof.
  intros m1 os1 m2 os2 n k [A B] L. split; intros; [apply A|apply B]; lia.
Qed.

Local Lemma agree_trans : forall m1 os1 m2 os2 m3 os3 n,
  agree m1 os1 m2 os2 n -> agree m2 os2 m3 os3 n -> agree m1 os1 m3 os3 n.
Proof.
  intros m1 os1 m2 os2 m3 os3 n [A1 B1] [A2 B2]. split; intros.
  - rewrite A1 by assumption. apply A2. assumption.
  - rewrite B1 by assumption. apply B2. assumption.
Qed.

Local Lemma agree_refl : forall m os n, agree m os m os n.
Proof. intros. split; intros; reflexivity. Qed.

(* A step changes only what closes or opens at its token. *)
Local Lemma agree_step : forall s n t st,
  agree (rs_pairs st) (rs_os st) (rs_pairs (rstep s n t st)) (rs_os (rstep s n t st)) n.
Proof.
  intros s n t st. destruct (rstep_grows s n t st) as [Gp Go]. split.
  - intros i j Hj. destruct Gp as [-> | [q ->]]; [reflexivity|]. cbn.
    split; [intros H0; right; exact H0|intros [E|H0]; [injection E as _ ->; lia|exact H0]].
  - intros q Hq. destruct Go as [-> | ->]; [reflexivity|]. cbn.
    split; [intros H0; right; exact H0|intros [E|H0]; [lia|exact H0]].
Qed.

(* The reading the run ends with agrees with its state on what is before
   the token at hand, and on what the token at hand closes. *)
Lemma rgo_agree : forall s f n st,
  rinv s n st -> chain s (rs_pairs st) n ->
  agree (rs_pairs st) (rs_os st) (rs_pairs (rgo s f n st)) (rs_os (rgo s f n st)) n
  /\ forall t, tok_of s n = Some t -> 0 < f ->
     agree (rs_pairs (rstep s n t st)) (rs_os (rstep s n t st))
           (rs_pairs (rgo s f n st)) (rs_os (rgo s f n st)) (S n).
Proof.
  intros s f. induction f as [|f IH]; intros n st I Hc.
  - split; [apply agree_refl|intros; lia].
  - cbn [rgo]. destruct (tok_of s n) as [t|] eqn:Ht; [|split; [apply agree_refl|discriminate]].
    destruct (rinv_next s n st t I Hc Ht) as [_ N].
    assert (Tail : agree (rs_pairs (rstep s n t st)) (rs_os (rstep s n t st))
                     (rs_pairs (match chain_next s (rs_pairs (rstep s n t st)) n with
                                | Some q => rgo s f q (rstep s n t st)
                                | None => rstep s n t st end))
                     (rs_os (match chain_next s (rs_pairs (rstep s n t st)) n with
                             | Some q => rgo s f q (rstep s n t st)
                             | None => rstep s n t st end)) (S n)).
    { destruct (chain_next s (rs_pairs (rstep s n t st)) n) as [q|] eqn:Hq; [|apply agree_refl].
      pose proof (chain_next_bound _ _ _ _ Hq) as Bq. destruct N as [I' Hc'].
      eapply agree_weaken; [exact (proj1 (IH q _ I' Hc'))|lia]. }
    split.
    + eapply agree_trans; [apply agree_step|]. eapply agree_weaken; [exact Tail|lia].
    + intros t' E _. injection E as <-. exact Tail.
Qed.

(*
The two strings
===============

`s` has the byte `c` at `p`, and `s'` a backslash before it.  A position
of `s` past `p` is one further on in `s'`.
*)

Section Escape.
Variables (pre post : string) (c : ascii).
Hypothesis Hc : text_byte c = true.

Local Notation s := (pre ++ String c post)%string.
Local Notation s' := (pre ++ String bslash (String c post))%string.
Local Notation p := (String.length pre).

Definition g (q : nat) : nat := if Nat.leb q p then q else S q.

Local Lemma sdrop_pre : forall q, q <= p -> forall w, sdrop q (pre ++ w) = (sdrop q pre ++ w)%string.
Proof. intros q L w. apply sdrop_app_le, L. Qed.

Local Lemma get_pre : forall q w, q < p -> get q (pre ++ w) = get q pre.
Proof.
  intros q w. revert q. induction pre as [|a x IH]; intros q L; cbn [String.length] in L; [lia|].
  destruct q; [reflexivity|]. apply IH. lia.
Qed.

Local Lemma sdrop_past : forall k w, sdrop (p + k) (pre ++ w) = sdrop k w.
Proof. intros k w. induction pre as [|a x IH]; [reflexivity|exact IH]. Qed.

Local Lemma get_past : forall k w, get (p + k) (pre ++ w) = get k w.
Proof. intros k w. induction pre as [|a x IH]; [reflexivity|exact IH]. Qed.

(* Past the byte, the tokens are the same, one byte on. *)
Lemma tok_after : forall q, p < q -> tok_at s' (S q) = tok_at s q.
Proof.
  intros q L. replace q with (p + S (q - S p)) by lia. set (k := q - S p).
  unfold tok_at. replace (S (p + S k)) with (p + S (S k)) by lia.
  rewrite !sdrop_past. replace (p + S (S k)) with (S (p + S k)) by lia.
  replace (p + S k) with (S (p + k)) at 2 by lia. cbn [before].
  rewrite !get_past. reflexivity.
Qed.

(* At the byte, the escape. *)
Lemma tok_at_p : tok_at s' p = Some (TEsc c, 2).
Proof.
  unfold tok_at. replace p with (p + 0) at 2 by lia. rewrite sdrop_past. cbn [sdrop next_tok].
  change (Ascii.eqb bslash nl_char) with false. change (is_bslash bslash) with true. cbn iota.
  unfold esc_tok. cbn [line_rest]. rewrite (c_not_nl c Hc). cbn [is_blank].
  rewrite (c_not_ws c Hc). reflexivity.
Qed.

Lemma before_le : forall q, q <= p -> before s' q = before s q.
Proof.
  intros [|q] L; [reflexivity|]. cbn [before]. rewrite !get_pre by lia. reflexivity.
Qed.

(* Before the byte, a token begins the same in both, or reads past it. *)
Lemma tok_before : forall q, q < p ->
  (c = rbrack -> esc_after false (sdrop q pre) = false) ->
  tok_at s' q = tok_at s q
  \/ (exists t l, tok_at s q = Some (t, l) /\ p < q + l)
  \/ (exists t, tok_at s q = Some (t, 1) /\ closer_over t (p - q) /\ text_closer (tok_at s' q))
  \/ (tok_at s q = Some (TText bang, 1)
      /\ exists lab l2, tok_at s (S q) = Some (TNote lab, l2) /\ p < S q + l2).
Proof.
  intros q L Hp.
  destruct (sdrop q pre) as [|a x] eqn:D.
  { apply (f_equal String.length) in D. rewrite sdrop_length in D. cbn in D. lia. }
  assert (Lx : String.length x = p - q - 1).
  { apply (f_equal String.length) in D. rewrite sdrop_length in D. cbn [String.length] in D. lia. }
  assert (T1 : tok_at s q = next_tok (before s q) (String a x ++ String c post)%string)
    by (unfold tok_at; rewrite sdrop_pre, D by lia; reflexivity).
  assert (T2 : tok_at s' q = next_tok (before s q) (String a x ++ String bslash (String c post))%string)
    by (unfold tok_at; rewrite before_le, sdrop_pre, D by lia; reflexivity).
  rewrite T1, T2.
  destruct (next_tok_ins c Hc (before s q) a x post Hp)
    as [E|[(t & l & E & Ll)|[(t & E & Co & Tc)|(-> & E & lab & l2 & E2 & Ll)]]].
  - left. exact E.
  - right; left. exists t, l. split; [exact E|lia].
  - right; right; left. exists t. split; [exact E|]. split; [|exact Tc].
    replace (p - q) with (S (String.length x)) by lia. exact Co.
  - right; right; right. split; [exact E|]. exists lab, l2. split; [|lia].
    unfold tok_at. cbn [before].
    assert (Ga : get q s = Some bang).
    { rewrite get_sdrop, sdrop_pre by lia. rewrite D. reflexivity. }
    rewrite Ga.
    assert (Sd : sdrop (S q) s = (x ++ String c post)%string).
    { replace (S q) with (q + 1) by lia. rewrite <- sdrop_sdrop, sdrop_pre by lia. rewrite D.
      reflexivity. }
    rewrite Sd. exact E2.
Qed.

(*
The reading of `s'`
-------------------

Its pairs are the pairs of `s`, moved by `g`.  Its open openers are
those of `s` moved too, but for an opener at `p`: none, or for `![`
the `[` two bytes on.
*)

Definition keep : bool :=
  match tok_at s p with Some (TOpen true, _) => true | _ => false end.

Definition h (j : nat) : nat := if Nat.eqb j p then p + 2 else g j.

Definition mlive (lv : list litem) : list litem :=
  map (fun e => (h (fst e), snd e))
    (filter (fun e => (keep || negb (Nat.eqb (fst e) p))%bool) lv).

Definition mpairs (m : matching) : matching := map (fun e => (g (fst e), g (snd e))) m.

Lemma g_lt : forall a b, a < b <-> g a < g b.
Proof.
  intros a b. unfold g.
  destruct (Nat.leb a p) eqn:A, (Nat.leb b p) eqn:B;
    apply Nat.leb_le in A || apply Nat.leb_gt in A; apply Nat.leb_le in B || apply Nat.leb_gt in B;
    lia.
Qed.

Lemma g_inj : forall a b, g a = g b -> a = b.
Proof.
  intros a b E. destruct (Nat.lt_trichotomy a b) as [L|[->|L]]; [|reflexivity|];
    apply g_lt in L; lia.
Qed.

Lemma is_closer_mpairs : forall m i, is_closer (mpairs m) (g i) = is_closer m i.
Proof.
  intros m i. unfold is_closer, mpairs. induction m as [|[a b] m IH]; [reflexivity|].
  cbn [map existsb fst snd]. rewrite IH. f_equal.
  destruct (Nat.eqb b i) eqn:E.
  - apply Nat.eqb_eq in E. subst. apply Nat.eqb_refl.
  - apply Nat.eqb_neq in E. apply Nat.eqb_neq. intros F. apply E, g_inj, F.
Qed.

Lemma is_opener_mpairs : forall m i, is_opener (mpairs m) (g i) = is_opener m i.
Proof.
  intros m i. unfold is_opener, mpairs. induction m as [|[a b] m IH]; [reflexivity|].
  cbn [map existsb fst snd]. rewrite IH. f_equal.
  destruct (Nat.eqb a i) eqn:E.
  - apply Nat.eqb_eq in E. subst. apply Nat.eqb_refl.
  - apply Nat.eqb_neq in E. apply Nat.eqb_neq. intros F. apply E, g_inj, F.
Qed.

Lemma pick_mlive : forall k lv,
  match pick k lv with
  | PFound j below => j <> p -> pick k (mlive lv) = PFound (g j) (mlive below)
  | PNone => pick k (mlive lv) = PNone
  end.
Proof.
  intros k lv. induction lv as [|[j k'] lv IH]; [reflexivity|].
  unfold mlive. cbn [pick filter fst snd].
  destruct (key_eq k k') eqn:K.
  - intros Hj. replace (Nat.eqb j p) with false by (symmetry; apply Nat.eqb_neq, Hj).
    rewrite orb_true_r. cbn [map pick fst snd]. rewrite K. unfold h.
    replace (Nat.eqb j p) with false by (symmetry; apply Nat.eqb_neq, Hj). reflexivity.
  - destruct (keep || negb (Nat.eqb j p))%bool; [cbn [map pick fst snd]; rewrite K|]; exact IH.
Qed.

Lemma mlive_cons : forall j k lv, j <> p -> mlive ((j, k) :: lv) = (g j, k) :: mlive lv.
Proof.
  intros j k lv Hj. unfold mlive. cbn [filter fst].
  replace (Nat.eqb j p) with false by (symmetry; apply Nat.eqb_neq, Hj).
  rewrite orb_true_r. cbn [map fst snd]. unfold h.
  replace (Nat.eqb j p) with false by (symmetry; apply Nat.eqb_neq, Hj). reflexivity.
Qed.

(* A step at a token other than the byte's, the same in both strings. *)
Lemma rstep_sim : forall q t st st', q <> p ->
  rs_pairs st' = mpairs (rs_pairs st) -> rs_live st' = mlive (rs_live st) ->
  (forall j k, In (j, k) (rs_live st) -> j <> p -> tok_end s' (g j) = g (tok_end s j)) ->
  (forall k j below, closes_as t = Some k -> pick k (rs_live st) = PFound j below -> j <> p) ->
  rs_pairs (rstep s' (g q) t st') = mpairs (rs_pairs (rstep s q t st))
  /\ rs_live (rstep s' (g q) t st') = mlive (rs_live (rstep s q t st)).
Proof.
  intros q t [lv m os] [lv' m' os'] Hq Ep El He Hn. cbn [rs_pairs rs_live] in *. subst lv' m'.
  unfold rstep. cbn [rs_live rs_pairs rs_os].
  destruct t as [d| |k mr op cl| |b rg|d|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn];
    try (split; reflexivity).
  - destruct cl.
    + pose proof (pick_mlive (KDelim k mr) lv) as P.
      destruct (pick (KDelim k mr) lv) as [j below|] eqn:Pk.
      * assert (Hj : j <> p) by exact (Hn _ _ _ eq_refl Pk). rewrite (P Hj).
        assert (Ij : In (j, KDelim k mr) lv).
        { clear -Pk. induction lv as [|[j' k'] lv IH]; [discriminate|]. cbn [pick] in Pk.
          destruct (key_eq (KDelim k mr) k') eqn:K.
          - injection Pk as <- _. apply key_eq_iff in K. subst. left. reflexivity.
          - right. apply IH, Pk. }
        rewrite (He j _ Ij Hj).
        destruct (Nat.ltb (tok_end s j) q) eqn:L.
        -- apply Nat.ltb_lt in L. apply g_lt in L. apply Nat.ltb_lt in L. rewrite L.
           split; reflexivity.
        -- apply Nat.ltb_ge in L.
           replace (Nat.ltb (g (tok_end s j)) (g q)) with false
             by (symmetry; apply Nat.ltb_ge; destruct (Nat.eq_dec (tok_end s j) q) as [->|N];
                 [lia|assert (q < tok_end s j) by lia; apply g_lt in H; lia]).
           destruct op; [|split; reflexivity]. unfold ropen. cbn [rs_live rs_pairs rs_os].
           split; [reflexivity|rewrite mlive_cons by exact Hq; reflexivity].
      * rewrite P. destruct op; [|split; reflexivity]. unfold ropen. cbn [rs_live rs_pairs rs_os].
        split; [reflexivity|rewrite mlive_cons by exact Hq; reflexivity].
    + destruct op; [|split; reflexivity]. unfold ropen. cbn [rs_live rs_pairs rs_os].
      split; [reflexivity|rewrite mlive_cons by exact Hq; reflexivity].
  - unfold ropen. cbn [rs_live rs_pairs rs_os].
    split; [reflexivity|rewrite mlive_cons by exact Hq; reflexivity].
  - pose proof (pick_mlive KBracket lv) as P.
    destruct (pick KBracket lv) as [j below|] eqn:Pk; [|rewrite P; split; reflexivity].
    rewrite (P (Hn _ _ _ eq_refl Pk)). split; reflexivity.
  - pose proof (pick_mlive KBracket lv) as P.
    destruct (pick KBracket lv) as [j below|] eqn:Pk; [|rewrite P; split; reflexivity].
    rewrite (P (Hn _ _ _ eq_refl Pk)). split; reflexivity.
Qed.

(* A token the reading may take as text. *)
Definition text_tok (t : token) : bool :=
  match t with TText _ | TOpen _ | TClose _ _ | TSpan _ _ => true | _ => false end.

Definition M : matching := fst (ref_read s).

Hypothesis Hchain : chain s M p.
Hypothesis Hopen : is_opener M p = false.
Hypothesis Hclose : is_closer M p = false.
Hypothesis Htext : exists t l, tok_at s p = Some (t, l) /\ text_tok t = true.

Lemma chain_next_ge : forall m q q1 t l,
  chain_next s m q = Some q1 -> tok_at s q = Some (t, l) -> q + l <= q1.
Proof.
  intros m q q1 t l Hn Ht. unfold chain_next in Hn. rewrite Ht in Hn.
  destruct t; try (injection Hn as <-; lia).
  - destruct (is_closer m q); injection Hn as <-; [|lia].
    destruct (tok_at_close s q dest region l Ht) as [-> _]. lia.
  - destruct (is_closer m q); injection Hn as <-; [|lia].
    destruct (tok_at_span s q body a l Ht) as [-> _]. lia.
Qed.

(* A token of the chain before `p` ends by `p`. *)
Lemma chain_before : forall q, chain s M q -> q < p ->
  exists q1, chain_next s M q = Some q1 /\ q1 <= p.
Proof. intros q Hq L. exact (chain_between s M p q Hq Hchain L). Qed.

Lemma pre_unescaped : forall q, chain s M q -> q < p ->
  esc_after false (sdrop q pre) = false.
Proof.
  intros q Hq L.
  assert (Gp : get p s = Some c) by (replace p with (p + 0) by lia; rewrite get_past; reflexivity).
  assert (Ep : esc_after false pre = false).
  { destruct (chain_unescaped s M p Hchain) as [E|[E|E]]; try rewrite Gp in E.
    - replace (substring 0 p s) with pre in E; [exact E|].
      rewrite substring_app_le by lia. clear. induction pre as [|a x IH]; [reflexivity|].
      cbn [String.length substring]. f_equal. exact IH.
    - injection E as E. rewrite E in Hc. discriminate Hc.
    - discriminate E. }
  rewrite <- (substring_sdrop_app q pre), esc_after_app in Ep.
  destruct (sdrop q pre) as [|a x] eqn:D; [reflexivity|].
  destruct (chain_unescaped s M q Hq) as [E|[E|E]].
  - rewrite substring_app_le in E by lia. rewrite E in Ep. exact Ep.
  - rewrite get_sdrop, sdrop_pre, D in E by lia. injection E as ->.
    cbn [esc_after] in Ep |- *. destruct (esc_after false (substring 0 q pre)); exact Ep.
  - rewrite get_sdrop, sdrop_pre, D in E by lia. discriminate E.
Qed.

(* Along the chain, a token before `p` is the same in `s'`, or it is a
   `]` that closes nothing, and in `s'` a `]` read alone. *)
Lemma tok_corr : forall q, chain s M q -> q < p ->
  tok_at s' q = tok_at s q
  \/ (exists t, tok_at s q = Some (t, 1) /\ closes_as t = Some KBracket
      /\ is_closer M q = false /\ text_closer (tok_at s' q)).
Proof.
  intros q Hq L.
  destruct (chain_before q Hq L) as (q1 & Hn & Le).
  destruct (tok_before q L (fun _ => pre_unescaped q Hq L))
    as [E|[(t & l & E & Ll)|[(t & E & Co & Tc)|(E & lab & l2 & E2 & Ll)]]].
  - left. exact E.
  - exfalso. pose proof (chain_next_ge M q q1 t l Hn E). lia.
  - right. exists t. split; [exact E|].
    destruct t; cbn [closer_over] in Co; try contradiction; (split; [reflexivity|]); (split; [|exact Tc]).
    + unfold chain_next in Hn. rewrite E in Hn.
      destruct (is_closer M q); [|reflexivity]. injection Hn as <-. lia.
    + unfold chain_next in Hn. rewrite E in Hn.
      destruct (is_closer M q); [|reflexivity]. injection Hn as <-. lia.
  - exfalso. unfold chain_next in Hn. rewrite E in Hn. injection Hn as <-.
    destruct (Nat.eq_dec (S q) p) as [Ep|Ep].
    + destruct Htext as (t & l & Et & Tt). rewrite <- Ep, E2 in Et. injection Et as <- _.
      discriminate Tt.
    + assert (Hq1 : chain s M (S q)).
      { apply (chain_step s M q); [exact Hq|]. unfold chain_next. rewrite E. f_equal. lia. }
      destruct (chain_before (S q) Hq1 ltac:(lia)) as (q2 & Hn2 & Le2).
      pose proof (chain_next_ge M (S q) q2 _ _ Hn2 E2). lia.
Qed.

Lemma g_below : forall q, q <= p -> g q = q.
Proof. intros q L. unfold g. apply Nat.leb_le in L. rewrite L. reflexivity. Qed.

Lemma g_above : forall q, p < q -> g q = S q.
Proof. intros q L. unfold g. apply Nat.leb_gt in L. rewrite L. reflexivity. Qed.

(* Off the byte, a token of the chain is the same in `s'`, or a `]` that
   closes nothing. *)
Lemma tok_off : forall q, chain s M q -> q <> p ->
  tok_at s' (g q) = tok_at s q
  \/ (q < p /\ exists t, tok_at s q = Some (t, 1) /\ closes_as t = Some KBracket
      /\ is_closer M q = false /\ text_closer (tok_at s' q)).
Proof.
  intros q Hq Hne. destruct (Nat.lt_ge_cases q p) as [L|L].
  - rewrite g_below by lia. destruct (tok_corr q Hq L) as [E|E]; [left; exact E|right; split; assumption].
  - left. rewrite g_above by lia. apply tok_after. lia.
Qed.

(* Where an opener's token ends. *)
Lemma tok_end_g : forall j k, chain s M j -> j <> p -> open_key s j = Some k ->
  tok_end s' (g j) = g (tok_end s j).
Proof.
  intros j k Hj Hne Ho. unfold open_key, tok_of in Ho.
  destruct (tok_at s j) as [[t l]|] eqn:Ht; [|discriminate Ho]. cbn [option_map] in Ho.
  unfold tok_end. destruct (tok_off j Hj Hne) as [E|(L & t' & E & Cl & _)].
  - rewrite E, Ht. destruct (Nat.lt_ge_cases j p) as [L|L].
    + destruct (chain_before j Hj L) as (q1 & Hn & Le).
      pose proof (chain_next_ge M j q1 t l Hn Ht).
      rewrite !g_below by lia. reflexivity.
    + rewrite !g_above by lia. reflexivity.
  - rewrite Ht in E. injection E as <- _.
    destruct t; cbn [opens_as closes_as] in Ho, Cl; try discriminate Ho; try discriminate Cl.
    destruct closes; discriminate Cl.
Qed.

(* The chain moves on alike, given the same token and the same verdict
   on whether it closes. *)
Lemma chain_next_g : forall P q q1, chain s M q -> q <> p -> tok_at s' (g q) = tok_at s q ->
  is_closer P q = is_closer M q -> chain_next s P q = Some q1 ->
  chain_next s' (mpairs P) (g q) = Some (g q1).
Proof.
  intros P q q1 Hq Hne Et Ec Hn.
  assert (HnM : chain_next s M q = Some q1)
    by (unfold chain_next in Hn |- *; rewrite <- Ec; exact Hn).
  unfold chain_next in Hn |- *. rewrite Et, is_closer_mpairs.
  destruct (tok_at s q) as [[t l]|] eqn:Ht; [|discriminate Hn].
  destruct (Nat.lt_ge_cases q p) as [L|L].
  - destruct (chain_before q Hq L) as (q2 & Hn2 & Le). rewrite HnM in Hn2. injection Hn2 as <-.
    rewrite !(g_below q1), !g_below by lia. exact Hn.
  - rewrite !g_above by lia.
    destruct t; try (injection Hn as <-; rewrite g_above by lia; reflexivity);
      destruct (is_closer P q); injection Hn as <-; rewrite g_above by lia; reflexivity.
Qed.

Lemma agree_closer : forall m1 os1 m2 os2 n i j, agree m1 os1 m2 os2 n -> j < n ->
  In (i, j) m1 <-> In (i, j) m2.
Proof. intros m1 os1 m2 os2 n i j [A _] L. apply A, L. Qed.

Lemma is_closer_agree : forall m1 os1 m2 os2 n q, agree m1 os1 m2 os2 n -> q < n ->
  is_closer m1 q = is_closer m2 q.
Proof.
  intros m1 os1 m2 os2 n q A L.
  destruct (is_closer m1 q) eqn:E1, (is_closer m2 q) eqn:E2; try reflexivity.
  - apply is_closer_iff in E1 as [i Hi]. apply (agree_closer _ _ _ _ _ i q A L) in Hi.
    assert (is_closer m2 q = true) by (apply is_closer_iff; exists i; exact Hi). congruence.
  - apply is_closer_iff in E2 as [i Hi]. apply (agree_closer _ _ _ _ _ i q A L) in Hi.
    assert (is_closer m1 q = true) by (apply is_closer_iff; exists i; exact Hi). congruence.
Qed.

Lemma tok_none_past : forall q, tok_at s q = None -> p < q.
Proof.
  intros q Hq. destruct Htext as (t & l & E & _).
  pose proof (tok_at_len s p t l E) as [_ L].
  unfold tok_at in Hq. destruct (sdrop q s) eqn:D; [|discriminate Hq].
  apply (f_equal String.length) in D. rewrite sdrop_length in D. cbn [String.length] in D.
  rewrite length_append in L, D. cbn [String.length] in L, D. lia.
Qed.

(* After `![` at `p`, `s'` has its `[` two bytes on, alone. *)
Lemma image_open_next : tok_at s p = Some (TOpen true, 2) -> tok_at s' (S (S p)) = Some (TOpen false, 1).
Proof.
  intros H. rewrite tok_after by lia.
  unfold tok_at in H |- *. replace p with (p + 0) in H at 2 by lia. rewrite sdrop_past in H.
  replace (S p) with (p + 1) by lia. rewrite sdrop_past. cbn [sdrop before] in *.
  replace (p + 0) with p by lia. replace p with (p + 0) at 1 by lia.
  replace (p + 0 + 1) with (S (p + 0)) by lia. cbn [before]. rewrite get_past. cbn [get].
  pose proof Hc as B; unfold text_byte in B.
  revert H. generalize (before s p) as pv. intros pv H.
  repeat (apply orb_true_iff in B as [B|B]); apply Ascii.eqb_eq in B; rewrite B in H |- *;
    cbn [next_tok] in H; injection H as H.
  - destruct (auto_tok_shape post) as [(? & ? & E)|E]; rewrite E in H; discriminate H.
  - unfold lbrack_tok in H. destruct (note_at post); discriminate H.
  - discriminate H0.
  - unfold bang_tok in H. destruct (starts_with lbrack post) eqn:S; [|discriminate H].
    destruct (note_at (sdrop 1 post)) eqn:N; [discriminate H|].
    revert S N. clear. intros S N.
    destruct post as [|d r]; [discriminate S|]. cbn [starts_with] in S.
    apply Ascii.eqb_eq in S. subst d. cbn [next_tok sdrop] in *. unfold lbrack_tok. rewrite N.
    reflexivity.
Qed.

Lemma rgo_sim : forall f q st st' f',
  rinv s q st -> chain s (rs_pairs st) q ->
  String.length s - q < f -> String.length s' - g q < f' ->
  rs_pairs (rgo s f q st) = M ->
  rs_pairs st' = mpairs (rs_pairs st) -> rs_live st' = mlive (rs_live st) ->
  rs_pairs (rgo s' f' (g q) st') = mpairs M.
Proof.
  intros f. induction f as [|f IH]; intros q st st' f' I Hq Lf Lf' Hfin Ep El; [lia|].
  destruct f' as [|f']; [lia|].
  destruct (rgo_agree s (S f) q st I Hq) as [A0 A1]. rewrite Hfin in A0, A1.
  pose proof (chain_agree s _ _ _ _ q q A0 (le_n q) Hq) as HqM.
  cbn [rgo] in Hfin |- *.
  destruct (tok_of s q) as [t|] eqn:Ht.
  2: { assert (Hn : tok_at s q = None)
         by (unfold tok_of in Ht; destruct (tok_at s q) as [[]|]; [discriminate|reflexivity]).
       pose proof (tok_none_past q Hn) as L. rewrite g_above by exact L.
       unfold tok_of. rewrite tok_after by exact L. rewrite Hn. cbn [option_map].
       rewrite Ep, Hfin. reflexivity. }
  specialize (A1 t eq_refl ltac:(lia)).
  assert (Ht' : exists l, tok_at s q = Some (t, l))
    by (unfold tok_of in Ht; destruct (tok_at s q) as [[t0 l]|];
        [injection Ht as <-; exists l; reflexivity|discriminate]).
  destruct Ht' as [l Htl].
  destruct (rinv_next s q st t I Hq Ht) as [_ N].
  destruct (chain_next s (rs_pairs (rstep s q t st)) q) as [q1|] eqn:Hq1.
  2: { exfalso. unfold chain_next in Hq1. rewrite Htl in Hq1.
       destruct t; try discriminate Hq1; destruct (is_closer _ q); discriminate Hq1. }
  destruct N as [I1 Hc1].
  pose proof (chain_next_bound _ _ _ _ Hq1) as Bq1.
  assert (Ccl : is_closer (rs_pairs (rstep s q t st)) q = is_closer M q)
    by exact (is_closer_agree _ _ _ _ _ q A1 (Nat.lt_succ_diag_r q)).
  assert (Ls : String.length s' = S (String.length s))
    by (rewrite !length_append; cbn [String.length]; lia).
  pose proof (tok_at_len s q t l Htl) as [_ Lq].
  assert (Lgq : g q <= q + 1) by (unfold g; destruct (Nat.leb q p); lia).
  assert (Lg : String.length s' - g q1 < f').
  { pose proof (proj1 (g_lt q q1) ltac:(lia)). lia. }
  destruct (Nat.eq_dec q p) as [Eqp|Hne].
  { (* the byte: an escape in `s'` *)
    subst q. rewrite (g_below p) by lia.
    unfold tok_of at 1. rewrite tok_at_p. cbn [option_map fst].
    replace (rstep s' p (TEsc c) st') with st' by (destruct st'; reflexivity).
    replace (chain_next s' (rs_pairs st') p) with (Some (p + 2))
      by (unfold chain_next; rewrite tok_at_p; reflexivity).
    destruct Htext as (tp & lp & Etp & Tp). rewrite Htl in Etp. injection Etp as <- <-.
    assert (Nc : is_closer (rs_pairs st) p = false).
    { destruct (is_closer (rs_pairs st) p) eqn:C; [|reflexivity].
      apply is_closer_iff in C as [i Hi]. pose proof (ri_bound_pairs s p st I i p Hi). lia. }
    destruct t; try discriminate Tp.
    - (* text *)
      pose proof (tok_at_text s p c0 l Htl) as ->.
      replace (rstep s p (TText c0) st) with st in * by (destruct st; reflexivity).
      unfold chain_next in Hq1. rewrite Htl in Hq1. injection Hq1 as <-.
      replace (p + 2) with (g (p + 1)) by (rewrite g_above by lia; lia).
      exact (IH (p + 1) st st' f' I1 Hc1 ltac:(lia) Lg Hfin Ep El).
    - destruct image.
      + (* `![`: its `[` opens two bytes on *)
        pose proof (tok_at_open_image s p l Htl) as ->.
        assert (Kp : keep = true) by (unfold keep; rewrite Htl; reflexivity).
        unfold chain_next in Hq1. rewrite Htl in Hq1. injection Hq1 as <-.
        destruct f' as [|f'']; [rewrite g_above in Lg by lia; lia|].
        cbn [rgo]. unfold tok_of at 1.
        replace (p + 2) with (S (S p)) by lia. rewrite image_open_next by exact Htl.
        cbn [option_map fst].
        set (st2 := rstep s' (S (S p)) (TOpen false) st').
        replace (chain_next s' (rs_pairs st2) (S (S p))) with (Some (g (p + 2))).
        2: { unfold chain_next. rewrite image_open_next by exact Htl. rewrite g_above by lia.
             f_equal. lia. }
        apply (IH (p + 2) _ st2 f'' I1 Hc1 ltac:(lia));
          [rewrite g_above in Lg |- * by lia; lia|exact Hfin| |].
        * unfold st2. cbn [rstep ropen rs_pairs rs_live rs_os]. destruct st'. cbn.
          cbn [Precedence.rs_pairs] in Ep. exact Ep.
        * unfold st2. destruct st as [lv m os]. cbn [rstep ropen Precedence.rs_live] in El |- *.
          rewrite El. unfold mlive. cbn [filter fst snd].
          rewrite Kp. cbn [orb map fst snd]. unfold h. rewrite Nat.eqb_refl. f_equal. f_equal. lia.
      + (* `[` *)
        pose proof (tok_at_open_plain s p l Htl) as ->.
        assert (Kp : keep = false) by (unfold keep; rewrite Htl; reflexivity).
        unfold chain_next in Hq1. rewrite Htl in Hq1. injection Hq1 as <-.
        replace (p + 2) with (g (p + 1)) by (rewrite g_above by lia; lia).
        apply (IH (p + 1) _ st' f' I1 Hc1 ltac:(lia) Lg Hfin).
        * rewrite Ep. destruct st. reflexivity.
        * rewrite El. destruct st as [lv m os]. unfold mlive.
          cbn [rstep ropen Precedence.rs_live filter fst].
          rewrite Kp, Nat.eqb_refl. reflexivity.
    - (* a `]` that closes nothing *)
      destruct (tok_at_close s p dest region l Htl) as [-> _].
      assert (Pk : pick KBracket (rs_live st) = PNone).
      { destruct (pick KBracket (rs_live st)) as [j below|] eqn:Pk; [|reflexivity]. exfalso.
        assert (Inj : In (j, p) (rs_pairs (rstep s p (TClose dest region) st)))
          by (unfold rstep; rewrite Pk; left; reflexivity).
        assert (is_closer (rs_pairs (rstep s p (TClose dest region) st)) p = true)
          by (apply is_closer_iff; exists j; exact Inj). congruence. }
      replace (rstep s p (TClose dest region) st) with st in *
        by (unfold rstep; rewrite Pk; destruct st; reflexivity).
      unfold chain_next in Hq1. rewrite Htl, Nc in Hq1. injection Hq1 as <-.
      replace (p + 2) with (g (p + 1)) by (rewrite g_above by lia; lia).
      exact (IH (p + 1) st st' f' I1 Hc1 ltac:(lia) Lg Hfin Ep El).
    - destruct (tok_at_span s p body a l Htl) as [-> _].
      assert (Pk : pick KBracket (rs_live st) = PNone).
      { destruct (pick KBracket (rs_live st)) as [j below|] eqn:Pk; [|reflexivity]. exfalso.
        assert (Inj : In (j, p) (rs_pairs (rstep s p (TSpan body a) st)))
          by (unfold rstep; rewrite Pk; left; reflexivity).
        assert (is_closer (rs_pairs (rstep s p (TSpan body a) st)) p = true)
          by (apply is_closer_iff; exists j; exact Inj). congruence. }
      replace (rstep s p (TSpan body a) st) with st in *
        by (unfold rstep; rewrite Pk; destruct st; reflexivity).
      unfold chain_next in Hq1. rewrite Htl, Nc in Hq1. injection Hq1 as <-.
      replace (p + 2) with (g (p + 1)) by (rewrite g_above by lia; lia).
      exact (IH (p + 1) st st' f' I1 Hc1 ltac:(lia) Lg Hfin Ep El). }
  destruct (tok_off q HqM Hne) as [E|(L & t0 & E0 & Ck & Cm & Tc)].
  - (* the same token *)
    assert (He : forall j k, In (j, k) (rs_live st) -> j <> p ->
                 tok_end s' (g j) = g (tok_end s j)).
    { intros j k Hj Hj'. apply (ri_live s q st I) in Hj as (Hos & Ljq & Ho & _ & _).
      destruct (proj1 (ri_os s q st I j Ljq) Hos) as (_ & Hcj & _).
      exact (tok_end_g j k (chain_agree s _ _ _ _ q j A0 ltac:(lia) Hcj) Hj' Ho). }
    assert (Hn : forall k j below, closes_as t = Some k ->
                 pick k (rs_live st) = PFound j below -> j <> p).
    { intros k j below Hk Pk ->.
      destruct (pick_found k _ p below (ri_desc s q st I) Pk) as [Ip _].
      apply (ri_live s q st I) in Ip as (_ & _ & Ho & _ & _).
      destruct Htext as (tp & lp & Etp & Tp). unfold open_key, tok_of in Ho. rewrite Etp in Ho.
      cbn [option_map fst] in Ho.
      assert (k = KBracket) as ->.
      { destruct tp; try discriminate Tp; cbn [opens_as] in Ho; congruence. }
      assert (Inp : In (p, q) (rs_pairs (rstep s q t st))).
      { unfold rstep. destruct t; cbn [closes_as] in Hk; try discriminate Hk;
          [destruct closes; discriminate Hk| |]; rewrite Pk; left; reflexivity. }
      apply (agree_closer _ _ _ _ _ p q A1 (Nat.lt_succ_diag_r q)) in Inp.
      assert (is_opener M p = true) by (apply is_opener_iff; exists q; exact Inp). congruence. }
    destruct (rstep_sim q t st st' Hne Ep El He Hn) as [Ep1 El1].
    unfold tok_of at 1. rewrite E, Htl. cbn [option_map fst]. rewrite Ep1.
    rewrite (chain_next_g _ q q1 HqM Hne E Ccl Hq1).
    exact (IH q1 _ _ f' I1 Hc1 ltac:(lia) Lg Hfin Ep1 El1).
  - (* a `]` that closes nothing *)
    rewrite Htl in E0. injection E0 as E1 E2. subst t0 l.
    assert (Pk : pick KBracket (rs_live st) = PNone).
    { destruct (pick KBracket (rs_live st)) as [j below|] eqn:Pk; [|reflexivity]. exfalso.
      assert (Inj : In (j, q) (rs_pairs (rstep s q t st))).
      { unfold rstep. destruct t; cbn [closes_as] in Ck; try discriminate Ck;
          [destruct closes; discriminate Ck| |]; rewrite Pk; left; reflexivity. }
      assert (is_closer (rs_pairs (rstep s q t st)) q = true)
        by (apply is_closer_iff; exists j; exact Inj). congruence. }
    assert (Same : rstep s q t st = st).
    { unfold rstep. destruct t; cbn [closes_as] in Ck; try discriminate Ck;
        [destruct closes; discriminate Ck| |]; rewrite Pk; destruct st; reflexivity. }
    rewrite Same in Hq1, Hfin, I1, Hc1.
    assert (Nc : is_closer (rs_pairs st) q = false).
    { destruct (is_closer (rs_pairs st) q) eqn:C; [|reflexivity].
      apply is_closer_iff in C as [i Hi]. pose proof (ri_bound_pairs s q st I i q Hi). lia. }
    assert (Q1 : q1 = q + 1).
    { unfold chain_next in Hq1. rewrite Htl, Nc in Hq1.
      destruct t; cbn [closes_as] in Ck; try discriminate Ck; [destruct closes; discriminate Ck| |];
        injection Hq1 as <-; reflexivity. }
    subst q1.
    assert (Nc' : is_closer (rs_pairs st') q = false).
    { rewrite Ep. rewrite <- (g_below q) by lia. rewrite is_closer_mpairs. exact Nc. }
    assert (Pk' : pick KBracket (rs_live st') = PNone).
    { pose proof (pick_mlive KBracket (rs_live st)) as P. rewrite Pk in P. rewrite El. exact P. }
    rewrite (g_below q) by lia. unfold tok_of at 1.
    destruct (tok_at s' q) as [[t' l']|] eqn:E'; [|contradiction Tc].
    cbn [option_map fst].
    assert (l' = 1 /\ rstep s' q t' st' = st') as [-> Same'].
    { destruct t'; destruct l' as [|[|]]; cbn [text_closer] in Tc; try contradiction;
        split; try reflexivity; unfold rstep; try rewrite Pk'; destruct st'; reflexivity. }
    rewrite Same'.
    assert (Cn : chain_next s' (rs_pairs st') q = Some (q + 1)).
    { unfold chain_next. rewrite E', Nc'.
      destruct t'; cbn [text_closer] in Tc; try contradiction; reflexivity. }
    rewrite Cn. rewrite <- (g_below (q + 1)) by lia.
    exact (IH (q + 1) st st' f' I1 Hc1 ltac:(lia) Lg Hfin Ep El).
Qed.

Lemma reading_s' : fst (ref_read s') = mpairs M.
Proof.
  unfold ref_read. cbn [fst]. replace 0 with (g 0) at 2 by (apply g_below; lia).
  apply (rgo_sim (S (String.length s)) 0 rstart rstart).
  - apply rinv_start.
  - constructor.
  - lia.
  - rewrite g_below by lia. rewrite !length_append. cbn [String.length]. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(*
The tree of `s'`
----------------
*)

(* The text the byte's token reads as is the byte, or for `![` the `!`
   and the `[` after it. *)
Lemma text_at_p : forall t l, tok_at s p = Some (t, l) -> text_tok t = true ->
  tok_text t = one c \/ (t = TOpen true /\ c = bang).
Proof.
  intros t l H Tt. unfold tok_at in H. replace p with (p + 0) in H at 2 by lia.
  rewrite sdrop_past in H. cbn [sdrop] in H. revert H. generalize (before s p) as pv. intros pv H.
  pose proof Hc as B; unfold text_byte in B.
  repeat (apply orb_true_iff in B as [B|B]); apply Ascii.eqb_eq in B; rewrite B in H |- *;
    cbn [next_tok] in H; injection H as H.
  - destruct (auto_tok_shape post) as [(? & ? & E)|E]; rewrite E in H; injection H as <- _;
      [discriminate Tt|left; reflexivity].
  - unfold lbrack_tok in H. destruct (note_at post); injection H as <- _; [discriminate Tt|].
    left. reflexivity.
  - subst t. destruct post as [|d r]; [left; reflexivity|].
    destruct (Ascii.eqb d lparen); [destruct (dest_close false 0 0 r); left; reflexivity|].
    destruct (Ascii.eqb d lbrack); [destruct (label_close false 0 r); left; reflexivity|].
    destruct (Ascii.eqb d lbrace); [destruct (spec_at r) as [[]|]|]; left; reflexivity.
  - unfold bang_tok in H. destruct (starts_with lbrack post);
      [destruct (note_at (sdrop 1 post))|]; injection H as <- _;
      [left; reflexivity|right; split; reflexivity|left; reflexivity].
Qed.

Lemma esc_text_c : esc_text c = one c.
Proof. unfold esc_text. rewrite (c_punct c Hc). reflexivity. Qed.

Lemma item_snoc_app : forall a b out, item_snoc b (item_snoc a out) = item_snoc (a ++ b) out.
Proof.
  intros a b [|x out]; [reflexivity|].
  destruct x as [[q [|kv at'] v]|m]; try reflexivity. destruct v; try reflexivity.
  cbn [item_snoc]. rewrite append_assoc. reflexivity.
Qed.

Lemma temit_str_app : forall a b fs top,
  (let '(fs', top') := temit_str a fs top in temit_str b fs' top') = temit_str (a ++ b) fs top.
Proof.
  intros a b [|[k acc] fs] top; cbn [temit_str]; rewrite item_snoc_app; reflexivity.
Qed.

Lemma at_rbrace_g : forall e, at_rbrace (get (g e) s') = at_rbrace (get e s).
Proof.
  intros e. destruct (Nat.lt_trichotomy e p) as [L|[->|L]].
  - rewrite g_below by lia. rewrite !get_pre by lia. reflexivity.
  - rewrite g_below by lia. replace p with (p + 0) by lia. rewrite !get_past. cbn [get].
    unfold at_rbrace. change (Ascii.eqb bslash rbrace) with false.
    pose proof Hc as B; unfold text_byte in B.
    repeat (apply orb_true_iff in B as [B|B]); apply Ascii.eqb_eq in B; rewrite B; reflexivity.
  - rewrite g_above by lia. replace (S e) with (p + S (S (e - p - 1))) by lia.
    replace e with (p + S (e - p - 1)) at 2 by lia. rewrite !get_past. reflexivity.
Qed.

(* A token of the chain off the byte, the same in `s'`, ends where `g`
   says. *)
Lemma tok_end_same : forall q, chain s M q -> q <> p -> tok_at s' (g q) = tok_at s q ->
  tok_end s' (g q) = g (tok_end s q).
Proof.
  intros q Hq Hne E. unfold tok_end. rewrite E.
  destruct (tok_at s q) as [[t l]|] eqn:Ht.
  - destruct (Nat.lt_ge_cases q p) as [L|L].
    + destruct (chain_before q Hq L) as (q1 & Hn & Le).
      pose proof (chain_next_ge M q q1 t l Hn Ht). rewrite !g_below by lia. reflexivity.
    + rewrite !g_above by lia. reflexivity.
  - reflexivity.
Qed.

(* Every opener of the reading is on the chain. *)
Lemma opener_on_chain : forall i j, In (i, j) M -> chain s M i.
Proof.
  intros i j H. destruct (ref_read_valid s) as (V1 & _ & V3). fold M in V1, V3.
  destruct (V1 i j H) as (k & _ & _ & ((Hos & _) & _) & _). apply V3 in Hos. apply Hos.
Qed.

Lemma tstep_same : forall q t hard fs top, chain s M q -> q <> p ->
  tok_at s' (g q) = tok_at s q ->
  tstep s' (mpairs M) (g q) t hard fs top = tstep s M q t hard fs top.
Proof.
  intros q t hard fs top Hq Hne E. unfold tstep.
  rewrite is_opener_mpairs, is_closer_mpairs, (tok_end_same q Hq Hne E), at_rbrace_g.
  reflexivity.
Qed.

Lemma tgo_sim : forall f q hard fs top f', chain s M q ->
  String.length s - q < f -> String.length s' - g q < f' ->
  tgo s' (mpairs M) f' (g q) hard fs top = tgo s M f q hard fs top.
Proof.
  intros f. induction f as [|f IH]; intros q hard fs top f' Hq Lf Lf'; [lia|].
  destruct f' as [|f']; [lia|].
  assert (Ls : String.length s' = S (String.length s))
    by (rewrite !length_append; cbn [String.length]; lia).
  cbn [tgo].
  destruct (tok_of s q) as [t|] eqn:Ht.
  2: { assert (Hn : tok_at s q = None)
         by (unfold tok_of in Ht; destruct (tok_at s q) as [[]|]; [discriminate|reflexivity]).
       pose proof (tok_none_past q Hn) as L. rewrite g_above by exact L.
       unfold tok_of. rewrite tok_after by exact L. rewrite Hn. reflexivity. }
  assert (Ht' : exists l, tok_at s q = Some (t, l))
    by (unfold tok_of in Ht; destruct (tok_at s q) as [[t0 l]|];
        [injection Ht as <-; exists l; reflexivity|discriminate]).
  destruct Ht' as [l Htl].
  pose proof (tok_at_len s q t l Htl) as [Hl0 Lq].
  assert (Lgq : g q <= q + 1) by (unfold g; destruct (Nat.leb q p); lia).
  destruct (chain_next s M q) as [q1|] eqn:Hq1.
  2: { exfalso. unfold chain_next in Hq1. rewrite Htl in Hq1.
       destruct t; try discriminate Hq1; destruct (is_closer _ q); discriminate Hq1. }
  pose proof (chain_next_bound _ _ _ _ Hq1) as Bq1.
  pose proof (chain_step s M q q1 Hq Hq1) as Hq1c.
  assert (Lg : String.length s' - g q1 < f').
  { pose proof (proj1 (g_lt q q1) ltac:(lia)). lia. }
  destruct (Nat.eq_dec q p) as [Eqp|Hne].
  { (* the byte: an escape in `s'` *)
    subst q. rewrite (g_below p) by lia.
    unfold tok_of at 1. rewrite tok_at_p. cbn [option_map fst].
    replace (tstep s' (mpairs M) p (TEsc c) hard fs top) with (temit_str (one c) fs top)
      by (unfold tstep; rewrite esc_text_c; reflexivity).
    replace (chain_next s' (mpairs M) p) with (Some (p + 2))
      by (unfold chain_next; rewrite tok_at_p; reflexivity).
    destruct Htext as (tp & lp & Etp & Tp). rewrite Htl in Etp. injection Etp as <- <-.
    assert (Tx : tstep s M p t hard fs top = temit_str (tok_text t) fs top).
    { destruct t; try discriminate Tp; unfold tstep; rewrite ?Hopen, ?Hclose;
        try reflexivity; destruct fs as [|[]]; reflexivity. }
    assert (Nh : is_hard t = false) by (destruct t; try discriminate Tp; reflexivity).
    rewrite Tx, Nh. cbn [is_hard].
    destruct (text_at_p t l Htl Tp) as [Et|[-> Ec]].
    - (* one byte *)
      rewrite Et.
      assert (l = 1).
      { destruct t; try discriminate Tp.
        - exact (tok_at_text s p c0 l Htl).
        - destruct image; [cbn [tok_text bracket_open] in Et; injection Et as _ E; discriminate E|].
          exact (tok_at_open_plain s p l Htl).
        - exact (proj1 (tok_at_close s p dest region l Htl)).
        - exact (proj1 (tok_at_span s p body a l Htl)). }
      subst l.
      assert (q1 = p + 1).
      { unfold chain_next in Hq1. rewrite Htl, Hclose in Hq1.
        destruct t; try discriminate Tp; injection Hq1 as <-; reflexivity. }
      subst q1.
      destruct (temit_str (one c) fs top) as [fs1 top1].
      replace (p + 2) with (g (p + 1)) by (rewrite g_above by lia; lia).
      exact (IH (p + 1) _ _ _ f' Hq1c ltac:(lia) Lg).
    - (* `![`: the `!`, then the `[` two bytes on *)
      pose proof (tok_at_open_image s p l Htl) as ->.
      assert (q1 = p + 2)
        by (unfold chain_next in Hq1; rewrite Htl in Hq1; injection Hq1 as <-; reflexivity).
      subst q1.
      destruct f' as [|f'']; [rewrite g_above in Lg by lia; lia|].
      assert (Ttx : tok_text (TOpen true) = (one c ++ one lbrack)%string)
        by (rewrite Ec; reflexivity).
      rewrite Ttx. cbn [tgo]. unfold tok_of at 1.
      replace (p + 2) with (S (S p)) by lia. rewrite image_open_next by exact Htl.
      cbn [option_map fst].
      assert (No : is_opener (mpairs M) (S (S p)) = false).
      { replace (S (S p)) with (g (p + 1)) by (rewrite g_above by lia; lia).
        rewrite is_opener_mpairs.
        destruct (is_opener M (p + 1)) eqn:O; [|reflexivity]. exfalso.
        apply is_opener_iff in O as [j Hj]. apply opener_on_chain in Hj.
        refine (chain_gap s M p (p + 2) (p + 1) Hchain _ ltac:(lia) Hj).
        rewrite Hq1; try (f_equal; lia). }
      rewrite <- temit_str_app.
      destruct (temit_str (one c) fs top) as [fs1 top1].
      unfold tstep at 1. rewrite No.
      destruct (temit_str (tok_text (TOpen false)) fs1 top1) as [fs2 top2] eqn:T2.
      replace (chain_next s' (mpairs M) (S (S p))) with (Some (g (S (S p)))).
      2: { unfold chain_next. rewrite image_open_next by exact Htl. rewrite g_above by lia.
           f_equal. lia. }
      cbn [is_hard]. cbn [tok_text bracket_open] in T2. rewrite T2.
      exact (IH (S (S p)) _ _ _ f'' ltac:(replace (S (S p)) with (p + 2) by lia; exact Hq1c)
               ltac:(lia) ltac:(rewrite g_above in Lg |- * by lia; lia)). }
  destruct (tok_off q Hq Hne) as [E|(L & t0 & E0 & Ck & Cm & Tc)].
  - (* the same token *)
    unfold tok_of at 1. rewrite E, Htl. cbn [option_map fst].
    rewrite tstep_same by assumption.
    destruct (tstep s M q t hard fs top) as [fs1 top1].
    rewrite (chain_next_g M q q1 Hq Hne E eq_refl Hq1).
    exact (IH q1 _ _ _ f' Hq1c ltac:(lia) Lg).
  - (* a `]` that closes nothing *)
    rewrite Htl in E0. injection E0 as E1 E2. subst t0 l.
    assert (Q1 : q1 = q + 1).
    { unfold chain_next in Hq1. rewrite Htl, Cm in Hq1.
      destruct t; cbn [closes_as] in Ck; try discriminate Ck; [destruct closes; discriminate Ck| |];
        injection Hq1 as <-; reflexivity. }
    subst q1.
    assert (Ts : tstep s M q t hard fs top = temit_str (one rbrack) fs top).
    { unfold tstep. rewrite Cm.
      destruct t; cbn [closes_as] in Ck; try discriminate Ck; [destruct closes; discriminate Ck| |];
        destruct fs as [|[]]; reflexivity. }
    assert (Nc' : is_closer (mpairs M) q = false)
      by (rewrite <- (g_below q) by lia; rewrite is_closer_mpairs; exact Cm).
    rewrite (g_below q) by lia. unfold tok_of at 1.
    destruct (tok_at s' q) as [[t' l']|] eqn:E'; [|contradiction Tc].
    cbn [option_map fst].
    assert (l' = 1 /\ tstep s' (mpairs M) q t' hard fs top = temit_str (one rbrack) fs top
            /\ is_hard t' = false) as (-> & Ts' & Hh).
    { destruct t'; destruct l' as [|[|]]; cbn [text_closer] in Tc; try contradiction;
        (split; [reflexivity|]); unfold tstep; try rewrite Nc';
        [subst c0| |]; (split; [destruct fs as [|[]]; reflexivity|reflexivity]). }
    rewrite Ts', Ts.
    assert (Cn : chain_next s' (mpairs M) q = Some (q + 1)).
    { unfold chain_next. rewrite E', Nc'.
      destruct t'; cbn [text_closer] in Tc; try contradiction; reflexivity. }
    rewrite Cn, Hh.
    replace (is_hard t) with false
      by (destruct t; cbn [closes_as] in Ck; try discriminate Ck; reflexivity).
    destruct (temit_str (one rbrack) fs top) as [fs1 top1].
    rewrite <- (g_below (q + 1)) at 1 by lia.
    exact (IH (q + 1) _ _ _ f' Hq1c ltac:(lia) Lg).
Qed.

Lemma no_trace_at : tree_of s' (fst (ref_read s')) = tree_of s M.
Proof.
  unfold tree_of. rewrite reading_s'. f_equal. f_equal.
  replace 0 with (g 0) at 1 by (apply g_below; lia).
  apply tgo_sim.
  - constructor.
  - lia.
  - rewrite g_below by lia. rewrite !length_append. cbn [String.length]. lia.
Qed.

End Escape.

(*
The theorem
===========
*)

(* The token at `p` is on the reading's chain, is in no pair, and is one
   a reading may take as text. *)
Definition read_as_text (s : string) (m : matching) (p : nat) : Prop :=
  chain s m p /\ is_opener m p = false /\ is_closer m p = false
  /\ exists t l, tok_at s p = Some (t, l) /\ text_tok t = true.

(* Escaping a `<`, `[`, `]` or `!` that begins a token read as text gives
   the same tree. *)
Theorem escape_no_trace : forall pre c post,
  text_byte c = true ->
  read_as_text (pre ++ String c post) (fst (ref_read (pre ++ String c post))) (String.length pre) ->
  tree_of (pre ++ String bslash (String c post))
          (fst (ref_read (pre ++ String bslash (String c post))))
  = tree_of (pre ++ String c post) (fst (ref_read (pre ++ String c post))).
Proof.
  intros pre c post Hc (Hch & Ho & Hcl & Ht).
  exact (no_trace_at pre post c Hc Hch Ho Hcl Ht).
Qed.

End WithTable.
