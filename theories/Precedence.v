(* ai-disclosure: autonomous *)

(* The reference's precedence rules for delimiters (syntax reference,
   "Precedence"), stated as a matching between openers and closers and
   independent of the scanner: the tokens of a line, the matchings the
   rules allow, the proof that exactly one exists, and the tree it
   describes. *)

From Stdlib Require Import String Ascii List Bool Lia Arith Sorted.
From DjotV Require Import Strings Ast InlineTable InlineView.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

(*
Tokens
======

The rows covered here are the bare ones whose unmatched token is its own
text (`_ * ^ ~` in djot's table).  The quotes are bare too, but an
unmatched quote is a curly quote and whether one may open depends on the
byte before it; the braced rows are reached only through `{`. *)

Definition bare_row (k : dstyle) : bool :=
  match dsyntax_of k, dc_decay cfg k with
  | DBare, DDSelf => true
  | _, _ => false
  end.

(* The bytes a line is drawn from: the characters of those rows, and
   bytes that no row and no other syntax claims.  The hyphen is claimed
   for dashes and the newline ends the line. *)
Definition in_alphabet (c : ascii) : bool :=
  (negb (Ascii.eqb c nl_char) && negb (dreserved c)
   && negb (Ascii.eqb c hyphen)
   && match dstyle_of c with Some k => bare_row k | None => true end)%bool.

Definition over_alphabet (s : string) : Prop :=
  forall c, In c (list_ascii_of_string s) -> in_alphabet c = true.

(* A text token is one byte, so that every token is nonempty. *)
Inductive token : Type :=
  | TText (c : ascii)
  | TDelim (k : dstyle) (opens closes : bool).

(* A run of a row's character is cut, left to right, into tokens of the
   row's width, and a remainder shorter than that is text.  A token may
   open when the byte after it is not whitespace, and may close when the
   byte before it is not (M2).  `prev` is the byte before `s`, and
   `skip` counts the bytes of a token already emitted that are still to
   be read. *)
Fixpoint lex (prev : option ascii) (skip : nat) (s : string) : list token :=
  match s with
  | EmptyString => []
  | String c rest =>
      match skip with
      | S n => lex (Some c) n rest
      | O =>
          match dstyle_of c with
          | Some k =>
              if prefix (dtoken k) s
              then TDelim k (nonspace_at (get (dwidth k) s)) (nonspace_at prev)
                     :: lex (Some c) (pred (dwidth k)) rest
              else TText c :: lex (Some c) 0 rest
          | None => TText c :: lex (Some c) 0 rest
          end
      end
  end.

Definition tokens (s : string) : list token := lex None 0 s.

(*
Matchings
=========

A matching is a list of pairs of token positions: `(i, j)` pairs the
opener at `i` with the closer at `j`.

An opener is *live* at `j` when it may still be closed there: it has not
been used as a closer, it has not been closed before `j`, and it is not
inside a pair that closed before `j`.  The last clause is the
reference's "any potential openers between the opener and the closer get
marked as regular text"; reading the pairs in the order of their closers
is "the first opener that gets closed takes precedence". *)

Definition matching : Type := list (nat * nat).

Definition may_open (ts : list token) (i : nat) (k : dstyle) : Prop :=
  exists cl, nth_error ts i = Some (TDelim k true cl).

Definition may_close (ts : list token) (j : nat) (k : dstyle) : Prop :=
  exists op, nth_error ts j = Some (TDelim k op true).

Definition closes (m : matching) (j : nat) : Prop :=
  exists i, In (i, j) m.

Definition live (ts : list token) (m : matching) (j p : nat) (k : dstyle)
  : Prop :=
  p < j /\ may_open ts p k /\ ~ closes m p
  /\ ~ (exists j', j' < j /\ In (p, j') m)
  /\ ~ (exists i' j', j' < j /\ In (i', j') m /\ i' < p < j').

(* "When there are multiple openers that might be matched with a given
   closer, the closest one is used." *)
Definition closest_live (ts : list token) (m : matching) (j : nat)
  (k : dstyle) (p : nat) : Prop :=
  live ts m j p k /\ forall q, live ts m j q k -> q <= p.

(* The matchings the rules allow.  A pair is a closer and the closest
   live opener of its style, with something between them (M3).  A closer
   left unmatched has no live opener of its style but one right before
   it, with nothing to enclose: `__a` pairs nothing, and the second `_`
   opens in its turn. *)
Definition valid (ts : list token) (m : matching) : Prop :=
  (forall i j, In (i, j) m ->
     exists k, may_close ts j k /\ closest_live ts m j k i /\ S i < j)
  /\ (forall j k, may_close ts j k -> ~ closes m j ->
        forall p, closest_live ts m j k p -> S p = j).

(*
The matching, computed
----------------------

Left to right, with the live openers innermost first.  A closer takes
the closest live opener of its style if something lies between them, and
the openers above it become text; otherwise the token opens, if it may. *)

Fixpoint pick (k : dstyle) (lv : list (nat * dstyle))
  : option (nat * list (nat * dstyle)) :=
  match lv with
  | [] => None
  | (p, k') :: rest => if dstyle_eq k k' then Some (p, rest) else pick k rest
  end.

Record rstate : Type := RState {
  rs_live : list (nat * dstyle);
  rs_pairs : matching
}.

Definition ropen (i : nat) (k : dstyle) (op : bool) (lv : list (nat * dstyle))
  : list (nat * dstyle) :=
  if op then (i, k) :: lv else lv.

Definition rstep (i : nat) (t : token) (s : rstate) : rstate :=
  match t with
  | TText _ => s
  | TDelim k op cl =>
      match (if cl then pick k (rs_live s) else None) with
      | Some (p, below) =>
          if Nat.ltb (S p) i
          then RState below ((p, i) :: rs_pairs s)
          else RState (ropen i k op (rs_live s)) (rs_pairs s)
      | None => RState (ropen i k op (rs_live s)) (rs_pairs s)
      end
  end.

Fixpoint rrun (i : nat) (ts : list token) (s : rstate) : rstate :=
  match ts with
  | [] => s
  | t :: rest => rrun (S i) rest (rstep i t s)
  end.

Definition ref_match (ts : list token) : matching :=
  rs_pairs (rrun 0 ts (RState [] [])).

(*
Uniqueness
----------

At most one matching is valid, so the rules determine it and `valid`,
not `ref_match`, is the specification.  The pairs are settled in the
order of their closers: whether an opener is live at `j` reads only the
pairs that closed before `j`. *)

Lemma may_close_fun : forall ts j k k',
  may_close ts j k -> may_close ts j k' -> k = k'.
Proof.
  intros ts j k k' [o1 H1] [o2 H2]. rewrite H1 in H2.
  injection H2 as E _. exact E.
Qed.

Lemma closest_live_fun : forall ts m j k p q,
  closest_live ts m j k p -> closest_live ts m j k q -> p = q.
Proof.
  intros ts m j k p q [Hp Mp] [Hq Mq].
  specialize (Mp q Hq). specialize (Mq p Hp). lia.
Qed.

Lemma live_agree : forall ts m1 m2 j p k,
  (forall i j', j' < j -> In (i, j') m1 -> In (i, j') m2) ->
  live ts m2 j p k -> live ts m1 j p k.
Proof.
  intros ts m1 m2 j p k E (Hlt & Ho & Hc & Hu & He).
  split; [exact Hlt|]. split; [exact Ho|]. split; [|split].
  - intros [i Hi]. apply Hc. exists i. apply E; [exact Hlt|exact Hi].
  - intros (j' & Hj' & Hi). apply Hu. exists j'. split; [exact Hj'|].
    apply E; assumption.
  - intros (i' & j' & Hj' & Hi & Hb). apply He. exists i', j'.
    split; [exact Hj'|]. split; [apply E; assumption|exact Hb].
Qed.

Lemma closest_live_agree : forall ts m1 m2 j k p,
  (forall i j', j' < j -> In (i, j') m1 <-> In (i, j') m2) ->
  closest_live ts m1 j k p -> closest_live ts m2 j k p.
Proof.
  intros ts m1 m2 j k p E [Hp Mp]. split.
  - apply (live_agree ts m2 m1); [|exact Hp].
    intros i j' Hj'. apply E, Hj'.
  - intros q Hq. apply Mp. apply (live_agree ts m1 m2); [|exact Hq].
    intros i j' Hj'. apply E, Hj'.
Qed.

Lemma closes_dec : forall m j, {closes m j} + {~ closes m j}.
Proof.
  intros m j.
  destruct (existsb (fun e => Nat.eqb (snd e) j) m) eqn:D.
  - left. apply existsb_exists in D as ([i j'] & Hin & Hj).
    apply Nat.eqb_eq in Hj. cbn in Hj. subst j'. exists i. exact Hin.
  - right. intros [i Hin].
    assert (existsb (fun e => Nat.eqb (snd e) j) m = true) as C.
    { apply existsb_exists. exists (i, j). split; [exact Hin|].
      apply Nat.eqb_refl. }
    rewrite D in C. discriminate.
Qed.

Local Lemma valid_step_in : forall ts ma mb j,
  valid ts ma -> valid ts mb ->
  (forall i j', j' < j -> In (i, j') ma <-> In (i, j') mb) ->
  forall i, In (i, j) ma -> In (i, j) mb.
Proof.
  intros ts ma mb j [Pa _] [Pb Ub] E i H.
  destruct (Pa i j H) as (k & Hk & Hcl & Hne).
  apply (closest_live_agree ts ma mb) in Hcl; [|exact E].
  destruct (closes_dec mb j) as [[i' Hi']|Hn].
  - destruct (Pb i' j Hi') as (k' & Hk' & Hcl' & _).
    rewrite <- (may_close_fun ts j k k' Hk Hk') in Hcl'.
    rewrite (closest_live_fun ts mb j k i i' Hcl Hcl'). exact Hi'.
  - specialize (Ub j k Hk Hn i Hcl). lia.
Qed.

Theorem valid_unique : forall ts m1 m2,
  valid ts m1 -> valid ts m2 -> forall i j, In (i, j) m1 <-> In (i, j) m2.
Proof.
  intros ts m1 m2 V1 V2 i j. revert i.
  induction j as [j IH] using lt_wf_ind. intros i. split.
  - apply (valid_step_in ts m1 m2 j V1 V2). intros i' j' Hj'. apply IH, Hj'.
  - apply (valid_step_in ts m2 m1 j V2 V1). intros i' j' Hj'.
    symmetry. apply IH, Hj'.
Qed.

(* "Containers can't overlap": a pair that opens inside another closes
   inside it. *)
Theorem valid_nested : forall ts m i j i' j',
  valid ts m -> In (i, j) m -> In (i', j') m -> i < i' < j -> j' < j.
Proof.
  intros ts m i j i' j' [P _] H H' Hb.
  destruct (P i j H) as (k & Hk & Hcl & _).
  destruct (P i' j' H') as (k' & Hk' & Hcl' & _).
  destruct (lt_eq_lt_dec j' j) as [[Hlt|Heq]|Hgt]; [exact Hlt| |].
  - subst j'. pose proof (may_close_fun ts j k k' Hk Hk') as <-.
    pose proof (closest_live_fun ts m j k i i' Hcl Hcl'). lia.
  - exfalso. destruct Hcl' as [(_ & _ & _ & _ & He) _].
    apply He. exists i, j. split; [exact Hgt|]. split; [exact H|].
    exact Hb.
Qed.

(*
The computed matching is valid
------------------------------

After the first `n` tokens, the live list holds exactly the openers live
at `n`, innermost first, and every pair and every closer so far obeys the
rules.  A new pair `(p, n)` leaves live at `n + 1` the openers below `p`,
which are the ones `pick` leaves below it. *)

Definition desc (lv : list (nat * dstyle)) : Prop :=
  StronglySorted (fun a b => fst b < fst a) lv.

Record rinv (ts : list token) (n : nat) (s : rstate) : Prop := RInv {
  ri_bound : forall i j, In (i, j) (rs_pairs s) -> j < n;
  ri_live : forall p k, In (p, k) (rs_live s) <-> live ts (rs_pairs s) n p k;
  ri_desc : desc (rs_live s);
  ri_pairs : forall i j, In (i, j) (rs_pairs s) ->
    exists k, may_close ts j k /\ closest_live ts (rs_pairs s) j k i
              /\ S i < j;
  ri_unmatched : forall j k, j < n -> may_close ts j k ->
    ~ closes (rs_pairs s) j ->
    forall p, closest_live ts (rs_pairs s) j k p -> S p = j
}.

Local Lemma dstyle_eq_iff : forall a b, dstyle_eq a b = true <-> a = b.
Proof. intros [] []; split; intros H; first [reflexivity | discriminate]. Qed.

Lemma pick_some : forall k lv p below,
  desc lv -> pick k lv = Some (p, below) ->
  In (p, k) lv
  /\ (forall q, In (q, k) lv -> q <= p)
  /\ (forall q k', In (q, k') below <-> In (q, k') lv /\ q < p)
  /\ desc below.
Proof.
  intros k lv. induction lv as [|[q k'] lv IH]; intros p below D H;
    [discriminate|].
  apply StronglySorted_inv in D as [D F].
  rewrite Forall_forall in F. cbn [pick] in H.
  destruct (dstyle_eq k k') eqn:E.
  - injection H as <- <-. apply dstyle_eq_iff in E. subst k'.
    split; [left; reflexivity|]. split; [|split; [|exact D]].
    + intros q' [Hq|Hq]; [inversion Hq; lia|].
      specialize (F _ Hq). cbn in F. lia.
    + intros q' k'. split.
      * intros Hq. split; [right; exact Hq|]. specialize (F _ Hq). exact F.
      * intros [[Hq|Hq] Hlt]; [inversion Hq; lia|exact Hq].
  - destruct (IH p below D H) as (Hin & Hmax & Hbelow & Dbelow).
    assert (q > p) as Hqp by (specialize (F _ Hin); exact F).
    split; [right; exact Hin|]. split; [|split; [|exact Dbelow]].
    + intros q' [Hq|Hq]; [|apply Hmax, Hq].
      inversion Hq; subst.
      assert (dstyle_eq k k = true) by (apply dstyle_eq_iff; reflexivity).
      congruence.
    + intros q' k''. rewrite Hbelow. split.
      * intros [Hq Hlt]. split; [right; exact Hq|exact Hlt].
      * intros [[Hq|Hq] Hlt]; [inversion Hq; lia|].
        split; [exact Hq|exact Hlt].
Qed.

Lemma pick_none : forall k lv, pick k lv = None -> forall q, ~ In (q, k) lv.
Proof.
  intros k lv. induction lv as [|[q k'] lv IH]; intros H q' Hin;
    [exact Hin|].
  cbn [pick] in H. destruct (dstyle_eq k k') eqn:E; [discriminate|].
  destruct Hin as [Hq|Hq]; [|exact (IH H q' Hq)].
  assert (k' = k) as -> by congruence.
  assert (dstyle_eq k k = true) by (apply dstyle_eq_iff; reflexivity).
  congruence.
Qed.

Local Lemma live_extend_none : forall ts m n q k,
  (forall i j, In (i, j) m -> S i < j /\ j < n) ->
  live ts m (S n) q k <-> live ts m n q k \/ (q = n /\ may_open ts n k).
Proof.
  intros ts m n q k B. unfold live, closes. split.
  - intros (Hlt & Ho & Hc & Hu & He).
    destruct (Nat.eq_dec q n) as [->|Hne];
      [right; split; [reflexivity|exact Ho]|].
    left. split; [lia|]. split; [exact Ho|]. split; [exact Hc|]. split.
    + intros (j' & Hj' & Hi). apply Hu. exists j'. split; [lia|exact Hi].
    + intros (i' & j' & Hj' & Hi & Hb). apply He. exists i', j'.
      split; [lia|]. split; [exact Hi|exact Hb].
  - intros [(Hlt & Ho & Hc & Hu & He)|[-> Ho]].
    + split; [lia|]. split; [exact Ho|]. split; [exact Hc|]. split.
      * intros (j' & Hj' & Hi). apply Hu. exists j'.
        split; [|exact Hi]. specialize (B _ _ Hi). lia.
      * intros (i' & j' & Hj' & Hi & Hb). apply He. exists i', j'.
        split; [|split; [exact Hi|exact Hb]]. specialize (B _ _ Hi). lia.
    + split; [lia|]. split; [exact Ho|]. split; [|split].
      * intros [i Hi]. specialize (B _ _ Hi). lia.
      * intros (j' & _ & Hi). specialize (B _ _ Hi). lia.
      * intros (i' & j' & _ & Hi & Hb). specialize (B _ _ Hi). lia.
Qed.


Local Lemma live_extend_pair : forall ts m n p q k,
  (forall i j, In (i, j) m -> j < n) -> p < n ->
  live ts ((p, n) :: m) (S n) q k <-> live ts m n q k /\ q < p.
Proof.
  intros ts m n p q k B Hp. unfold live, closes. split.
  - intros (Hlt & Ho & Hc & Hu & He).
    assert (q <> n) as Hqn.
    { intros ->. apply Hc. exists p. left. reflexivity. }
    assert (q <> p) as Hqp.
    { intros ->. apply Hu. exists n. split; [lia|left; reflexivity]. }
    assert (~ (p < q < n)) as Hin.
    { intros Hb. apply He. exists p, n. split; [lia|].
      split; [left; reflexivity|exact Hb]. }
    split; [|lia].
    split; [lia|]. split; [exact Ho|]. split; [|split].
    + intros [i Hi]. apply Hc. exists i. right. exact Hi.
    + intros (j' & Hj' & Hi). apply Hu. exists j'.
      split; [lia|right; exact Hi].
    + intros (i' & j' & Hj' & Hi & Hb). apply He. exists i', j'.
      split; [lia|]. split; [right; exact Hi|exact Hb].
  - intros [(Hlt & Ho & Hc & Hu & He) Hqp].
    split; [lia|]. split; [exact Ho|]. split; [|split].
    + intros [i [E|Hi]]; [injection E as _ ->; lia|].
      apply Hc. exists i. exact Hi.
    + intros (j' & Hj' & [E|Hi]); [injection E as -> _; lia|].
      apply Hu. exists j'. split; [apply B in Hi; exact Hi|exact Hi].
    + intros (i' & j' & Hj' & [E|Hi] & Hb); [injection E as -> ->; lia|].
      apply He. exists i', j'. split; [apply B in Hi; exact Hi|].
      split; [exact Hi|exact Hb].
Qed.


(* The pairs closed before `j` are the same once a pair closes at
   `n >= j`. *)
Local Lemma agree_before_pair : forall (m : matching) p n j,
  j <= n -> forall i j', j' < j -> In (i, j') ((p, n) :: m) <-> In (i, j') m.
Proof.
  intros m p n j Hj i j' Hj'. cbn. split; [|intros H; right; exact H].
  intros [E|H]; [injection E as _ ->; lia|exact H].
Qed.


Local Lemma rinv_keep : forall ts n lv m lv',
  rinv ts n (RState lv m) ->
  (forall p k, In (p, k) lv' <-> In (p, k) lv \/ (p = n /\ may_open ts n k)) ->
  desc lv' ->
  (forall k, may_close ts n k ->
     forall p, closest_live ts m n k p -> S p = n) ->
  rinv ts (S n) (RState lv' m).
Proof.
  intros ts n lv m lv' [Bd Lv Ds Pr Un] Hlv' D' Hn.
  cbn [rs_live rs_pairs] in *.
  assert (B : forall i j, In (i, j) m -> S i < j /\ j < n).
  { intros i j H. destruct (Pr i j H) as (_ & _ & _ & Hne).
    split; [exact Hne|exact (Bd i j H)]. }
  constructor; cbn [rs_live rs_pairs].
  - intros i j H. specialize (Bd i j H). lia.
  - intros p k. rewrite Hlv', live_extend_none by exact B. rewrite Lv.
    reflexivity.
  - exact D'.
  - exact Pr.
  - intros j k Hj Hk Hc p Hp. destruct (Nat.eq_dec j n) as [->|Hne].
    + exact (Hn k Hk p Hp).
    + apply (Un j k); [lia|exact Hk|exact Hc|exact Hp].
Qed.


Local Lemma rinv_pair : forall ts n lv m p k below,
  rinv ts n (RState lv m) -> may_close ts n k ->
  closest_live ts m n k p -> S p < n ->
  (forall q k', In (q, k') below <-> In (q, k') lv /\ q < p) -> desc below ->
  rinv ts (S n) (RState below ((p, n) :: m)).
Proof.
  intros ts n lv m p k below [Bd Lv Ds Pr Un] Hk Hcl Hne Hbelow Db.
  cbn [rs_live rs_pairs] in *.
  assert (Agree : forall j, j <= n -> forall i j', j' < j ->
            In (i, j') m <-> In (i, j') ((p, n) :: m)).
  { intros j Hj i j' Hj'. symmetry.
    apply (agree_before_pair m p n j Hj i j' Hj'). }
  constructor; cbn [rs_live rs_pairs].
  - intros i j [E|H]; [injection E as _ <-; lia|].
    specialize (Bd i j H). lia.
  - intros q k'. rewrite Hbelow, live_extend_pair by (exact Bd || lia).
    rewrite Lv. reflexivity.
  - exact Db.
  - intros i j [E|H].
    + injection E as <- <-. exists k. split; [exact Hk|].
      split; [|exact Hne].
      apply (closest_live_agree ts m); [apply Agree; lia|exact Hcl].
    + destruct (Pr i j H) as (k' & Hk' & Hc' & Hn'). exists k'.
      split; [exact Hk'|]. split; [|exact Hn'].
      apply (closest_live_agree ts m); [|exact Hc'].
      apply Agree. specialize (Bd i j H). lia.
  - intros j k' Hj Hk' Hc q Hq. destruct (Nat.eq_dec j n) as [->|Hjn].
    + exfalso. apply Hc. exists p. left. reflexivity.
    + apply (Un j k'); [lia|exact Hk'|..].
      * intros [i Hi]. apply Hc. exists i. right. exact Hi.
      * apply (closest_live_agree ts ((p, n) :: m)); [|exact Hq].
        intros i j' Hj'. symmetry. apply (Agree j); lia.
Qed.


Lemma rinv_step : forall ts n s t,
  nth_error ts n = Some t -> rinv ts n s -> rinv ts (S n) (rstep n t s).
Proof.
  intros ts n [lv m] t Hn I.
  pose proof I as [Bd Lv Ds Pr Un]. cbn [rs_live rs_pairs] in *.
  assert (Lt : forall p k, In (p, k) lv -> p < n).
  { intros p k H. apply Lv in H. destruct H as [H _]. exact H. }
  destruct t as [c|k op cl]; cbn [rstep rs_live rs_pairs].
  - apply (rinv_keep ts n lv m lv I).
    + intros p k. split; [intros H; left; exact H|].
      intros [H|[-> [cl H]]]; [exact H|]. rewrite Hn in H. discriminate.
    + exact Ds.
    + intros k [op H]. rewrite Hn in H. discriminate.
  - assert (Ro : forall p k', In (p, k') (ropen n k op lv)
                  <-> In (p, k') lv \/ (p = n /\ may_open ts n k')).
    { intros p k'. unfold ropen, may_open. rewrite Hn. destruct op; cbn.
      - split.
        + intros [E|H]; [|left; exact H].
          right. injection E as -> ->.
          split; [reflexivity|exists cl; reflexivity].
        + intros [H|[-> [cl' E]]]; [right; exact H|].
          left. injection E as -> _. reflexivity.
      - split; [intros H; left; exact H|].
        intros [H|[-> [cl' E]]]; [exact H|discriminate]. }
    assert (Dr : desc (ropen n k op lv)).
    { unfold ropen. destruct op; [|exact Ds]. constructor; [exact Ds|].
      apply Forall_forall. intros [p k'] H. cbn. exact (Lt p k' H). }
    assert (Mc : forall k', may_close ts n k' -> cl = true /\ k' = k).
    { intros k' [op' H]. rewrite Hn in H. injection H as -> _ ->.
      split; reflexivity. }
    destruct cl; [destruct (pick k lv) as [[p below]|] eqn:P|].
    + destruct (pick_some k lv p below Ds P) as (Hin & Hmax & Hbelow & Db).
      assert (Hcl : closest_live ts m n k p).
      { split; [apply Lv, Hin|]. intros q Hq. apply Hmax, Lv, Hq. }
      destruct (Nat.ltb (S p) n) eqn:L.
      * apply Nat.ltb_lt in L.
        apply (rinv_pair ts n lv m p k below I);
          [exists op; exact Hn|exact Hcl|exact L|exact Hbelow|exact Db].
      * apply Nat.ltb_ge in L. apply (rinv_keep ts n lv m _ I Ro Dr).
        intros k' Hk' p' Hp'. destruct (Mc k' Hk') as [_ ->].
        rewrite <- (closest_live_fun ts m n k p p' Hcl Hp').
        specialize (Lt p k Hin). lia.
    + apply (rinv_keep ts n lv m _ I Ro Dr).
      intros k' Hk' p' [Hp' _]. destruct (Mc k' Hk') as [_ ->].
      apply Lv in Hp'. destruct (pick_none k lv P p' Hp').
    + apply (rinv_keep ts n lv m _ I Ro Dr).
      intros k' Hk'. destruct (Mc k' Hk') as [E _]. discriminate.
Qed.


Lemma rinv_run : forall ts pre suf s,
  ts = (pre ++ suf)%list -> rinv ts (length pre) s ->
  rinv ts (length ts) (rrun (length pre) suf s).
Proof.
  intros ts pre suf. revert pre.
  induction suf as [|t rest IH]; intros pre s E I; cbn [rrun].
  - rewrite E, app_nil_r. rewrite E, app_nil_r in I. exact I.
  - assert (Hn : nth_error ts (length pre) = Some t).
    { rewrite E, nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
    specialize (IH (pre ++ [t])%list (rstep (length pre) t s)).
    rewrite length_app in IH. cbn [length] in IH. rewrite Nat.add_1_r in IH.
    apply IH; [rewrite E, <- app_assoc; reflexivity|].
    apply rinv_step; [exact Hn|exact I].
Qed.


Theorem ref_match_valid : forall ts, valid ts (ref_match ts).
Proof.
  intros ts. unfold ref_match.
  assert (I0 : rinv ts (length (@nil token)) (RState [] [])).
  { constructor; cbn [rs_live rs_pairs length].
    - intros i j [].
    - intros p k. split; [intros []|intros [H _]; lia].
    - constructor.
    - intros i j [].
    - intros j k H. lia. }
  pose proof (rinv_run ts [] ts _ eq_refl I0) as [_ _ _ Pr Un].
  split; [exact Pr|].
  intros j k Hk. apply Un; [|exact Hk].
  destruct Hk as [op H]. apply nth_error_Some. rewrite H. discriminate.
Qed.


(*
The tree
========

What a matching describes: each pair becomes its row's node around the
tokens between, and every other token is text.  Adjacent text is one
`Str`, as the scanner writes it. *)

Definition str_snoc (s : string) (out : inlines) : inlines :=
  match out with
  | Node p [] (Str t) :: rest => Node p [] (Str (t ++ s)) :: rest
  | _ => mk (Str s) :: out
  end.

Definition tok_text (t : token) : string :=
  match t with TText c => one c | TDelim k _ _ => dtoken k end.

(* The frames of the open pairs, innermost first, each with its style and
   its content reversed, above the reversed top level. *)
Definition tframes : Type := list (dstyle * inlines).

Definition temit (n : node inline) (fs : tframes) (top : inlines)
  : tframes * inlines :=
  match fs with
  | [] => ([], n :: top)
  | (k, acc) :: rest => ((k, n :: acc) :: rest, top)
  end.

Definition temit_str (s : string) (fs : tframes) (top : inlines)
  : tframes * inlines :=
  match fs with
  | [] => ([], str_snoc s top)
  | (k, acc) :: rest => ((k, str_snoc s acc) :: rest, top)
  end.

Definition is_opener (m : matching) (i : nat) : bool :=
  existsb (fun e => Nat.eqb (fst e) i) m.

Definition is_closer (m : matching) (j : nat) : bool :=
  existsb (fun e => Nat.eqb (snd e) j) m.

Fixpoint tree_go (m : matching) (i : nat) (ts : list token)
  (fs : tframes) (top : inlines) : inlines :=
  match ts with
  | [] => List.rev top
  | t :: rest =>
      let '(fs', top') :=
        match t, fs with
        | TDelim k _ _, _ =>
            if is_opener m i then ((k, []) :: fs, top)
            else match is_closer m i, fs with
                 | true, (k', acc) :: fs0 =>
                     temit (mk (dnode k' (List.rev acc))) fs0 top
                 | _, _ => temit_str (tok_text t) fs top
                 end
        | TText _, _ => temit_str (tok_text t) fs top
        end in
      tree_go m (S i) rest fs' top'
  end.

(* A valid matching closes every pair it opens, so no frame is left at
   the end; `tree_go` drops any that are. *)
Definition tree_of (ts : list token) (m : matching) : inlines :=
  tree_go m 0 ts [] [].

End WithTable.
