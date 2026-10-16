(* ai-disclosure: autonomous *)

(** * A rendering with no redundant escape

   `irredundant_spec` is `Render.render_djot` with escapes taken out
   while the parse stays the same: it deletes a backslash, or a `{` and a
   later `}`, whenever what is left parses to the document, until no such
   deletion is left (`shrink`).

   So its theorems hold by construction.  It parses back to every
   canonical document (`spec_roundtrip`), and deleting any one of its
   backslashes (`spec_backslash`), or a brace pair (`spec_braces`),
   changes the parse.  None speaks of escapes: a backslash in a code
   block or in `\\` is content, and deleting it changes the parse for
   that reason.

   `render_djot_irredundant` is the renderer to run.  It runs the same
   test incrementally, reparsing from the line a deletion changes until
   the parser is idle again, and is the specification
   (`irredundant_is_spec`), so the theorems are its own:
   `irredundant_roundtrip`, `irredundant_backslash` and
   `irredundant_braces`.  The braces are those with no empty line between
   them, which a span cannot cross. *)

From Stdlib Require Import String Ascii List Bool Arith Lia.
From DjotV Require Import Strings Ast AstEq Attributes InlineTable Step Render
  Roundtrip.
Import ListNotations.

Local Open Scope string_scope.

(*
Deletions
=========
*)

(* `s` without its byte at `i`. *)
Fixpoint del (i : nat) (s : string) : string :=
  match s, i with
  | EmptyString, _ => EmptyString
  | String _ rest, 0 => rest
  | String c rest, S i' => String c (del i' rest)
  end.

Lemma del_length : forall i s, i < String.length s ->
  String.length (del i s) = String.length s - 1.
Proof.
  induction i as [|i IH]; intros [|c s] H; cbn in *; try lia.
  rewrite IH by lia. lia.
Qed.

Lemma get_length : forall i s c, String.get i s = Some c -> i < String.length s.
Proof.
  induction i as [|i IH]; intros [|d s] c H; cbn in *; try discriminate; [lia|].
  apply IH in H. lia.
Qed.

(* The byte from [p] on that is a newline before an empty line, or the
   end of [s].  A braced span cannot cross an empty line. *)
Fixpoint stop_go (fuel p : nat) (s : string) : nat :=
  match fuel with
  | 0 => p
  | S f =>
      match String.get p s, String.get (S p) s with
      | Some c, Some d =>
          if Ascii.eqb c "010"%char && Ascii.eqb d "010"%char then p
          else stop_go f (S p) s
      | _, _ => String.length s
      end
  end.

Definition para_stop (s : string) (p : nat) : nat := stop_go (String.length s - p) p s.

(* Whether a newline before an empty line sits at a byte in [p, q). *)
Definition blank_between (s : string) (p q : nat) : Prop :=
  exists r, p <= r < q /\ String.get r s = Some "010"%char
            /\ String.get (S r) s = Some "010"%char.

Lemma stop_go_ge : forall s f q, q <= String.length s -> q <= stop_go f q s.
Proof.
  intros s f. induction f as [|f IH]; intros q Hq; cbn [stop_go]; [lia|].
  destruct (String.get q s) as [c|]; [|lia].
  destruct (String.get (S q) s) as [d|] eqn:Ed; [|lia].
  destruct (Ascii.eqb c "010"%char && Ascii.eqb d "010"%char); [lia|].
  apply get_length in Ed. specialize (IH (S q) ltac:(lia)). lia.
Qed.

Lemma get_some : forall i s, i < String.length s -> exists c, String.get i s = Some c.
Proof.
  induction i as [|i IH]; intros [|c s] H; cbn in *; try lia; [eauto|].
  apply IH. lia.
Qed.

Lemma stop_go_beyond : forall s f p j,
  p <= j -> j < String.length s -> j < p + f -> String.get j s <> Some "010"%char ->
  ~ blank_between s p j -> j < stop_go f p s.
Proof.
  intros s f. induction f as [|f IH]; intros p j Hp Hj Hf Hn Hb; cbn [stop_go]; [lia|].
  destruct (get_some p s ltac:(lia)) as [c Ec]. rewrite Ec.
  destruct (String.get (S p) s) as [d|] eqn:Ed; [|lia].
  destruct (Ascii.eqb c "010"%char && Ascii.eqb d "010"%char) eqn:E.
  - exfalso. apply andb_true_iff in E as [E1 E2].
    apply Ascii.eqb_eq in E1, E2. subst c d.
    destruct (Nat.eq_dec p j) as [->|Hne]; [contradiction|].
    apply Hb. exists p. repeat split; [lia|lia|exact Ec|exact Ed].
  - destruct (Nat.eq_dec p j) as [->|Hne].
    + pose proof (stop_go_ge s f (S j)). apply get_length in Ed. lia.
    + apply IH; [lia|exact Hj|lia|exact Hn|].
      intros [r [Hr Hrs]]. apply Hb. exists r. split; [lia|exact Hrs].
Qed.

Lemma para_stop_beyond : forall s p j,
  p <= j -> j < String.length s -> String.get j s <> Some "010"%char ->
  ~ blank_between s p j -> j < para_stop s p.
Proof.
  intros s p j Hp Hj Hn Hb. apply stop_go_beyond; auto; lia.
Qed.

(* A deletion: the string left, and the bytes deleted, a backslash's or
   a `{`'s and the `}`'s. *)
Definition cand : Type := (string * (nat * option nat))%type.

Definition apply_del (d : nat * option nat) (s : string) : string :=
  match d with
  | (i, None) => del i s
  | (i, Some j) => del i (del j s)
  end.

(* The deletions a spelling is tested against: each backslash, and each
   `{` with each `}` after it and no empty line between.  [deletions_at]
   are those starting at byte [i]. *)
Definition deletions_at (s : string) (i : nat) : list cand :=
  match String.get i s with
  | Some c =>
      if Ascii.eqb c bslash then [(del i s, (i, None))]
      else if Ascii.eqb c lbrace then
        flat_map
          (fun j =>
             match String.get j s with
             | Some d => if Ascii.eqb d rbrace then [(del i (del j s), (i, Some j))] else []
             | None => []
             end)
          (seq (S i) (para_stop s (S i) - S i))
      else []
  | None => []
  end.

Definition deletions (s : string) : list cand :=
  flat_map (deletions_at s) (seq 0 (String.length s)).

Lemma deletions_backslash : forall s i,
  String.get i s = Some bslash -> In (del i s, (i, None)) (deletions s).
Proof.
  intros s i H. apply in_flat_map. exists i. split.
  - apply in_seq. apply get_length in H. lia.
  - unfold deletions_at. rewrite H. cbn. left. reflexivity.
Qed.

Lemma deletions_braces : forall s i j,
  String.get i s = Some lbrace -> String.get j s = Some rbrace -> i < j ->
  ~ blank_between s i j -> In (del i (del j s), (i, Some j)) (deletions s).
Proof.
  intros s i j Hi Hj Hij Hb. apply in_flat_map. exists i. split.
  - apply in_seq. apply get_length in Hi. lia.
  - unfold deletions_at. rewrite Hi. cbn. apply in_flat_map. exists j. split.
    + apply in_seq. apply get_length in Hj as Hl.
      assert (j < para_stop s (S i)); [|lia].
      apply para_stop_beyond; [lia | exact Hl | rewrite Hj; discriminate |].
      intros [r [Hr Hrs]]. apply Hb. exists r. split; [lia | exact Hrs].
    + rewrite Hj. cbn. left. reflexivity.
Qed.

(* What a deletion says of its bytes: the byte at [i] is a backslash, or
   it is a `{` and the one at [j], after it, a `}`. *)
Definition del_ok (s : string) (d : nat * option nat) : Prop :=
  match d with
  | (i, None) => String.get i s = Some bslash
  | (i, Some j) => String.get i s = Some lbrace /\ String.get j s = Some rbrace /\ i < j
  end.

Lemma deletions_spec : forall s c, In c (deletions s) ->
  fst c = apply_del (snd c) s /\ del_ok s (snd c).
Proof.
  intros s c H. apply in_flat_map in H as [i [Hi H]]. apply in_seq in Hi.
  unfold deletions_at in H. destruct (String.get i s) as [x|] eqn:Ex; [|destruct H].
  destruct (Ascii.eqb x bslash) eqn:Eb.
  { destruct H as [<-|[]]. apply Ascii.eqb_eq in Eb. subst x. cbn. auto. }
  destruct (Ascii.eqb x lbrace) eqn:El; [|destruct H].
  apply Ascii.eqb_eq in El. subst x.
  apply in_flat_map in H as [j [Hj H]]. apply in_seq in Hj.
  destruct (String.get j s) as [y|] eqn:Ey; [|destruct H].
  destruct (Ascii.eqb y rbrace) eqn:Er; [|destruct H].
  apply Ascii.eqb_eq in Er. subst y.
  destruct H as [<-|[]]. cbn. repeat split; auto; lia.
Qed.

Lemma deletions_shorter : forall s c, In c (deletions s) ->
  String.length (fst c) < String.length s.
Proof.
  intros s c H. apply deletions_spec in H as [-> H].
  destruct c as [t [i [j|]]]; cbn in *.
  - destruct H as [Hi [Hj Hij]]. apply get_length in Hi, Hj.
    rewrite del_length; rewrite del_length by lia; lia.
  - apply get_length in H. rewrite del_length by lia. lia.
Qed.

(*
Shrinking
=========
*)

(* The first of [l] that [f] accepts, with what [f] returns for it. *)
Fixpoint pick {B : Type} (f : cand -> option B) (l : list cand) : option (cand * B) :=
  match l with
  | [] => None
  | c :: rest => match f c with Some b => Some (c, b) | None => pick f rest end
  end.

Lemma pick_some : forall {B} (f : cand -> option B) l c b,
  pick f l = Some (c, b) -> In c l /\ f c = Some b.
Proof.
  intros B f l c b. induction l as [|x l IH]; cbn; [discriminate|].
  destruct (f x) as [y|] eqn:E.
  - intros H. injection H as <- <-. auto.
  - intros H. apply IH in H as [H1 H2]. auto.
Qed.

Lemma pick_none : forall {B} (f : cand -> option B) l,
  pick f l = None -> forall c, In c l -> f c = None.
Proof.
  intros B f l. induction l as [|x l IH]; cbn; [tauto|].
  destruct (f x) eqn:E; [discriminate|].
  intros H c [<-|Hc]; [exact E | exact (IH H c Hc)].
Qed.

Lemma pick_app : forall {B} (f : cand -> option B) l1 l2,
  pick f (l1 ++ l2) = match pick f l1 with Some r => Some r | None => pick f l2 end.
Proof.
  intros B f l1 l2. induction l1 as [|x l1 IH]; [reflexivity|].
  cbn. destruct (f x); [reflexivity | exact IH].
Qed.

(* The first deletion at byte [i] that [f] accepts, found without
   building the list. *)
Definition first_at {B : Type} (f : cand -> option B) (s : string) (i : nat)
  : option (cand * B) :=
  let test c := match f c with Some b => Some (c, b) | None => None end in
  match String.get i s with
  | Some c =>
      if Ascii.eqb c bslash then test (del i s, (i, None))
      else if Ascii.eqb c lbrace then
        (fix go (m j : nat) : option (cand * B) :=
           match m with
           | 0 => None
           | S m' =>
               match match String.get j s with
                     | Some d =>
                         if Ascii.eqb d rbrace then test (del i (del j s), (i, Some j))
                         else None
                     | None => None
                     end with
               | Some r => Some r
               | None => go m' (S j)
               end
           end) (para_stop s (S i) - S i) (S i)
      else None
  | None => None
  end.

Lemma first_at_pick : forall {B} (f : cand -> option B) s i,
  first_at f s i = pick f (deletions_at s i).
Proof.
  intros B f s i. unfold first_at, deletions_at.
  destruct (String.get i s) as [c|]; [|reflexivity].
  destruct (Ascii.eqb c bslash); [cbn; destruct (f (del i s, (i, None))); reflexivity|].
  destruct (Ascii.eqb c lbrace); [|reflexivity].
  set (m := para_stop s (S i) - S i). clearbody m.
  generalize (S i) as j. induction m as [|m IH]; intros j; [reflexivity|].
  cbn [seq flat_map]. rewrite pick_app, <- IH.
  destruct (String.get j s) as [d|]; [|reflexivity].
  destruct (Ascii.eqb d rbrace); [|reflexivity].
  cbn. destruct (f (del i (del j s), (i, Some j))); reflexivity.
Qed.

(* The first deletion [f] accepts at one of [bytes], with its byte. *)
Fixpoint first_in {B : Type} (f : cand -> option B) (s : string) (bytes : list nat)
  : option (cand * B * nat) :=
  match bytes with
  | [] => None
  | i :: rest =>
      match first_at f s i with
      | Some (c, b) => Some (c, b, i)
      | None => first_in f s rest
      end
  end.

Lemma first_in_some : forall {B} (f : cand -> option B) s l c b i,
  first_in f s l = Some (c, b, i) -> In i l /\ first_at f s i = Some (c, b).
Proof.
  intros B f s l c b i. induction l as [|x l IH]; cbn; [discriminate|].
  destruct (first_at f s x) as [[u y]|] eqn:E.
  - intros H. injection H as <- <- <-. auto.
  - intros H. apply IH in H as [H1 H2]. auto.
Qed.

Lemma first_in_none : forall {B} (f : cand -> option B) s l,
  first_in f s l = None -> forall i, In i l -> first_at f s i = None.
Proof.
  intros B f s l. induction l as [|x l IH]; cbn; [tauto|].
  destruct (first_at f s x) as [[u y]|] eqn:E; [discriminate|].
  intros H i [<-|Hi]; [exact E | exact (IH H i Hi)].
Qed.

(* [first_in] over the [n] bytes from [i], counting rather than
   building the list. *)
Fixpoint first_from {B : Type} (f : cand -> option B) (s : string) (n i : nat)
  : option (cand * B * nat) :=
  match n with
  | 0 => None
  | S m =>
      match first_at f s i with
      | Some (c, b) => Some (c, b, i)
      | None => first_from f s m (S i)
      end
  end.

Lemma first_from_in : forall {B} (f : cand -> option B) s n i,
  first_from f s n i = first_in f s (seq i n).
Proof.
  intros B f s n. induction n as [|n IH]; intros i; [reflexivity|].
  cbn. rewrite IH. reflexivity.
Qed.

(* The next deletion: from byte [k] on, where the last one was, and from
   the start if there is none there. *)
Definition next {B : Type} (f : cand -> option B) (k : nat) (s : string)
  : option (cand * B * nat) :=
  match first_from f s (String.length s - k) k with
  | Some r => Some r
  | None => first_from f s (String.length s) 0
  end.

Lemma next_some : forall {B} (f : cand -> option B) k s c b i,
  next f k s = Some (c, b, i) -> In c (deletions s) /\ f c = Some b.
Proof.
  intros B f k s c b i H. unfold next in H. rewrite !first_from_in in H.
  assert (Hl : exists l, first_in f s l = Some (c, b, i)
                         /\ forall x, In x l -> x < String.length s).
  { destruct (first_in f s (seq k _)) as [r|] eqn:E.
    - exists (seq k (String.length s - k)). injection H as ->.
      split; [exact E | intros x Hx; apply in_seq in Hx; lia].
    - exists (seq 0 (String.length s)).
      split; [exact H | intros x Hx; apply in_seq in Hx; lia]. }
  destruct Hl as [l [E Hb]]. apply first_in_some in E as [Hi E].
  rewrite first_at_pick in E. apply pick_some in E as [Ht Hf].
  split; [|exact Hf]. apply in_flat_map. exists i.
  split; [apply in_seq; specialize (Hb i Hi); lia | exact Ht].
Qed.

Lemma next_none : forall {B} (f : cand -> option B) k s,
  next f k s = None -> forall c, In c (deletions s) -> f c = None.
Proof.
  intros B f k s H c Hc. unfold next in H. rewrite !first_from_in in H.
  destruct (first_in f s (seq k _)); [discriminate|].
  apply in_flat_map in Hc as [i [Hi Hc]].
  pose proof (first_in_none _ _ _ H i Hi) as E.
  rewrite first_at_pick in E. exact (pick_none _ _ E c Hc).
Qed.

(* Two tests that accept the same deletions of [s] find the same next
   one. *)
Definition agree {B B'} (f : cand -> option B) (g : cand -> option B') (c : cand) : Prop :=
  match f c, g c with Some _, Some _ | None, None => True | _, _ => False end.

Lemma pick_same : forall {B B'} (f : cand -> option B) (g : cand -> option B') l,
  (forall c, In c l -> agree f g c) ->
  match pick f l, pick g l with
  | Some (c, _), Some (c', _) => c = c'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros B B' f g l H. induction l as [|x l IH]; cbn; [exact I|].
  specialize (H x (or_introl eq_refl)) as Hx. unfold agree in Hx.
  destruct (f x), (g x); try contradiction; [reflexivity|].
  apply IH. intros c Hc. apply H. right. exact Hc.
Qed.

Lemma first_in_same : forall {B B'} (f : cand -> option B) (g : cand -> option B') s l,
  (forall i, In i l -> forall c, In c (deletions_at s i) -> agree f g c) ->
  match first_in f s l, first_in g s l with
  | Some (c, _, i), Some (c', _, i') => c = c' /\ i = i'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros B B' f g s l H. induction l as [|x l IH]; cbn; [exact I|].
  pose proof (pick_same f g (deletions_at s x) (H x (or_introl eq_refl))) as Hx.
  rewrite <- !first_at_pick in Hx.
  destruct (first_at f s x) as [[c b]|], (first_at g s x) as [[c' b']|];
    try contradiction; [split; [exact Hx | reflexivity]|].
  apply IH. intros i Hi. apply H. right. exact Hi.
Qed.

Lemma next_same : forall {B B'} (f : cand -> option B) (g : cand -> option B') k s,
  (forall c, In c (deletions s) -> agree f g c) ->
  match next f k s, next g k s with
  | Some (c, _, i), Some (c', _, i') => c = c' /\ i = i'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros B B' f g k s H.
  assert (Hin : forall l, (forall i, In i l -> i < String.length s) ->
            forall i, In i l -> forall c, In c (deletions_at s i) -> agree f g c).
  { intros l Hl i Hi c Hc. apply H. apply in_flat_map. exists i.
    split; [apply in_seq; specialize (Hl i Hi); lia | exact Hc]. }
  unfold next. rewrite !first_from_in.
  assert (B1 : forall i, In i (seq k (String.length s - k)) -> i < String.length s)
    by (intros i Hi; apply in_seq in Hi; lia).
  assert (B2 : forall i, In i (seq 0 (String.length s)) -> i < String.length s)
    by (intros i Hi; apply in_seq in Hi; lia).
  pose proof (first_in_same f g s _ (Hin _ B1)) as H1.
  pose proof (first_in_same f g s _ (Hin _ B2)) as H2.
  destruct (first_in f s (seq k _)) as [[[c b] i]|], (first_in g s (seq k _)) as [[[c' b'] i']|];
    try contradiction; [exact H1|].
  exact H2.
Qed.

(* Takes the next deletion the test accepts, while there is one.  The
   test carries what it knows of the current string, [kn], and returns
   it for the string it accepts.  Each deletion is shorter, so a fuel of
   the length runs to the end. *)
Fixpoint shrink_by {C : Type} (test : C -> cand -> option C) (fuel k : nat)
  (kn : C) (s : string) : string :=
  match fuel with
  | 0 => s
  | S f =>
      match next (test kn) k s with
      | Some (c, kn', i) => shrink_by test f i kn' (fst c)
      | None => s
      end
  end.

Definition accept (ok : string -> bool) (_ : unit) (c : cand) : option unit :=
  if ok (fst c) then Some tt else None.

Definition shrink (ok : string -> bool) (fuel : nat) (s : string) : string :=
  shrink_by (accept ok) fuel 0 tt s.

Lemma shrink_ok : forall ok f s, ok s = true -> ok (shrink ok f s) = true.
Proof.
  intros ok f. unfold shrink. generalize 0.
  induction f as [|f IH]; intros k s H; cbn [shrink_by]; [exact H|].
  destruct (next (accept ok tt) k s) as [[[c []] i]|] eqn:E; [|exact H].
  apply IH. apply next_some in E as [_ E]. unfold accept in E.
  destruct (ok (fst c)); [reflexivity | discriminate].
Qed.

Lemma shrink_final : forall ok f s, String.length s <= f ->
  forall c, In c (deletions (shrink ok f s)) -> ok (fst c) = false.
Proof.
  intros ok f. unfold shrink. generalize 0.
  induction f as [|f IH]; intros k s Hf c Hc; cbn [shrink_by] in Hc.
  - destruct s; [destruct Hc | cbn in Hf; lia].
  - destruct (next (accept ok tt) k s) as [[[c' []] i]|] eqn:E.
    + apply next_some in E as [Hin _]. apply deletions_shorter in Hin.
      apply (IH i (fst c')); [lia | exact Hc].
    + pose proof (next_none _ _ _ E c Hc) as N. unfold accept in N.
      destruct (ok (fst c)); [discriminate | reflexivity].
Qed.

(* A test whose knowledge [R] tracks the string, and that accepts the
   deletions [ok] accepts, shrinks as [ok] does. *)
Lemma shrink_by_accept : forall {C} (test : C -> cand -> option C) (R : C -> string -> Prop)
  ok f k kn s,
  (forall kn s c, R kn s -> ok s = true -> In c (deletions s) ->
     match test kn c with
     | Some kn' => ok (fst c) = true /\ R kn' (fst c)
     | None => ok (fst c) = false
     end) ->
  R kn s -> ok s = true ->
  shrink_by test f k kn s = shrink_by (accept ok) f k tt s.
Proof.
  intros C test R ok f. induction f as [|f IH]; intros k kn s H Hr Hs; [reflexivity|].
  cbn [shrink_by].
  assert (Ha : forall c, In c (deletions s) -> agree (test kn) (accept ok tt) c).
  { intros c Hc. pose proof (H kn s c Hr Hs Hc) as Hk. unfold agree, accept.
    destruct (test kn c) as [kn'|]; [destruct Hk as [-> _]; exact I | rewrite Hk; exact I]. }
  pose proof (next_same (test kn) (accept ok tt) k s Ha) as N.
  destruct (next (test kn) k s) as [[[c kn'] i]|] eqn:E1,
           (next (accept ok tt) k s) as [[[c' []] i']|] eqn:E2; try contradiction; [|reflexivity].
  destruct N as [<- <-].
  apply next_some in E1 as [Hin E1].
  pose proof (H kn s c Hr Hs Hin) as Hk. rewrite E1 in Hk. destruct Hk as [Hc Hr'].
  apply IH; assumption.
Qed.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
The specification
=================

Every test parses the whole document.
*)

Definition parses_to (want : blocks) (t : string) : bool :=
  blocks_eqb (parse_blocks t) want.

Lemma parses_to_eq : forall want t, parses_to want t = true <-> parse_blocks t = want.
Proof. intros. apply blocks_eqb_eq. Qed.

Definition irredundant_spec (bs : blocks) : string :=
  let s := render_djot bs in
  shrink (parses_to (parse_blocks s)) (String.length s) s.

Lemma spec_parse : forall bs,
  parse_blocks (irredundant_spec bs) = parse_blocks (render_djot bs).
Proof.
  intros bs. apply parses_to_eq, shrink_ok, parses_to_eq. reflexivity.
Qed.

Theorem spec_roundtrip : forall cbs, cblocks_ok cbs = true ->
  parse_blocks (irredundant_spec (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. intros cbs H. rewrite spec_parse. apply roundtrip_blocks, H. Qed.

Theorem spec_backslash : forall bs i,
  String.get i (irredundant_spec bs) = Some bslash ->
  parse_blocks (del i (irredundant_spec bs)) <> parse_blocks (irredundant_spec bs).
Proof.
  intros bs i H Hp. rewrite spec_parse in Hp. unfold irredundant_spec in *.
  apply parses_to_eq in Hp.
  pose proof (shrink_final _ _ (render_djot bs) (le_n _) _ (deletions_backslash _ _ H)) as F.
  cbn [fst] in F. rewrite F in Hp. discriminate.
Qed.

Theorem spec_braces : forall bs i j,
  String.get i (irredundant_spec bs) = Some lbrace ->
  String.get j (irredundant_spec bs) = Some rbrace -> i < j ->
  ~ blank_between (irredundant_spec bs) i j ->
  parse_blocks (del i (del j (irredundant_spec bs)))
  <> parse_blocks (irredundant_spec bs).
Proof.
  intros bs i j Hi Hj Hij Hb Hp. rewrite spec_parse in Hp. unfold irredundant_spec in *.
  apply parses_to_eq in Hp.
  pose proof (shrink_final _ _ (render_djot bs) (le_n _) _
                (deletions_braces _ _ _ Hi Hj Hij Hb)) as F.
  cbn [fst] in F. rewrite F in Hp. discriminate.
Qed.

(*
The renderer
============

The specification's test, run incrementally.  The current string's
parse is kept as a trace: for each line, the state before it and the
blocks its step commits, with the lines themselves.  A deletion carries
the bytes it deletes, so the lines it changes are found and rebuilt
without splitting the string (`del_lines`).  It is tested by running the
parser from the first changed line until both runs are idle with the
rest of the lines the same; from there the two parses agree
(`prefix_determinism`), so the blocks committed until then decide.  A
deletion the lines cannot place falls back to splitting the string and
comparing its lines (`walk_test`).
*)

(* Two states the runs can resync at: both idle.  Resyncing also where
   two open containers' states are equal was measured and saved nothing. *)
Definition same_state (a b : pstate) : bool :=
  match a, b with PPara [], PPara [] => true | _, _ => false end.

Lemma same_state_eq : forall a b, same_state a b = true -> a = b.
Proof. intros [[]| | | | | | | | | | | |] [[]| | | | | | | | | | | |]; cbn; congruence. Qed.

(* A run, one entry per line: the line, the state before it, and the
   blocks its step commits. *)
Definition entry : Type := string * pstate * blocks.

Fixpoint trace (ls : list string) (st : pstate) : list entry * pstate :=
  match ls with
  | [] => ([], st)
  | l :: rest =>
      let '(bs, st') := step l st in
      let '(tr, fin) := trace rest st' in
      ((l, st, bs) :: tr, fin)
  end.

(* The state a run is in at its first entry. *)
Definition state_of (tr : list entry) (fin : pstate) : pstate :=
  match tr with (_, st, _) :: _ => st | [] => fin end.

(* What the rest of a run parses to. *)
Definition rest_of (tr : list entry) (fin : pstate) : blocks :=
  (flat_map (fun e => snd e) tr ++ finish fin)%list.

(* The current string, as the test knows it: its lines, whether it ends
   in a newline, and its run. *)
Record known : Type := Known
  { k_lines : list string
  ; k_nl : bool
  ; k_trace : list entry
  ; k_fin : pstate }.

(* By its last byte: destructing the string would copy a suffix per byte
   under the native extraction. *)
Definition ends_nl (s : string) : bool :=
  match String.get (pred (String.length s)) s with
  | Some c => Ascii.eqb c "010"%char
  | None => false
  end.

Definition known_of (s : string) : known :=
  let ls := split_lines s in
  let run := trace ls (PPara []) in
  Known ls (ends_nl s) (fst run) (snd run).

(* The candidate's run from the first line that differs.  [cand] and
   [ref] are the blocks the two runs committed since, [acc] the
   candidate's entries so far, reversed.  [n] entries are left of the
   current run, and the last [d] lines of both are the same, so where
   both runs are idle with [n <= d] the rest of the two runs agree. *)
Fixpoint resync (d n : nat) (stc : pstate) (cand ref : blocks) (acc : list entry)
  (tr : list entry) (ls : list string) (fin : pstate) : option (list entry * pstate) :=
  match tr, ls with
  | (_, st, bs) :: tr', l :: ls' =>
      if same_state stc st && Nat.leb n d then
        if blocks_eqb cand ref then Some (rev_append acc tr, fin) else None
      else
        let '(bs', stc') := step l stc in
        resync d (pred n) stc' (cand ++ bs')%list (ref ++ bs)%list
          ((l, stc, bs') :: acc) tr' ls' fin
  | _, _ =>
      let run := trace ls stc in
      if blocks_eqb (cand ++ rest_of (fst run) (snd run))%list (ref ++ rest_of tr fin)%list
      then Some (rev_append acc (fst run), snd run) else None
  end.

(* Past the lines both strings share. *)
Fixpoint walk (d n : nat) (acc : list entry) (tr : list entry) (ls : list string)
  (fin : pstate) : option (list entry * pstate) :=
  match tr, ls with
  | (l, st, bs) :: tr', l' :: ls' =>
      if String.eqb l l' then walk d (pred n) ((l, st, bs) :: acc) tr' ls' fin
      else resync d n st [] [] acc tr ls fin
  | (_, st, _) :: _, [] => resync d n st [] [] acc tr ls fin
  | [], _ => resync d n fin [] [] acc tr ls fin
  end.

Fixpoint common_prefix (xs ys : list string) : nat :=
  match xs, ys with
  | x :: xs', y :: ys' => if String.eqb x y then S (common_prefix xs' ys') else 0
  | _, _ => 0
  end.

(* Accepts [t] when it parses as the string [kn] knows, and returns what
   is then known of [t]: reparsing from the first line that differs,
   found by comparing the lines. *)
Definition walk_test (kn : known) (t : string) : option known :=
  let ls := split_lines t in
  let n := List.length (k_trace kn) in
  let d := if Nat.eqb (List.length ls) n
           then common_prefix (rev (k_lines kn)) (rev ls) else 0 in
  match walk d n [] (k_trace kn) ls (k_fin kn) with
  | Some (tr, fin) => Some (Known ls (ends_nl t) tr fin)
  | None => None
  end.

(* The line [i] falls on, and its column there. *)
Fixpoint locate (i : nat) (ls : list string) : option (nat * nat) :=
  match ls with
  | [] => None
  | l :: rest =>
      if Nat.ltb i (String.length l) then Some (0, i)
      else if Nat.eqb i (String.length l) then None
      else match locate (i - S (String.length l)) rest with
           | Some (a, c) => Some (S a, c)
           | None => None
           end
  end.

Fixpoint replace (a : nat) (f : string -> string) (ls : list string) : list string :=
  match ls, a with
  | [], _ => []
  | l :: rest, 0 => f l :: rest
  | l :: rest, S a' => l :: replace a' f rest
  end.

(* The lines of the string a deletion leaves, and the first and last of
   them it changed. *)
Definition del_lines (d : nat * option nat) (ls : list string)
  : option (list string * nat * nat) :=
  match d with
  | (i, None) =>
      match locate i ls with
      | Some (a, c) => Some (replace a (del c) ls, a, a)
      | None => None
      end
  | (i, Some j) =>
      match locate j ls with
      | Some (b, cj) =>
          let ls1 := replace b (del cj) ls in
          match locate i ls1 with
          | Some (a, ci) => Some (replace a (del ci) ls1, Nat.min a b, Nat.max a b)
          | None => None
          end
      | None => None
      end
  end.

(* Whether lines joined back, with or without a final newline, split
   into the same lines: the last is nonempty, or the newline follows it. *)
Definition ends_ok (ls : list string) (e : bool) : bool :=
  match ls with
  | [] => negb e
  | _ => e || nonempty_str (last ls EmptyString)
  end.

(* The test the renderer runs: the changed lines from the deletion's
   bytes, then a reparse from the first of them.  A deletion it cannot
   place, or one that would empty the last line, goes to [walk_test]. *)
Definition fast_test (kn : known) (c : cand) : option known :=
  match del_lines (snd c) (k_lines kn) with
  | Some (ls, lo, hi) =>
      if ends_ok ls (k_nl kn) then
        let tr := skipn lo (k_trace kn) in
        let n := List.length (k_trace kn) - lo in
        let d := n - (S hi - lo) in
        match resync d n (state_of tr (k_fin kn)) [] [] (rev (firstn lo (k_trace kn)))
                tr (skipn lo ls) (k_fin kn) with
        | Some (tr', fin) => Some (Known ls (k_nl kn) tr' fin)
        | None => None
        end
      else walk_test kn (fst c)
  | None => walk_test kn (fst c)
  end.

(*
Why the test is the parse test
------------------------------
*)

Definition line_of (e : entry) : string := fst (fst e).

(* [tr] and [fin] are a run of their own lines. *)
Definition is_run (tr : list entry) (fin : pstate) : Prop :=
  trace (map line_of tr) (state_of tr fin) = (tr, fin).

Lemma trace_lines : forall ls st, map line_of (fst (trace ls st)) = ls.
Proof.
  induction ls as [|l ls IH]; intros st; [reflexivity|]. cbn [trace].
  destruct (step l st) as [bs st']. specialize (IH st').
  destruct (trace ls st') as [tr fin]. cbn in *. rewrite IH. reflexivity.
Qed.

Lemma trace_parse : forall ls st,
  parse_lines ls st = rest_of (fst (trace ls st)) (snd (trace ls st)).
Proof.
  induction ls as [|l ls IH]; intros st; [reflexivity|]. cbn [trace parse_lines].
  destruct (step l st) as [bs st']. rewrite IH.
  destruct (trace ls st') as [tr fin]. unfold rest_of. cbn. rewrite app_assoc. reflexivity.
Qed.

Lemma state_of_trace : forall ls st,
  state_of (fst (trace ls st)) (snd (trace ls st)) = st.
Proof.
  intros [|l ls] st; [reflexivity|]. cbn [trace].
  destruct (step l st) as [bs st']. destruct (trace ls st'). reflexivity.
Qed.

Lemma trace_is_run : forall ls st,
  is_run (fst (trace ls st)) (snd (trace ls st)).
Proof.
  intros ls st. unfold is_run. rewrite trace_lines, state_of_trace.
  destruct (trace ls st); reflexivity.
Qed.

Lemma is_run_tail : forall l st bs tr fin,
  is_run ((l, st, bs) :: tr) fin ->
  step l st = (bs, state_of tr fin) /\ is_run tr fin.
Proof.
  intros l st bs tr fin H. unfold is_run in H. cbn [map line_of fst state_of trace] in H.
  destruct (step l st) as [bs0 st1] eqn:Es.
  destruct (trace (map line_of tr) st1) as [tr0 fin0] eqn:Et.
  injection H as -> -> ->.
  assert (E : state_of tr fin = st1).
  { pose proof (state_of_trace (map line_of tr) st1) as E. rewrite Et in E. exact E. }
  rewrite E. split; [reflexivity|]. unfold is_run. rewrite E. exact Et.
Qed.

(* What [d] and [n] say: [n] entries are left, and the last [d] lines of
   the two runs are the same, unless [d] is 0. *)
Definition tails_agree (d n : nat) (tr : list entry) (ls : list string) : Prop :=
  n = List.length tr
  /\ (d = 0 \/ (List.length ls = n /\ skipn (n - d) (map line_of tr) = skipn (n - d) ls)).

Lemma tails_agree_tail : forall d n e tr l ls,
  tails_agree d n (e :: tr) (l :: ls) -> tails_agree d (pred n) tr ls.
Proof.
  intros d n e tr l ls [Hn [Hd|[Hl Hs]]]; cbn [List.length] in *; subst n.
  - split; [reflexivity | left; exact Hd].
  - split; [reflexivity | right]. split; [lia|]. cbn [pred].
    destruct (S (List.length tr) - d) as [|k] eqn:Ek.
    + cbn [skipn map] in Hs. injection Hs as _ Hs.
      replace (List.length tr - d) with 0 by lia. exact Hs.
    + cbn [skipn map] in Hs. replace (List.length tr - d) with k by lia. exact Hs.
Qed.

Lemma tails_agree_here : forall d n tr ls,
  tails_agree d n tr ls -> tr <> [] -> Nat.leb n d = true -> map line_of tr = ls.
Proof.
  intros d n tr ls [Hn [Hd|[Hl Hs]]] Hne Hle; apply Nat.leb_le in Hle.
  - subst d. destruct tr; [contradiction | cbn in Hn; lia].
  - replace (n - d) with 0 in Hs by lia. exact Hs.
Qed.

Lemma resync_spec : forall d n stc cand ref acc tr ls fin,
  tails_agree d n tr ls -> is_run tr fin ->
  match resync d n stc cand ref acc tr ls fin with
  | Some (tr', fin') =>
      (cand ++ parse_lines ls stc = ref ++ rest_of tr fin)%list
      /\ (tr', fin') = (rev_append acc (fst (trace ls stc)), snd (trace ls stc))
  | None => (cand ++ parse_lines ls stc <> ref ++ rest_of tr fin)%list
  end.
Proof.
  intros d n stc cand ref acc tr. revert n stc cand ref acc.
  induction tr as [|[[l0 st] bs] tr IH]; intros n stc cand ref acc ls fin Ha Hr.
  - cbn [resync]. rewrite <- trace_parse.
    destruct (blocks_eqb _ _) eqn:E.
    + apply blocks_eqb_eq in E. split; [exact E | reflexivity].
    + intros H. apply (proj2 (blocks_eqb_eq _ _)) in H. congruence.
  - destruct ls as [|l ls].
    + cbn [resync]. rewrite <- trace_parse.
      destruct (blocks_eqb _ _) eqn:E.
      * apply blocks_eqb_eq in E. split; [exact E | reflexivity].
      * intros H. apply (proj2 (blocks_eqb_eq _ _)) in H. congruence.
    + cbn [resync].
      destruct (same_state stc st && Nat.leb n d) eqn:Es.
      * (* Resynced: the rest of the candidate is the rest of the run. *)
        apply andb_true_iff in Es as [Es Hle]. apply same_state_eq in Es. subst st.
        pose proof (tails_agree_here _ _ _ _ Ha ltac:(discriminate) Hle) as Hl.
        unfold is_run in Hr. rewrite Hl in Hr. cbn [state_of] in Hr.
        rewrite trace_parse, Hr. cbn [fst snd].
        destruct (blocks_eqb cand ref) eqn:E.
        -- apply blocks_eqb_eq in E. subst. split; reflexivity.
        -- intros H. apply app_inv_tail in H. apply (proj2 (blocks_eqb_eq _ _)) in H.
           congruence.
      * apply is_run_tail in Hr as [Hstep Hr].
        apply tails_agree_tail in Ha.
        destruct (step l stc) as [bs' stc'] eqn:Ec.
        specialize (IH (pred n) stc' (cand ++ bs')%list (ref ++ bs)%list
                      ((l, stc, bs') :: acc) ls fin Ha Hr).
        cbn [parse_lines trace]. rewrite Ec.
        destruct (trace ls stc') as [trc finc] eqn:Et.
        unfold rest_of in *. cbn [flat_map snd] in *. rewrite !app_assoc in *.
        destruct (resync _ _ _ _ _ _ _ _ _) as [[tr' fin']|]; cbn [fst snd rev_append] in *;
          exact IH.
Qed.

Lemma walk_spec : forall d n acc tr ls fin,
  tails_agree d n tr ls -> is_run tr fin ->
  match walk d n acc tr ls fin with
  | Some (tr', fin') =>
      parse_lines ls (state_of tr fin) = rest_of tr fin
      /\ (tr', fin') = (rev_append acc (fst (trace ls (state_of tr fin))),
                        snd (trace ls (state_of tr fin)))
  | None => parse_lines ls (state_of tr fin) <> rest_of tr fin
  end.
Proof.
  intros d n acc tr. revert n acc.
  induction tr as [|[[l0 st] bs] tr IH]; intros n acc ls fin Ha Hr.
  - cbn [walk state_of]. pose proof (resync_spec d n fin [] [] acc [] ls fin Ha Hr) as H.
    destruct (resync _ _ _ _ _ _ _ _ _) as [[tr' fin']|]; exact H.
  - destruct ls as [|l ls].
    + cbn [walk state_of]. pose proof (resync_spec d n st [] [] acc _ [] fin Ha Hr) as H.
      destruct (resync _ _ _ _ _ _ _ _ _) as [[tr' fin']|]; exact H.
    + cbn [walk state_of]. destruct (String.eqb l0 l) eqn:E.
      * apply String.eqb_eq in E. subst l0.
        apply is_run_tail in Hr as [Hstep Hr]. apply tails_agree_tail in Ha.
        specialize (IH (pred n) ((l, st, bs) :: acc) ls fin Ha Hr).
        cbn [parse_lines trace]. rewrite Hstep.
        destruct (trace ls (state_of tr fin)) as [trc finc] eqn:Et.
        unfold rest_of in *. cbn [flat_map snd fst] in *.
        destruct (walk _ _ _ _ _ _) as [[tr' fin']|].
        -- destruct IH as [IH1 IH2]. rewrite IH1, <- app_assoc.
           split; [reflexivity|exact IH2].
        -- intros H. rewrite <- app_assoc in H. apply app_inv_head in H. exact (IH H).
      * pose proof (resync_spec d n st [] [] acc _ (l :: ls) fin Ha Hr) as H.
        destruct (resync _ _ _ _ _ _ _ _ _) as [[tr' fin']|]; exact H.
Qed.

Lemma common_prefix_firstn : forall xs ys,
  firstn (common_prefix xs ys) xs = firstn (common_prefix xs ys) ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys]; cbn; try reflexivity.
  destruct (String.eqb x y) eqn:E; [|reflexivity].
  apply String.eqb_eq in E. subst y. cbn. rewrite IH. reflexivity.
Qed.

Lemma walk_test_correct : forall s t,
  match walk_test (known_of s) t with
  | Some kn => parse_blocks t = parse_blocks s /\ kn = known_of t
  | None => parse_blocks t <> parse_blocks s
  end.
Proof.
  intros s t. unfold walk_test, known_of. cbn [k_trace k_fin k_lines].
  set (ls0 := split_lines s). set (ls := split_lines t).
  set (tr0 := fst (trace ls0 (PPara []))). set (fin0 := snd (trace ls0 (PPara []))).
  assert (Hr : is_run tr0 fin0) by apply trace_is_run.
  assert (Hst : state_of tr0 fin0 = PPara []) by apply state_of_trace.
  assert (Hl0 : map line_of tr0 = ls0) by apply trace_lines.
  assert (Hlen : List.length tr0 = List.length ls0)
    by (rewrite <- Hl0, length_map; reflexivity).
  set (d := if Nat.eqb (List.length ls) (List.length tr0)
            then common_prefix (rev ls0) (rev ls) else 0).
  assert (Ha : tails_agree d (List.length tr0) tr0 ls).
  { split; [reflexivity|]. unfold d. destruct (Nat.eqb _ _) eqn:E; [|left; reflexivity].
    right. apply Nat.eqb_eq in E. split; [exact E|]. rewrite Hl0.
    pose proof (common_prefix_firstn (rev ls0) (rev ls)) as Hc.
    rewrite !firstn_rev in Hc. apply (f_equal (@rev string)) in Hc.
    rewrite !rev_involutive in Hc. rewrite Hlen in *. rewrite E in Hc. exact Hc. }
  pose proof (walk_spec d (List.length tr0) [] tr0 ls fin0 Ha Hr) as W.
  rewrite Hst in W.
  assert (Hs : parse_blocks s = rest_of tr0 fin0) by (unfold parse_blocks; apply trace_parse).
  destruct (walk _ _ _ _ _ _) as [[tr fin]|].
  - destruct W as [W1 W2]. injection W2 as -> ->. split; [|reflexivity].
    unfold parse_blocks. fold ls. rewrite W1. symmetry. exact Hs.
  - intros H. apply W. unfold parse_blocks in H. fold ls in H. rewrite H. exact Hs.
Qed.


(*
The lines a deletion leaves
---------------------------
*)

(* Lines joined back, with a final newline or without. *)
Definition join (ls : list string) (e : bool) : string :=
  (String.concat nl ls ++ (if e then nl else EmptyString))%string.

Lemma join_cons : forall l rest e,
  join (l :: rest) e
  = (l ++ match rest with
          | [] => if e then nl else EmptyString
          | _ => String "010" (join rest e)
          end)%string.
Proof.
  intros l rest e. unfold join. destruct rest as [|r rest]; [reflexivity|].
  change (String.concat nl (l :: r :: rest)) with (l ++ nl ++ String.concat nl (r :: rest))%string.
  rewrite !append_assoc. reflexivity.
Qed.

Lemma ends_nl_app : forall a b, b <> EmptyString -> ends_nl (a ++ b) = ends_nl b.
Proof.
  intros a b Hb. unfold ends_nl. rewrite length_append.
  destruct b as [|x b]; [contradiction|]. cbn [String.length pred].
  replace (pred (String.length a + S (String.length b)))
    with (String.length b + String.length a) by lia.
  rewrite <- append_correct2. reflexivity.
Qed.

Lemma first_nl : forall s,
  no_nl s = true \/ exists x r, no_nl x = true /\ s = (x ++ String "010" r)%string.
Proof.
  induction s as [|c s IH]; [left; reflexivity|].
  destruct (Ascii.eqb c "010"%char) eqn:E.
  - apply Ascii.eqb_eq in E. subst c. right. exists EmptyString, s. split; reflexivity.
  - destruct IH as [H|[x [r [Hx ->]]]].
    + left. cbn. rewrite E, H. reflexivity.
    + right. exists (String c x), r. split; [cbn; rewrite E, Hx; reflexivity | reflexivity].
Qed.

Lemma ends_nl_cons : forall c r, r <> EmptyString -> ends_nl (String c r) = ends_nl r.
Proof. intros c r H. exact (ends_nl_app (String c EmptyString) r H). Qed.

Lemma ends_nl_no_nl : forall s, no_nl s = true -> ends_nl s = false.
Proof.
  induction s as [|c s IH]; intros H; [reflexivity|].
  cbn [no_nl] in H. apply andb_true_iff in H as [Hc Hs].
  destruct s as [|d s].
  - unfold ends_nl. cbn. destruct (Ascii.eqb c "010"%char); [discriminate|reflexivity].
  - rewrite ends_nl_cons by discriminate. exact (IH Hs).
Qed.

Lemma split_lines_nonempty : forall r, r <> EmptyString -> split_lines r <> [].
Proof.
  intros r Hr. destruct (first_nl r) as [H|[x [r' [Hx ->]]]].
  - rewrite split_lines_single by assumption. discriminate.
  - rewrite split_lines_line by assumption. discriminate.
Qed.

Lemma join_split : forall s, join (split_lines s) (ends_nl s) = s.
Proof.
  intros s. remember (String.length s) as n eqn:Hn. revert s Hn.
  induction n as [n IH] using lt_wf_ind. intros s Hn.
  destruct (first_nl s) as [H|[x [r [Hx ->]]]].
  - destruct s as [|c s']; [reflexivity|].
    rewrite split_lines_single by (assumption || discriminate).
    rewrite ends_nl_no_nl by assumption. unfold join. cbn. rewrite append_empty_r. reflexivity.
  - rewrite split_lines_line by assumption.
    rewrite ends_nl_app by discriminate.
    destruct (string_dec r EmptyString) as [->|Hr]; [reflexivity|].
    rewrite ends_nl_cons by exact Hr.
    pose proof (split_lines_nonempty r Hr) as Hne.
    rewrite join_cons. destruct (split_lines r) as [|y ys] eqn:E; [contradiction|].
    rewrite <- E. f_equal. f_equal.
    apply (IH (String.length r)); [|reflexivity].
    rewrite Hn, length_append. cbn. lia.
Qed.

Lemma split_lines_no_nl : forall s, forallb no_nl (split_lines s) = true.
Proof.
  intros s. remember (String.length s) as n eqn:Hn. revert s Hn.
  induction n as [n IH] using lt_wf_ind. intros s Hn.
  destruct (first_nl s) as [H|[x [r [Hx ->]]]].
  - destruct s as [|c s']; [reflexivity|].
    rewrite split_lines_single by (assumption || discriminate).
    cbn [forallb]. rewrite H. reflexivity.
  - rewrite split_lines_line by assumption. cbn [forallb]. rewrite Hx.
    apply (IH (String.length r)); [|reflexivity]. rewrite Hn, length_append. cbn. lia.
Qed.

Lemma split_join : forall ls e, forallb no_nl ls = true -> ends_ok ls e = true ->
  split_lines (join ls e) = ls.
Proof.
  intros [|a ls] e Hn He.
  - destruct e; [discriminate|reflexivity].
  - unfold join. destruct e.
    + pose proof (split_join_line a ls EmptyString Hn) as H. rewrite app_nil_r in H. exact H.
    + rewrite append_empty_r. apply split_join_last; [exact Hn|].
      cbn [ends_ok orb] in He. destruct (last (a :: ls) EmptyString); discriminate.
Qed.

Lemma ends_nl_join : forall ls e, forallb no_nl ls = true -> ends_ok ls e = true ->
  ends_nl (join ls e) = e.
Proof.
  intros [|a ls] e Hn He.
  - destruct e; [discriminate|reflexivity].
  - unfold join. destruct e.
    + rewrite ends_nl_app by discriminate. reflexivity.
    + rewrite append_empty_r. cbn [ends_ok orb] in He.
      revert a Hn He. induction ls as [|b ls IH]; intros a Hn He.
      * cbn in Hn. rewrite andb_true_r in Hn. exact (ends_nl_no_nl a Hn).
      * cbn [forallb] in Hn. apply andb_true_iff in Hn as [Ha Hn].
        change (String.concat nl (a :: b :: ls))
          with (a ++ nl ++ String.concat nl (b :: ls))%string.
        assert (Hne : String.concat nl (b :: ls) <> EmptyString).
        { clear IH Ha Hn. revert b He. induction ls as [|c ls IH]; intros b He.
          - cbn in *. destruct b; discriminate.
          - change (String.concat nl (b :: c :: ls))
              with (b ++ nl ++ String.concat nl (c :: ls))%string.
            destruct b; cbn; discriminate. }
        rewrite ends_nl_app by (destruct (String.concat nl (b :: ls)); [contradiction|discriminate]).
        rewrite ends_nl_app by exact Hne.
        apply IH; [cbn [forallb]; exact Hn | exact He].
Qed.

Lemma del_app_l : forall i x y, i < String.length x ->
  del i (x ++ y) = (del i x ++ y)%string.
Proof.
  induction i as [|i IH]; intros [|c x] y H; cbn in *; try lia; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Lemma del_app_r : forall x i y, String.length x <= i ->
  del i (x ++ y) = (x ++ del (i - String.length x) y)%string.
Proof.
  induction x as [|c x IH]; intros i y H; cbn in *; [rewrite Nat.sub_0_r; reflexivity|].
  destruct i as [|i]; [lia|]. cbn. rewrite IH by lia. reflexivity.
Qed.

Lemma replace_length : forall a f ls, List.length (replace a f ls) = List.length ls.
Proof. induction a as [|a IH]; intros f [|l ls]; cbn; auto. Qed.

Lemma del_join : forall ls e i a c, locate i ls = Some (a, c) ->
  del i (join ls e) = join (replace a (del c) ls) e.
Proof.
  induction ls as [|l rest IH]; intros e i a c H; [discriminate|].
  cbn [locate] in H.
  destruct (Nat.ltb i (String.length l)) eqn:Hlt.
  - injection H as <- <-. apply Nat.ltb_lt in Hlt.
    rewrite join_cons. cbn [replace]. rewrite join_cons. apply del_app_l. exact Hlt.
  - destruct (Nat.eqb i (String.length l)) eqn:Heq; [discriminate|].
    destruct (locate (i - S (String.length l)) rest) as [[a' c']|] eqn:El; [|discriminate].
    injection H as <- <-. apply Nat.ltb_ge in Hlt. apply Nat.eqb_neq in Heq.
    destruct rest as [|r rest]; [discriminate|].
    cbn [replace]. rewrite !join_cons.
    destruct (replace a' (del c') (r :: rest)) as [|r' rest'] eqn:Er.
    { pose proof (replace_length a' (del c') (r :: rest)) as Hl. rewrite Er in Hl. discriminate. }
    rewrite del_app_r by lia. f_equal.
    replace (i - String.length l) with (S (i - S (String.length l))) by lia.
    cbn [del]. f_equal. rewrite <- Er, <- join_cons. apply IH. exact El.
Qed.

Lemma locate_bound : forall i ls a c, locate i ls = Some (a, c) -> a < List.length ls.
Proof.
  intros i ls. revert i. induction ls as [|l rest IH]; intros i a c H; [discriminate|].
  cbn [locate] in H. cbn [List.length].
  destruct (Nat.ltb i (String.length l)); [injection H as <- _; lia|].
  destruct (Nat.eqb i (String.length l)); [discriminate|].
  destruct (locate _ rest) as [[a' c']|] eqn:E; [|discriminate].
  injection H as <- _. apply IH in E. lia.
Qed.

Lemma replace_firstn : forall a f ls k, k <= a -> firstn k (replace a f ls) = firstn k ls.
Proof.
  induction a as [|a IH]; intros f [|l ls] [|k] H; cbn; auto; try lia.
  f_equal. apply IH. lia.
Qed.

Lemma replace_skipn : forall a f ls k, a < k -> skipn k (replace a f ls) = skipn k ls.
Proof.
  induction a as [|a IH]; intros f [|l ls] [|k] H; cbn; auto; try lia.
  apply IH. lia.
Qed.

Lemma del_no_nl : forall c l, no_nl l = true -> no_nl (del c l) = true.
Proof.
  induction c as [|c IH]; intros [|x l] H; cbn in *; auto.
  - apply andb_true_iff in H as [_ H]. exact H.
  - apply andb_true_iff in H as [Hx H]. rewrite Hx, IH by exact H. reflexivity.
Qed.

Lemma replace_no_nl : forall a c ls, forallb no_nl ls = true ->
  forallb no_nl (replace a (del c) ls) = true.
Proof.
  induction a as [|a IH]; intros c [|l ls] H; cbn in *; auto;
    apply andb_true_iff in H as [Hl H].
  - rewrite del_no_nl, H by exact Hl. reflexivity.
  - rewrite Hl, IH by exact H. reflexivity.
Qed.

Lemma del_lines_spec : forall d ls e ls' lo hi,
  forallb no_nl ls = true -> del_lines d ls = Some (ls', lo, hi) ->
  apply_del d (join ls e) = join ls' e
  /\ lo <= hi /\ hi < List.length ls /\ List.length ls' = List.length ls
  /\ firstn lo ls' = firstn lo ls /\ skipn (S hi) ls' = skipn (S hi) ls
  /\ forallb no_nl ls' = true.
Proof.
  intros [i [j|]] ls e ls' lo hi Hn H; cbn [del_lines apply_del] in H |- *.
  - destruct (locate j ls) as [[b cj]|] eqn:Ej; [|discriminate].
    destruct (locate i (replace b (del cj) ls)) as [[a ci]|] eqn:Ei; [|discriminate].
    injection H as <- <- <-.
    pose proof (locate_bound _ _ _ _ Ej) as Hb.
    pose proof (locate_bound _ _ _ _ Ei) as Ha. rewrite replace_length in Ha.
    rewrite (del_join _ _ _ _ _ Ej), (del_join _ _ _ _ _ Ei).
    repeat split; try lia.
    + rewrite !replace_length. reflexivity.
    + rewrite replace_firstn, replace_firstn by lia. reflexivity.
    + rewrite replace_skipn, replace_skipn by lia. reflexivity.
    + apply replace_no_nl, replace_no_nl, Hn.
  - destruct (locate i ls) as [[a c]|] eqn:Ei; [|discriminate].
    injection H as <- <- <-.
    pose proof (locate_bound _ _ _ _ Ei) as Ha.
    rewrite (del_join _ _ _ _ _ Ei).
    repeat split; try lia.
    + apply replace_length.
    + apply replace_firstn. lia.
    + apply replace_skipn. lia.
    + apply replace_no_nl, Hn.
Qed.

(* A run splits where its lines do. *)
Lemma trace_app : forall xs ys st,
  trace (xs ++ ys) st
  = (fst (trace xs st) ++ fst (trace ys (snd (trace xs st))),
     snd (trace ys (snd (trace xs st))))%list.
Proof.
  induction xs as [|x xs IH]; intros ys st.
  - cbn. destruct (trace ys st); reflexivity.
  - cbn [app trace]. destruct (step x st) as [bs st']. rewrite IH.
    destruct (trace xs st') as [tx fx]. cbn [fst snd]. destruct (trace ys fx). reflexivity.
Qed.

Lemma rest_of_app : forall x y fin,
  rest_of (x ++ y) fin = (flat_map (fun e => snd e) x ++ rest_of y fin)%list.
Proof. intros. unfold rest_of. rewrite flat_map_app, app_assoc. reflexivity. Qed.

Lemma parse_lines_app : forall xs ys st,
  parse_lines (xs ++ ys) st
  = (flat_map (fun e => snd e) (fst (trace xs st)) ++ parse_lines ys (snd (trace xs st)))%list.
Proof.
  intros. rewrite !trace_parse, trace_app. cbn [fst snd]. apply rest_of_app.
Qed.

Lemma fast_test_correct : forall s c, In c (deletions s) ->
  match fast_test (known_of s) c with
  | Some kn => parse_blocks (fst c) = parse_blocks s /\ kn = known_of (fst c)
  | None => parse_blocks (fst c) <> parse_blocks s
  end.
Proof.
  intros s c Hc. destruct (deletions_spec s c Hc) as [Ht _].
  pose proof (walk_test_correct s (fst c)) as W.
  unfold fast_test.
  destruct (del_lines (snd c) (k_lines (known_of s))) as [[[ls' lo] hi]|] eqn:Ed; [|exact W].
  destruct (ends_ok ls' (k_nl (known_of s))) eqn:Ee; [|exact W].
  clear W. unfold known_of in Ed, Ee |- *. cbn [k_lines k_nl k_trace k_fin] in *.
  set (ls := split_lines s) in *. set (e := ends_nl s) in *.
  pose proof (split_lines_no_nl s) as Hn. fold ls in Hn.
  destruct (del_lines_spec _ _ e _ _ _ Hn Ed) as (Hj & Hlh & Hhl & Hlen & Hfst & Hskp & Hn').
  (* The candidate's lines. *)
  assert (Hc' : fst c = join ls' e).
  { rewrite Ht, <- Hj. unfold ls, e. rewrite join_split. reflexivity. }
  assert (Hsplit : split_lines (fst c) = ls') by (rewrite Hc'; apply split_join; assumption).
  assert (Hend : ends_nl (fst c) = e) by (rewrite Hc'; apply ends_nl_join; assumption).
  (* The current run, cut where the candidate's first changes. *)
  set (A := trace (firstn lo ls) (PPara [])).
  set (B := trace (skipn lo ls) (snd A)).
  assert (Etr : trace ls (PPara []) = (fst A ++ fst B, snd B)%list).
  { unfold B, A. rewrite <- trace_app, firstn_skipn. reflexivity. }
  assert (HlA : List.length (fst A) = lo).
  { pose proof (trace_lines (firstn lo ls) (PPara [])) as L. fold A in L.
    apply (f_equal (@List.length string)) in L. rewrite length_map, length_firstn in L. lia. }
  assert (HlB : List.length (fst B) = List.length ls - lo).
  { pose proof (trace_lines (skipn lo ls) (snd A)) as L. fold B in L.
    apply (f_equal (@List.length string)) in L. rewrite length_map, length_skipn in L. lia. }
  rewrite Etr. cbn [fst snd].
  rewrite length_app, HlA, HlB.
  replace (skipn lo (fst A ++ fst B)%list) with (fst B)
    by (rewrite skipn_app, HlA, Nat.sub_diag, skipn_all2 by lia; reflexivity).
  replace (firstn lo (fst A ++ fst B)%list) with (fst A)
    by (rewrite firstn_app, HlA, Nat.sub_diag, firstn_all2 by lia; cbn;
        rewrite app_nil_r; reflexivity).
  assert (Hst : state_of (fst B) (snd B) = snd A) by apply state_of_trace.
  rewrite Hst.
  replace (lo + (List.length ls - lo) - lo) with (List.length ls - lo) by lia.
  set (n := List.length ls - lo). set (d := n - (S hi - lo)).
  assert (Ha : tails_agree d n (fst B) (skipn lo ls')).
  { split; [unfold n; lia|]. right. split; [rewrite length_skipn, Hlen; reflexivity|].
    assert (Hm : map line_of (fst B) = skipn lo ls) by apply trace_lines.
    rewrite Hm. replace (n - d) with (S hi - lo) by (unfold d, n; lia).
    rewrite !skipn_skipn. replace (S hi - lo + lo) with (S hi) by lia. symmetry. exact Hskp. }
  assert (Hr : is_run (fst B) (snd B)) by apply trace_is_run.
  pose proof (resync_spec d n (snd A) [] [] (rev (fst A)) (fst B) (skipn lo ls') (snd B) Ha Hr)
    as R.
  cbn [app] in R.
  assert (Ps : parse_blocks s
               = (flat_map (fun e => snd e) (fst A) ++ rest_of (fst B) (snd B))%list).
  { unfold parse_blocks. fold ls. rewrite trace_parse, Etr. apply rest_of_app. }
  assert (Pt : parse_blocks (fst c)
               = (flat_map (fun e => snd e) (fst A) ++ parse_lines (skipn lo ls') (snd A))%list).
  { unfold parse_blocks. rewrite Hsplit, <- (firstn_skipn lo ls') at 1.
    rewrite Hfst, parse_lines_app. reflexivity. }
  destruct (resync _ _ _ _ _ _ _ _ _) as [[tr' fin']|].
  - destruct R as [R1 R2]. injection R2 as -> ->. split.
    + rewrite Pt, Ps, R1. reflexivity.
    + rewrite Hsplit, Hend.
      assert (T' : trace ls' (PPara [])
                   = (fst A ++ fst (trace (skipn lo ls') (snd A)),
                      snd (trace (skipn lo ls') (snd A)))%list).
      { rewrite <- (firstn_skipn lo ls') at 1. rewrite Hfst, trace_app. reflexivity. }
      rewrite T'. cbn [fst snd]. rewrite rev_append_rev, rev_involutive. reflexivity.
  - intros H. apply R. rewrite Pt, Ps in H. apply app_inv_head in H. exact H.
Qed.

Definition render_djot_irredundant (bs : blocks) : string :=
  let s := render_djot bs in shrink_by fast_test (String.length s) 0 (known_of s) s.

Theorem irredundant_is_spec : forall bs,
  render_djot_irredundant bs = irredundant_spec bs.
Proof.
  intros bs. unfold render_djot_irredundant, irredundant_spec, shrink.
  apply (shrink_by_accept _ (fun kn s => kn = known_of s)); [|reflexivity|].
  - intros kn s c -> Hs Hc. pose proof (fast_test_correct s c Hc) as H.
    apply parses_to_eq in Hs. rewrite Hs in H.
    destruct (fast_test (known_of s) c); [split; [apply parses_to_eq|]; apply H|].
    destruct (parses_to (parse_blocks (render_djot bs)) (fst c)) eqn:E; [|reflexivity].
    apply parses_to_eq in E. contradiction.
  - apply parses_to_eq. reflexivity.
Qed.

Theorem irredundant_roundtrip : forall cbs, cblocks_ok cbs = true ->
  parse_blocks (render_djot_irredundant (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof. intros. rewrite irredundant_is_spec. apply spec_roundtrip. assumption. Qed.

Theorem irredundant_backslash : forall bs i,
  String.get i (render_djot_irredundant bs) = Some bslash ->
  parse_blocks (del i (render_djot_irredundant bs))
  <> parse_blocks (render_djot_irredundant bs).
Proof. intros bs. rewrite irredundant_is_spec. apply spec_backslash. Qed.

Theorem irredundant_braces : forall bs i j,
  String.get i (render_djot_irredundant bs) = Some lbrace ->
  String.get j (render_djot_irredundant bs) = Some rbrace -> i < j ->
  ~ blank_between (render_djot_irredundant bs) i j ->
  parse_blocks (del i (del j (render_djot_irredundant bs)))
  <> parse_blocks (render_djot_irredundant bs).
Proof. intros bs. rewrite irredundant_is_spec. apply spec_braces. Qed.

End WithTable.
