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

(* The deletions a spelling is tested against: each backslash, and each
   `{` with each `}` after it and no empty line between.  [deletions_at]
   are those starting at byte [i]. *)
Definition deletions_at (s : string) (i : nat) : list string :=
  match String.get i s with
  | Some c =>
      if Ascii.eqb c bslash then [del i s]
      else if Ascii.eqb c lbrace then
        flat_map
          (fun j =>
             match String.get j s with
             | Some d => if Ascii.eqb d rbrace then [del i (del j s)] else []
             | None => []
             end)
          (seq (S i) (para_stop s (S i) - S i))
      else []
  | None => []
  end.

Definition deletions (s : string) : list string :=
  flat_map (deletions_at s) (seq 0 (String.length s)).

Lemma deletions_backslash : forall s i,
  String.get i s = Some bslash -> In (del i s) (deletions s).
Proof.
  intros s i H. apply in_flat_map. exists i. split.
  - apply in_seq. apply get_length in H. lia.
  - unfold deletions_at. rewrite H. cbn. left. reflexivity.
Qed.

Lemma deletions_braces : forall s i j,
  String.get i s = Some lbrace -> String.get j s = Some rbrace -> i < j ->
  ~ blank_between s i j -> In (del i (del j s)) (deletions s).
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

Lemma deletions_shorter : forall s t, In t (deletions s) -> String.length t < String.length s.
Proof.
  intros s t H. apply in_flat_map in H as [i [Hi H]]. apply in_seq in Hi.
  unfold deletions_at in H. destruct (String.get i s) as [c|] eqn:Ec; [|destruct H].
  destruct (Ascii.eqb c bslash).
  { destruct H as [<-|[]]. rewrite del_length by lia. lia. }
  destruct (Ascii.eqb c lbrace); [|destruct H].
  apply in_flat_map in H as [j [Hj H]]. apply in_seq in Hj.
  destruct (String.get j s) as [d|] eqn:Ed; [|destruct H].
  destruct (Ascii.eqb d rbrace); [|destruct H].
  destruct H as [<-|[]]. apply get_length in Ed.
  rewrite del_length; rewrite del_length by lia; lia.
Qed.

(*
Shrinking
=========
*)

(* The first of [l] that [f] accepts, with what [f] returns for it. *)
Fixpoint pick {B : Type} (f : string -> option B) (l : list string)
  : option (string * B) :=
  match l with
  | [] => None
  | t :: rest => match f t with Some b => Some (t, b) | None => pick f rest end
  end.

Lemma pick_some : forall {B} (f : string -> option B) l t b,
  pick f l = Some (t, b) -> In t l /\ f t = Some b.
Proof.
  intros B f l t b. induction l as [|x l IH]; cbn; [discriminate|].
  destruct (f x) as [y|] eqn:E.
  - intros H. injection H as <- <-. auto.
  - intros H. apply IH in H as [H1 H2]. auto.
Qed.

Lemma pick_none : forall {B} (f : string -> option B) l,
  pick f l = None -> forall t, In t l -> f t = None.
Proof.
  intros B f l. induction l as [|x l IH]; cbn; [tauto|].
  destruct (f x) eqn:E; [discriminate|].
  intros H t [<-|Ht]; [exact E | exact (IH H t Ht)].
Qed.

Lemma pick_app : forall {B} (f : string -> option B) l1 l2,
  pick f (l1 ++ l2) = match pick f l1 with Some r => Some r | None => pick f l2 end.
Proof.
  intros B f l1 l2. induction l1 as [|x l1 IH]; [reflexivity|].
  cbn. destruct (f x); [reflexivity | exact IH].
Qed.

(* The first deletion at byte [i] that [f] accepts, found without
   building the list. *)
Definition first_at {B : Type} (f : string -> option B) (s : string) (i : nat)
  : option (string * B) :=
  let test t := match f t with Some b => Some (t, b) | None => None end in
  match String.get i s with
  | Some c =>
      if Ascii.eqb c bslash then test (del i s)
      else if Ascii.eqb c lbrace then
        (fix go (m j : nat) : option (string * B) :=
           match m with
           | 0 => None
           | S m' =>
               match match String.get j s with
                     | Some d => if Ascii.eqb d rbrace then test (del i (del j s)) else None
                     | None => None
                     end with
               | Some r => Some r
               | None => go m' (S j)
               end
           end) (para_stop s (S i) - S i) (S i)
      else None
  | None => None
  end.

Lemma first_at_pick : forall {B} (f : string -> option B) s i,
  first_at f s i = pick f (deletions_at s i).
Proof.
  intros B f s i. unfold first_at, deletions_at.
  destruct (String.get i s) as [c|]; [|reflexivity].
  destruct (Ascii.eqb c bslash); [cbn; destruct (f (del i s)); reflexivity|].
  destruct (Ascii.eqb c lbrace); [|reflexivity].
  set (m := para_stop s (S i) - S i). clearbody m.
  generalize (S i) as j. induction m as [|m IH]; intros j; [reflexivity|].
  cbn [seq flat_map]. rewrite pick_app, <- IH.
  destruct (String.get j s) as [d|]; [|reflexivity].
  destruct (Ascii.eqb d rbrace); [|reflexivity].
  cbn. destruct (f (del i (del j s))); reflexivity.
Qed.

(* The first deletion [f] accepts at one of [bytes], with its byte. *)
Fixpoint first_in {B : Type} (f : string -> option B) (s : string) (bytes : list nat)
  : option (string * B * nat) :=
  match bytes with
  | [] => None
  | i :: rest =>
      match first_at f s i with
      | Some (t, b) => Some (t, b, i)
      | None => first_in f s rest
      end
  end.

Lemma first_in_some : forall {B} (f : string -> option B) s l t b i,
  first_in f s l = Some (t, b, i) -> In i l /\ first_at f s i = Some (t, b).
Proof.
  intros B f s l t b i. induction l as [|x l IH]; cbn; [discriminate|].
  destruct (first_at f s x) as [[u y]|] eqn:E.
  - intros H. injection H as <- <- <-. auto.
  - intros H. apply IH in H as [H1 H2]. auto.
Qed.

Lemma first_in_none : forall {B} (f : string -> option B) s l,
  first_in f s l = None -> forall i, In i l -> first_at f s i = None.
Proof.
  intros B f s l. induction l as [|x l IH]; cbn; [tauto|].
  destruct (first_at f s x) as [[u y]|] eqn:E; [discriminate|].
  intros H i [<-|Hi]; [exact E | exact (IH H i Hi)].
Qed.

(* [first_in] over the [n] bytes from [i], counting rather than
   building the list. *)
Fixpoint first_from {B : Type} (f : string -> option B) (s : string) (n i : nat)
  : option (string * B * nat) :=
  match n with
  | 0 => None
  | S m =>
      match first_at f s i with
      | Some (t, b) => Some (t, b, i)
      | None => first_from f s m (S i)
      end
  end.

Lemma first_from_in : forall {B} (f : string -> option B) s n i,
  first_from f s n i = first_in f s (seq i n).
Proof.
  intros B f s n. induction n as [|n IH]; intros i; [reflexivity|].
  cbn. rewrite IH. reflexivity.
Qed.

(* The next deletion: from byte [k] on, where the last one was, and from
   the start if there is none there. *)
Definition next {B : Type} (f : string -> option B) (k : nat) (s : string)
  : option (string * B * nat) :=
  match first_from f s (String.length s - k) k with
  | Some r => Some r
  | None => first_from f s (String.length s) 0
  end.

Lemma next_some : forall {B} (f : string -> option B) k s t b i,
  next f k s = Some (t, b, i) -> In t (deletions s) /\ f t = Some b.
Proof.
  intros B f k s t b i H. unfold next in H. rewrite !first_from_in in H.
  assert (Hl : exists l, first_in f s l = Some (t, b, i)
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

Lemma next_none : forall {B} (f : string -> option B) k s,
  next f k s = None -> forall t, In t (deletions s) -> f t = None.
Proof.
  intros B f k s H t Ht. unfold next in H. rewrite !first_from_in in H.
  destruct (first_in f s (seq k _)); [discriminate|].
  apply in_flat_map in Ht as [i [Hi Ht]].
  pose proof (first_in_none _ _ _ H i Hi) as E.
  rewrite first_at_pick in E. exact (pick_none _ _ E t Ht).
Qed.

(* Two tests that accept the same deletions of [s] find the same next
   one. *)
Definition agree {B B'} (f : string -> option B) (g : string -> option B') (t : string) : Prop :=
  match f t, g t with Some _, Some _ | None, None => True | _, _ => False end.

Lemma pick_same : forall {B B'} (f : string -> option B) (g : string -> option B') l,
  (forall t, In t l -> agree f g t) ->
  match pick f l, pick g l with
  | Some (t, _), Some (t', _) => t = t'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros B B' f g l H. induction l as [|x l IH]; cbn; [exact I|].
  specialize (H x (or_introl eq_refl)) as Hx. unfold agree in Hx.
  destruct (f x), (g x); try contradiction; [reflexivity|].
  apply IH. intros t Ht. apply H. right. exact Ht.
Qed.

Lemma first_in_same : forall {B B'} (f : string -> option B) (g : string -> option B') s l,
  (forall i, In i l -> forall t, In t (deletions_at s i) -> agree f g t) ->
  match first_in f s l, first_in g s l with
  | Some (t, _, i), Some (t', _, i') => t = t' /\ i = i'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros B B' f g s l H. induction l as [|x l IH]; cbn; [exact I|].
  pose proof (pick_same f g (deletions_at s x) (H x (or_introl eq_refl))) as Hx.
  rewrite <- !first_at_pick in Hx.
  destruct (first_at f s x) as [[t b]|], (first_at g s x) as [[t' b']|];
    try contradiction; [split; [exact Hx | reflexivity]|].
  apply IH. intros i Hi. apply H. right. exact Hi.
Qed.

Lemma next_same : forall {B B'} (f : string -> option B) (g : string -> option B') k s,
  (forall t, In t (deletions s) -> agree f g t) ->
  match next f k s, next g k s with
  | Some (t, _, i), Some (t', _, i') => t = t' /\ i = i'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros B B' f g k s H.
  assert (Hin : forall l, (forall i, In i l -> i < String.length s) ->
            forall i, In i l -> forall t, In t (deletions_at s i) -> agree f g t).
  { intros l Hl i Hi t Ht. apply H. apply in_flat_map. exists i.
    split; [apply in_seq; specialize (Hl i Hi); lia | exact Ht]. }
  unfold next. rewrite !first_from_in.
  assert (B1 : forall i, In i (seq k (String.length s - k)) -> i < String.length s)
    by (intros i Hi; apply in_seq in Hi; lia).
  assert (B2 : forall i, In i (seq 0 (String.length s)) -> i < String.length s)
    by (intros i Hi; apply in_seq in Hi; lia).
  pose proof (first_in_same f g s _ (Hin _ B1)) as H1.
  pose proof (first_in_same f g s _ (Hin _ B2)) as H2.
  destruct (first_in f s (seq k _)) as [[[t b] i]|], (first_in g s (seq k _)) as [[[t' b'] i']|];
    try contradiction; [exact H1|].
  exact H2.
Qed.

(* Takes the next deletion the test accepts, while there is one.  The
   test carries what it knows of the current string, [c], and returns it
   for the string it accepts.  Each deletion is shorter, so a fuel of the
   length runs to the end. *)
Fixpoint shrink_by {C : Type} (test : C -> string -> option C) (fuel k : nat)
  (c : C) (s : string) : string :=
  match fuel with
  | 0 => s
  | S f =>
      match next (test c) k s with
      | Some (t, c', i) => shrink_by test f i c' t
      | None => s
      end
  end.

Definition accept (ok : string -> bool) (_ : unit) (t : string) : option unit :=
  if ok t then Some tt else None.

Definition shrink (ok : string -> bool) (fuel : nat) (s : string) : string :=
  shrink_by (accept ok) fuel 0 tt s.

Lemma shrink_ok : forall ok f s, ok s = true -> ok (shrink ok f s) = true.
Proof.
  intros ok f. unfold shrink. generalize 0.
  induction f as [|f IH]; intros k s H; cbn [shrink_by]; [exact H|].
  destruct (next (accept ok tt) k s) as [[[t []] i]|] eqn:E; [|exact H].
  apply IH. apply next_some in E as [_ E]. unfold accept in E.
  destruct (ok t); [reflexivity | discriminate].
Qed.

Lemma shrink_final : forall ok f s, String.length s <= f ->
  forall t, In t (deletions (shrink ok f s)) -> ok t = false.
Proof.
  intros ok f. unfold shrink. generalize 0.
  induction f as [|f IH]; intros k s Hf t Ht; cbn [shrink_by] in Ht.
  - destruct s; [destruct Ht | cbn in Hf; lia].
  - destruct (next (accept ok tt) k s) as [[[t' []] i]|] eqn:E.
    + apply next_some in E as [Hin _]. apply deletions_shorter in Hin.
      apply (IH i t'); [lia | exact Ht].
    + pose proof (next_none _ _ _ E t Ht) as N. unfold accept in N.
      destruct (ok t); [discriminate | reflexivity].
Qed.

(* A test whose knowledge [R] tracks the string, and that accepts the
   deletions [ok] accepts, shrinks as [ok] does. *)
Lemma shrink_by_accept : forall {C} (test : C -> string -> option C) (R : C -> string -> Prop)
  ok f k c s,
  (forall c s t, R c s -> ok s = true -> In t (deletions s) ->
     match test c t with Some c' => ok t = true /\ R c' t | None => ok t = false end) ->
  R c s -> ok s = true ->
  shrink_by test f k c s = shrink_by (accept ok) f k tt s.
Proof.
  intros C test R ok f. induction f as [|f IH]; intros k c s H Hr Hs; [reflexivity|].
  cbn [shrink_by].
  assert (Ha : forall t, In t (deletions s) -> agree (test c) (accept ok tt) t).
  { intros t Ht. pose proof (H c s t Hr Hs Ht) as Hc. unfold agree, accept.
    destruct (test c t) as [c'|]; [destruct Hc as [-> _]; exact I | rewrite Hc; exact I]. }
  pose proof (next_same (test c) (accept ok tt) k s Ha) as N.
  destruct (next (test c) k s) as [[[t c'] i]|] eqn:E1,
           (next (accept ok tt) k s) as [[[t' []] i']|] eqn:E2; try contradiction; [|reflexivity].
  destruct N as [<- <-].
  apply next_some in E1 as [Hin E1].
  pose proof (H c s t Hr Hs Hin) as Hc. rewrite E1 in Hc. destruct Hc as [Ht Hr'].
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
  rewrite (shrink_final _ _ (render_djot bs) (le_n _) _ (deletions_backslash _ _ H)) in Hp.
  discriminate.
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
  rewrite (shrink_final _ _ (render_djot bs) (le_n _) _
             (deletions_braces _ _ _ Hi Hj Hij Hb)) in Hp.
  discriminate.
Qed.

(*
The renderer
============

The specification's test, run incrementally.  The current string's
parse is kept as a trace: for each line, the state before it and the
blocks its step commits.  A deletion is tested by running the parser
from the first line that differs, until both runs are idle with the
rest of the lines the same; from there the two parses agree
(`prefix_determinism`), so the blocks committed until then decide.
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

(* What the rest of a run parses to. *)
Definition rest_of (tr : list entry) (fin : pstate) : blocks :=
  (flat_map (fun e => snd e) tr ++ finish fin)%list.

(* The current string, as the test knows it: its lines, reversed, and
   its run. *)
Record known : Type := Known
  { k_rev : list string
  ; k_trace : list entry
  ; k_fin : pstate }.

Definition known_of (s : string) : known :=
  let ls := split_lines s in
  let run := trace ls (PPara []) in
  Known (rev ls) (fst run) (snd run).

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
   is then known of [t]. *)
Definition fast_test (kn : known) (t : string) : option known :=
  let ls := split_lines t in
  let rls := rev ls in
  let n := List.length (k_trace kn) in
  let d := if Nat.eqb (List.length ls) n then common_prefix (k_rev kn) rls else 0 in
  match walk d n [] (k_trace kn) ls (k_fin kn) with
  | Some (tr, fin) => Some (Known rls tr fin)
  | None => None
  end.

(*
Why the test is the parse test
------------------------------
*)

Definition line_of (e : entry) : string := fst (fst e).

(* The state a run is in at its first entry. *)
Definition state_of (tr : list entry) (fin : pstate) : pstate :=
  match tr with (_, st, _) :: _ => st | [] => fin end.

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

Lemma fast_test_correct : forall s t,
  match fast_test (known_of s) t with
  | Some kn => parse_blocks t = parse_blocks s /\ kn = known_of t
  | None => parse_blocks t <> parse_blocks s
  end.
Proof.
  intros s t. unfold fast_test, known_of. cbn [k_trace k_fin k_rev].
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

Definition render_djot_irredundant (bs : blocks) : string :=
  let s := render_djot bs in shrink_by fast_test (String.length s) 0 (known_of s) s.

Theorem irredundant_is_spec : forall bs,
  render_djot_irredundant bs = irredundant_spec bs.
Proof.
  intros bs. unfold render_djot_irredundant, irredundant_spec, shrink.
  apply (shrink_by_accept _ (fun kn s => kn = known_of s)); [|reflexivity|].
  - intros kn s t -> Hs _. pose proof (fast_test_correct s t) as H.
    apply parses_to_eq in Hs. rewrite Hs in H.
    destruct (fast_test (known_of s) t); [split; [apply parses_to_eq|]; apply H|].
    destruct (parses_to (parse_blocks (render_djot bs)) t) eqn:E; [|reflexivity].
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
