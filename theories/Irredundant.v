(* ai-disclosure: autonomous *)

(** * A rendering with no redundant escape

   `irredundant_spec` is `Render.render_djot` with escapes taken out
   while the parse stays the same: it deletes a backslash, or a `{` and a
   later `}`, whenever what is left parses to the document, until no such
   deletion is left (`shrink`).

   So its theorems hold by construction.  It parses back to every
   canonical document (`spec_roundtrip`), and deleting any one of its
   backslashes (`spec_backslash`), or any brace pair (`spec_braces`),
   changes the parse.  None speaks of escapes: a backslash in a code
   block or in `\\` is content, and deleting it changes the parse for
   that reason.

   A test parses the whole document, so this is a specification and not
   a renderer to run: about 20 s on the README.  `render_djot_irredundant`
   shrinks one top-level block at a time, each tested on its own, and is
   to carry the same theorems
   (`.project/261007.plan.irredundant-escapes.md`). *)

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

(* The deletions a spelling is tested against: each backslash, and each
   `{` with each `}` after it.  [deletions_at] are those starting at byte
   [i]. *)
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
          (seq (S i) (String.length s - S i))
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
  In (del i (del j s)) (deletions s).
Proof.
  intros s i j Hi Hj Hij. apply in_flat_map. exists i. split.
  - apply in_seq. apply get_length in Hi. lia.
  - unfold deletions_at. rewrite Hi. cbn. apply in_flat_map. exists j. split.
    + apply in_seq. apply get_length in Hj. lia.
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
  destruct (String.get j s) as [d|]; [|destruct H].
  destruct (Ascii.eqb d rbrace); [|destruct H].
  destruct H as [<-|[]].
  rewrite del_length; rewrite del_length by lia; lia.
Qed.

(*
Shrinking
=========
*)

Lemma find_app_first : forall {A} (ok : A -> bool) l1 l2,
  find ok (l1 ++ l2) = match find ok l1 with Some y => Some y | None => find ok l2 end.
Proof.
  intros A ok l1 l2. induction l1 as [|x l1 IH]; [reflexivity|].
  cbn. destruct (ok x); [reflexivity | exact IH].
Qed.

(* The first deletion at byte [i] that [ok] accepts, found without
   building the list. *)
Definition first_at (ok : string -> bool) (s : string) (i : nat) : option string :=
  let test t := if ok t then Some t else None in
  match String.get i s with
  | Some c =>
      if Ascii.eqb c bslash then test (del i s)
      else if Ascii.eqb c lbrace then
        (fix go (js : list nat) : option string :=
           match js with
           | [] => None
           | j :: rest =>
               match match String.get j s with
                     | Some d => if Ascii.eqb d rbrace then test (del i (del j s)) else None
                     | None => None
                     end with
               | Some t => Some t
               | None => go rest
               end
           end) (seq (S i) (String.length s - S i))
      else None
  | None => None
  end.

Lemma first_at_find : forall ok s i, first_at ok s i = find ok (deletions_at s i).
Proof.
  intros ok s i. unfold first_at, deletions_at.
  destruct (String.get i s) as [c|]; [|reflexivity].
  destruct (Ascii.eqb c bslash); [reflexivity|].
  destruct (Ascii.eqb c lbrace); [|reflexivity].
  induction (seq (S i) (String.length s - S i)) as [|j js IH]; [reflexivity|].
  cbn [flat_map]. rewrite find_app_first, <- IH.
  destruct (String.get j s) as [d|]; [|reflexivity].
  destruct (Ascii.eqb d rbrace); [|reflexivity].
  cbn. destruct (ok (del i (del j s))); reflexivity.
Qed.

(* The first deletion [ok] accepts at one of [bytes], with its byte. *)
Fixpoint first_in (ok : string -> bool) (s : string) (bytes : list nat)
  : option (string * nat) :=
  match bytes with
  | [] => None
  | i :: rest =>
      match first_at ok s i with
      | Some t => Some (t, i)
      | None => first_in ok s rest
      end
  end.

Lemma first_in_some : forall ok s l t i,
  first_in ok s l = Some (t, i) -> In i l /\ first_at ok s i = Some t.
Proof.
  intros ok s l t i. induction l as [|x l IH]; cbn; [discriminate|].
  destruct (first_at ok s x) as [u|] eqn:E.
  - intros H. injection H as <- <-. auto.
  - intros H. apply IH in H as [H1 H2]. auto.
Qed.

Lemma first_in_none : forall ok s l,
  first_in ok s l = None -> forall i, In i l -> first_at ok s i = None.
Proof.
  intros ok s l. induction l as [|x l IH]; cbn; [tauto|].
  destruct (first_at ok s x) eqn:E; [discriminate|].
  intros H i [<-|Hi]; [exact E | exact (IH H i Hi)].
Qed.

(* The next deletion: from byte [k] on, where the last one was, and from
   the start if there is none there. *)
Definition next (ok : string -> bool) (k : nat) (s : string) : option (string * nat) :=
  match first_in ok s (seq k (String.length s - k)) with
  | Some r => Some r
  | None => first_in ok s (seq 0 (String.length s))
  end.

Lemma next_some : forall ok k s t i,
  next ok k s = Some (t, i) -> In t (deletions s) /\ ok t = true.
Proof.
  intros ok k s t i H. unfold next in H.
  assert (Hl : exists l, first_in ok s l = Some (t, i)
                         /\ forall x, In x l -> x < String.length s).
  { destruct (first_in ok s (seq k _)) as [r|] eqn:E.
    - exists (seq k (String.length s - k)). injection H as ->.
      split; [exact E | intros x Hx; apply in_seq in Hx; lia].
    - exists (seq 0 (String.length s)).
      split; [exact H | intros x Hx; apply in_seq in Hx; lia]. }
  destruct Hl as [l [E Hb]]. apply first_in_some in E as [Hi E].
  rewrite first_at_find in E. apply find_some in E as [Ht Hok].
  split; [|exact Hok]. apply in_flat_map. exists i.
  split; [apply in_seq; specialize (Hb i Hi); lia | exact Ht].
Qed.

Lemma next_none : forall ok k s,
  next ok k s = None -> forall t, In t (deletions s) -> ok t = false.
Proof.
  intros ok k s H t Ht. unfold next in H.
  destruct (first_in ok s (seq k _)); [discriminate|].
  apply in_flat_map in Ht as [i [Hi Ht]].
  pose proof (first_in_none _ _ _ H i Hi) as E.
  rewrite first_at_find in E. exact (find_none _ _ E t Ht).
Qed.

(* Takes the next deletion [ok] accepts, while there is one.  Each is
   shorter, so a fuel of the length runs to the end. *)
Fixpoint shrink_from (ok : string -> bool) (fuel k : nat) (s : string) : string :=
  match fuel with
  | 0 => s
  | S f =>
      match next ok k s with
      | Some (t, i) => shrink_from ok f i t
      | None => s
      end
  end.

Definition shrink (ok : string -> bool) (fuel : nat) (s : string) : string :=
  shrink_from ok fuel 0 s.

Lemma shrink_ok : forall ok f s, ok s = true -> ok (shrink ok f s) = true.
Proof.
  intros ok f. unfold shrink. generalize 0.
  induction f as [|f IH]; intros k s H; cbn [shrink_from]; [exact H|].
  destruct (next ok k s) as [[t i]|] eqn:E; [|exact H].
  apply IH. apply next_some in E as [_ E]. exact E.
Qed.

Lemma shrink_final : forall ok f s, String.length s <= f ->
  forall t, In t (deletions (shrink ok f s)) -> ok t = false.
Proof.
  intros ok f. unfold shrink. generalize 0.
  induction f as [|f IH]; intros k s Hf t Ht; cbn [shrink_from] in Ht.
  - destruct s; [destruct Ht | cbn in Hf; lia].
  - destruct (next ok k s) as [[t' i]|] eqn:E.
    + apply next_some in E as [Hin _]. apply deletions_shorter in Hin.
      apply (IH i t'); [lia | exact Ht].
    + exact (next_none _ _ _ E t Ht).
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
  let s := render_djot bs in shrink (parses_to bs) (String.length s) s.

Theorem spec_roundtrip : forall cbs, cblocks_ok cbs = true ->
  parse_blocks (irredundant_spec (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof.
  intros cbs H. apply parses_to_eq, shrink_ok, parses_to_eq, roundtrip_blocks, H.
Qed.

Theorem spec_backslash : forall bs i,
  String.get i (irredundant_spec bs) = Some bslash ->
  parse_blocks (del i (irredundant_spec bs)) <> bs.
Proof.
  intros bs i H Hp. unfold irredundant_spec in *.
  apply parses_to_eq in Hp.
  rewrite (shrink_final _ _ (render_djot bs) (le_n _) _ (deletions_backslash _ _ H)) in Hp.
  discriminate.
Qed.

Theorem spec_braces : forall bs i j,
  String.get i (irredundant_spec bs) = Some lbrace ->
  String.get j (irredundant_spec bs) = Some rbrace -> i < j ->
  parse_blocks (del i (del j (irredundant_spec bs))) <> bs.
Proof.
  intros bs i j Hi Hj Hij Hp. unfold irredundant_spec in *.
  apply parses_to_eq in Hp.
  rewrite (shrink_final _ _ (render_djot bs) (le_n _) _ (deletions_braces _ _ _ Hi Hj Hij)) in Hp.
  discriminate.
Qed.

(*
A block at a time
=================

Each top-level block is shrunk on its own, tested by parsing its lines
as a document that must be that one block.  Nothing here is proved yet.
*)

Definition block_lines (n : node block) : list string :=
  let ls := render_node_lines n in
  let s := String.concat nl ls in
  let ok := parses_to [n] in
  if ok s then split_lines (shrink ok (String.length s) s) else ls.

Definition render_djot_irredundant (bs : blocks) : string :=
  String.concat nl (sep_lines (map block_lines bs)).

End WithTable.
