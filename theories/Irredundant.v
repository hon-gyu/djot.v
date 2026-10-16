(* ai-disclosure: autonomous *)

(** * A rendering with no redundant escape

   `render_djot_irredundant` is `Render.render_djot` with escapes taken
   out while the parse stays the same: it deletes a backslash, or a `{`
   and a later `}`, whenever what is left parses to the document, until
   no such deletion is left (`shrink`).

   So both of its theorems hold by construction.  It parses back to every
   canonical document (`irredundant_roundtrip`), and deleting any one of
   its backslashes (`irredundant_backslash`), or any brace pair
   (`irredundant_braces`), changes the parse.  Neither speaks of escapes:
   a backslash in a code block or in `\\` is content, and deleting it
   changes the parse for that reason.

   A test parses the whole document, so this is a specification and not
   a renderer to run: about 20 s on the README.  A renderer that tests a
   paragraph at a time is to be proved equal to it
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
   `{` with each `}` after it. *)
Definition deletions (s : string) : list string :=
  flat_map
    (fun i =>
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
       end)
    (seq 0 (String.length s)).

Lemma deletions_backslash : forall s i,
  String.get i s = Some bslash -> In (del i s) (deletions s).
Proof.
  intros s i H. apply in_flat_map. exists i. split.
  - apply in_seq. apply get_length in H. lia.
  - rewrite H. cbn. left. reflexivity.
Qed.

Lemma deletions_braces : forall s i j,
  String.get i s = Some lbrace -> String.get j s = Some rbrace -> i < j ->
  In (del i (del j s)) (deletions s).
Proof.
  intros s i j Hi Hj Hij. apply in_flat_map. exists i. split.
  - apply in_seq. apply get_length in Hi. lia.
  - rewrite Hi. cbn. apply in_flat_map. exists j. split.
    + apply in_seq. apply get_length in Hj. lia.
    + rewrite Hj. cbn. left. reflexivity.
Qed.

Lemma deletions_shorter : forall s t, In t (deletions s) -> String.length t < String.length s.
Proof.
  intros s t H. apply in_flat_map in H as [i [Hi H]]. apply in_seq in Hi.
  destruct (String.get i s) as [c|] eqn:Ec; [|destruct H].
  destruct (Ascii.eqb c bslash).
  { destruct H as [<-|[]]. rewrite del_length by lia. lia. }
  destruct (Ascii.eqb c lbrace); [|destruct H].
  apply in_flat_map in H as [j [Hj H]]. apply in_seq in Hj.
  destruct (String.get j s) as [d|]; [|destruct H].
  destruct (Ascii.eqb d rbrace); [|destruct H].
  destruct H as [<-|[]].
  rewrite del_length; rewrite del_length by lia; lia.
Qed.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
The spelling
============
*)

(* Takes the first deletion that still parses to [want], while there is
   one.  Each is shorter, so a fuel of the length runs to the end. *)
Fixpoint shrink (fuel : nat) (want : blocks) (s : string) : string :=
  match fuel with
  | 0 => s
  | S f =>
      match find (fun t => blocks_eqb (parse_blocks t) want) (deletions s) with
      | Some t => shrink f want t
      | None => s
      end
  end.

Definition render_djot_irredundant (bs : blocks) : string :=
  let s := render_djot bs in shrink (String.length s) bs s.

Lemma shrink_parse : forall f want s,
  parse_blocks s = want -> parse_blocks (shrink f want s) = want.
Proof.
  induction f as [|f IH]; intros want s H; cbn [shrink]; [exact H|].
  destruct (find _ (deletions s)) as [t|] eqn:E; [|exact H].
  apply IH. apply find_some in E as [_ E]. apply blocks_eqb_eq. exact E.
Qed.

Lemma shrink_final : forall f want s, String.length s <= f ->
  forall t, In t (deletions (shrink f want s)) -> parse_blocks t <> want.
Proof.
  induction f as [|f IH]; intros want s Hf t Ht; cbn [shrink] in Ht.
  - destruct s; [destruct Ht | cbn in Hf; lia].
  - destruct (find _ (deletions s)) as [t'|] eqn:E.
    + apply find_some in E as [Hin _]. apply deletions_shorter in Hin.
      apply (IH want t'); [lia | exact Ht].
    + intros Hp. apply (find_none _ _ E) in Ht.
      rewrite Hp in Ht. rewrite (proj2 (blocks_eqb_eq want want) eq_refl) in Ht.
      discriminate.
Qed.

(*
The theorems
============
*)

Theorem irredundant_roundtrip : forall cbs, cblocks_ok cbs = true ->
  parse_blocks (render_djot_irredundant (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof.
  intros cbs H. apply shrink_parse, roundtrip_blocks, H.
Qed.

Theorem irredundant_backslash : forall cbs i,
  String.get i (render_djot_irredundant (blocks_of_cblocks cbs)) = Some bslash ->
  parse_blocks (del i (render_djot_irredundant (blocks_of_cblocks cbs)))
  <> blocks_of_cblocks cbs.
Proof.
  intros cbs i H. unfold render_djot_irredundant in *.
  eapply shrink_final; [apply le_n | apply deletions_backslash, H].
Qed.

Theorem irredundant_braces : forall cbs i j,
  String.get i (render_djot_irredundant (blocks_of_cblocks cbs)) = Some lbrace ->
  String.get j (render_djot_irredundant (blocks_of_cblocks cbs)) = Some rbrace ->
  i < j ->
  parse_blocks (del i (del j (render_djot_irredundant (blocks_of_cblocks cbs))))
  <> blocks_of_cblocks cbs.
Proof.
  intros cbs i j Hi Hj Hij. unfold render_djot_irredundant in *.
  eapply shrink_final; [apply le_n | apply deletions_braces; assumption].
Qed.

End WithTable.
