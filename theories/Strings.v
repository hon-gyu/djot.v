(* Byte-string utilities and their lemmas: whitespace, reversal, line
   splitting/joining, and small list/bool helpers.  Everything here is
   parser-agnostic; Line.v builds classification on top, Parser.v the
   block structure. *)

From Stdlib Require Import String Ascii List Bool Lia.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope char_scope.

(*
Whitespace and blank lines
==========================
*)

Definition is_ws (c : ascii) : bool :=
  Ascii.eqb c " " || Ascii.eqb c "009" || Ascii.eqb c "013".

Fixpoint is_blank (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => is_ws c && is_blank s'
  end.

Lemma is_blank_cons :
  forall c s, is_blank (String c s) = (is_ws c && is_blank s)%bool.
Proof. reflexivity. Qed.

Definition nonblank (l : string) : bool := negb (is_blank l).

(*
Shape helpers
=============
*)

Definition nonempty {A : Type} (l : list A) : bool :=
  match l with [] => false | _ => true end.

Definition nonempty_str (s : string) : bool :=
  match s with EmptyString => false | _ => true end.

Lemma nonempty_str_intro :
  forall s, s <> EmptyString -> nonempty_str s = true.
Proof. destruct s; [congruence | reflexivity]. Qed.

Lemma nonblank_nonempty :
  forall s, is_blank s = false -> nonempty_str s = true.
Proof. destruct s; simpl; [congruence | reflexivity]. Qed.

Lemma nonempty_app_singleton :
  forall {A : Type} (l : list A) (x : A), nonempty (l ++ [x])%list = true.
Proof. intros A l x. destruct l; reflexivity. Qed.

Lemma forallb_rev :
  forall {A : Type} (f : A -> bool) (l : list A),
    forallb f (rev l) = forallb f l.
Proof.
  intros A f l.
  induction l as [|x l IH]; simpl.
  - reflexivity.
  - rewrite forallb_app, IH. simpl.
    destruct (f x), (forallb f l); reflexivity.
Qed.

(*
Append and reverse
==================
*)

Lemma append_empty_r : forall s, s ++ "" = s.
Proof.
  induction s as [|c s IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma append_assoc : forall a b c, (a ++ b) ++ c = a ++ (b ++ c).
Proof.
  induction a as [|x a IH]; intros; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Fixpoint rev_string_aux (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c s' => rev_string_aux s' (String c acc)
  end.

Definition rev_string (s : string) : string := rev_string_aux s EmptyString.

Lemma rev_aux_app :
  forall s acc, rev_string_aux s acc = rev_string s ++ acc.
Proof.
  induction s as [|c s IH]; intros acc; simpl.
  - reflexivity.
  - rewrite IH. unfold rev_string. simpl. rewrite (IH (String c "")).
    rewrite append_assoc. reflexivity.
Qed.

Lemma rev_string_cons :
  forall c s, rev_string (String c s) = rev_string s ++ String c "".
Proof.
  intros c s. unfold rev_string. simpl. apply rev_aux_app.
Qed.

Lemma rev_string_app :
  forall a b, rev_string (a ++ b) = rev_string b ++ rev_string a.
Proof.
  induction a as [|c a IH]; intros b; simpl.
  - rewrite append_empty_r. reflexivity.
  - rewrite !rev_string_cons, IH, append_assoc. reflexivity.
Qed.

Lemma rev_string_involutive : forall s, rev_string (rev_string s) = s.
Proof.
  induction s as [|c s IH].
  - reflexivity.
  - rewrite rev_string_cons, rev_string_app, IH. reflexivity.
Qed.

Lemma rev_aux_length :
  forall s acc,
    String.length (rev_string_aux s acc) =
    (String.length s + String.length acc)%nat.
Proof.
  induction s as [|c s IH]; intros acc; simpl.
  - reflexivity.
  - rewrite IH. simpl. lia.
Qed.

Lemma rev_length :
  forall s, String.length (rev_string s) = String.length s.
Proof.
  intros s. unfold rev_string. rewrite rev_aux_length. simpl. lia.
Qed.

Lemma rev_aux_blank :
  forall s acc, is_blank (rev_string_aux s acc) = (is_blank s && is_blank acc)%bool.
Proof.
  induction s as [|c s IH]; intros acc; simpl.
  - reflexivity.
  - rewrite IH. simpl.
    destruct (is_ws c), (is_blank s), (is_blank acc); reflexivity.
Qed.

Lemma rev_blank : forall s, is_blank (rev_string s) = is_blank s.
Proof.
  intros s. unfold rev_string. rewrite rev_aux_blank. simpl.
  apply andb_true_r.
Qed.

(*
Trailing-whitespace stripping
=============================
*)

Fixpoint drop_leading_ws (s : string) : string :=
  match s with
  | String c s' => if is_ws c then drop_leading_ws s' else s
  | EmptyString => EmptyString
  end.

Definition strip_trailing_ws (s : string) : string :=
  rev_string (drop_leading_ws (rev_string s)).

Lemma drop_leading_ws_nonempty :
  forall s, is_blank s = false -> drop_leading_ws s <> EmptyString.
Proof.
  induction s as [|c s IH]; intros H.
  - discriminate.
  - rewrite is_blank_cons in H. cbn [drop_leading_ws].
    destruct (is_ws c) eqn:E.
    + apply IH. rewrite andb_true_l in H. exact H.
    + discriminate.
Qed.

Lemma strip_trailing_ws_nonempty :
  forall s, is_blank s = false -> nonempty_str (strip_trailing_ws s) = true.
Proof.
  intros s H. unfold strip_trailing_ws.
  apply nonempty_str_intro.
  intros Hrev.
  assert (Hd : drop_leading_ws (rev_string s) <> EmptyString).
  { apply drop_leading_ws_nonempty. rewrite rev_blank. exact H. }
  apply Hd.
  apply (f_equal String.length) in Hrev.
  rewrite rev_length in Hrev. simpl in Hrev.
  destruct (drop_leading_ws (rev_string s)); [reflexivity | discriminate].
Qed.

(*
Lines: splitting and joining
============================
*)

Definition nl : string := String "010" EmptyString.

Fixpoint split_lines_aux (s : string) (cur : string) : list string :=
  match s with
  | EmptyString =>
      match cur with
      | EmptyString => []
      | _ => [rev_string cur]
      end
  | String c s' =>
      if Ascii.eqb c "010"
      then rev_string cur :: split_lines_aux s' EmptyString
      else split_lines_aux s' (String c cur)
  end.

Definition split_lines (s : string) : list string := split_lines_aux s EmptyString.

Fixpoint no_nl (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => negb (Ascii.eqb c "010") && no_nl s'
  end.

(* A line as produced by a renderer: nonblank and newline-free. *)
Definition line_ok (l : string) : bool := nonblank l && no_nl l.

Lemma line_ok_no_nl : forall l, line_ok l = true -> no_nl l = true.
Proof.
  intros l H. unfold line_ok in H. apply andb_true_iff in H as [_ H]. exact H.
Qed.

Lemma line_ok_nonblank : forall l, line_ok l = true -> is_blank l = false.
Proof.
  intros l H. unfold line_ok, nonblank in H.
  apply andb_true_iff in H as [H _]. apply negb_true_iff in H. exact H.
Qed.

Lemma line_ok_nonempty : forall l, line_ok l = true -> l <> EmptyString.
Proof.
  intros l H E. subst. discriminate (line_ok_nonblank _ H).
Qed.

Lemma split_aux_no_nl :
  forall x cur, no_nl x = true ->
  split_lines_aux x cur =
  match rev_string_aux x cur with
  | EmptyString => []
  | String _ _ => [rev_string (rev_string_aux x cur)]
  end.
Proof.
  induction x as [|c x IH]; intros cur H; simpl.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hc Hx].
    apply negb_true_iff in Hc. rewrite Hc.
    apply IH. exact Hx.
Qed.

Lemma split_lines_single :
  forall x, no_nl x = true -> x <> EmptyString -> split_lines x = [x].
Proof.
  intros x H Hne. unfold split_lines.
  rewrite (split_aux_no_nl x EmptyString H).
  rewrite rev_aux_app, append_empty_r.
  destruct (rev_string x) eqn:E.
  - exfalso. apply Hne.
    apply (f_equal String.length) in E. rewrite rev_length in E.
    destruct x; [reflexivity | discriminate].
  - rewrite <- E, rev_string_involutive. reflexivity.
Qed.

Lemma split_lines_line :
  forall x r, no_nl x = true ->
  split_lines (x ++ String "010" r) = x :: split_lines r.
Proof.
  intros x r H. unfold split_lines.
  (* aux with a general accumulator *)
  assert (Haux : forall x cur, no_nl x = true ->
    split_lines_aux (x ++ String "010" r) cur =
    rev_string (rev_string_aux x cur) :: split_lines_aux r EmptyString).
  { induction x0 as [|c x0 IH]; intros cur Hx; simpl.
    - reflexivity.
    - simpl in Hx. apply andb_true_iff in Hx as [Hc Hx].
      apply negb_true_iff in Hc. rewrite Hc.
      apply IH. exact Hx. }
  rewrite (Haux x EmptyString H).
  rewrite rev_aux_app, append_empty_r, rev_string_involutive.
  reflexivity.
Qed.

Lemma split_lines_cons_nl :
  forall r, split_lines (String "010" r) = EmptyString :: split_lines r.
Proof. reflexivity. Qed.

(*
Joined nonblank lines split back exactly
----------------------------------------
*)

Lemma split_join_last :
  forall a ls, forallb line_ok (a :: ls) = true ->
  split_lines (String.concat nl (a :: ls)) = a :: ls.
Proof.
  intros a ls. revert a.
  induction ls as [|b ls IH]; intros a H; simpl in H;
    apply andb_true_iff in H as [Ha Hrest].
  - simpl. apply split_lines_single.
    + apply line_ok_no_nl; exact Ha.
    + apply line_ok_nonempty; exact Ha.
  - change (String.concat nl (a :: b :: ls))
      with (a ++ String "010" (String.concat nl (b :: ls))).
    rewrite split_lines_line by (apply line_ok_no_nl; exact Ha).
    f_equal. apply IH. exact Hrest.
Qed.

Lemma split_join_line :
  forall a ls r, forallb line_ok (a :: ls) = true ->
  split_lines (String.concat nl (a :: ls) ++ String "010" r) =
  ((a :: ls) ++ split_lines r)%list.
Proof.
  intros a ls. revert a.
  induction ls as [|b ls IH]; intros a r H; simpl in H;
    apply andb_true_iff in H as [Ha Hrest].
  - simpl. apply split_lines_line. apply line_ok_no_nl; exact Ha.
  - change (String.concat nl (a :: b :: ls))
      with (a ++ String "010" (String.concat nl (b :: ls))).
    rewrite append_assoc. simpl.
    rewrite split_lines_line by (apply line_ok_no_nl; exact Ha).
    simpl. f_equal. apply IH. exact Hrest.
Qed.
