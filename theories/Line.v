(* Line classification: the prefix-determinism seam.

   Block structure in djot is a function of what each line looks like
   (spec: "blocks can be parsed line by line ... the contribution a line
   makes to block-level structure never depends on a future line").  This
   module gives each line its kind; the parser consumes kinds, and the
   classifier is the single place a new block construct's start syntax is
   added.  Renderability (Render.v) is phrased as "each rendered line
   classifies as intended", which is what makes roundtrip proofs local. *)

From Stdlib Require Import String Ascii Bool PeanoNat.
From DjotV Require Import Strings.

Local Open Scope string_scope.
Local Open Scope char_scope.

(* An opened code fence: its character (` or ~), length, and info string
   (language, or =FORMAT for raw blocks). *)
Record fence : Type := Fence
  { f_ch : ascii; f_len : nat; f_info : string }.

Inductive line_kind : Type :=
  | KBlank              (* only whitespace *)
  | KThematic           (* thematic break: 3+ of - or * (mixed ok), ws between *)
  | KFence (f : fence)  (* code fence opener *)
  | KText.              (* anything else: paragraph text *)

(*
Recognizers
===========
*)

Definition is_marker (c : ascii) : bool :=
  Ascii.eqb c "-" || Ascii.eqb c "*".

(* djot.js pattThematicBreak: markers and whitespace only, >= 3 markers.
   (Indentation is allowed; leading ws goes through the ws branch.) *)

Fixpoint thematic_count (s : string) (count : nat) : bool :=
  match s with
  | EmptyString => Nat.leb 3 count
  | String c s' =>
      if is_marker c then thematic_count s' (S count)
      else if is_ws c then thematic_count s' count
      else false
  end.

Definition is_thematic (l : string) : bool := thematic_count l 0.

(* Code fences, per djot.js pattCodeFence:
   3+ of a uniform fence char (` or ~), optional ws, one info token
   containing neither whitespace nor backticks, optional trailing ws.
   The fence may be indented.  A close line is the same char, at least
   the open length, and nothing else but whitespace. *)

Fixpoint count_run (c : ascii) (s : string) : nat * string :=
  match s with
  | String c' s' =>
      if Ascii.eqb c c'
      then let (n, r) := count_run c s' in (S n, r)
      else (O, s)
  | EmptyString => (O, s)
  end.

Definition is_info_char (c : ascii) : bool :=
  negb (is_ws c || Ascii.eqb c "`" || Ascii.eqb c "010").

Fixpoint take_info (s : string) : string * string :=
  match s with
  | String c s' =>
      if is_info_char c
      then let (info, r) := take_info s' in (String c info, r)
      else (EmptyString, s)
  | EmptyString => (EmptyString, s)
  end.

Definition fence_open (l : string) : option fence :=
  match drop_leading_ws l with
  | String c _ as l' =>
      if Ascii.eqb c "`" || Ascii.eqb c "~"
      then
        let (n, r) := count_run c l' in
        if Nat.leb 3 n
        then
          let (info, r') := take_info (drop_leading_ws r) in
          if is_blank r' then Some (Fence c n info) else None
        else None
      else None
  | EmptyString => None
  end.

Definition fence_close (f : fence) (l : string) : bool :=
  let (n, r) := count_run (f_ch f) (drop_leading_ws l) in
  Nat.leb (f_len f) n && is_blank r.

Definition classify (l : string) : line_kind :=
  if is_blank l then KBlank
  else match fence_open l with
       | Some f => KFence f
       | None => if is_thematic l then KThematic else KText
       end.

(*
Classification facts
====================
*)

Lemma classify_blank :
  forall l, is_blank l = true -> classify l = KBlank.
Proof. intros l H. unfold classify. rewrite H. reflexivity. Qed.

Lemma classify_kblank_blank :
  forall l, classify l = KBlank -> is_blank l = true.
Proof.
  intros l H. unfold classify in H.
  destruct (is_blank l); [reflexivity|].
  destruct (fence_open l); [discriminate|].
  destruct (is_thematic l); discriminate.
Qed.

Lemma classify_not_kblank_nonblank :
  forall l, classify l <> KBlank -> is_blank l = false.
Proof.
  intros l H. destruct (is_blank l) eqn:E; [|reflexivity].
  exfalso. apply H, classify_blank, E.
Qed.

Lemma classify_ktext :
  forall l,
    is_blank l = false -> fence_open l = None -> is_thematic l = false ->
    classify l = KText.
Proof.
  intros l Hb Hf Ht. unfold classify. rewrite Hb, Hf, Ht. reflexivity.
Qed.

(* The canonical thematic-break rendering classifies as one. *)
Lemma classify_canonical_thematic : classify "* * * *" = KThematic.
Proof. reflexivity. Qed.

Definition is_text (l : string) : bool :=
  match classify l with KText => true | _ => false end.

Lemma is_text_classify :
  forall l, is_text l = true -> classify l = KText.
Proof.
  intros l H. unfold is_text in H.
  destruct (classify l); (discriminate || reflexivity).
Qed.

(*
Canonical code fences
=====================

The renderer emits backtick fences of length 3; these lemmas say such
lines classify as intended. *)

Fixpoint all_info_chars (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => is_info_char c && all_info_chars s'
  end.

(* Decompose the all_info_chars head fact into its three components. *)
Lemma info_char_parts :
  forall c, is_info_char c = true ->
  is_ws c = false /\ Ascii.eqb c "`" = false /\ Ascii.eqb c "010" = false.
Proof.
  intros c H. unfold is_info_char in H. apply negb_true_iff in H.
  apply orb_false_iff in H as [H Hn]. apply orb_false_iff in H as [Hw Hb].
  auto.
Qed.

Lemma count_run_info :
  forall info, all_info_chars info = true ->
  count_run "`" info = (O, info).
Proof.
  intros info H. destruct info as [|c info']; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [Hc _].
  apply info_char_parts in Hc as (_ & Hb & _).
  cbn [count_run].
  destruct (Ascii.eqb "`" c) eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst c.
  rewrite Ascii.eqb_refl in Hb. discriminate.
Qed.

Lemma drop_leading_ws_info :
  forall info, all_info_chars info = true ->
  drop_leading_ws info = info.
Proof.
  intros info H. destruct info as [|c info']; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [Hc _].
  apply info_char_parts in Hc as (Hw & _ & _).
  cbn [drop_leading_ws]. rewrite Hw. reflexivity.
Qed.

Lemma take_info_all :
  forall info, all_info_chars info = true ->
  take_info info = (info, EmptyString).
Proof.
  induction info as [|c info IH]; intros H; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [Hc Hinfo].
  cbn [take_info]. rewrite Hc, (IH Hinfo). reflexivity.
Qed.

Lemma drop_head_nonws :
  forall c s, is_ws c = false -> drop_leading_ws (String c s) = String c s.
Proof. intros c s H. cbn [drop_leading_ws]. rewrite H. reflexivity. Qed.

Lemma fence_open_backtick :
  forall info, all_info_chars info = true ->
  fence_open ("```" ++ info) = Some (Fence "`" 3 info).
Proof.
  intros info H.
  assert (E3 : count_run "`"
                 (String "`" (String "`" (String "`" info))) = (3, info)).
  { cbn [count_run Ascii.eqb]. rewrite (count_run_info info H). reflexivity. }
  unfold fence_open.
  change ("```" ++ info) with (String "`" (String "`" (String "`" info))).
  rewrite drop_head_nonws by reflexivity.
  cbn [Ascii.eqb orb].
  rewrite E3.
  cbn [Nat.leb].
  rewrite (drop_leading_ws_info info H), (take_info_all info H).
  reflexivity.
Qed.

Lemma classify_backtick_fence :
  forall info, all_info_chars info = true ->
  classify ("```" ++ info) = KFence (Fence "`" 3 info).
Proof.
  intros info H. unfold classify.
  change (is_blank ("```" ++ info)) with false.
  rewrite (fence_open_backtick info H). reflexivity.
Qed.

Lemma fence_close_canonical :
  forall info, fence_close (Fence "`" 3 info) "```" = true.
Proof. reflexivity. Qed.
