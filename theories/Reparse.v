(* ai-disclosure: ai-generated *)

(** * Reparsing after a replacement

   A document's lines, cut at every point where the block fold is idle.
   Each piece is parsed on its own, from the idle state, with its lines
   numbered from 0.  The semantic parse is the pieces' blocks in order
   (`pieces_parse`), and the located parse is the same with each piece's
   positions shifted to where its first line is (`parse_blocks_located`).

   `splice` replaces a run of pieces with new lines.  It parses the new
   lines, then continues into the following pieces only until the fold is
   idle at the end of one, and keeps the rest (`replace_reuses`).  The
   result is the pieces of the edited lines (`splice_pieces`), for any new
   lines and for both parses. *)

From Stdlib Require Import String List Bool PeanoNat Lia.
From DjotV Require Import Strings Ast InlineTable Step.
Import ListNotations.

(*
Pieces
======
*)

Record piece : Type := Piece
  { piece_lines : list string
  ; piece_blocks : blocks }.

Definition pieces_text (cs : list piece) : list string :=
  concat (map piece_lines cs).

Definition pieces_tree (cs : list piece) : blocks :=
  concat (map piece_blocks cs).

Lemma pieces_text_app :
  forall xs ys, pieces_text (xs ++ ys) = (pieces_text xs ++ pieces_text ys)%list.
Proof.
  intros xs ys. unfold pieces_text. rewrite map_app, concat_app. reflexivity.
Qed.

Lemma pieces_tree_app :
  forall xs ys, pieces_tree (xs ++ ys) = (pieces_tree xs ++ pieces_tree ys)%list.
Proof.
  intros xs ys. unfold pieces_tree. rewrite map_app, concat_app. reflexivity.
Qed.

(* The piece being read: its lines so far, last first, the blocks they
   emitted, the fold's state, and how many lines it has. *)
Record pending : Type := Pending
  { pend_lines : list string
  ; pend_blocks : blocks
  ; pend_state : pstate
  ; pend_count : nat }.

Definition fresh : pending := Pending [] [] (PPara []) 0.

Lemma is_idle_true : forall st, is_idle st = true -> st = PPara [].
Proof.
  intros [[|c cur]| | | | | | | | | | | |]; cbn; congruence.
Qed.

(*
Cutting
=======

Over any fold step that is told the line's index within its piece, and
the matching `finish`.
*)

Section Cut.
Variable stp : nat -> string -> pstate -> blocks * pstate.
Variable fin : pstate -> blocks.

(* Feed lines to the piece being read, emitting it each time the fold is
   idle. *)
Fixpoint cut (ls : list string) (p : pending) : list piece * pending :=
  match ls with
  | [] => ([], p)
  | l :: rest =>
      let (out, st) := stp (pend_count p) l (pend_state p) in
      let lines := l :: pend_lines p in
      let bs := (pend_blocks p ++ out)%list in
      if is_idle st
      then let (cs, p') := cut rest fresh in (Piece (rev lines) bs :: cs, p')
      else cut rest (Pending lines bs st (S (pend_count p)))
  end.

(* End of input: the piece being read, if it has lines, is the last. *)
Definition close (p : pending) : list piece :=
  match pend_lines p with
  | [] => []
  | _ => [Piece (rev (pend_lines p)) (pend_blocks p ++ fin (pend_state p))]
  end.

Definition pieces (ls : list string) : list piece :=
  let (cs, p) := cut ls fresh in (cs ++ close p)%list.

Lemma cut_app :
  forall xs ys p,
    cut (xs ++ ys) p
    = let (cs1, p1) := cut xs p in
      let (cs2, p2) := cut ys p1 in ((cs1 ++ cs2)%list, p2).
Proof.
  induction xs as [|x xs IH]; intros ys p.
  - cbn. destruct (cut ys p). reflexivity.
  - cbn [app cut]. destruct (stp (pend_count p) x (pend_state p)) as [out st].
    destruct (is_idle st).
    + rewrite IH. destruct (cut xs fresh) as [cs1 p1].
      destruct (cut ys p1) as [cs2 p2]. reflexivity.
    + apply IH.
Qed.

Lemma cut_text :
  forall ls p,
    (pieces_text (fst (cut ls p)) ++ rev (pend_lines (snd (cut ls p))))%list
    = (rev (pend_lines p) ++ ls)%list.
Proof.
  induction ls as [|l rest IH]; intros p.
  - cbn. rewrite app_nil_r. reflexivity.
  - cbn [cut]. destruct (stp (pend_count p) l (pend_state p)) as [out st].
    destruct (is_idle st).
    + pose proof (IH fresh) as H. destruct (cut rest fresh) as [cs p'].
      cbn [fst snd pend_lines fresh rev app] in *.
      unfold pieces_text in *. cbn [map concat piece_lines].
      rewrite <- app_assoc, H. cbn. rewrite <- app_assoc. reflexivity.
    + rewrite IH. cbn [pend_lines rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma close_text : forall p, pieces_text (close p) = rev (pend_lines p).
Proof.
  intros [[|l lines] bs st n]; [reflexivity|].
  unfold pieces_text, close. cbn [map concat pend_lines piece_lines].
  rewrite app_nil_r. reflexivity.
Qed.

Theorem pieces_text_pieces : forall ls, pieces_text (pieces ls) = ls.
Proof.
  intros ls. unfold pieces. pose proof (cut_text ls fresh) as H.
  destruct (cut ls fresh) as [cs p]. cbn in H.
  rewrite pieces_text_app, close_text. exact H.
Qed.

(*
Canonical pieces
----------------

What makes the pieces of a text unique: each piece but the last is cut
alone into itself, and the last is what is left pending when its lines
are cut.  A splice keeps that shape, so it gives the pieces of the
edited text.
*)

(* A piece that the cut emits whole, ending idle. *)
Definition minimal (c : piece) : Prop :=
  cut (piece_lines c) fresh = ([c], fresh).

(* A pending piece that cutting its own lines reaches. *)
Definition reached (p : pending) : Prop :=
  cut (rev (pend_lines p)) fresh = ([], p).

Definition canon (cs : list piece) : Prop :=
  exists xs p, cs = (xs ++ close p)%list /\ Forall minimal xs /\ reached p.

Lemma reached_fresh : reached fresh.
Proof. reflexivity. Qed.

Lemma cut_reached :
  forall ls p, reached p ->
    Forall minimal (fst (cut ls p)) /\ reached (snd (cut ls p)).
Proof.
  induction ls as [|l rest IH]; intros p Hp; [split; [constructor|exact Hp]|].
  assert (Hl : cut (rev (l :: pend_lines p)) fresh = cut [l] p).
  { cbn [rev]. rewrite cut_app, Hp. destruct (cut [l] p). reflexivity. }
  cbn [cut] in Hl |- *. destruct (stp (pend_count p) l (pend_state p)) as [out st].
  destruct (is_idle st).
  - cbn in Hl. destruct (IH fresh reached_fresh) as [Hm Hr].
    destruct (cut rest fresh) as [cs p']. cbn [fst snd] in *.
    split; [constructor; [exact Hl|exact Hm]|exact Hr].
  - apply IH. exact Hl.
Qed.

Lemma cut_minimal :
  forall xs, Forall minimal xs -> cut (pieces_text xs) fresh = (xs, fresh).
Proof.
  intros xs H. induction H as [|x xs Hx _ IH]; [reflexivity|].
  unfold pieces_text. cbn [map concat]. fold (pieces_text xs).
  rewrite cut_app, Hx, IH. reflexivity.
Qed.

Lemma pieces_app :
  forall xs ys, Forall minimal xs ->
    pieces (pieces_text xs ++ ys) = (xs ++ pieces ys)%list.
Proof.
  intros xs ys H. unfold pieces. rewrite cut_app, cut_minimal by exact H.
  destruct (cut ys fresh). rewrite app_assoc. reflexivity.
Qed.

Lemma canon_pieces : forall cs, canon cs -> pieces (pieces_text cs) = cs.
Proof.
  intros cs (xs & p & -> & Hm & Hr).
  rewrite pieces_text_app, close_text, pieces_app by exact Hm.
  unfold pieces. rewrite Hr. reflexivity.
Qed.

Lemma pieces_canon : forall ls, canon (pieces ls).
Proof.
  intros ls. unfold pieces.
  destruct (cut_reached ls fresh reached_fresh) as [Hm Hr].
  destruct (cut ls fresh) as [cs p]. exists cs, p. auto.
Qed.

Lemma close_length : forall p, length (close p) <= 1.
Proof. intros [[|l lines] bs st n]; cbn; lia. Qed.

Lemma canon_skipn : forall cs j, canon cs -> canon (skipn j cs).
Proof.
  intros cs j (xs & p & -> & Hm & Hr).
  destruct (Nat.le_gt_cases j (length xs)) as [Hj|Hj].
  - rewrite skipn_app, (proj2 (Nat.sub_0_le j (length xs)) Hj). cbn [skipn].
    exists (skipn j xs), p. split; [reflexivity|].
    split; [|exact Hr].
    rewrite <- (firstn_skipn j xs) in Hm. apply Forall_app in Hm. apply Hm.
  - rewrite skipn_app, skipn_all2 by lia. cbn [app].
    pose proof (close_length p) as Hl.
    rewrite skipn_all2 by lia.
    exists [], fresh. split; [reflexivity|]. split; [constructor|apply reached_fresh].
Qed.

Lemma canon_firstn :
  forall cs i, canon cs -> i < length cs -> Forall minimal (firstn i cs).
Proof.
  intros cs i (xs & p & -> & Hm & _) Hi.
  rewrite length_app in Hi. pose proof (close_length p).
  rewrite firstn_app, (proj2 (Nat.sub_0_le i (length xs)) ltac:(lia)).
  cbn [firstn]. rewrite app_nil_r.
  rewrite <- (firstn_skipn i xs) in Hm. apply Forall_app in Hm. apply Hm.
Qed.

(*
Replacing
---------
*)

(* Continue the piece being read into the pieces after the edit, until
   the fold is idle at the end of one; from there the old pieces stand. *)
Fixpoint settle (p : pending) (post : list piece) : list piece :=
  if is_idle (pend_state p) then (close p ++ post)%list
  else match post with
       | [] => close p
       | c :: post' =>
           let (cs, p') := cut (piece_lines c) p in (cs ++ settle p' post')%list
       end.

(* `new` in place of whatever lay between `pre` and `post`. *)
Definition replace (pre : list piece) (new : list string) (post : list piece)
  : list piece :=
  let (cs, p) := cut new fresh in (pre ++ cs ++ settle p post)%list.

(* `new` in place of pieces `i` to `j - 1`.  An edit that reaches the end
   also takes the last piece before it, since that one may not end
   idle. *)
Definition splice (cs : list piece) (i j : nat) (new : list string)
  : list piece :=
  match skipn j cs, i with
  | [], S i' => replace (firstn i' cs)
                  (pieces_text (firstn 1 (skipn i' cs)) ++ new)%list []
  | post, _ => replace (firstn i cs) new post
  end.

(* A cut ends on the fresh pending or on one with a line and a state that
   is not idle. *)
Definition settled_or_open (p : pending) : Prop :=
  p = fresh \/ (pend_lines p <> [] /\ is_idle (pend_state p) = false).

Lemma cut_shape :
  forall ls p, settled_or_open p -> settled_or_open (snd (cut ls p)).
Proof.
  induction ls as [|l rest IH]; intros p Hp; [exact Hp|].
  cbn [cut]. destruct (stp (pend_count p) l (pend_state p)) as [out st].
  destruct (is_idle st) eqn:Hi.
  - pose proof (IH fresh (or_introl eq_refl)) as H.
    destruct (cut rest fresh). exact H.
  - apply IH. right. split; [discriminate|exact Hi].
Qed.

Lemma reached_idle :
  forall p, reached p -> is_idle (pend_state p) = true -> p = fresh.
Proof.
  intros p Hr Hi. unfold reached in Hr.
  pose proof (cut_shape (rev (pend_lines p)) fresh (or_introl eq_refl)) as H.
  rewrite Hr in H. cbn [snd] in H. destruct H as [H|[_ H]]; [exact H|congruence].
Qed.

Lemma settle_cut :
  forall post p, reached p -> canon post ->
    settle p post
    = let (cs, p') := cut (pieces_text post) p in (cs ++ close p')%list.
Proof.
  induction post as [|c post IH]; intros p Hr Hc; cbn [settle].
  - destruct (is_idle (pend_state p)); rewrite ?app_nil_r; reflexivity.
  - destruct (is_idle (pend_state p)) eqn:Hi.
    + rewrite (reached_idle p Hr Hi). cbn [close pend_lines fresh app].
      pose proof (canon_pieces _ Hc) as H. unfold pieces in H. symmetry. exact H.
    + destruct (cut_reached (piece_lines c) p Hr) as [_ Hr'].
      unfold pieces_text. cbn [map concat]. fold (pieces_text post).
      rewrite cut_app. destruct (cut (piece_lines c) p) as [cs p'].
      cbn [snd] in Hr'.
      assert (Hc' : canon post).
      { replace post with (skipn 1 (c :: post)) by reflexivity.
        apply canon_skipn, Hc. }
      rewrite (IH p' Hr' Hc'). destruct (cut (pieces_text post) p').
      rewrite app_assoc. reflexivity.
Qed.

Theorem replace_pieces :
  forall pre new post, canon post ->
    replace pre new post = (pre ++ pieces (new ++ pieces_text post))%list.
Proof.
  intros pre new post Hc. unfold replace, pieces.
  rewrite cut_app.
  destruct (cut_reached new fresh reached_fresh) as [_ Hr].
  destruct (cut new fresh) as [cs p]. cbn [snd] in Hr.
  rewrite (settle_cut post p Hr Hc).
  destruct (cut (pieces_text post) p). rewrite !app_assoc. reflexivity.
Qed.

(** Splicing the pieces of a text gives the pieces of the edited text. *)
Theorem splice_pieces :
  forall ls i j new,
    let cs := pieces ls in
    i <= j -> j <= length cs ->
    splice cs i j new
    = pieces (pieces_text (firstn i cs) ++ new ++ pieces_text (skipn j cs)).
Proof.
  intros ls i j new cs Hij Hj. pose proof (pieces_canon ls) as Hc. fold cs in Hc.
  assert (Hnil : canon []) by (exists [], fresh; repeat split; constructor).
  unfold splice. destruct (skipn j cs) as [|c post] eqn:Hpost.
  - destruct i as [|i']; rewrite replace_pieces by exact Hnil; [reflexivity|].
    cbn [pieces_text map concat]. rewrite !app_nil_r.
    replace (S i') with (i' + 1) by lia. rewrite firstn_skipn_comm.
    replace (firstn i' cs) with (firstn i' (firstn (i' + 1) cs))
      by (rewrite firstn_firstn; f_equal; lia).
    set (F := firstn (i' + 1) cs). rewrite <- (firstn_skipn i' F) at 3.
    rewrite pieces_text_app, <- app_assoc, (pieces_app (firstn i' F)); [reflexivity|].
    unfold F. rewrite firstn_firstn, Nat.min_l by lia.
    apply canon_firstn; [exact Hc|lia].
  - assert (Hi : i < length cs).
    { destruct (Nat.lt_ge_cases j (length cs)) as [Hlt|Hge]; [lia|].
      rewrite skipn_all2 in Hpost by exact Hge. discriminate. }
    rewrite <- Hpost, replace_pieces by (apply canon_skipn, Hc).
    rewrite pieces_app; [reflexivity|]. apply canon_firstn; assumption.
Qed.

(*
What is reused
--------------
*)

Lemma settle_reuses :
  forall post p, exists mid k, settle p post = (mid ++ skipn k post)%list.
Proof.
  induction post as [|c post IH]; intros p; cbn [settle].
  - destruct (is_idle (pend_state p));
      exists (close p), 0; rewrite ?app_nil_r; reflexivity.
  - destruct (is_idle (pend_state p)).
    + exists (close p), 0. reflexivity.
    + destruct (cut (piece_lines c) p) as [cs p'].
      destruct (IH p') as (mid & k & H).
      exists (cs ++ mid)%list, (S k). rewrite H, app_assoc. reflexivity.
Qed.

(** The pieces before the edit are kept, and the pieces after it from
    some point on. *)
Theorem replace_reuses :
  forall pre new post,
    exists mid k, replace pre new post = (pre ++ mid ++ skipn k post)%list.
Proof.
  intros pre new post. unfold replace. destruct (cut new fresh) as [cs p].
  destruct (settle_reuses post p) as (mid & k & H).
  exists (cs ++ mid)%list, k. rewrite H, <- app_assoc. reflexivity.
Qed.

(** New lines that leave the fold idle are the only ones parsed: the
    pieces after them are all kept. *)
Theorem replace_idle :
  forall pre new post,
    is_idle (pend_state (snd (cut new fresh))) = true ->
    replace pre new post = (pre ++ pieces new ++ post)%list.
Proof.
  intros pre new post Hidle. unfold replace, pieces.
  destruct (cut new fresh) as [cs p]. cbn [snd] in Hidle.
  destruct post as [|c post]; cbn [settle];
    rewrite Hidle; rewrite ?app_assoc, ?app_nil_r; reflexivity.
Qed.

End Cut.

(*
The two parses
==============
*)

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
Semantic
--------
*)

Definition sem_step (_ : nat) (l : string) (st : pstate) : blocks * pstate :=
  step l st.

Definition sem_pieces (ls : list string) : list piece :=
  pieces sem_step finish ls.

Lemma cut_parse :
  forall ls p,
    (pend_blocks p ++ parse_lines ls (pend_state p))%list
    = (pieces_tree (fst (cut sem_step ls p))
       ++ pend_blocks (snd (cut sem_step ls p))
       ++ finish (pend_state (snd (cut sem_step ls p))))%list.
Proof.
  induction ls as [|l rest IH]; intros p; [reflexivity|].
  cbn [cut parse_lines]. unfold sem_step.
  destruct (step l (pend_state p)) as [out st] eqn:Hs.
  destruct (is_idle st) eqn:Hi.
  - apply is_idle_true in Hi. subst st.
    pose proof (IH fresh) as H. cbn [pend_blocks pend_state fresh app] in H.
    fold sem_step in H |- *.
    destruct (cut sem_step rest fresh) as [cs p']. cbn [fst snd] in *.
    unfold pieces_tree in *. cbn [map concat piece_blocks].
    rewrite H, !app_assoc. reflexivity.
  - fold sem_step. rewrite app_assoc. apply (IH (Pending _ _ st _)).
Qed.

Theorem pieces_parse :
  forall ls, parse_lines ls (PPara []) = pieces_tree (sem_pieces ls).
Proof.
  intros ls. unfold sem_pieces, pieces. pose proof (cut_parse ls fresh) as H.
  pose proof (cut_shape sem_step ls fresh (or_introl eq_refl)) as Hs.
  destruct (cut sem_step ls fresh) as [cs p]. cbn [fst snd] in *.
  cbn [pend_blocks pend_state fresh app] in H. rewrite H, pieces_tree_app.
  f_equal. destruct Hs as [->|[Hne _]]; [reflexivity|].
  destruct p as [[|l lines] bs st n]; [contradiction|].
  unfold pieces_tree, close. cbn. rewrite app_nil_r. reflexivity.
Qed.

(** The edited lines parse to the spliced pieces' blocks. *)
Corollary splice_parse :
  forall ls i j new,
    let cs := sem_pieces ls in
    i <= j -> j <= length cs ->
    parse_lines (pieces_text (firstn i cs) ++ new ++ pieces_text (skipn j cs))
      (PPara [])
    = pieces_tree (splice sem_step finish cs i j new).
Proof.
  intros ls i j new cs Hij Hj. unfold cs, sem_pieces.
  rewrite (splice_pieces sem_step finish ls i j new Hij Hj), pieces_parse.
  reflexivity.
Qed.

(*
Located
-------
*)

(* The located step at a line's index within its piece. *)
Definition loc_step (k : nat) (l : string) (st : pstate) : blocks * pstate :=
  @step T K (LineIxAt k) located_pos l st.

Definition loc_pieces (ls : list string) : list piece :=
  pieces loc_step (@finish T K located_pos) ls.

(* Each piece's blocks with its positions moved to where its first line
   is. *)
Fixpoint assemble (off : nat) (cs : list piece) : blocks :=
  match cs with
  | [] => []
  | c :: rest =>
      (Shift.of_blocks off (piece_blocks c)
       ++ assemble (off + length (piece_lines c)) rest)%list
  end.

(** The located parse: piece by piece, each from the idle state with its
    lines numbered from 0, then shifted into place. *)
Definition parse_blocks_located (s : string) : blocks :=
  assemble 0 (loc_pieces (split_lines s)).

Lemma assemble_app :
  forall xs ys off,
    assemble off (xs ++ ys)
    = (assemble off xs ++ assemble (off + length (pieces_text xs)) ys)%list.
Proof.
  induction xs as [|x xs IH]; intros ys off.
  - cbn. rewrite Nat.add_0_r. reflexivity.
  - cbn [app assemble]. rewrite IH, app_assoc. unfold pieces_text.
    cbn [map concat]. rewrite length_app, Nat.add_assoc. reflexivity.
Qed.

Definition erase_piece (c : piece) : piece :=
  Piece (piece_lines c) (Erase.of_blocks (piece_blocks c)).

Definition erase_pending (p : pending) : pending :=
  Pending (pend_lines p) (Erase.of_blocks (pend_blocks p))
    (Step.StateErase.state (pend_state p)) (pend_count p).

Lemma cut_erase :
  forall ls p,
    (map erase_piece (fst (cut loc_step ls p)), erase_pending (snd (cut loc_step ls p)))
    = cut sem_step ls (erase_pending p).
Proof.
  induction ls as [|l rest IH]; intros p; [reflexivity|].
  cbn [cut].
  pose proof (@step_erase T K (LineIxAt (pend_count p)) l (pend_state p)) as Hs.
  unfold Step.StateErase.result in Hs.
  fold (loc_step (pend_count p) l (pend_state p)) in Hs.
  destruct (loc_step (pend_count p) l (pend_state p)) as [out st].
  cbn [erase_pending pend_count pend_state pend_lines pend_blocks].
  cbn [fst snd] in Hs. unfold sem_step at 1. rewrite <- Hs, is_idle_erase.
  destruct (is_idle st).
  - pose proof (IH fresh) as H. change (erase_pending fresh) with fresh in H.
    rewrite <- H. destruct (cut loc_step rest fresh) as [cs p']. cbn [fst snd map].
    unfold erase_piece at 1. cbn [piece_lines piece_blocks].
    rewrite Erase.blocks_app. reflexivity.
  - rewrite IH. unfold erase_pending. cbn [pend_lines pend_blocks pend_state pend_count].
    rewrite Erase.blocks_app. reflexivity.
Qed.

Lemma close_erase :
  forall p,
    map erase_piece (close (@finish T K located_pos) p)
    = close finish (erase_pending p).
Proof.
  intros [[|l lines] bs st n]; [reflexivity|].
  unfold close, erase_pending, erase_piece.
  cbn [pend_lines pend_blocks pend_state map piece_lines piece_blocks].
  rewrite Erase.blocks_app, finish_erase. reflexivity.
Qed.

Lemma loc_pieces_erase :
  forall ls, map erase_piece (loc_pieces ls) = sem_pieces ls.
Proof.
  intros ls. unfold loc_pieces, sem_pieces, pieces.
  pose proof (cut_erase ls fresh) as H.
  destruct (cut loc_step ls fresh) as [cs p]. cbn [fst snd] in H.
  change (erase_pending fresh) with fresh in H. rewrite <- H.
  rewrite map_app, close_erase. reflexivity.
Qed.

Lemma assemble_erase :
  forall cs off,
    Erase.of_blocks (assemble off cs) = pieces_tree (map erase_piece cs).
Proof.
  induction cs as [|c cs IH]; intros off; [reflexivity|].
  cbn [assemble map]. rewrite Erase.blocks_app, Shift.erase_blocks, IH.
  reflexivity.
Qed.

(** Erasing positions gives the semantic parse. *)
Theorem parse_blocks_located_erase :
  forall s, Erase.of_blocks (parse_blocks_located s)
            = @parse_blocks T K semantic_line_ix semantic_pos s.
Proof.
  intros s. unfold parse_blocks_located, parse_blocks.
  rewrite assemble_erase, loc_pieces_erase, pieces_parse. reflexivity.
Qed.

(** The located parse of edited lines, from the spliced pieces.  The
    pieces `replace_reuses` keeps carry their blocks unchanged, and
    `assemble` shifts them by their new offset (`assemble_app`). *)
Theorem splice_located :
  forall ls i j new s',
    let cs := loc_pieces ls in
    i <= j -> j <= length cs ->
    split_lines s'
      = (pieces_text (firstn i cs) ++ new ++ pieces_text (skipn j cs))%list ->
    parse_blocks_located s'
    = assemble 0 (splice loc_step (@finish T K located_pos) cs i j new).
Proof.
  intros ls i j new s' cs Hij Hj Hs. unfold parse_blocks_located, loc_pieces.
  rewrite Hs. f_equal. symmetry. apply splice_pieces; assumption.
Qed.

End WithTable.
