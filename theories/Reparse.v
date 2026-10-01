(* ai-disclosure: ai-generated *)

(** * Reparsing after a replacement

   A document's lines, cut at every point where the fold is idle.  Each
   piece parses on its own, and the document's blocks are the pieces'
   blocks in order (`pieces_parse`).

   `splice` replaces any range of pieces with new lines.  It parses the
   new lines, then continues into the following pieces only until the
   fold is idle at the end of one, and keeps the rest unparsed
   (`splice_parse`, `replace_reuses`).  The result is the parse of the
   edited lines whatever the new lines are, so a caller needs no check
   and no fallback. *)

From Stdlib Require Import String List Bool PeanoNat Lia.
From DjotV Require Import Strings Ast InlineTable Inline Step Uniformity Document.
Import ListNotations.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

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

(* A piece the fold runs from idle to idle. *)
Definition closed (c : piece) : Prop :=
  run_lines (piece_lines c) (PPara []) = (piece_blocks c, PPara []).

(* The last piece may end anywhere; its blocks include what `finish`
   closes. *)
Definition finished (c : piece) : Prop :=
  parse_lines (piece_lines c) (PPara []) = piece_blocks c.

(* Every piece closed, except possibly the last. *)
Inductive pieces_ok : list piece -> Prop :=
  | CutNil : pieces_ok []
  | CutLast : forall c, finished c -> pieces_ok [c]
  | CutCons : forall c cs, closed c -> pieces_ok cs -> pieces_ok (c :: cs).

Lemma finish_idle : finish (PPara []) = [].
Proof. reflexivity. Qed.

Theorem pieces_ok_parse :
  forall cs, pieces_ok cs ->
    parse_lines (pieces_text cs) (PPara []) = pieces_tree cs.
Proof.
  intros cs H. induction H as [|c Hc|c cs Hc _ IH].
  - reflexivity.
  - unfold pieces_text, pieces_tree. cbn [map concat]. rewrite !app_nil_r.
    exact Hc.
  - unfold pieces_text, pieces_tree in *. cbn [map concat].
    rewrite parse_lines_app_run, Hc, IH. reflexivity.
Qed.

Lemma pieces_ok_app :
  forall xs ys, Forall closed xs -> pieces_ok ys -> pieces_ok (xs ++ ys).
Proof.
  intros xs ys Hx Hy. induction Hx as [|x xs Hx _ IH]; [exact Hy|].
  apply CutCons; assumption.
Qed.

(* Every piece but the last is followed by one, so it is closed. *)
Lemma pieces_ok_firstn :
  forall cs i, pieces_ok cs -> i < length cs -> Forall closed (firstn i cs).
Proof.
  intros cs i H. revert i. induction H as [|c Hc|c cs Hc Hcs IH]; intros i Hi.
  - cbn in Hi. lia.
  - destruct i; cbn in Hi |- *; [constructor|lia].
  - destruct i; cbn in Hi |- *; [constructor|].
    constructor; [exact Hc|apply IH; lia].
Qed.

Lemma pieces_ok_skipn :
  forall cs j, pieces_ok cs -> pieces_ok (skipn j cs).
Proof.
  intros cs j H. revert j. induction H as [|c Hc|c cs Hc Hcs IH]; intros j.
  - destruct j; constructor.
  - destruct j; cbn; [apply CutLast; exact Hc|destruct j; constructor].
  - destruct j; cbn; [apply CutCons; assumption|apply IH].
Qed.

Lemma pieces_text_app :
  forall xs ys, pieces_text (xs ++ ys) = (pieces_text xs ++ pieces_text ys)%list.
Proof.
  intros xs ys. unfold pieces_text. rewrite map_app, concat_app. reflexivity.
Qed.

(*
Cutting
=======
*)

(* The piece being read: its lines so far, last first, the blocks they
   emitted, and the fold's state. *)
Record pending : Type := Pending
  { pend_lines : list string
  ; pend_blocks : blocks
  ; pend_state : pstate }.

Definition fresh : pending := Pending [] [] (PPara []).

Definition pending_ok (p : pending) : Prop :=
  run_lines (rev (pend_lines p)) (PPara []) = (pend_blocks p, pend_state p).

(* Feed lines to the piece being read, emitting it each time the fold is
   idle. *)
Fixpoint cut (ls : list string) (p : pending) : list piece * pending :=
  match ls with
  | [] => ([], p)
  | l :: rest =>
      let (out, st) := step l (pend_state p) in
      let lines := l :: pend_lines p in
      let bs := (pend_blocks p ++ out)%list in
      if is_idle st
      then let (cs, p') := cut rest fresh in (Piece (rev lines) bs :: cs, p')
      else cut rest (Pending lines bs st)
  end.

(* End of input: the piece being read, if it has lines, is the last. *)
Definition close (p : pending) : list piece :=
  match pend_lines p with
  | [] => []
  | _ => [Piece (rev (pend_lines p)) (pend_blocks p ++ finish (pend_state p))]
  end.

Definition pieces (ls : list string) : list piece :=
  let (cs, p) := cut ls fresh in (cs ++ close p)%list.

Lemma fresh_ok : pending_ok fresh.
Proof. reflexivity. Qed.

Lemma is_idle_true : forall st, is_idle st = true -> st = PPara [].
Proof.
  intros [[|c cur]| | | | | | | | | | | |]; cbn; congruence.
Qed.

Lemma pending_ok_push :
  forall p l out st,
    pending_ok p -> step l (pend_state p) = (out, st) ->
    run_lines (rev (l :: pend_lines p)) (PPara [])
    = ((pend_blocks p ++ out)%list, st).
Proof.
  intros p l out st Hp Hs. cbn [rev].
  apply (run_lines_continue _ _ _ _ _ _ _ Hp).
  cbn [run_lines]. rewrite Hs. cbn [run_lines]. rewrite app_nil_r. reflexivity.
Qed.

Lemma cut_spec :
  forall ls p, pending_ok p ->
    Forall closed (fst (cut ls p))
    /\ pending_ok (snd (cut ls p))
    /\ (pieces_text (fst (cut ls p)) ++ rev (pend_lines (snd (cut ls p))))%list
       = (rev (pend_lines p) ++ ls)%list.
Proof.
  induction ls as [|l rest IH]; intros p Hp.
  - cbn. rewrite app_nil_r. auto.
  - cbn [cut]. destruct (step l (pend_state p)) as [out st] eqn:Hs.
    pose proof (pending_ok_push p l out st Hp Hs) as Hrun.
    destruct (is_idle st) eqn:Hi.
    + apply is_idle_true in Hi. subst st.
      destruct (IH fresh fresh_ok) as (Hcl & Hok & Htext).
      destruct (cut rest fresh) as [cs p'] eqn:Hc. cbn [fst snd] in *.
      split; [constructor; [exact Hrun|exact Hcl]|split; [exact Hok|]].
      unfold pieces_text in *. cbn [map concat]. rewrite <- app_assoc, Htext.
      cbn. rewrite <- app_assoc. reflexivity.
    + destruct (IH (Pending (l :: pend_lines p) (pend_blocks p ++ out) st) Hrun)
        as (Hcl & Hok & Htext).
      split; [exact Hcl|split; [exact Hok|]].
      rewrite Htext. cbn [pend_lines rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma close_ok : forall p, pending_ok p -> pieces_ok (close p).
Proof.
  intros [lines bs st] Hp. unfold close, pending_ok in *. cbn [pend_lines] in *.
  destruct lines as [|l lines]; [constructor|].
  apply CutLast. unfold finished. cbn [piece_lines piece_blocks].
  exact (parse_lines_run _ _ _ _ Hp).
Qed.

Lemma close_text :
  forall p, pending_ok p -> pieces_text (close p) = rev (pend_lines p).
Proof.
  intros [[|l lines] bs st] Hp; [reflexivity|].
  unfold pieces_text, close. cbn [map concat pend_lines piece_lines].
  rewrite app_nil_r. reflexivity.
Qed.

Theorem pieces_spec :
  forall ls, pieces_ok (pieces ls) /\ pieces_text (pieces ls) = ls.
Proof.
  intros ls. unfold pieces.
  destruct (cut_spec ls fresh fresh_ok) as (Hcl & Hok & Htext).
  destruct (cut ls fresh) as [cs p]. cbn [fst snd] in *.
  split; [apply pieces_ok_app; [exact Hcl|apply close_ok, Hok]|].
  rewrite pieces_text_app, close_text by exact Hok. exact Htext.
Qed.

Corollary pieces_parse :
  forall ls, parse_lines ls (PPara []) = pieces_tree (pieces ls).
Proof.
  intros ls. destruct (pieces_spec ls) as [Hc Ht].
  rewrite <- (pieces_ok_parse _ Hc), Ht. reflexivity.
Qed.

(*
Replacing
=========
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

(* `new` in place of whatever lay between `pre` and `post`.  `pre` must
   end idle. *)
Definition replace (pre : list piece) (new : list string) (post : list piece)
  : list piece :=
  let (cs, p) := cut new fresh in (pre ++ cs ++ settle p post)%list.

(* `new` in place of pieces `i` to `j - 1`.  An edit that reaches the end
   also reparses the last piece before it, since that one may not end
   idle. *)
Definition splice (cs : list piece) (i j : nat) (new : list string)
  : list piece :=
  match skipn j cs, i with
  | [], S i' => replace (firstn i' cs)
                  (pieces_text (firstn 1 (skipn i' cs)) ++ new)%list []
  | post, _ => replace (firstn i cs) new post
  end.

Lemma close_closed :
  forall p, pending_ok p -> is_idle (pend_state p) = true -> Forall closed (close p).
Proof.
  intros [[|l lines] bs st] Hp Hi; [constructor|].
  cbn [pend_state] in Hi. apply is_idle_true in Hi. subst st.
  unfold close, closed, pending_ok in *. cbn [pend_lines pend_blocks pend_state] in *.
  constructor; [|constructor]. cbn [piece_lines piece_blocks].
  rewrite finish_idle, app_nil_r. exact Hp.
Qed.

Lemma settle_spec :
  forall post p, pending_ok p -> pieces_ok post ->
    pieces_ok (settle p post)
    /\ pieces_text (settle p post) = (rev (pend_lines p) ++ pieces_text post)%list.
Proof.
  induction post as [|c post IH]; intros p Hp Hpost; cbn [settle].
  - destruct (is_idle (pend_state p)); rewrite ?app_nil_r;
      (split; [apply close_ok, Hp|rewrite close_text by exact Hp;
               reflexivity]).
  - destruct (is_idle (pend_state p)) eqn:Hi.
    + split; [apply pieces_ok_app; [apply close_closed; assumption|exact Hpost]|].
      rewrite pieces_text_app, close_text by exact Hp. reflexivity.
    + destruct (cut_spec (piece_lines c) p Hp) as (Hcl & Hok & Htext).
      destruct (cut (piece_lines c) p) as [cs p']. cbn [fst snd] in *.
      assert (Hrest : pieces_ok post)
        by (inversion Hpost; subst; [constructor|assumption]).
      destruct (IH p' Hok Hrest) as [Hc' Ht'].
      split; [apply pieces_ok_app; assumption|].
      rewrite pieces_text_app, Ht', app_assoc, Htext.
      unfold pieces_text. cbn [map concat]. rewrite app_assoc. reflexivity.
Qed.

Theorem replace_spec :
  forall pre new post,
    Forall closed pre -> pieces_ok post ->
    pieces_ok (replace pre new post)
    /\ pieces_text (replace pre new post)
       = (pieces_text pre ++ new ++ pieces_text post)%list.
Proof.
  intros pre new post Hpre Hpost. unfold replace.
  destruct (cut_spec new fresh fresh_ok) as (Hcl & Hok & Htext).
  destruct (cut new fresh) as [cs p]. cbn [fst snd] in *.
  destruct (settle_spec post p Hok Hpost) as [Hc Ht].
  split; [apply pieces_ok_app; [exact Hpre|apply pieces_ok_app; assumption]|].
  cbn [pend_lines fresh rev app] in Htext.
  rewrite !pieces_text_app, Ht, <- Htext, !app_assoc. reflexivity.
Qed.

Theorem splice_spec :
  forall cs i j new,
    pieces_ok cs -> i <= j -> j <= length cs ->
    pieces_ok (splice cs i j new)
    /\ pieces_text (splice cs i j new)
       = (pieces_text (firstn i cs) ++ new ++ pieces_text (skipn j cs))%list.
Proof.
  intros cs i j new Hcs Hij Hj. unfold splice.
  destruct (skipn j cs) as [|c post] eqn:Hpost.
  - destruct i as [|i'].
    + apply replace_spec; [constructor|constructor].
    + destruct (replace_spec (firstn i' cs)
                  (pieces_text (firstn 1 (skipn i' cs)) ++ new) []
                  (pieces_ok_firstn cs i' Hcs ltac:(lia)) CutNil) as [Hc Ht].
      split; [exact Hc|]. rewrite Ht, !app_assoc, <- pieces_text_app.
      replace (S i') with (i' + 1) by lia. rewrite firstn_skipn_comm.
      replace (firstn i' cs) with (firstn i' (firstn (i' + 1) cs))
        by (rewrite firstn_firstn; f_equal; lia).
      rewrite firstn_skipn. reflexivity.
  - assert (Hi : i < length cs).
    { destruct (Nat.lt_ge_cases j (length cs)) as [Hlt|Hge]; [lia|].
      rewrite skipn_all2 in Hpost by exact Hge. discriminate. }
    rewrite <- Hpost.
    apply replace_spec;
      [apply pieces_ok_firstn; assumption|apply pieces_ok_skipn; exact Hcs].
Qed.

(** The edited lines parse to the spliced pieces' blocks. *)
Corollary splice_parse :
  forall cs i j new,
    pieces_ok cs -> i <= j -> j <= length cs ->
    parse_lines (pieces_text (firstn i cs) ++ new ++ pieces_text (skipn j cs))
      (PPara [])
    = pieces_tree (splice cs i j new).
Proof.
  intros cs i j new Hcs Hij Hj.
  destruct (splice_spec cs i j new Hcs Hij Hj) as [Hc Ht].
  rewrite <- Ht. apply pieces_ok_parse, Hc.
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

Lemma cut_state :
  forall ls p, pend_state (snd (cut ls p)) = snd (run_lines ls (pend_state p)).
Proof.
  induction ls as [|l rest IH]; intros p; [reflexivity|].
  cbn [cut run_lines]. destruct (step l (pend_state p)) as [out st] eqn:Hs.
  destruct (is_idle st) eqn:Hi.
  - apply is_idle_true in Hi. subst st.
    destruct (cut rest fresh) as [cs p'] eqn:Hc.
    pose proof (IH fresh) as H. rewrite Hc in H. cbn [snd] in *.
    rewrite H. cbn [pend_state fresh].
    destruct (run_lines rest (PPara [])). reflexivity.
  - rewrite IH. cbn [pend_state]. destruct (run_lines rest st). reflexivity.
Qed.

(** New lines that leave the fold idle are the only ones parsed: the
    pieces after them are all kept. *)
Theorem replace_idle :
  forall pre new post,
    snd (run_lines new (PPara [])) = PPara [] ->
    replace pre new post = (pre ++ pieces new ++ post)%list.
Proof.
  intros pre new post Hidle. unfold replace, pieces.
  pose proof (cut_state new fresh) as Hst. cbn [pend_state fresh] in Hst.
  destruct (cut new fresh) as [cs p]. cbn [snd] in Hst.
  destruct post as [|c post]; cbn [settle];
    rewrite Hst, Hidle; cbn [is_idle]; rewrite ?app_assoc; reflexivity.
Qed.

(*
The document pass
=================

`parse_doc` is `doc_pass` over the block parse, so a spliced document is
the pass over the spliced pieces.  The pass reads the whole block list,
and the examples after this section show what an edit changes through
it outside the edited lines.
*)

Theorem parse_doc_pieces :
  forall s, @parse_doc T K semantic_pos s
            = doc_pass (pieces_tree (pieces (split_lines s))).
Proof.
  intros s. unfold parse_doc, parse_blocks. rewrite pieces_parse. reflexivity.
Qed.

Corollary parse_doc_splice :
  forall cs i j new s,
    pieces_ok cs -> i <= j -> j <= length cs ->
    split_lines s
      = (pieces_text (firstn i cs) ++ new ++ pieces_text (skipn j cs))%list ->
    @parse_doc T K semantic_pos s = doc_pass (pieces_tree (splice cs i j new)).
Proof.
  intros cs i j new s Hcs Hij Hj Hs. unfold parse_doc, parse_blocks.
  rewrite Hs. f_equal. apply splice_parse; assumption.
Qed.

End WithTable.

(*
What the pass changes outside an edit
-------------------------------------

Each pair below differs only in its first block.
*)

Local Open Scope string_scope.

(* An id taken before a heading renumbers that heading's auto id. *)
Example pass_renumbers_id :
  nth_error (doc_blocks (parse_doc "x

# a")) 1
  = Some (Node NoPos [("id", "a")]
            (Section [Node NoPos [] (Heading 1 [Node NoPos [] (Str "a")])]))
  /\ nth_error (doc_blocks (parse_doc "{#a}
x

# a")) 1
  = Some (Node NoPos [("id", "a-1")]
            (Section [Node NoPos [] (Heading 1 [Node NoPos [] (Str "a")])])).
Proof. split; vm_compute; reflexivity. Qed.

(* A heading moves the blocks after it into its section. *)
Example pass_moves_sections :
  length (doc_blocks (parse_doc "# a

x

y")) = 1
  /\ length (doc_blocks (parse_doc "# a

# b

y")) = 2.
Proof. split; vm_compute; reflexivity. Qed.

(* A reference definition changes the table a link elsewhere resolves
   against, not the link. *)
Example pass_reference_table :
  hd_error (doc_blocks (parse_doc "[t][r]

x"))
  = hd_error (doc_blocks (parse_doc "[t][r]

[r]: u"))
  /\ doc_references (parse_doc "[t][r]

x") = []
  /\ doc_references (parse_doc "[t][r]

[r]: u") = [("r", ("u", []))].
Proof. repeat split; vm_compute; reflexivity. Qed.

(* Likewise a footnote definition and the note map. *)
Example pass_note_map :
  hd_error (doc_blocks (parse_doc "a[^n]

x"))
  = hd_error (doc_blocks (parse_doc "a[^n]

[^n]: x"))
  /\ doc_footnotes (parse_doc "a[^n]

x") = []
  /\ doc_footnotes (parse_doc "a[^n]

[^n]: x")
     = [("n", [Node NoPos [] (Para [Node NoPos [] (Str "x")])])].
Proof. repeat split; vm_compute; reflexivity. Qed.
