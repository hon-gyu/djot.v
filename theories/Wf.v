(* Well-formedness of the djot AST, as a decidable boolean predicate,
   plus the theorem that the parser only produces well-formed output.

   Conditions mirror the QCheck generator predicates (no empty
   paragraphs, no empty containers, no empty lists) plus a canonicality
   condition (no adjacent plain Str nodes) that exact-equality roundtrip
   needs. *)

From Stdlib Require Import String Ascii List Bool PeanoNat.
From DjotV Require Import Strings Line Ast Parser.
Import ListNotations.

Local Open Scope string_scope.

(*
Canonicality of inline sequences
================================

Two adjacent attribute-less Str nodes should have been merged into one
(djoths's Inlines Semigroup does this on append). *)

Definition plain_str (n : node inline) : bool :=
  match n with Node _ [] (Str _) => true | _ => false end.

Fixpoint no_adjacent_str (ns : list (node inline)) : bool :=
  match ns with
  | n1 :: ((n2 :: _) as rest) =>
      negb (plain_str n1 && plain_str n2) && no_adjacent_str rest
  | _ => true
  end.

(*
Inline well-formedness
======================
*)

Fixpoint wf_inline (il : inline) : bool :=
  let wf_ils :=
    fix go (ns : list (node inline)) : bool :=
      match ns with
      | [] => true
      | Node _ _ x :: rest => wf_inline x && go rest
      end in
  let wf_container :=
    fun ns => nonempty ns && wf_ils ns && no_adjacent_str ns in
  match il with
  | Str s => nonempty_str s
  | Emph ns | Strong ns | Highlight ns | Insert ns | Delete ns
  | Superscript ns | Subscript ns | Span ns | Quoted _ ns =>
      wf_container ns
  | Link ns _ | Image ns _ =>
      (* link/image text may be empty: [](url) is valid djot *)
      wf_ils ns && no_adjacent_str ns
  | _ => true
  end.

Definition wf_inlines (ns : inlines) : bool :=
  forallb (fun n => wf_inline (node_contents n)) ns && no_adjacent_str ns.

(*
Block well-formedness
=====================
*)

Fixpoint wf_block (b : block) : bool :=
  let wf_bs :=
    fix go (ns : list (node block)) : bool :=
      match ns with
      | [] => true
      | Node _ _ x :: rest => wf_block x && go rest
      end in
  let wf_items :=
    fix goi (its : list (list (node block))) : bool :=
      match its with
      | [] => true
      | it :: rest => nonempty it && wf_bs it && goi rest
      end in
  let wf_task_items :=
    fix got (its : list (task_status * list (node block))) : bool :=
      match its with
      | [] => true
      | (_, it) :: rest => nonempty it && wf_bs it && got rest
      end in
  let wf_def_items :=
    fix god (its : list (inlines * list (node block))) : bool :=
      match its with
      | [] => true
      | (term, it) :: rest => wf_inlines term && wf_bs it && god rest
      end in
  match b with
  | Para ils => nonempty ils && wf_inlines ils
  | Section bs | BlockQuote bs | Div bs => nonempty bs && wf_bs bs
  | Heading level ils => Nat.leb 1 level && wf_inlines ils
  | CodeBlock _ _ => true
  | OrderedList _ _ items => nonempty items && wf_items items
  | BulletList _ items => nonempty items && wf_items items
  | TaskList _ items => nonempty items && wf_task_items items
  | DefinitionList _ items => nonempty items && wf_def_items items
  | ThematicBreak => true
  | Table caption rows =>
      match caption with Some bs => nonempty bs && wf_bs bs | None => true end
      && forallb
           (fun row =>
              forallb (fun c => match c with Cell _ _ ils => wf_inlines ils end)
                row)
           rows
  | RawBlock _ _ => true
  end.

Definition wf_blocks (bs : blocks) : bool :=
  forallb (fun n => wf_block (node_contents n)) bs.

Definition wf_doc (d : doc) : bool :=
  wf_blocks (doc_blocks d)
  && forallb (fun p => wf_blocks (snd p)) (doc_footnotes d).

(*
Equation lemmas
===============
*)

Lemma wf_inlines_cons :
  forall n ns,
    wf_inlines (n :: ns) =
    (wf_inline (node_contents n)
     && forallb (fun m => wf_inline (node_contents m)) ns
     && no_adjacent_str (n :: ns))%bool.
Proof. reflexivity. Qed.

Lemma wf_blocks_cons :
  forall n bs,
    wf_blocks (n :: bs) = (wf_block (node_contents n) && wf_blocks bs)%bool.
Proof. reflexivity. Qed.

Lemma no_adjacent_cons_false :
  forall n ns,
    plain_str n = false -> no_adjacent_str ns = true ->
    no_adjacent_str (n :: ns) = true.
Proof.
  intros n ns H Hns. destruct ns as [|m ns']; simpl.
  - reflexivity.
  - simpl in Hns. rewrite H. simpl. exact Hns.
Qed.

Lemma no_adjacent_cons2 :
  forall n1 n2 ns,
    plain_str n2 = false -> no_adjacent_str (n2 :: ns) = true ->
    no_adjacent_str (n1 :: n2 :: ns) = true.
Proof.
  intros n1 n2 ns H Hns. simpl. rewrite H, andb_false_r. simpl.
  simpl in Hns. rewrite H in Hns. simpl in Hns.
  destruct ns as [|n3 ns']; [reflexivity | exact Hns].
Qed.

(*
Paragraph assembly is well-formed
=================================
*)

Lemma para_inlines_nonempty :
  forall ls, ls <> [] -> nonempty (para_inlines ls) = true.
Proof.
  intros ls H. destruct ls as [|x [|y r]]; [congruence | reflexivity | reflexivity].
Qed.

Lemma para_inlines_wf :
  forall ls, forallb nonblank ls = true ->
  wf_inlines (para_inlines ls) = true.
Proof.
  induction ls as [|x rest IH]; intros H; simpl in H.
  - reflexivity.
  - apply andb_true_iff in H as [Hx Hrest].
    unfold nonblank in Hx. apply negb_true_iff in Hx.
    destruct rest as [|y rest'].
    + (* single line: one stripped Str *)
      rewrite para_inlines_one, wf_inlines_cons. simpl.
      rewrite (strip_trailing_ws_nonempty _ Hx). reflexivity.
    + (* x, then SoftBreak, then the rest *)
      specialize (IH Hrest).
      unfold wf_inlines in IH. apply andb_true_iff in IH as [IHwf IHadj].
      rewrite para_inlines_cons2.
      unfold wf_inlines. apply andb_true_iff. split.
      * simpl. rewrite (nonblank_nonempty _ Hx). simpl. exact IHwf.
      * apply no_adjacent_cons2; [reflexivity|].
        apply no_adjacent_cons_false; [reflexivity|]. exact IHadj.
Qed.

Lemma flush_para_wf :
  forall c cur' k,
    forallb nonblank (c :: cur') = true ->
    wf_blocks k = true ->
    wf_blocks (mk (Para (para_inlines (rev (c :: cur')))) :: k) = true.
Proof.
  intros c cur' k Hcur Hk.
  rewrite wf_blocks_cons. cbn [node_contents mk wf_block].
  rewrite para_inlines_wf by (rewrite forallb_rev; exact Hcur).
  rewrite Hk.
  rewrite para_inlines_nonempty; [reflexivity|].
  simpl rev. destruct (rev cur'); discriminate.
Qed.

(*
The parser produces well-formed output
======================================
*)

(* Fenced blocks are always well-formed, whatever the info and content. *)
Lemma fence_block_wf :
  forall f content, wf_block (node_contents (fence_block f content)) = true.
Proof.
  intros f content. unfold fence_block.
  destruct (f_info f) as [|c info]; [reflexivity|].
  destruct (Ascii.eqb c "=")%char eqn:E.
  - apply Ascii.eqb_eq in E. subst c. reflexivity.
  - (* CodeBlock branch: the match on c is a 256-way character match;
       wf_block is true for both CodeBlock and RawBlock, so conversion
       closes it after destructing c's bits *)
    destruct c as [[|] [|] [|] [|] [|] [|] [|] [|]]; reflexivity.
Qed.

Definition state_wf (st : pstate) : bool :=
  match st with
  | PPara cur => forallb nonblank cur
  | PFence _ _ => true
  end.

Lemma parse_lines_wf :
  forall lines st,
    state_wf st = true ->
    wf_blocks (parse_lines lines st) = true.
Proof.
  induction lines as [|l rest IH]; intros st Hst.
  - destruct st as [cur|f acc].
    + destruct cur as [|c cur']; [reflexivity|].
      rewrite parse_lines_nil_cons.
      apply flush_para_wf; [exact Hst | reflexivity].
    + rewrite parse_lines_fence_eof.
      rewrite wf_blocks_cons, fence_block_wf. reflexivity.
  - destruct st as [cur|f acc].
    + destruct (classify l) eqn:E.
      * (* blank: flush *)
        destruct cur as [|c cur'].
        -- rewrite parse_lines_blank_nil by exact E. apply IH. reflexivity.
        -- rewrite parse_lines_blank_cons by exact E.
           apply flush_para_wf; [exact Hst |].
           apply IH. reflexivity.
      * (* thematic: new block, or paragraph continuation *)
        destruct cur as [|c cur'].
        -- rewrite parse_lines_thematic_nil by exact E.
           rewrite wf_blocks_cons. simpl. apply IH. reflexivity.
        -- rewrite parse_lines_cont by (rewrite E; discriminate).
           apply IH.
           assert (Hl : is_blank l = false)
             by (apply classify_not_kblank_nonblank; rewrite E; discriminate).
           simpl. unfold nonblank. rewrite Hl. simpl. exact Hst.
      * (* fence open, or paragraph continuation *)
        destruct cur as [|c cur'].
        -- rewrite (parse_lines_fence_open _ _ _ E).
           apply IH. reflexivity.
        -- rewrite parse_lines_cont by (rewrite E; discriminate).
           apply IH.
           assert (Hl : is_blank l = false)
             by (apply classify_not_kblank_nonblank; rewrite E; discriminate).
           simpl. unfold nonblank. rewrite Hl. simpl. exact Hst.
      * (* text: accumulate *)
        rewrite parse_lines_text by exact E.
        apply IH.
        assert (Hl : is_blank l = false)
          by (apply classify_not_kblank_nonblank; rewrite E; discriminate).
        simpl. unfold nonblank. rewrite Hl. simpl. exact Hst.
    + destruct (fence_close f l) eqn:E.
      * rewrite parse_lines_fence_close by exact E.
        rewrite wf_blocks_cons, fence_block_wf.
        apply IH. reflexivity.
      * rewrite parse_lines_fence_content by exact E.
        apply IH. reflexivity.
Qed.

Theorem wf_parse : forall s, wf_doc (parse_doc s) = true.
Proof.
  intros s. unfold wf_doc, parse_doc. simpl.
  rewrite andb_true_r.
  apply parse_lines_wf. reflexivity.
Qed.
