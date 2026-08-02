(* Well-formedness of the djot AST, as a decidable boolean predicate.

   This is the Phase 1 `wf_block` deliverable in its first (extrinsic)
   form: conditions the parser's output always satisfies and the renderer
   may rely on.  The conditions mirror the runtime predicates of the QCheck
   generator work (no empty paragraphs, no empty containers, no empty
   lists) plus a canonicality condition (no adjacent plain Str nodes) that
   djoths maintains via its Inlines Semigroup and that exact-equality
   roundtrip will need.

   The first theorem, `wf_parse`, proves the toy parser total *and*
   well-formed on every input.  It is stated over the full AST, so it only
   grows stronger as the parser gains constructs. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Ast Parser.
Import ListNotations.

Local Open Scope string_scope.

(*
Basic shape predicates
======================
*)

Definition nonempty {A : Type} (l : list A) : bool :=
  match l with [] => false | _ => true end.

Definition nonempty_str (s : string) : bool :=
  match s with EmptyString => false | _ => true end.

(* Canonicality: two adjacent attribute-less Str nodes should have been
   merged into one (djoths's Inlines Semigroup does this on append). *)

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
Auxiliary lemmas about the line functions
=========================================
*)

Lemma rev_aux_blank :
  forall s acc, is_blank (rev_string_aux s acc) = is_blank s && is_blank acc.
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

Lemma is_blank_cons :
  forall c s, is_blank (String c s) = is_ws c && is_blank s.
Proof. reflexivity. Qed.

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

Lemma nonempty_str_length :
  forall s, s <> EmptyString -> nonempty_str s = true.
Proof.
  destruct s; [congruence | reflexivity].
Qed.

Lemma strip_trailing_ws_nonempty :
  forall s, is_blank s = false -> nonempty_str (strip_trailing_ws s) = true.
Proof.
  intros s H. unfold strip_trailing_ws.
  apply nonempty_str_length.
  intros Hrev.
  assert (Hd : drop_leading_ws (rev_string s) <> EmptyString).
  { apply drop_leading_ws_nonempty. rewrite rev_blank. exact H. }
  apply Hd.
  apply (f_equal String.length) in Hrev.
  rewrite rev_length in Hrev. simpl in Hrev.
  destruct (drop_leading_ws (rev_string s)); [reflexivity | discriminate].
Qed.

Lemma nonblank_nonempty :
  forall s, is_blank s = false -> nonempty_str s = true.
Proof.
  destruct s; simpl; [congruence | reflexivity].
Qed.

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
The parser produces well-formed output
======================================
*)

Definition nonblank (l : string) : bool := negb (is_blank l).

(* Definitional equations, used instead of simpl/cbn to keep goals from
   over-reducing into nested matches. *)

Lemma para_inlines_one :
  forall x, para_inlines [x] = [mk (Str (strip_trailing_ws x))].
Proof. reflexivity. Qed.

Lemma para_inlines_cons2 :
  forall x y rest,
    para_inlines (x :: y :: rest) =
    mk (Str x) :: mk SoftBreak :: para_inlines (y :: rest).
Proof. reflexivity. Qed.

Lemma wf_inlines_cons :
  forall n ns,
    wf_inlines (n :: ns) =
    (wf_inline (node_contents n) && forallb (fun m => wf_inline (node_contents m)) ns
     && no_adjacent_str (n :: ns))%bool.
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

Lemma nonempty_app_singleton :
  forall {A : Type} (l : list A) (x : A), nonempty (l ++ [x]) = true.
Proof.
  intros A l x. destruct l; reflexivity.
Qed.

Lemma wf_blocks_para :
  forall ils rest,
    wf_blocks (mk (Para ils) :: rest) =
    (nonempty ils && wf_inlines ils && wf_blocks rest)%bool.
Proof. reflexivity. Qed.

Lemma group_paras_flush_wf :
  forall c cur' k,
    forallb nonblank (c :: cur') = true ->
    wf_blocks k = true ->
    wf_blocks (mk (Para (para_inlines (rev (c :: cur')))) :: k) = true.
Proof.
  intros c cur' k Hcur Hk.
  rewrite wf_blocks_para.
  rewrite para_inlines_wf by (rewrite forallb_rev; exact Hcur).
  rewrite Hk.
  rewrite para_inlines_nonempty; [reflexivity|].
  simpl rev. destruct (rev cur'); discriminate.
Qed.

Lemma group_paras_wf :
  forall lines cur,
    forallb nonblank cur = true ->
    wf_blocks (group_paras lines cur) = true.
Proof.
  induction lines as [|l rest IH]; intros cur Hcur.
  - (* end of input: flush *)
    destruct cur as [|c cur']; [reflexivity|].
    apply group_paras_flush_wf; [exact Hcur | reflexivity].
  - cbn [group_paras]. destruct (is_blank l) eqn:E.
    + (* blank line: flush, restart with empty accumulator *)
      destruct cur as [|c cur'].
      * apply IH. reflexivity.
      * apply group_paras_flush_wf; [exact Hcur |].
        apply IH. reflexivity.
    + (* nonblank line: accumulate *)
      apply IH. simpl. unfold nonblank. rewrite E. simpl. exact Hcur.
Qed.

Theorem wf_parse : forall s, wf_doc (parse_doc s) = true.
Proof.
  intros s. unfold wf_doc, parse_doc. simpl.
  rewrite andb_true_r.
  apply group_paras_wf. reflexivity.
Qed.
