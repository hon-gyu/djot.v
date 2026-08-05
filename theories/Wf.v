(* Well-formedness of the djot AST, as a decidable boolean predicate,
   plus the theorem that the parser only produces well-formed output.

   Two kinds of condition:
   - Structural: no empty containers, no empty containers, no empty lists
     - record what the parser can emit
   - Canonicality: _
*)

From Stdlib Require Import String Ascii List Bool PeanoNat.
From DjotV Require Import Strings Line Ast Parser.
Import ListNotations.

Local Open Scope string_scope.

(*
Canonicality of inline sequences
================================

Two adjacent attribute-less Str nodes should have been merged into one
(djoths's Inlines Semigroup does this on append). *)

(* An attribute-less Str node — the kind that would have been merged
   with a neighbour.  A Str *with* attributes is a distinct node. *)
Definition plain_str (n : node inline) : bool :=
  match n with Node _ [] (Str _) => true | _ => false end.

(* No two plain Str nodes sit next to each other. *)
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

(* Well-formedness of one inline.  The inner fixpoints are inlined by
   hand because `inline` is nested through `list (node _)`, which Rocq's
   guard checker will not accept as a plain mutual recursion. *)
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

(* Well-formedness of one block; same hand-inlined-fixpoint shape as
   wf_inline, one helper per container flavour.  A new block construct
   gets its case in the final match. *)
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
  | Section bs | Div bs => nonempty bs && wf_bs bs
  (* A block quote may be empty: a bare ">" line is a valid, contentless
     quote (djot.js emits <blockquote></blockquote> for it), so this is
     the one container without a nonempty obligation. *)
  | BlockQuote bs => wf_bs bs
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

(* The top-level predicate: body and footnote bodies are well-formed.
   (Reference maps carry no blocks, so nothing to check there.) *)
Definition wf_doc (d : doc) : bool :=
  wf_blocks (doc_blocks d) && 
  forallb (fun p : string * blocks => wf_blocks (snd p)) (doc_footnotes d).

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

(* wf_block's hand-inlined block-list fixpoint is wf_blocks.  Stated for
   the one container that carries no side condition, so the equation is
   an identity rather than an implication. *)
Lemma wf_block_quote :
  forall bs, wf_block (BlockQuote bs) = wf_blocks bs.
Proof.
  induction bs as [|n bs IH]; [reflexivity|].
  destruct n as [p a x].
  change (wf_block (BlockQuote (Node p a x :: bs)))
    with (wf_block x && wf_block (BlockQuote bs))%bool.
  rewrite IH. reflexivity.
Qed.

Lemma wf_blocks_app :
  forall bs1 bs2,
    wf_blocks (bs1 ++ bs2)%list = (wf_blocks bs1 && wf_blocks bs2)%bool.
Proof. intros bs1 bs2. unfold wf_blocks. apply forallb_app. Qed.

Lemma wf_blocks_rev :
  forall bs, wf_blocks (rev bs) = wf_blocks bs.
Proof. intros bs. unfold wf_blocks. apply forallb_rev. Qed.

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

(* The fold's invariant: an open paragraph only ever holds nonblank
   lines (a blank line flushes it), which is what makes the emitted Para
   well-formed; a quote's already-closed blocks are well-formed, and so
   is its contents' state, recursively.  A fence accumulator needs no
   invariant — its content is verbatim and CodeBlock/RawBlock are
   unconditionally well-formed. *)
Fixpoint state_wf (st : pstate) : bool :=
  match st with
  | PPara cur => forallb nonblank cur
  | PFence _ _ => true
  | PQuote done inner => wf_blocks done && state_wf inner
  end.

(* Closing the stack at end of input preserves the invariant. *)
Lemma finish_wf :
  forall st, state_wf st = true -> wf_blocks (finish st) = true.
Proof.
  induction st as [cur|f acc|done inner IH]; intros H.
  - destruct cur as [|c cur']; [reflexivity|].
    cbn [finish]. apply flush_para_wf; [exact H | reflexivity].
  - cbn [finish]. rewrite wf_blocks_cons, fence_block_wf. reflexivity.
  - cbn [state_wf] in H. apply andb_true_iff in H as [Hd Hi].
    cbn [finish]. rewrite wf_blocks_cons. cbn [node_contents mk].
    rewrite wf_block_quote, wf_blocks_app, wf_blocks_rev, Hd, (IH Hi).
    reflexivity.
Qed.

(* Pushing a nonblank line onto a paragraph accumulator is invisible to
   the invariant.  Stated as a lemma because `unfold nonblank` under
   forallb's function argument leaves nothing to rewrite. *)
Lemma forallb_nonblank_cons :
  forall l cur,
    is_blank l = false ->
    forallb nonblank (l :: cur) = forallb nonblank cur.
Proof.
  intros l cur H. cbn [forallb]. unfold nonblank. rewrite H. reflexivity.
Qed.

(* The line a KText classification describes is nonblank. *)
Lemma classify_ktext_nonblank :
  forall l, classify l = KText -> is_blank l = false.
Proof.
  intros l H. apply classify_not_kblank_nonblank. rewrite H. discriminate.
Qed.

(* A lazy line joins the innermost paragraph; nonblank is all that
   paragraph accumulator needs. *)
Lemma feed_lazy_wf :
  forall l st,
    is_blank l = false -> state_wf st = true ->
    state_wf (feed_lazy l st) = true.
Proof.
  induction st as [cur|f acc|done inner IH]; intros Hl H.
  - cbn [feed_lazy state_wf] in *. rewrite forallb_nonblank_cons by exact Hl.
    exact H.
  - reflexivity.
  - cbn [feed_lazy state_wf] in *. apply andb_true_iff in H as [Hd Hi].
    rewrite Hd, (IH Hl Hi). reflexivity.
Qed.

(* Opening a block from an idle state. *)
Lemma open_kind_wf :
  forall l k,
    classify l = k ->
    wf_blocks (fst (open_kind l k)) = true
    /\ state_wf (snd (open_kind l k)) = true.
Proof.
  intros l k H. destruct k; cbn [open_kind fst snd]; try (split; reflexivity).
  (* KText: the accumulator gains one line, which must be nonblank *)
  split; [reflexivity|].
  cbn [state_wf].
  rewrite forallb_nonblank_cons by (apply classify_ktext_nonblank; exact H).
  reflexivity.
Qed.

(* One transition preserves the invariant and emits only well-formed
   blocks.  Proved on fuel, since that is what `step` recurses on. *)
Lemma step_fuel_wf :
  forall n l st,
    state_wf st = true ->
    wf_blocks (fst (step_fuel n l st)) = true
    /\ state_wf (snd (step_fuel n l st)) = true.
Proof.
  induction n as [|n IH]; intros l st H; [split; [reflexivity | exact H]|].
  cbn [step_fuel].
  destruct st as [cur|f acc|done inner].
  - (* idle, or an open paragraph *)
    destruct cur as [|c cur'].
    + destruct (classify l) as [| |g|rest|] eqn:E;
        try (apply open_kind_wf; exact E).
      (* KQuote: descend into the enclosed line *)
      destruct (IH rest (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n rest (PPara [])) as [bs inner].
      cbn [fst snd] in Hb, Hs |- *.
      split; [reflexivity|].
      cbn [state_wf]. rewrite wf_blocks_rev, Hb. exact Hs.
    + destruct (classify l) as [| |g|rest|] eqn:E; cbn [fst snd].
      1: (split; [| reflexivity];
          apply flush_para_wf; [exact H | reflexivity]).
      all: split; [reflexivity|];
           cbn [state_wf];
           rewrite forallb_nonblank_cons
             by (apply classify_not_kblank_nonblank; rewrite E; discriminate);
           exact H.
  - (* inside a fence: only the close test *)
    destruct (fence_close f l); cbn [fst snd].
    + rewrite wf_blocks_cons, fence_block_wf. split; reflexivity.
    + split; reflexivity.
  - (* inside a quote *)
    pose proof H as H0. cbn [state_wf] in H0.
    apply andb_true_iff in H0 as [Hd Hi].
    assert (Hbq : wf_block (BlockQuote (rev done ++ finish inner)%list) = true).
    { rewrite wf_block_quote, wf_blocks_app, wf_blocks_rev, Hd, (finish_wf _ Hi).
      reflexivity. }
    destruct (classify l) as [| |g|rest|] eqn:E.
    4: { (* quote prefix: descend into the enclosed line *)
      destruct (IH rest inner Hi) as [Hb Hs].
      destruct (step_fuel n rest inner) as [bs inner'].
      cbn [fst snd] in Hb, Hs |- *.
      split; [reflexivity|].
      cbn [state_wf]. rewrite wf_blocks_app, wf_blocks_rev, Hb, Hd. exact Hs. }
    4: { (* text without the prefix: lazy continuation, or close *)
      cbn [is_lazy]. destruct (lazy_ok inner) eqn:El; cbn [open_kind fst snd].
      - split; [reflexivity|].
        cbn [state_wf]. rewrite Hd. cbn [andb].
        apply feed_lazy_wf;
          [apply classify_ktext_nonblank; exact E | exact Hi].
      - split.
        + rewrite wf_blocks_cons. cbn [node_contents mk]. rewrite Hbq.
          cbn [andb]. reflexivity.
        + cbn [state_wf].
          rewrite forallb_nonblank_cons
            by (apply classify_ktext_nonblank; exact E).
          reflexivity. }
    (* every other kind closes the quote and reopens outside it *)
    all: cbn [is_lazy open_kind fst snd]; split;
         [ rewrite wf_blocks_cons; cbn [node_contents mk]; rewrite Hbq;
           cbn [andb]; reflexivity
         | reflexivity ].
Qed.

Lemma step_wf :
  forall l st,
    state_wf st = true ->
    wf_blocks (fst (step l st)) = true /\ state_wf (snd (step l st)) = true.
Proof. intros l st H. apply step_fuel_wf. exact H. Qed.

Lemma parse_lines_wf :
  forall lines st,
    state_wf st = true ->
    wf_blocks (parse_lines lines st) = true.
Proof.
  induction lines as [|l rest IH]; intros st Hst.
  - apply finish_wf. exact Hst.
  - destruct (step_wf l st Hst) as [Hb Hs].
    destruct (step l st) as [bs st'] eqn:Es.
    cbn [fst snd] in Hb, Hs.
    rewrite (parse_lines_step _ _ _ _ _ Es), wf_blocks_app, Hb.
    apply IH. exact Hs.
Qed.

(** The parser cannot produce a malformed document. *)
Theorem wf_parse : forall s, wf_doc (parse_doc s) = true.
Proof.
  intros s. unfold wf_doc, parse_doc. simpl.
  rewrite andb_true_r.
  apply parse_lines_wf. reflexivity.
Qed.

(*
Completeness
============
*)

(** wf = image(parse_doc): the converse of wf_parse, which alone permits
   any weaker predicate.  Asserted nowhere: false as stated, see
   wf_complete_false. *)
Definition wf_complete : Prop :=
  forall d, wf_doc d = true -> exists s, parse_doc s = d.

(* The block constructs Parser.v has a rule for.  The rest of `block` is
   transcribed from djoths and unreachable.  Recursive, so a quote whose
   contents are unreachable is itself unreachable. *)
Fixpoint supported (b : block) : bool :=
  let sup_bs :=
    fix go (ns : list (node block)) : bool :=
      match ns with
      | [] => true
      | Node _ _ x :: rest => supported x && go rest
      end in
  match b with
  | Para _ | ThematicBreak | CodeBlock _ _ | RawBlock _ _ => true
  | BlockQuote bs => sup_bs bs
  | _ => false
  end.

Definition supported_blocks (bs : blocks) : bool :=
  forallb (fun n => supported (node_contents n)) bs.

Lemma supported_blocks_cons :
  forall n bs,
    supported_blocks (n :: bs)
    = (supported (node_contents n) && supported_blocks bs)%bool.
Proof. reflexivity. Qed.

Lemma supported_blocks_app :
  forall bs1 bs2,
    supported_blocks (bs1 ++ bs2)%list
    = (supported_blocks bs1 && supported_blocks bs2)%bool.
Proof. intros bs1 bs2. unfold supported_blocks. apply forallb_app. Qed.

Lemma supported_blocks_rev :
  forall bs, supported_blocks (rev bs) = supported_blocks bs.
Proof. intros bs. unfold supported_blocks. apply forallb_rev. Qed.

Lemma supported_quote :
  forall bs, supported (BlockQuote bs) = supported_blocks bs.
Proof.
  induction bs as [|n bs IH]; [reflexivity|].
  destruct n as [p a x].
  change (supported (BlockQuote (Node p a x :: bs)))
    with (supported x && supported (BlockQuote bs))%bool.
  rewrite IH. reflexivity.
Qed.

Lemma fence_block_supported :
  forall f content, supported (node_contents (fence_block f content)) = true.
Proof.
  intros f content. unfold fence_block.
  destruct (f_info f) as [|c info]; [reflexivity|].
  destruct (Ascii.eqb c "=")%char eqn:E.
  - apply Ascii.eqb_eq in E. subst c. reflexivity.
  - destruct c as [[|] [|] [|] [|] [|] [|] [|] [|]]; reflexivity.
Qed.

(* The same shape as state_wf: only a quote's closed blocks carry an
   obligation. *)
Fixpoint state_supported (st : pstate) : bool :=
  match st with
  | PPara _ | PFence _ _ => true
  | PQuote done inner => supported_blocks done && state_supported inner
  end.

Lemma finish_supported :
  forall st, state_supported st = true -> supported_blocks (finish st) = true.
Proof.
  induction st as [cur|f acc|done inner IH]; intros H.
  - destruct cur as [|c cur']; reflexivity.
  - cbn [finish]. rewrite supported_blocks_cons, fence_block_supported.
    reflexivity.
  - cbn [state_supported] in H. apply andb_true_iff in H as [Hd Hi].
    cbn [finish]. rewrite supported_blocks_cons. cbn [node_contents mk].
    rewrite supported_quote, supported_blocks_app, supported_blocks_rev, Hd,
      (IH Hi).
    reflexivity.
Qed.

Lemma feed_lazy_supported :
  forall l st,
    state_supported st = true -> state_supported (feed_lazy l st) = true.
Proof.
  induction st as [cur|f acc|done inner IH]; intros H; [reflexivity | reflexivity |].
  cbn [feed_lazy state_supported] in *.
  apply andb_true_iff in H as [Hd Hi]. rewrite Hd, (IH Hi). reflexivity.
Qed.

(* Same case analysis as step_fuel_wf: the emitted constructors are
   supported unconditionally, so only the quote accumulator is threaded. *)
Lemma step_fuel_supported :
  forall n l st,
    state_supported st = true ->
    supported_blocks (fst (step_fuel n l st)) = true
    /\ state_supported (snd (step_fuel n l st)) = true.
Proof.
  induction n as [|n IH]; intros l st H; [split; [reflexivity | exact H]|].
  cbn [step_fuel].
  destruct st as [cur|f acc|done inner].
  - destruct cur as [|c cur'].
    + destruct (classify l) as [| |g|rest|] eqn:E;
        try (cbn [open_kind fst snd]; split; reflexivity).
      destruct (IH rest (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n rest (PPara [])) as [bs inner].
      cbn [fst snd] in Hb, Hs |- *.
      split; [reflexivity|].
      cbn [state_supported]. rewrite supported_blocks_rev, Hb. exact Hs.
    + destruct (classify l); cbn [fst snd]; split; reflexivity.
  - destruct (fence_close f l); cbn [fst snd].
    + rewrite supported_blocks_cons, fence_block_supported. split; reflexivity.
    + split; reflexivity.
  - pose proof H as H0. cbn [state_supported] in H0.
    apply andb_true_iff in H0 as [Hd Hi].
    assert (Hbq : supported (BlockQuote (rev done ++ finish inner)%list) = true).
    { rewrite supported_quote, supported_blocks_app, supported_blocks_rev, Hd,
        (finish_supported _ Hi).
      reflexivity. }
    destruct (classify l) as [| |g|rest|] eqn:E.
    4: { destruct (IH rest inner Hi) as [Hb Hs].
         destruct (step_fuel n rest inner) as [bs inner'].
         cbn [fst snd] in Hb, Hs |- *.
         split; [reflexivity|].
         cbn [state_supported].
         rewrite supported_blocks_app, supported_blocks_rev, Hb, Hd. exact Hs. }
    4: { cbn [is_lazy]. destruct (lazy_ok inner); cbn [open_kind fst snd].
         - split; [reflexivity|].
           cbn [state_supported]. rewrite Hd. cbn [andb].
           apply feed_lazy_supported. exact Hi.
         - split; [| reflexivity].
           rewrite supported_blocks_cons. cbn [node_contents mk].
           rewrite Hbq. cbn [andb]. reflexivity. }
    all: cbn [is_lazy open_kind fst snd]; split;
         [ rewrite supported_blocks_cons; cbn [node_contents mk]; rewrite Hbq;
           cbn [andb]; reflexivity
         | reflexivity ].
Qed.

Lemma parse_lines_supported :
  forall lines st,
    state_supported st = true ->
    supported_blocks (parse_lines lines st) = true.
Proof.
  induction lines as [|l rest IH]; intros st Hst.
  - apply finish_supported. exact Hst.
  - destruct (step_fuel_supported (S (String.length l)) l st Hst) as [Hb Hs].
    change (step_fuel (S (String.length l)) l st) with (step l st) in Hb, Hs.
    destruct (step l st) as [bs st'] eqn:Es.
    cbn [fst snd] in Hb, Hs.
    rewrite (parse_lines_step _ _ _ _ _ Es), supported_blocks_app, Hb.
    apply IH. exact Hs.
Qed.

(* Counterexample: a `Section` doc, well-formed and unreachable.  The gap
   is coverage, not a missing wf condition, so completeness has to be
   restated over the parser's fragment in canonical form, i.e. Render.v's
   cb_ok cblocks. *)
Theorem wf_complete_false : ~ wf_complete.
Proof.
  intros Hc.
  destruct (Hc {| doc_blocks := [mk (Section [mk ThematicBreak])]
                ; doc_footnotes := []
                ; doc_references := []
                ; doc_auto_references := []
                ; doc_auto_identifiers := [] |} eq_refl) as [s Hs].
  pose proof (parse_lines_supported (split_lines s) (PPara []) eq_refl) as Hsup.
  change (parse_lines (split_lines s) (PPara []))
    with (doc_blocks (parse_doc s)) in Hsup.
  rewrite Hs in Hsup. discriminate.
Qed.
