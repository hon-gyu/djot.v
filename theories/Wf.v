(* ai-disclosure: autonomous *)

(* Well-formedness of the djot AST as a decidable boolean predicate, and
   the theorems that the parser only produces well-formed output
   (`wf_parse`, `wf_parse_doc`).

   The conditions record what the parser can emit: canonical inline
   sequences (no two adjacent plain `Str`s), a heading's level of at
   least 1, nonempty lists and sections, and the
   classifier's guarantees on reference definitions.  This is a claim
   about the parser, not the roundtrip's hypothesis (`roundtrip_blocks`
   quantifies over `cb_ok`), and `wf_complete_false` shows it does not
   characterize parser output. *)

From Stdlib Require Import String Ascii List Bool PeanoNat.
From DjotV Require Import Strings Line Ast Attributes Parser Document.
Import ListNotations.

Local Open Scope string_scope.

(* The delimiter table this file is read at.  Implicit, so nothing below
   mentions it: what it buys is that the statements quantify over the
   family rather than over djot's spelling. *)
Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(* `InlineScan.sem_flush` is local to its own section, and the invariant
   proofs below meet the same two spellings: a generic definition
   unfolded at the semantic instances leaves the located forms, which
   `rewrite` and `destruct` do not match against the names the theory is
   stated in. *)
Ltac sem_flush :=
  try change (@flush_text_at semantic_pos semantic_inline_cursor)
    with flush_text;
  repeat match goal with
  | |- context [@flush_text_to_at semantic_pos semantic_inline_cursor
                  ?stop ?txt ?o] =>
      change (@flush_text_to_at semantic_pos semantic_inline_cursor
                stop txt o)
        with (flush_text txt o)
  end;
  repeat match goal with
  | |- context [@oclose ?TT semantic_pos ?k ?m ?stop ?o] =>
      change (@oclose TT semantic_pos k m stop o) with (@sclose TT k m o)
  end.

(*
Canonicality of inline sequences
================================

Two adjacent attribute-less Str nodes should have been merged into one
(djoths's Inlines Semigroup does this on append). *)

(*
Inline well-formedness
======================
*)

(* Well-formedness of one inline.  The inner fixpoints are inlined by
   hand because `inline` is nested through `list (node _)`, which Rocq's
   guard checker will not accept as a plain mutual recursion. *)
Local Fixpoint wf_inline (il : inline) : bool :=
  let wf_ils :=
    fix go (ns : list (node inline)) : bool :=
      match ns with
      | [] => true
      | Node _ _ x :: rest => wf_inline x && go rest
      end in
  (* No nonempty obligation: a delimiter scope whose whole content is an
     attribute spec with nothing to attach to closes onto nothing, and
     djot.js builds the empty node for it (`*{.a}*` is
     `<strong></strong>`).  Such a node does not render back -- `**` is
     literal -- but rendering back is `cb_ok`'s condition, asked of
     canonical documents, and this is not one. *)
  let wf_container :=
    fun ns => wf_ils ns && no_adjacent_str ns in
  match il with
  | Str s => nonempty_str s
  | Emph ns | Strong ns | Highlight ns | Insert ns | Delete ns
  | Superscript ns | Subscript ns | Quoted _ ns =>
      wf_container ns
  | Link ns _ | Image ns _ | Span _ ns =>
      (* a bracketed construct may be empty: `[](url)` and `[]{.a}` are
         both valid djot, and djot.js builds the empty node for each *)
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
Local Fixpoint wf_block (b : block) : bool :=
  let wf_bs :=
    fix go (ns : list (node block)) : bool :=
      match ns with
      | [] => true
      | Node _ _ x :: rest => wf_block x && go rest
      end in
  (* Items carry no nonempty obligation: a bare `-` is a valid, empty
     list item (djot.js emits <li></li>), the same way a bare `>` is a
     valid empty quote. *)
  let wf_items :=
    fix goi (its : list (node (list (node block)))) : bool :=
      match its with
      | [] => true
      | Node _ _ it :: rest => wf_bs it && goi rest
      end in
  let wf_task_items :=
    fix got (its : list (node (task_status * list (node block)))) : bool :=
      match its with
      | [] => true
      (* No nonemptiness: `- [ ]` alone is a task item with no content,
         which djot.js renders as `<li><input/></li>`.  Same evidence as
         the bullet item's, one construct over. *)
      | Node _ _ (_, it) :: rest => wf_bs it && got rest
      end in
  let wf_def_items :=
    fix god (its : list (node (node inlines * node (list (node block))))) : bool :=
      match its with
      | [] => true
      | Node _ _ (Node _ _ term, Node _ _ it) :: rest =>
          wf_inlines term && wf_bs it && god rest
      end in
  match b with
  (* A paragraph may be empty for the reason a delimiter node may: its
     line held nothing but a spec with nothing to attach to.  djot.js
     emits `<p></p>` for `{.a}{.b}` and so do we. *)
  | Para ils => wf_inlines ils
  | Section bs => nonempty bs && wf_bs bs
  (* A block quote may be empty: a bare ">" line is a valid, contentless
     quote (djot.js emits <blockquote></blockquote> for it).  A div may be
     empty for the same reason and on the same evidence: `:::` then `:::`
     renders as `<div>\n</div>` in djot.js. *)
  | BlockQuote bs | Div _ bs => wf_bs bs
  | Heading level ils => Nat.leb 1 level && wf_inlines ils
  | CodeBlock _ _ => true
  | OrderedList _ _ items => nonempty items && wf_items items
  | BulletList _ _ items => nonempty items && wf_items items
  | TaskList _ items => nonempty items && wf_task_items items
  | DefinitionList _ items => nonempty items && wf_def_items items
  | ThematicBreak => true
  (* What the classifier can hand back, and so what rendering the block
     back onto one line has to survive: a label with no `]` to end it
     early and no leading `^` to make it a footnote's, and a destination
     that is one whitespace-free run. *)
  | RefDef label dest =>
      no_char "]"%char label && negb (is_footnote_label label) && no_ws dest
  | FootnoteDef label bs => nonempty_str label && wf_bs bs
  | Table caption rows =>
      wf_inlines (node_contents caption)
      && forallb
           (fun row =>
              forallb (fun c => match node_contents c with Cell _ _ ils => wf_inlines ils end)
                (node_contents row))
           rows
  | RawBlock _ _ => true
  (* A label is well formed, exactly as a paragraph's inlines are.  That
     it is *one* inline is not asked here: a label of two elements is not
     something the parser produces -- `key_label_ok` is what stops it --
     but the reason it is excluded is that it does not render back, which
     is the canonical view's business.  Nonemptiness is the same
     condition one notch weaker, and is left out for the same reason. *)
  | Ext_keyed label b => wf_inlines label && wf_bs [b]
  | Ext_callout _ _ title bs => wf_inlines title && wf_bs bs
  end.

Definition wf_blocks (bs : blocks) : bool :=
  forallb (fun n => wf_block (node_contents n)) bs.

Local Lemma wf_block_footnote :
  forall label bs,
    wf_block (FootnoteDef label bs) = (nonempty_str label && wf_blocks bs)%bool.
Proof.
  intros label bs. cbn [wf_block]. f_equal.
  induction bs as [|[p a b] rest IH]; [reflexivity|].
  cbn [wf_blocks forallb node_contents]. rewrite IH. reflexivity.
Qed.

Local Lemma wf_block_keyed :
  forall label b,
    wf_block (Ext_keyed label b)
    = (wf_inlines label && wf_blocks [b])%bool.
Proof. intros label [p a x]. reflexivity. Qed.

Local Lemma wf_block_callout :
  forall kind fold title bs,
    wf_block (Ext_callout kind fold title bs)
    = (wf_inlines title && wf_blocks bs)%bool.
Proof.
  intros kind fold title bs. cbn [wf_block]. f_equal.
  induction bs as [|[p a b] rest IH]; [reflexivity|].
  cbn [wf_blocks forallb node_contents]. rewrite IH. reflexivity.
Qed.

(* Well-formedness reads payloads, never attributes, so hanging block
   attributes on a node is invisible to it. *)
Local Lemma wf_blocks_decorate_head :
  forall a bs, wf_blocks (decorate_head a bs) = wf_blocks bs.
Proof. intros a bs. destruct bs as [|[q a' x] rest]; reflexivity. Qed.

(* The top-level predicate: body and footnote bodies are well-formed.
   (Reference maps carry no blocks, so nothing to check there.) *)
Definition wf_doc (d : doc) : bool :=
  wf_blocks (doc_blocks d) && 
  forallb (fun p : string * blocks => wf_blocks (snd p)) (doc_footnotes d).

(*
Equation lemmas
===============
*)

Local Lemma wf_inlines_cons :
  forall n ns,
    wf_inlines (n :: ns) =
    (wf_inline (node_contents n)
     && forallb (fun m => wf_inline (node_contents m)) ns
     && no_adjacent_str (n :: ns))%bool.
Proof. reflexivity. Qed.

Local Lemma wf_blocks_cons :
  forall n bs,
    wf_blocks (n :: bs) = (wf_block (node_contents n) && wf_blocks bs)%bool.
Proof. reflexivity. Qed.

(* wf_block's hand-inlined block-list fixpoint is wf_blocks.  Stated for
   the one container that carries no side condition, so the equation is
   an identity rather than an implication. *)
Local Lemma wf_block_quote :
  forall bs, wf_block (BlockQuote bs) = wf_blocks bs.
Proof.
  induction bs as [|n bs IH]; [reflexivity|].
  destruct n as [p a x].
  change (wf_block (BlockQuote (Node p a x :: bs)))
    with (wf_block x && wf_block (BlockQuote bs))%bool.
  rewrite IH. reflexivity.
Qed.

(* Divs share BlockQuote's clause, so they share its lemma's shape. *)
Local Lemma wf_block_div :
  forall name bs, wf_block (Div name bs) = wf_blocks bs.
Proof.
  intros name.
  induction bs as [|n bs IH]; [reflexivity|].
  destruct n as [p a x].
  change (wf_block (Div name (Node p a x :: bs)))
    with (wf_block x && wf_block (Div name bs))%bool.
  rewrite IH. reflexivity.
Qed.

(* A div's node carries a class attribute when it has one; `wf_block`
   reads only the payload, so the wrapper is irrelevant to it. *)
Local Lemma div_block_wf :
  forall cls bs,
    wf_blocks bs = true -> wf_blocks [div_block cls bs] = true.
Proof.
  intros cls bs H. unfold div_block.
  destruct bdiv_names; [|destruct (String.eqb cls EmptyString)];
    rewrite wf_blocks_cons; cbn [node_contents mk];
    rewrite wf_block_div, H; reflexivity.
Qed.

(* wf_block's hand-inlined item-list fixpoint, named for the same reason
   as wf_block_quote. *)
Local Lemma wf_block_bullet :
  forall bc sp items,
    wf_block (BulletList bc sp items)
    = (nonempty items && forallb (fun it => wf_blocks (node_contents it)) items)%bool.
Proof.
  intros bc sp items.
  assert (H : forall its,
             (fix goi (l : list (node (list (node block)))) : bool :=
                match l with
                | [] => true
                | Node _ _ it :: rest => (wf_block (BlockQuote it) && goi rest)%bool
                end) its = forallb (fun it => wf_blocks (node_contents it)) its).
  { induction its as [|[p a it] rest IH]; [reflexivity|].
    cbn [forallb node_contents]. rewrite wf_block_quote, IH. reflexivity. }
  change (wf_block (BulletList bc sp items))
    with (nonempty items
          && (fix goi (l : list (node (list (node block)))) : bool :=
                match l with
                | [] => true
                | Node _ _ it :: rest => (wf_block (BlockQuote it) && goi rest)%bool
                end) items)%bool.
  rewrite H. reflexivity.
Qed.

(* The ordered flavour asks for exactly the same thing, which is what
   lets `finish_wf` stay one case: `list_block` chooses the wrapper, and
   `wf_block` cannot tell the two apart. *)
Local Lemma wf_block_olist :
  forall oa sp items,
    wf_block (OrderedList oa sp items)
    = (nonempty items && forallb (fun it => wf_blocks (node_contents it)) items)%bool.
Proof.
  intros oa sp items.
  assert (H : forall its,
             (fix goi (l : list (node (list (node block)))) : bool :=
                match l with
                | [] => true
                | Node _ _ it :: rest => (wf_block (BlockQuote it) && goi rest)%bool
                end) its = forallb (fun it => wf_blocks (node_contents it)) its).
  { induction its as [|[p a it] rest IH]; [reflexivity|].
    cbn [forallb node_contents]. rewrite wf_block_quote, IH. reflexivity. }
  change (wf_block (OrderedList oa sp items))
    with (nonempty items
          && (fix goi (l : list (node (list (node block)))) : bool :=
                match l with
                | [] => true
                | Node _ _ it :: rest => (wf_block (BlockQuote it) && goi rest)%bool
                end) items)%bool.
  rewrite H. reflexivity.
Qed.

(* What `wf_block` asks of one definition item: a term is inlines and
   asks only `wf_inlines`. *)
Local Definition wf_def_entry (ti : node (node inlines * node blocks)) : bool :=
  (wf_inlines (node_contents (fst (node_contents ti)))
   && wf_blocks (node_contents (snd (node_contents ti))))%bool.

Local Lemma wf_block_deflist :
  forall sp items,
    wf_block (DefinitionList sp items)
    = (nonempty items && forallb wf_def_entry items)%bool.
Proof.
  intros sp items.
  assert (H : forall its,
             (fix god (l : list (node (node inlines * node (list (node block))))) : bool :=
                match l with
                | [] => true
                | Node _ _ (Node _ _ term, Node _ _ it) :: rest =>
                    (wf_inlines term && wf_block (BlockQuote it) && god rest)%bool
                end) its
             = forallb wf_def_entry its).
  { induction its as [|[p a [[tp ta term] [dp da it]]] rest IH]; [reflexivity|].
    cbn [forallb wf_def_entry fst snd node_contents]. rewrite wf_block_quote, IH.
    reflexivity. }
  change (wf_block (DefinitionList sp items))
    with (nonempty items
          && (fix god (l : list (node (node inlines * node (list (node block))))) : bool :=
                match l with
                | [] => true
                | Node _ _ (Node _ _ term, Node _ _ it) :: rest =>
                    (wf_inlines term && wf_block (BlockQuote it) && god rest)%bool
                end) items)%bool.
  rewrite H. reflexivity.
Qed.

(* Splitting the term off an item keeps it well-formed: the term's
   inlines are the leading paragraph's, which `wf_blocks` already
   checked, and the definition is the rest of a list it checked. *)
Local Lemma wf_def_split :
  forall bs ils def,
    wf_blocks bs = true ->
    def_split bs = Some (ils, def) ->
    (wf_inlines ils && wf_blocks def)%bool = true.
Proof.
  induction bs as [|[q a x] rest IH]; intros ils def H E; [discriminate|].
  rewrite wf_blocks_cons in H. apply andb_true_iff in H as [Hx Hrest].
  cbn [def_split] in E. destruct x; try discriminate E.
  - injection E as <- <-.
    cbn [node_contents wf_block] in Hx. rewrite Hx, Hrest. reflexivity.
  - destruct (def_split rest) as [[ils' more]|] eqn:Es; [|discriminate E].
    injection E as <- <-.
    pose proof (IH ils' more Hrest eq_refl) as Hi.
    apply andb_true_iff in Hi as [Hi Hm].
    rewrite Hi, wf_blocks_cons, Hx, Hm. reflexivity.
  - destruct (def_split rest) as [[ils' more]|] eqn:Es; [|discriminate E].
    injection E as <- <-.
    pose proof (IH ils' more Hrest eq_refl) as Hi.
    apply andb_true_iff in Hi as [Hi Hm].
    rewrite Hi, wf_blocks_cons, Hx, Hm. reflexivity.
Qed.

Local Lemma wf_def_node :
  forall bs, wf_blocks bs = true -> wf_def_entry (def_node bs) = true.
Proof.
  intros bs H. unfold def_node, wf_def_entry.
  destruct (def_split bs) as [[ils def]|] eqn:E.
  - rewrite (def_item_some bs _ E). cbn [fst snd node_contents mk].
    exact (wf_def_split bs ils def H E).
  - rewrite (def_item_none bs E). cbn [fst snd node_contents mk]. rewrite H.
    reflexivity.
Qed.

Local Lemma wf_def_items :
  forall its,
    forallb wf_blocks its = true -> forallb wf_def_entry (def_items its) = true.
Proof.
  unfold def_items. induction its as [|it rest IH]; [reflexivity|].
  cbn [forallb map]. intros H.
  apply andb_true_iff in H as [Hit Hrest].
  rewrite (wf_def_node it Hit), (IH Hrest). reflexivity.
Qed.

Local Lemma nonempty_def_items :
  forall its, nonempty (def_items its) = nonempty its.
Proof. intros [|it rest]; reflexivity. Qed.

(* As `wf_block_bullet`, for the flavour whose items carry a status. *)
Local Lemma wf_block_tasklist :
  forall sp items,
    wf_block (TaskList sp items)
    = (nonempty items
       && forallb (fun ti => wf_blocks (snd (node_contents ti))) items)%bool.
Proof.
  intros sp items.
  assert (H : forall its,
             (fix got (l : list (node (task_status * list (node block)))) : bool :=
                match l with
                | [] => true
                | Node _ _ (_, it) :: rest => (wf_block (BlockQuote it) && got rest)%bool
                end) its = forallb (fun ti => wf_blocks (snd (node_contents ti))) its).
  { induction its as [|[p a [st it]] rest IH]; [reflexivity|].
    cbn [forallb snd node_contents]. rewrite wf_block_quote, IH. reflexivity. }
  change (wf_block (TaskList sp items))
    with (nonempty items
          && (fix got (l : list (node (task_status * list (node block)))) : bool :=
                match l with
                | [] => true
                | Node _ _ (_, it) :: rest => (wf_block (BlockQuote it) && got rest)%bool
                end) items)%bool.
  rewrite H. reflexivity.
Qed.

Local Lemma nonempty_task_items :
  forall chks its, nonempty (task_items chks its) = nonempty its.
Proof. intros chks [|it rest]; [reflexivity|destruct chks; reflexivity]. Qed.

(* Pairing the statuses onto the items is invisible to `wf_block`. *)
Local Lemma wf_task_items :
  forall (chks : list task_status) its,
    forallb wf_blocks its = true ->
    forallb (fun ti => wf_blocks (snd (node_contents ti))) (task_items chks its) = true.
Proof.
  intros chks its. revert chks.
  induction its as [|it rest IH]; intros chks H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hit Hrest].
  destruct chks as [|c cs]; cbn [task_items forallb snd node_contents mk];
    rewrite Hit; apply IH, Hrest.
Qed.

Local Lemma forallb_mk :
  forall (A : Type) (f : A -> bool) xs,
    forallb (fun n => f (node_contents n)) (map mk xs) = forallb f xs.
Proof.
  intros A f xs. induction xs as [|x xs IH]; [reflexivity|].
  cbn [map forallb node_contents mk]. rewrite IH. reflexivity.
Qed.

Local Lemma nonempty_map :
  forall (A B : Type) (f : A -> B) xs, nonempty (map f xs) = nonempty xs.
Proof. intros A B f [|x xs]; reflexivity. Qed.

(* A closed list is well-formed when its items are, whichever flavour
   `list_block` picks.  An implication: `wf_def_items` gives the
   definition flavour in this direction only. *)
Local Lemma wf_list_block :
  forall ls last,
    (nonempty (rev (last :: ls_items ls))
     && forallb wf_blocks (rev (last :: ls_items ls)))%bool = true ->
    wf_block (node_contents (list_block ls last)) = true.
Proof.
  intros ls last H. apply andb_true_iff in H as [Hne Hall].
  unfold list_block, styles_list_checked, styles_list.
  destruct (ls_styles ls) as [|[[c|c|n d] st] ss].
  - cbn [node_contents mk].
    rewrite wf_block_bullet, nonempty_map, (forallb_mk _ wf_blocks).
    apply andb_true_iff. split; assumption.
  - destruct (Ascii.eqb c ":" && bdeflists)%bool; cbn [node_contents mk].
    + rewrite wf_block_deflist. apply andb_true_iff. split.
      * rewrite nonempty_def_items. exact Hne.
      * apply wf_def_items, Hall.
    + rewrite wf_block_bullet, nonempty_map, (forallb_mk _ wf_blocks).
      apply andb_true_iff. split; assumption.
  - cbn [node_contents mk].
    rewrite wf_block_tasklist. apply andb_true_iff. split.
    + rewrite nonempty_task_items. exact Hne.
    + apply wf_task_items, Hall.
  - cbn [node_contents mk].
    rewrite wf_block_olist, nonempty_map, (forallb_mk _ wf_blocks).
    apply andb_true_iff. split; assumption.
Qed.

Local Lemma nonempty_rev :
  forall (A : Type) (l : list A), nonempty (rev l) = nonempty l.
Proof.
  intros A l. destruct l as [|x l']; [reflexivity|].
  cbn [rev nonempty]. destruct (rev l') as [|y r]; reflexivity.
Qed.

Local Lemma nonempty_app_r :
  forall (A : Type) (l1 l2 : list A),
    nonempty l2 = true -> nonempty (l1 ++ l2)%list = true.
Proof. intros A [|x l1] l2 H; [exact H|reflexivity]. Qed.

Local Lemma wf_blocks_app :
  forall bs1 bs2,
    wf_blocks (bs1 ++ bs2)%list = (wf_blocks bs1 && wf_blocks bs2)%bool.
Proof. intros bs1 bs2. unfold wf_blocks. apply forallb_app. Qed.

Local Lemma wf_blocks_rev :
  forall bs, wf_blocks (rev bs) = wf_blocks bs.
Proof. intros bs. unfold wf_blocks. apply forallb_rev. Qed.

Local Lemma no_adjacent_cons_false :
  forall n ns,
    plain_str n = false -> no_adjacent_str ns = true ->
    no_adjacent_str (n :: ns) = true.
Proof.
  intros n ns H Hns. destruct ns as [|m ns']; simpl.
  - reflexivity.
  - simpl in Hns. rewrite H. simpl. exact Hns.
Qed.

Local Lemma no_adjacent_cons2 :
  forall n1 n2 ns,
    plain_str n2 = false -> no_adjacent_str (n2 :: ns) = true ->
    no_adjacent_str (n1 :: n2 :: ns) = true.
Proof.
  intros n1 n2 ns H Hns. simpl. rewrite H, andb_false_r. simpl.
  simpl in Hns. rewrite H in Hns. simpl in Hns.
  destruct ns as [|n3 ns']; [reflexivity | exact Hns].
Qed.

(*
The inline scan emits a well-formed sequence
============================================
`no_adjacent_str` recurses from the front while `InlineScan.iscan` accumulates
at the front of a *reversed* list, so the invariant needs one snoc lemma
and then reads off the scanner states.
Why it holds: `flush_text` is the only thing that pushes a `Str`, and it
runs exactly on the transition into `IOpen`, whose own next push is a
`Verbatim`.  So a `Str` is never pushed onto a `Str`.  That is what
`iscan_wf`'s `IText` case records, by asserting the head is not a `Str`
whenever text is still being accumulated. *)

Local Lemma no_adjacent_str_app2 :
  forall l a b,
    no_adjacent_str (l ++ [a])%list = true ->
    (plain_str a && plain_str b)%bool = false ->
    no_adjacent_str (l ++ [a; b])%list = true.
Proof.
  induction l as [|x l IH]; intros a b H Hc.
  - cbn [app no_adjacent_str]. rewrite Hc. reflexivity.
  - destruct l as [|y l'].
    + cbn [app no_adjacent_str] in H |- *.
      apply andb_true_iff in H as [H1 _].
      rewrite H1, Hc. reflexivity.
    + cbn [app no_adjacent_str] in H |- *.
      apply andb_true_iff in H as [H1 H2].
      rewrite H1. cbn [andb]. exact (IH a b H2 Hc).
Qed.

Local Lemma no_adjacent_str_app2_l :
  forall l a b,
    no_adjacent_str (l ++ [a; b])%list = true ->
    no_adjacent_str (l ++ [a])%list = true.
Proof.
  induction l as [|x l IH]; intros a b H; [reflexivity|].
  destruct l as [|y l'].
  - cbn [app no_adjacent_str] in H |- *.
    apply andb_true_iff in H as [H1 _]. rewrite H1. reflexivity.
  - cbn [app no_adjacent_str] in H |- *.
    apply andb_true_iff in H as [H1 H2].
    rewrite H1. cbn [andb]. exact (IH a b H2).
Qed.

Local Lemma no_adjacent_str_app2_pair :
  forall l a b,
    no_adjacent_str (l ++ [a; b])%list = true ->
    (plain_str a && plain_str b)%bool = false.
Proof.
  induction l as [|x l IH]; intros a b H.
  - cbn [app no_adjacent_str] in H.
    apply andb_true_iff in H as [H _]. apply negb_true_iff in H. exact H.
  - destruct l as [|y l'].
    + cbn [app no_adjacent_str] in H.
      apply andb_true_iff in H as [_ H].
      apply andb_true_iff in H as [H _]. apply negb_true_iff in H. exact H.
    + cbn [app no_adjacent_str] in H.
      apply andb_true_iff in H as [_ H]. exact (IH a b H).
Qed.

(* A scope holds items, not nodes, so both questions are asked of one.  A
   waiting spec is not a plain `Str` and never merges with a neighbour --
   but it may *vanish* when it resolves, which is what
   `oresolve_go`'s flag is for, and why the seam obligation here is still
   only about the nodes on either side of it. *)
Local Definition plain_item (i : oitem) : bool :=
  match i with OIn n => plain_str n | OMark _ _ _ => false end.

Local Fixpoint no_adjacent_item (l : oitems) : bool :=
  match l with
  | i1 :: ((i2 :: _) as rest) =>
      negb (plain_item i1 && plain_item i2) && no_adjacent_item rest
  | _ => true
  end.

(* A waiting spec has no condition of its own: it carries no source, and
   what it resolves to is `rlist_ok_attach`'s business. *)
Local Definition oitem_ok (i : oitem) : bool :=
  match i with
  | OIn n => wf_inline (node_contents n)
  | OMark _ _ _ => true
  end.

Local Definition hd_str (out : oitems) : bool :=
  match out with i :: _ => plain_item i | [] => false end.

(* What a scope carries.  What a *resolved* list carries is `rlist_ok`
   below; `oresolve_ok` is the bridge. *)
Local Definition ilist_ok (out : oitems) : bool :=
  (forallb oitem_ok out && no_adjacent_item (List.rev out))%bool.

Local Definition rlist_ok (out : inlines) : bool :=
  (forallb (fun n => wf_inline (node_contents n)) out
   && no_adjacent_str (List.rev out))%bool.

(* `no_adjacent_item` is `no_adjacent_str` over a wider element type, so
   the three list facts it needs are proved again rather than reused. *)
Local Lemma no_adjacent_item_app2 :
  forall l a b,
    no_adjacent_item (l ++ [a])%list = true ->
    (plain_item a && plain_item b)%bool = false ->
    no_adjacent_item (l ++ [a; b])%list = true.
Proof.
  induction l as [|x l IH]; intros a b H Hc; cbn [app no_adjacent_item].
  - rewrite Hc. reflexivity.
  - destruct l as [|y l']; cbn [app no_adjacent_item] in H |- *.
    + apply andb_true_iff in H as [H1 _]. rewrite H1, Hc. reflexivity.
    + apply andb_true_iff in H as [H1 H2]. rewrite H1; cbn [andb].
      exact (IH a b H2 Hc).
Qed.

Local Lemma no_adjacent_item_app2_l :
  forall l a b,
    no_adjacent_item (l ++ [a; b])%list = true ->
    no_adjacent_item (l ++ [a])%list = true.
Proof.
  induction l as [|x l IH]; intros a b H; cbn [app no_adjacent_item] in H |- *.
  - reflexivity.
  - destruct l as [|y l']; cbn [app no_adjacent_item] in H |- *.
    + apply andb_true_iff in H as [H1 _]. rewrite H1. reflexivity.
    + apply andb_true_iff in H as [H1 H2]. rewrite H1; cbn [andb].
      exact (IH a b H2).
Qed.

Local Lemma no_adjacent_item_app2_pair :
  forall l a b,
    no_adjacent_item (l ++ [a; b])%list = true ->
    (plain_item a && plain_item b)%bool = false.
Proof.
  induction l as [|x l IH]; intros a b H; cbn [app no_adjacent_item] in H.
  - apply andb_true_iff in H as [H _]. apply negb_true_iff in H. exact H.
  - destruct l as [|y l']; cbn [app no_adjacent_item] in H.
    + apply andb_true_iff in H as [_ H].
      apply andb_true_iff in H as [H _]. apply negb_true_iff in H. exact H.
    + apply andb_true_iff in H as [_ H]. exact (IH a b H).
Qed.

Local Lemma ilist_ok_push :
  forall n out,
    ilist_ok out = true ->
    oitem_ok n = true ->
    (plain_item n && hd_str out)%bool = false ->
    ilist_ok (n :: out) = true.
Proof.
  intros n out H Hn Hc. unfold ilist_ok in *.
  apply andb_true_iff in H as [Hall Hadj].
  apply andb_true_iff. split; [cbn [forallb]; rewrite Hn, Hall; reflexivity|].
  cbn [List.rev]. destruct out as [|m out'].
  - reflexivity.
  - cbn [List.rev] in Hadj |- *. rewrite <- app_assoc. cbn [app].
    apply no_adjacent_item_app2; [exact Hadj|].
    cbn [hd_str] in Hc. rewrite andb_comm. exact Hc.
Qed.

(*
The scope stack
---------------
Every scope's list carries the invariant a flat list does, and the two
operations that move inlines between scopes -- closing, which turns a
scope into a node, and abandoning, which splices it into the level below
as text -- are where it has to be re-established.  Abandoning is the
interesting one: it is the only place two `Str` nodes can meet, which is
why `oapp` merges its seam rather than concatenating. *)

Local Lemma no_adjacent_str_last_subst :
  forall l a b,
    plain_str a = plain_str b ->
    no_adjacent_str (l ++ [a])%list = no_adjacent_str (l ++ [b])%list.
Proof.
  induction l as [|x l IH]; intros a b H; [reflexivity|].
  destruct l as [|y l'].
  - cbn [app no_adjacent_str]. rewrite H. reflexivity.
  - cbn [app no_adjacent_str] in IH |- *. rewrite (IH a b H). reflexivity.
Qed.

Local Lemma hd_str_is_starts_str : forall l, hd_str l = starts_str l.
Proof. intros [|[[? [|? ?] ?]|?] ?]; reflexivity. Qed.

Local Lemma no_adjacent_item_snoc_ext :
  forall l n m,
    plain_item n = plain_item m ->
    no_adjacent_item (l ++ [n])%list = no_adjacent_item (l ++ [m])%list.
Proof.
  induction l as [|x l IH]; intros n m H; [reflexivity|].
  destruct l as [|y l']; cbn [app no_adjacent_item].
  - rewrite H. reflexivity.
  - f_equal. exact (IH n m H).
Qed.

Local Lemma no_adjacent_item_last_subst :
  forall l a b,
    plain_item a = plain_item b ->
    no_adjacent_item (l ++ [a])%list = no_adjacent_item (l ++ [b])%list.
Proof. exact no_adjacent_item_snoc_ext. Qed.

(* `no_adjacent_str` reads nothing but `plain_str` of each node, so the
   element at the end may be swapped for any other with the same verdict.
   `oattach_list` is the one writer that replaces a node in place. *)
Local Lemma no_adjacent_str_snoc_ext :
  forall l n m,
    plain_str n = plain_str m ->
    no_adjacent_str (l ++ [n])%list = no_adjacent_str (l ++ [m])%list.
Proof.
  induction l as [|x l IH]; intros n m H; [reflexivity|].
  destruct l as [|y l']; cbn [app no_adjacent_str].
  - rewrite H. reflexivity.
  - f_equal. exact (IH n m H).
Qed.

(* Decorating the most recent node keeps the scope well-formed: the
   payload is untouched, so `wf_inline` transfers, and the seam is
   decided by `plain_str` alone. *)
Local Lemma ilist_ok_reattr :
  forall n m out,
    ilist_ok (OIn n :: out) = true ->
    node_contents m = node_contents n ->
    plain_str m = false -> plain_str n = false ->
    ilist_ok (OIn m :: out) = true.
Proof.
  intros n m out H Hc Hm Hn. unfold ilist_ok in *.
  cbn [forallb List.rev oitem_ok] in *. rewrite Hc.
  rewrite (no_adjacent_item_snoc_ext (List.rev out) (OIn m) (OIn n)
             (eq_trans Hm (eq_sym Hn))).
  exact H.
Qed.

Local Lemma ilist_ok_osnoc :
  forall n out,
    ilist_ok out = true ->
    oitem_ok n = true ->
    ilist_ok (osnoc n out) = true.
Proof.
  intros n out Ho Hn. destruct (plain_item n) eqn:Hpn.
  - (* n is a plain `Str`: the head of `out` decides whether they merge *)
    destruct n as [[c [|q qs] j]|na]; [|discriminate|discriminate].
    destruct j; try discriminate.
    destruct out as [|[[a [|p ps] i]|ma] out'];
      [unfold osnoc; apply ilist_ok_push;
        [exact Ho | exact Hn | reflexivity] | | |].
    2: { unfold osnoc. apply ilist_ok_push;
           [exact Ho | exact Hn | reflexivity]. }
    2: { unfold osnoc. apply ilist_ok_push;
           [exact Ho | exact Hn | reflexivity]. }
    destruct i;
      try (unfold osnoc; apply ilist_ok_push;
           [exact Ho | exact Hn | reflexivity]).
    (* the one merging case: two plain `Str` nodes become one *)
    unfold osnoc, ilist_ok in *. cbn [oitem_ok node_contents wf_inline] in Hn.
    apply andb_true_iff in Ho as [Hall Hadj].
    cbn [forallb oitem_ok node_contents wf_inline] in Hall.
    apply andb_true_iff in Hall as [Ht Hall].
    apply andb_true_iff. split.
    + cbn [forallb oitem_ok node_contents wf_inline].
      rewrite Hall, andb_true_r.
      destruct s0; [discriminate | reflexivity].
    + cbn [List.rev] in Hadj |- *.
      rewrite (no_adjacent_item_last_subst (List.rev out')
                 (OIn (Node (merge_text_pos a c) [] (Str (s0 ++ s))))
                 (OIn (Node a [] (Str s0))));
        [exact Hadj | reflexivity].
  - (* n is not a plain `Str`: no merge, and nothing to check *)
    replace (osnoc n out) with (n :: out)%list;
      [apply ilist_ok_push;
        [exact Ho | exact Hn | rewrite Hpn; reflexivity]|].
    destruct out as [|[[a [|p ps] i]|ma] out']; try reflexivity.
    destruct i; try reflexivity.
    destruct n as [[c [|q qs] j]|na]; try reflexivity.
    destruct j; try reflexivity. discriminate.
Qed.

Local Lemma hd_str_oapp :
  forall cur out, nonempty cur = true -> hd_str (oapp cur out) = hd_str cur.
Proof.
  intros [|n [|m cur']] out H; [discriminate| |rewrite oapp_cons2; reflexivity].
  rewrite oapp_one. destruct out as [|[[a [|p ps] i]|ma] out'];
    try (unfold osnoc; destruct n as [[c d j]|na]; reflexivity).
  unfold osnoc. destruct i;
    try (destruct n as [[c d j]|na]; reflexivity).
  destruct n as [[c [|q qs] j]|na]; try reflexivity.
  destruct j; reflexivity.
Qed.

Local Lemma ilist_ok_oapp :
  forall cur out,
    ilist_ok cur = true -> ilist_ok out = true ->
    ilist_ok (oapp cur out) = true.
Proof.
  induction cur as [|n cur IH]; intros out Hc Ho; [exact Ho|].
  unfold ilist_ok in Hc. apply andb_true_iff in Hc as [Hall Hadj].
  cbn [forallb] in Hall. apply andb_true_iff in Hall as [Hn Hall].
  destruct cur as [|m cur'].
  - rewrite oapp_one. apply ilist_ok_osnoc; [exact Ho | exact Hn].
  - cbn [List.rev] in Hadj. rewrite <- app_assoc in Hadj. cbn [app] in Hadj.
    assert (Hct : ilist_ok (m :: cur') = true).
    { unfold ilist_ok. rewrite Hall. cbn [List.rev].
      exact (no_adjacent_item_app2_l _ _ _ Hadj). }
    rewrite oapp_cons2.
    apply ilist_ok_push; [apply IH; assumption | exact Hn |].
    rewrite (hd_str_oapp (m :: cur') out eq_refl). cbn [hd_str].
    rewrite andb_comm. exact (no_adjacent_item_app2_pair _ _ _ Hadj).
Qed.

(*
Resolution
----------

The scope invariant is about *items*, and `wf_inlines` is about nodes.
`oresolve` is the bridge, and these are the list facts it needs on the
node side -- the same three as above, over `isnoc` rather than `osnoc`.
*)

(* Merging attributes onto a node cannot turn it into a plain `Str`:
   either it already carried some, and `Attr.merge_cons` says it still
   does, or it carried none and its payload was not a `Str`. *)
Local Lemma plain_str_reattr :
  forall p a' v a,
    plain_str (Node p a' v) = false ->
    plain_str (Node p (Attr.merge a a') v) = false.
Proof.
  intros p [|kv a'] v a H;
    [|destruct (Attr.merge_cons a kv a') as [x [r E]]; rewrite E; reflexivity].
  destruct (Attr.merge a []) as [|z r];
    [destruct v; try reflexivity; discriminate H|reflexivity].
Qed.

Local Lemma istarts_str_cons :
  forall m out, istarts_str (m :: out)%list = plain_str m.
Proof.
  intros [q [|kv b] w] out; [destruct w; reflexivity|reflexivity].
Qed.

Local Lemma rlist_ok_push :
  forall n out,
    rlist_ok out = true ->
    wf_inline (node_contents n) = true ->
    (plain_str n && istarts_str out)%bool = false ->
    rlist_ok (n :: out) = true.
Proof.
  intros n out H Hn Hc. unfold rlist_ok in *.
  apply andb_true_iff in H as [Hall Hadj].
  apply andb_true_iff. split; [cbn [forallb]; rewrite Hn, Hall; reflexivity|].
  cbn [List.rev]. destruct out as [|m out'].
  - reflexivity.
  - cbn [List.rev] in Hadj |- *. rewrite <- app_assoc. cbn [app].
    apply no_adjacent_str_app2; [exact Hadj|].
    rewrite istarts_str_cons in Hc. rewrite andb_comm. exact Hc.
Qed.

Local Lemma rlist_ok_tail :
  forall n out, rlist_ok (n :: out)%list = true -> rlist_ok out = true.
Proof.
  intros n out H. unfold rlist_ok in *.
  apply andb_true_iff in H as [Hall Hadj].
  cbn [forallb] in Hall. apply andb_true_iff in Hall as [_ Hall].
  rewrite Hall. cbn [List.rev] in Hadj.
  destruct out as [|m out']; [reflexivity|].
  cbn [List.rev] in Hadj |- *.
  rewrite <- app_assoc in Hadj. cbn [app] in Hadj.
  exact (no_adjacent_str_app2_l _ _ _ Hadj).
Qed.

Local Lemma rlist_ok_reattr :
  forall n m out,
    rlist_ok (n :: out) = true ->
    node_contents m = node_contents n ->
    plain_str m = false -> plain_str n = false ->
    rlist_ok (m :: out) = true.
Proof.
  intros n m out H Hc Hm Hn. unfold rlist_ok in *.
  cbn [forallb List.rev] in *. rewrite Hc.
  rewrite (no_adjacent_str_snoc_ext (List.rev out) m n
             (eq_trans Hm (eq_sym Hn))).
  exact H.
Qed.

Local Lemma istarts_str_isnoc :
  forall n out, istarts_str (isnoc n out) = plain_str n.
Proof.
  intros [p a v] out. unfold isnoc.
  destruct out as [|[q [|kv b] w] l];
    [ rewrite istarts_str_cons; reflexivity
    | | rewrite istarts_str_cons; reflexivity ].
  destruct w; try (rewrite istarts_str_cons; reflexivity).
  destruct a as [|ka a']; [|rewrite istarts_str_cons; reflexivity].
  destruct v; try (rewrite istarts_str_cons; reflexivity).
Qed.

Local Lemma rlist_ok_isnoc :
  forall n out,
    rlist_ok out = true ->
    wf_inline (node_contents n) = true ->
    rlist_ok (isnoc n out) = true.
Proof.
  intros n out Ho Hn. destruct (plain_str n) eqn:Hpn.
  - destruct n as [c [|q qs] j]; [|discriminate].
    destruct j; try discriminate.
    destruct out as [|[a [|p ps] i] out'];
      [unfold isnoc; apply rlist_ok_push;
        [exact Ho | exact Hn | reflexivity] | |].
    2: { unfold isnoc. apply rlist_ok_push;
           [exact Ho | exact Hn | reflexivity]. }
    destruct i;
      try (unfold isnoc; apply rlist_ok_push;
           [exact Ho | exact Hn | reflexivity]).
    unfold isnoc, rlist_ok in *. cbn [node_contents wf_inline] in Hn.
    apply andb_true_iff in Ho as [Hall Hadj].
    cbn [forallb node_contents wf_inline] in Hall.
    apply andb_true_iff in Hall as [Ht Hall].
    apply andb_true_iff. split.
    + cbn [forallb node_contents wf_inline]. rewrite Hall, andb_true_r.
      destruct s0; [discriminate | reflexivity].
    + cbn [List.rev] in Hadj |- *.
      rewrite (no_adjacent_str_last_subst (List.rev out')
                 (Node (merge_text_pos a c) [] (Str (s0 ++ s)))
                 (Node a [] (Str s0)));
        [exact Hadj | reflexivity].
  - replace (isnoc n out) with (n :: out)%list;
      [apply rlist_ok_push;
        [exact Ho | exact Hn | rewrite Hpn; reflexivity]|].
    destruct out as [|[a [|p ps] i] out']; try reflexivity.
    destruct i; try reflexivity.
    destruct n as [c [|q qs] j]; [|reflexivity].
    destruct j; try reflexivity. discriminate.
Qed.

(* Where a spec lands, on a list that already satisfies the invariant.
   Every disposition either leaves the list alone or replaces its head
   by nodes carrying its payload, so no condition on the spec is
   needed. *)
Local Lemma rlist_ok_attach :
  forall a spec word_start out,
    rlist_ok out = true ->
    rlist_ok (oattach_list a spec word_start out) = true.
Proof.
  intros a spec word_start out Ho. unfold oattach_list.
  destruct out as [|[p a' v] out].
  - exact Ho.
  - assert (Hre : plain_str (Node p a' v) = false ->
                  rlist_ok (add_inline_role RAttrSpec spec
                              (Node p (Attr.merge a a') v) :: out) = true).
    { intros Hp. apply rlist_ok_reattr with (n := Node p a' v);
        [exact Ho | reflexivity | apply plain_str_reattr, Hp | exact Hp]. }
    destruct a' as [|kv a'']; destruct v;
      try (apply Hre; reflexivity); try exact Ho.
    (* the one case left: a plain `Str` head, which the spec splits *)
    destruct (last_ws_split s) as [pre w] eqn:Es.
    destruct (nonempty_str w) eqn:Ew; [|exact Ho].
    destruct a as [|ka a2]; [exact Ho|].
    destruct (split_text_pos p word_start) as [pp wp] eqn:Esp.
    assert (Hrest : rlist_ok out = true) by exact (rlist_ok_tail _ _ Ho).
    apply rlist_ok_isnoc; [|exact Ew].
    destruct (nonempty_str pre) eqn:Ep; [|exact Hrest].
    apply rlist_ok_isnoc; [exact Hrest|exact Ep].
Qed.

(* The bridge.  Note what the input invariant does *not* say: it allows
   two plain `Str` items with a spec between them, because that spec may
   vanish -- and when it does, `oresolve_go`'s flag makes the next node
   merge rather than sit adjacent. *)
Local Lemma oresolve_go_ok :
  forall l,
    ilist_ok l = true ->
    rlist_ok (fst (oresolve_go l)) = true
    /\ (snd (oresolve_go l) = false ->
        istarts_str (fst (oresolve_go l)) = hd_str l).
Proof.
  induction l as [|i l IH]; intros H; [split; [reflexivity|reflexivity]|].
  assert (Hl : ilist_ok l = true).
  { unfold ilist_ok in H |- *.
    apply andb_true_iff in H as [Hall Hadj].
    cbn [forallb] in Hall. apply andb_true_iff in Hall as [_ Hall].
    rewrite Hall. cbn [List.rev] in Hadj.
    destruct l as [|m l']; [reflexivity|].
    cbn [List.rev] in Hadj |- *.
    rewrite <- app_assoc in Hadj. cbn [app] in Hadj.
    exact (no_adjacent_item_app2_l _ _ _ Hadj). }
  destruct (IH Hl) as [Hok Hhd].
  unfold ilist_ok in H. apply andb_true_iff in H as [Hall Hadj].
  cbn [forallb] in Hall. apply andb_true_iff in Hall as [Hi _].
  cbn [oresolve_go]. destruct (oresolve_go l) as [out m]; cbn [fst snd] in *.
  destruct i as [n|a].
  - cbn [oitem_ok] in Hi. destruct m.
    + split; [apply rlist_ok_isnoc; assumption|].
      intros _. cbn [fst]. rewrite istarts_str_isnoc. reflexivity.
    + assert (Hseam : (plain_str n && istarts_str out)%bool = false).
      { rewrite (Hhd eq_refl). destruct l as [|m' l']; [apply andb_false_r|].
        cbn [List.rev] in Hadj. rewrite <- app_assoc in Hadj.
        cbn [app] in Hadj.
        pose proof (no_adjacent_item_app2_pair _ _ _ Hadj) as Hc.
        cbn [plain_item hd_str] in Hc |- *. rewrite andb_comm. exact Hc. }
      split; [apply rlist_ok_push; assumption|].
      intros _. cbn [fst]. rewrite istarts_str_cons. reflexivity.
  - cbn [oitem_ok] in Hi.
    split; [apply rlist_ok_attach; assumption|].
    cbn [fst snd]. intros Hs. exact Hs.
Qed.

Local Lemma oresolve_ok :
  forall l, ilist_ok l = true -> rlist_ok (oresolve l) = true.
Proof. intros l H. apply (proj1 (oresolve_go_ok l H)). Qed.

Local Definition frames_ok (stk : list frame) : bool :=
  forallb (fun f => ilist_ok (fr_out f)) stk.

Local Definition oscope_ok (o : ostate) : bool :=
  (ilist_ok (os_out o) && frames_ok (os_stk o))%bool.

Local Fixpoint iscan_wf (st : iscan) : bool :=
  match st with
  | IText _ _ _ o | IEscWs _ _ _ o | IBrace _ _ o
  | IDelim _ _ _ _ _ o | IDollar _ _ _ o | IPeriod _ _ _ o
  | IDash _ _ _ o =>
      (oscope_ok o && negb (hd_str (ocur o)))%bool
  | IOpen _ _ o => oscope_ok o
  (* A raw spec is the same: what it owes is a node -- a `Verbatim` or a
     `RawInline` -- and neither is a `Str`, so the scope it lands in
     needs no head condition either. *)
  | IVerb _ _ _ _ o | IRaw _ _ o => oscope_ok o
  (* The bracket modes carry the label's classified children, which the
     literal fallback emits one by one and the balanced close wraps in a
     `Link`; both need them well-formed and non-adjacent, which is
     exactly `wf_inlines`.  Neither carries the head condition the text
     states do, because the fallback reabsorbs a flushed `Str` before it
     writes anything -- that is what `opop_str` is for. *)
  (* An autolink candidate holds pending text and no children, and the
     text is what it flushes whichever way it ends -- so it carries the
     text states' head condition and nothing else.  A `]` waiting for the
     byte after it is the same shape: it has closed nothing, and its
     buffer is the one the literal continuation appends to. *)
  | IBang _ _ o | IAuto _ _ o | IClosed _ o =>
      (oscope_ok o && negb (hd_str (ocur o)))%bool
  | ISpan kids _ _ _ _ o | IReference kids _ _ _ o =>
      (oscope_ok o && wf_inlines kids)%bool
  (* An attribute candidate owes both its interpretations: the scope and
     seam condition its successful attachment will use, and the ordinary
     scan selected if the candidate never closes. *)
  | IAttr _ _ _ _ sh o =>
      (oscope_ok o && negb (hd_str (ocur o)) && iscan_wf sh)%bool
  | IDollarMath _ _ _ _ _ sh o | IDollarMathClose _ _ _ _ sh o =>
      (oscope_ok o && negb (hd_str (ocur o)) && iscan_wf sh)%bool
  (* A symbol candidate also carries the reading selected on failure. *)
  | ISymbol _ _ sh o =>
      (oscope_ok o && negb (hd_str (ocur o)) && iscan_wf sh)%bool
  (* A destination owes both its readings: the `kids` and the scope the
     balanced `)` will emit into, and the ordinary scan that the end of
     the paragraph keeps instead. *)
  | IDest kids _ _ _ _ _ sh o =>
      (oscope_ok o && wf_inlines kids && iscan_wf sh)%bool
  (* A footnote label carries no children -- it discards what the
     brackets would have held -- and no head condition either, for the
     bracket modes' reason: `bnote_lit` reabsorbs the flushed `Str`
     through `opop_str` before it writes. *)
  | INote _ _ _ _ o => oscope_ok o
  | IWiki _ _ _ _ _ o => oscope_ok o
  end.

(* `wf_inline`'s inline-list check, as a global fixpoint with the same
   body: the local one is not nameable, and every container obligation
   below needs to talk about it. *)
Local Fixpoint wf_ils (ns : list (node inline)) : bool :=
  match ns with
  | [] => true
  | Node _ _ x :: rest => wf_inline x && wf_ils rest
  end.

Local Lemma wf_ils_forallb :
  forall ns, wf_ils ns = forallb (fun n => wf_inline (node_contents n)) ns.
Proof.
  induction ns as [|[p a x] ns IH]; [reflexivity|].
  cbn [wf_ils forallb node_contents]. rewrite IH. reflexivity.
Qed.

Local Lemma wf_inline_dnode :
  forall k ns, rlist_ok (List.rev ns) = true -> wf_inline (dnode k ns) = true.
Proof.
  intros k ns Hok. unfold rlist_ok in Hok.
  apply andb_true_iff in Hok as [Hall Hadj].
  rewrite forallb_rev in Hall. rewrite List.rev_involutive in Hadj.
  rewrite <- wf_ils_forallb in Hall.
  destruct k; cbn [dnode];
    match goal with
    | |- wf_inline ?X = true =>
        change (wf_inline X) with (wf_ils ns && no_adjacent_str ns)%bool
    end;
    rewrite Hall, Hadj; reflexivity.
Qed.

(* The bracket node, both spellings.  Same two conditions as
   `wf_inline_dnode`, since neither carries a nonemptiness one. *)
Local Lemma wf_inline_bnode :
  forall img ns tgt,
    wf_ils ns = true -> no_adjacent_str ns = true ->
    wf_inline (bnode img ns tgt) = true.
Proof.
  intros img ns tgt Hw Ha. destruct img; cbn [bnode];
    match goal with
    | |- wf_inline ?X = true =>
        change (wf_inline X) with (wf_ils ns && no_adjacent_str ns)%bool
    end; rewrite Hw, Ha; reflexivity.
Qed.

(*
The scope operations preserve it
--------------------------------
*)

Local Lemma ocur_emit : forall n o, ocur (oemit n o) = (OIn n :: ocur o)%list.
Proof. intros n [out [|f stk]]; reflexivity. Qed.

Local Lemma ocur_mark :
  forall a spec o,
    ocur (omark a spec o) = (OMark a spec (os_word_start o) :: ocur o)%list.
Proof. intros a spec [out [|f stk] word]; reflexivity. Qed.

(* A closed backtick run emits a `Verbatim` or a `Math`, and neither is
   a container or a plain `Str` -- which is all the scope invariant asks
   of it. *)
Local Lemma wf_inline_vnode : forall vk s, wf_inline (vnode vk s) = true.
Proof. intros [|st|prefix] s; reflexivity. Qed.

Local Lemma plain_str_vnode : forall vk s, plain_str (mk (vnode vk s)) = false.
Proof. intros [|st|prefix] s; reflexivity. Qed.

Local Lemma starts_str_vnode :
  forall vk s out, starts_str (OIn (mk (vnode vk s)) :: out) = false.
Proof. intros [|st|prefix] s out; reflexivity. Qed.

Local Lemma oscope_ok_emit :
  forall n o,
    oscope_ok o = true ->
    wf_inline (node_contents n) = true ->
    (plain_str n && starts_str (ocur o))%bool = false ->
    oscope_ok (oemit n o) = true.
Proof.
  intros n [out [|f stk]] Ho Hn Hc; unfold oscope_ok, oemit, ocur in *;
    cbn [os_out os_stk frames_ok forallb fr_out fr_kind fr_marked] in *.
  - apply andb_true_iff in Ho as [Ho _]. rewrite andb_true_r.
    apply (ilist_ok_push (OIn n)); [exact Ho | exact Hn |].
    rewrite hd_str_is_starts_str. exact Hc.
  - apply andb_true_iff in Ho as [Hb Hf].
    apply andb_true_iff in Hf as [Hff Hf].
    rewrite Hb, Hf, !andb_true_r.
    apply (ilist_ok_push (OIn n)); [exact Hff | exact Hn |].
    rewrite hd_str_is_starts_str. exact Hc.
Qed.

(* A waiting spec is never a plain `Str`, so it needs no seam condition:
   whatever it resolves to, `oresolve_go` rejoins the neighbours itself. *)
Local Lemma oscope_ok_mark :
  forall a spec o, oscope_ok o = true -> oscope_ok (omark a spec o) = true.
Proof.
  intros a spec [out [|f stk] word] Ho; unfold oscope_ok, omark in *;
    cbn [os_out os_stk os_word_start frames_ok forallb fr_out fr_kind
         fr_marked] in *.
  - apply andb_true_iff in Ho as [Ho _]. rewrite andb_true_r.
    apply (ilist_ok_push (OMark a spec word));
      [exact Ho | reflexivity | reflexivity].
  - apply andb_true_iff in Ho as [Hb Hf].
    apply andb_true_iff in Hf as [Hff Hf].
    rewrite Hb, Hf, !andb_true_r.
    apply (ilist_ok_push (OMark a spec word));
      [exact Hff | reflexivity | reflexivity].
Qed.

Local Lemma oscope_ok_emit_merge :
  forall n o,
    oscope_ok o = true ->
    wf_inline (node_contents n) = true ->
    oscope_ok (oemit_merge n o) = true.
Proof.
  intros n [out [|f stk]] Ho Hn; unfold oscope_ok, oemit_merge in *;
    cbn [os_out os_stk frames_ok forallb fr_out fr_kind fr_marked] in *.
  - apply andb_true_iff in Ho as [Ho _]. rewrite andb_true_r.
    apply ilist_ok_osnoc; assumption.
  - apply andb_true_iff in Ho as [Hb Hf].
    apply andb_true_iff in Hf as [Hff Hf].
    rewrite Hb, Hf, andb_true_r.
    apply ilist_ok_osnoc; assumption.
Qed.

Local Lemma oscope_ok_emit_all_merge :
  forall ns o,
    oscope_ok o = true ->
    forallb (fun n => wf_inline (node_contents n)) ns = true ->
    oscope_ok (oemit_all_merge ns o) = true.
Proof.
  induction ns as [|n ns IH]; intros o Ho Hns; [exact Ho|].
  cbn [oemit_all_merge forallb] in Hns |- *.
  apply andb_true_iff in Hns as [Hn Hns].
  apply IH; [apply oscope_ok_emit_merge; assumption|exact Hns].
Qed.

Local Lemma oscope_ok_push_at :
  forall k m cm open o,
    oscope_ok o = true -> oscope_ok (opush_at k m cm open o) = true.
Proof.
  intros k m cm open [out stk] H. unfold oscope_ok, opush_at in *;
    cbn [os_out os_stk frames_ok forallb fr_out] in *.
  change (ilist_ok []) with true. rewrite andb_true_l. exact H.
Qed.

Local Lemma oscope_ok_push :
  forall k m o, oscope_ok o = true -> oscope_ok (opush k m o) = true.
Proof. intros k m o H. apply oscope_ok_push_at, H. Qed.

Local Lemma oscope_ok_bpush :
  forall image o, oscope_ok o = true -> oscope_ok (bpush image o) = true.
Proof.
  intros image [out stk word] H. unfold oscope_ok, bpush in *;
    cbn [os_out os_stk frames_ok forallb fr_out] in *.
  change (ilist_ok []) with true. rewrite andb_true_l. exact H.
Qed.

Local Lemma oscope_ok_tag_push :
  forall name start o, oscope_ok o = true -> oscope_ok (tag_push name start o) = true.
Proof.
  intros name start [out stk word] H. unfold oscope_ok, tag_push in *;
    cbn [os_out os_stk frames_ok forallb fr_out] in *.
  change (ilist_ok []) with true. rewrite andb_true_l. exact H.
Qed.

Local Lemma oscope_ok_dpush :
  forall image open o,
    oscope_ok o = true -> oscope_ok (dpush image open o) = true.
Proof.
  intros image open [out stk word] H. unfold oscope_ok, dpush in *;
    cbn [os_out os_stk frames_ok forallb fr_out] in *.
  change (ilist_ok []) with true. rewrite andb_true_l. exact H.
Qed.

Local Lemma frames_ok_tail :
  forall f stk, frames_ok (f :: stk) = true -> frames_ok stk = true.
Proof.
  intros f stk H. unfold frames_ok in *. cbn [forallb] in H.
  apply andb_true_iff in H as [_ H]. exact H.
Qed.

Local Lemma frames_ok_head :
  forall f stk, frames_ok (f :: stk) = true -> ilist_ok (fr_out f) = true.
Proof.
  intros f stk H. unfold frames_ok in *. cbn [forallb] in H.
  apply andb_true_iff in H as [H _]. exact H.
Qed.

(* An abandoned opener decays to a `Str` of its own source text, which is
   nonempty by construction -- a bracket writes its own byte, and a
   delimiter writes its row's token, which an admissible table never
   leaves empty. *)
Local Lemma fr_src_nonempty : forall f, nonempty_str (fr_src f) = true.
Proof.
  intros [kind marked out]. unfold fr_src; cbn [fr_kind fr_marked].
  destruct kind as [k|image|image|name].
  - apply ddecay_str_nonempty.
  - destruct image; reflexivity.
  - destruct image; reflexivity.
  - destruct name; reflexivity.
Qed.

Local Lemma ilist_ok_src : forall f, ilist_ok [OIn (mk (Str (fr_src f)))] = true.
Proof.
  intros f. unfold ilist_ok.
  cbn [forallb oitem_ok node_contents mk List.rev].
  cbn [wf_inline no_adjacent_item]. rewrite (fr_src_nonempty f). reflexivity.
Qed.

Local Lemma oclose_go_ok :
  forall stk k m pend content open rest,
    frames_ok stk = true -> ilist_ok pend = true ->
    oclose_go k m pend stk = Some (content, open, rest) ->
    (ilist_ok content && frames_ok rest)%bool = true.
Proof.
  induction stk as [|f stk IH]; intros k m pend content open rest Hs Hp E;
    [discriminate|].
  cbn [oclose_go] in E.
  destruct (dmatch k m f) eqn:Em.
  { destruct (nonempty (oapp pend (fr_out f))); [|discriminate].
    injection E as <- <- <-. rewrite (frames_ok_tail f stk Hs), andb_true_r.
    apply ilist_ok_oapp; [exact Hp | exact (frames_ok_head f stk Hs)]. }
  destruct (fr_barrier f); [discriminate|].
  apply (IH k m (oapp (oapp pend (fr_out f)) [OIn (mk (Str (fr_src f)))])
           content open rest (frames_ok_tail f stk Hs)); [|exact E].
  apply ilist_ok_oapp;
    [apply ilist_ok_oapp; [exact Hp | exact (frames_ok_head f stk Hs)]
    |apply ilist_ok_src].
Qed.

Local Lemma oclose_go_nonempty :
  forall stk k m pend content open rest,
    oclose_go k m pend stk = Some (content, open, rest) ->
    nonempty content = true.
Proof.
  induction stk as [|f stk IH]; intros k m pend content open rest E;
    [discriminate|].
  cbn [oclose_go] in E.
  destruct (dmatch k m f) eqn:Em.
  { destruct (nonempty (oapp pend (fr_out f))) eqn:En; [|discriminate].
    injection E as <- <- <-. exact En. }
  destruct (fr_barrier f); [discriminate|].
  exact (IH k m (oapp (oapp pend (fr_out f)) [OIn (mk (Str (fr_src f)))])
           content open rest E).
Qed.

Local Lemma oclose_ok :
  forall k m o o',
    oscope_ok o = true -> sclose k m o = Some o' ->
    (oscope_ok o' && negb (starts_str (ocur o')))%bool = true.
Proof.
  intros k m o o' Ho E. unfold sclose, oclose in E.
  destruct (oclose_go k m [] (os_stk o)) as [[[content open] rest]|] eqn:Eg;
    [|discriminate].
  injection E as <-. rewrite ?imk_semantic.
  apply andb_true_iff in Ho as [Hb Hs].
  pose proof (oclose_go_ok (os_stk o) k m [] content open rest Hs eq_refl Eg)
    as Hcr.
  apply andb_true_iff in Hcr as [Hc Hr].
  assert (Hnode :
    wf_inline (node_contents (mk (dnode k (List.rev (oresolve content)))))
    = true).
  { cbn [node_contents mk]. apply wf_inline_dnode.
    rewrite List.rev_involutive. exact (oresolve_ok content Hc). }
  rewrite ocur_emit.
  assert (Hplain :
    plain_str (mk (dnode k (List.rev (oresolve content)))) = false)
    by (destruct k; reflexivity).
  assert (Hstart :
    starts_str (OIn (mk (dnode k (List.rev (oresolve content))))
                 :: ocur (OState (os_out o) rest (os_word_start o))) = false)
    by (destruct k; reflexivity).
  rewrite Hstart, andb_true_r.
  apply oscope_ok_emit;
    [|exact Hnode | rewrite Hplain; reflexivity].
  unfold oscope_ok; cbn [os_out os_stk os_word_start].
  rewrite Hb, Hr. reflexivity.
Qed.

(*
The transitions preserve it
---------------------------
*)

Local Lemma iscan_wf_text :
  forall esc txt prev o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (IText esc txt prev o) = true.
Proof.
  intros esc txt prev o Ho Hs. cbn [iscan_wf].
  rewrite Ho, hd_str_is_starts_str, Hs. reflexivity.
Qed.

(* The same, of a state the line break has reset: the word start is no
   part of either obligation. *)
Local Lemma oscope_ok_word_reset :
  forall o, oscope_ok (oword_reset o) = oscope_ok o.
Proof. intros o. reflexivity. Qed.

Local Lemma ocur_word_reset : forall o, ocur (oword_reset o) = ocur o.
Proof. intros o. reflexivity. Qed.

Local Lemma iscan_wf_text_reset :
  forall esc txt prev o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (IText esc txt prev (oword_reset o)) = true.
Proof.
  intros esc txt prev o Ho Hs. cbn [iscan_wf].
  rewrite oscope_ok_word_reset, ocur_word_reset, Ho,
    hd_str_is_starts_str, Hs. reflexivity.
Qed.

(* Only the scopes stay well-formed: after a flush the current head *is*
   a `Str`, which is exactly why the head condition is attached to the
   states that still have text pending and not to `IOpen` and `IVerb` --
   a flush happens only on the way into a verbatim, whose own next
   emission is a `Verbatim`. *)
Local Lemma iscan_wf_flush :
  forall txt o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    oscope_ok (flush_text txt o) = true.
Proof.
  intros txt o Ho Hs. unfold flush_text, flush_text_at.
  destruct (nonempty_str txt) eqn:Ht; [|exact Ho].
  apply oscope_ok_emit; [exact Ho | exact Ht | rewrite Hs; apply andb_false_r].
Qed.

(* Closing a bracket is `oclose` without the node: it abandons the
   delimiter scopes above the bracket the same way, and hands back the
   label rather than wrapping it, so the label carries the list
   invariant and the restored state carries the scope one. *)
Local Lemma bclose_go_ok :
  forall stk pend content image open rest,
    frames_ok stk = true -> ilist_ok pend = true ->
    bclose_go pend stk = Some (content, image, open, rest) ->
    (ilist_ok content && frames_ok rest)%bool = true.
Proof.
  induction stk as [|f stk IH]; intros pend content image open rest Hs Hp E;
    [discriminate|].
  cbn [bclose_go] in E. destruct (fr_kind f).
  - apply (IH (oapp (oapp pend (fr_out f)) [OIn (mk (Str (fr_src f)))])
            content image open rest (frames_ok_tail f stk Hs)); [|exact E].
    apply ilist_ok_oapp;
      [apply ilist_ok_oapp; [exact Hp | exact (frames_ok_head f stk Hs)]
      |apply ilist_ok_src].
  - injection E as <- <- <- <-. rewrite (frames_ok_tail f stk Hs), andb_true_r.
    apply ilist_ok_oapp; [exact Hp | exact (frames_ok_head f stk Hs)].
  - discriminate E.
  - discriminate E.
Qed.

(* The same for a named bracket's close. *)
Local Lemma tag_close_go_ok :
  forall stk pend content name open rest,
    frames_ok stk = true -> ilist_ok pend = true ->
    tag_close_go pend stk = Some (content, name, open, rest) ->
    (ilist_ok content && frames_ok rest)%bool = true.
Proof.
  induction stk as [|f stk IH]; intros pend content name open rest Hs Hp E;
    [discriminate|].
  cbn [tag_close_go] in E. destruct (fr_kind f).
  - apply (IH (oapp (oapp pend (fr_out f)) [OIn (mk (Str (fr_src f)))])
            content name open rest (frames_ok_tail f stk Hs)); [|exact E].
    apply ilist_ok_oapp;
      [apply ilist_ok_oapp; [exact Hp | exact (frames_ok_head f stk Hs)]
      |apply ilist_ok_src].
  - discriminate E.
  - discriminate E.
  - injection E as <- <- <- <-. rewrite (frames_ok_tail f stk Hs), andb_true_r.
    apply ilist_ok_oapp; [exact Hp | exact (frames_ok_head f stk Hs)].
Qed.

Local Lemma tag_close_ok :
  forall o kids name open o',
    oscope_ok o = true -> tag_close o = Some (kids, name, open, o') ->
    (oscope_ok o' && wf_inlines kids)%bool = true.
Proof.
  intros o kids name open o' Ho E. unfold tag_close in E.
  destruct (tag_close_go [] (os_stk o)) as [[[[content nm] op] rest]|] eqn:Eg;
    [|discriminate].
  injection E as <- <- <- <-.
  apply andb_true_iff in Ho as [Hb Hs].
  pose proof (tag_close_go_ok (os_stk o) [] content nm op rest Hs eq_refl Eg)
    as Hcr.
  apply andb_true_iff in Hcr as [Hc Hr].
  pose proof (oresolve_ok content Hc) as Hres.
  unfold rlist_ok in Hres. apply andb_true_iff in Hres as [Hall Hadj].
  apply andb_true_iff. split.
  - unfold oscope_ok; cbn [os_out os_stk os_word_start].
    rewrite Hb, Hr. reflexivity.
  - unfold wf_inlines. rewrite forallb_rev, Hall. cbn [andb]. exact Hadj.
Qed.

Local Lemma bclose_ok :
  forall o kids image open o',
    oscope_ok o = true -> bclose o = Some (kids, image, open, o') ->
    (oscope_ok o' && wf_inlines kids)%bool = true.
Proof.
  intros o kids image open o' Ho E. unfold bclose in E.
  destruct (bclose_go [] (os_stk o)) as [[[[content im] op] rest]|] eqn:Eg;
    [|discriminate].
  injection E as <- <- <- <-.
  apply andb_true_iff in Ho as [Hb Hs].
  pose proof (bclose_go_ok (os_stk o) [] content im op rest Hs eq_refl Eg)
    as Hcr.
  apply andb_true_iff in Hcr as [Hc Hr].
  pose proof (oresolve_ok content Hc) as Hres.
  unfold rlist_ok in Hres. apply andb_true_iff in Hres as [Hall Hadj].
  apply andb_true_iff. split.
  - unfold oscope_ok; cbn [os_out os_stk os_word_start].
    rewrite Hb, Hr. reflexivity.
  - unfold wf_inlines. rewrite forallb_rev, Hall. cbn [andb]. exact Hadj.
Qed.

(*
Putting a bracket back as text preserves it
-------------------------------------------

The fallback is the one place a scope's output is *read back*, and the
two obligations it has to re-establish are the ones every text state
carries.  Popping the flushed `Str` is what makes the head condition
hold with nothing else emitted, and alternating `Str` with non-`Str`
emissions is what makes it hold once something is. *)

Local Lemma ilist_ok_tail :
  forall n out, ilist_ok (n :: out)%list = true -> ilist_ok out = true.
Proof.
  intros n out H. unfold ilist_ok in *.
  apply andb_true_iff in H as [Hall Hadj].
  cbn [forallb] in Hall. apply andb_true_iff in Hall as [_ Hall].
  rewrite Hall. cbn [List.rev] in Hadj.
  destruct out as [|m out']; [reflexivity|].
  cbn [List.rev] in Hadj |- *.
  rewrite <- app_assoc in Hadj. cbn [app] in Hadj.
  exact (no_adjacent_item_app2_l _ _ _ Hadj).
Qed.

Local Lemma ilist_ok_head_pop :
  forall n out,
    ilist_ok (n :: out)%list = true -> plain_item n = true ->
    hd_str out = false.
Proof.
  intros n out H Hp. unfold ilist_ok in H.
  apply andb_true_iff in H as [_ Hadj].
  destruct out as [|m out']; [reflexivity|].
  cbn [List.rev] in Hadj. rewrite <- app_assoc in Hadj. cbn [app] in Hadj.
  pose proof (no_adjacent_item_app2_pair _ _ _ Hadj) as Hc.
  cbn [hd_str]. destruct (plain_item m); [|reflexivity].
  rewrite Hp in Hc. discriminate.
Qed.

Local Lemma opop_str_ok :
  forall o,
    oscope_ok o = true ->
    oscope_ok (snd (opop_str o)) = true
    /\ starts_str (ocur (snd (opop_str o))) = false.
Proof.
  intros [out stk word] H. unfold opop_str, ocur; cbn [os_out os_stk].
  destruct stk as [|f fs].
  - destruct out as [|[[a [|p ps] i]|ma] rest]; cbn [snd os_out os_stk];
      try (split; [exact H | reflexivity]).
    destruct i; cbn [snd os_out os_stk];
      try (split; [exact H | reflexivity]).
    unfold oscope_ok in H |- *; cbn [os_out os_stk frames_ok] in H |- *.
    rewrite andb_true_r in H |- *.
    split; [exact (ilist_ok_tail _ _ H)|].
    rewrite <- hd_str_is_starts_str.
    exact (ilist_ok_head_pop _ _ H eq_refl).
  - destruct f as [kind marked fopen fout];
      cbn [fr_out fr_kind fr_marked fr_open].
    destruct fout as [|[[a [|p ps] i]|ma] rest];
      cbn [snd os_out os_stk fr_out];
      try (split; [exact H | reflexivity]).
    destruct i; cbn [snd os_out os_stk fr_out];
      try (split; [exact H | reflexivity]).
    unfold oscope_ok in H |- *;
      cbn [os_out os_stk frames_ok forallb fr_out] in H |- *.
    apply andb_true_iff in H as [Hb H].
    apply andb_true_iff in H as [Hf Hs].
    rewrite Hb, Hs, andb_true_r, andb_true_l.
    split; [exact (ilist_ok_tail _ _ Hf)|].
    rewrite <- hd_str_is_starts_str.
    exact (ilist_ok_head_pop _ _ Hf eq_refl).
Qed.

Local Lemma bflat_ok :
  forall kids txt o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    wf_inlines kids = true ->
    oscope_ok (snd (bflat kids txt o)) = true
    /\ starts_str (ocur (snd (bflat kids txt o))) = false.
Proof.
  induction kids as [|n kids IH]; intros txt o Ho Hs Hk;
    cbn [bflat]; [split; assumption|].
  unfold wf_inlines in Hk. apply andb_true_iff in Hk as [Hall Hadj].
  cbn [forallb] in Hall. apply andb_true_iff in Hall as [Hn Hall].
  assert (Hrest : wf_inlines kids = true).
  { unfold wf_inlines. rewrite Hall. cbn [andb].
    destruct kids as [|m kids']; [reflexivity|].
    cbn [no_adjacent_str] in Hadj. apply andb_true_iff in Hadj as [_ Hadj].
    exact Hadj. }
  assert (Hemit : forall p attrs x,
             n = Node p attrs x -> plain_str n = false ->
             oscope_ok (oemit n (flush_text txt o)) = true
             /\ starts_str (ocur (oemit n (flush_text txt o))) = false).
  { intros p attrs x En Hp.
    pose proof (iscan_wf_flush txt o Ho Hs) as Hf.
    split.
    - apply oscope_ok_emit; [exact Hf | exact Hn | rewrite Hp; reflexivity].
    - rewrite ocur_emit, <- hd_str_is_starts_str. cbn [hd_str]. exact Hp. }
  destruct n as [p [|q qs] x].
  - destruct x;
      try (destruct (Hemit p [] _ eq_refl eq_refl) as [H1 H2];
           apply IH; assumption).
    apply IH; assumption.
  - destruct (Hemit p (q :: qs) _ eq_refl eq_refl) as [H1 H2].
    apply IH; assumption.
Qed.

Local Lemma bsplit_nl_ok :
  forall s txt o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    oscope_ok (snd (bsplit_nl s txt o)) = true
    /\ starts_str (ocur (snd (bsplit_nl s txt o))) = false.
Proof.
  induction s as [|c s IH]; intros txt o Ho Hs; cbn [bsplit_nl];
    [split; assumption|].
  destruct (Ascii.eqb c nl_char); [|apply IH; assumption].
  apply IH.
  - apply oscope_ok_emit;
      [apply iscan_wf_flush; assumption | reflexivity | apply andb_false_l].
  - rewrite ocur_emit. reflexivity.
Qed.

(* The ordinary reading a `](` opens: the label goes into a fresh frame,
   which is empty, so the head condition holds however the label ends. *)
Local Lemma idest_open_wf :
  forall kids image open o,
    oscope_ok o = true -> wf_inlines kids = true ->
    iscan_wf (idest_open kids image open o) = true.
Proof.
  intros kids image open o Ho Hk. unfold idest_open; tred.
  destruct (bflat_ok kids EmptyString (dpush image open o)
              (oscope_ok_dpush image open o Ho) eq_refl Hk) as [H1 H2].
  destruct (bflat kids EmptyString (dpush image open o)) as [txt o1];
    cbn [snd] in H1, H2.
  apply iscan_wf_text; assumption.
Qed.

Local Lemma bclosed_lit_ok :
  forall kids image o,
    oscope_ok o = true -> wf_inlines kids = true ->
    oscope_ok (snd (bclosed_lit kids image o)) = true
    /\ starts_str (ocur (snd (bclosed_lit kids image o))) = false.
Proof.
  intros kids image o Ho Hk. unfold bclosed_lit.
  destruct (opop_str_ok o Ho) as [H1 H2].
  destruct (opop_str o) as [pre o1]; cbn [snd] in H1, H2 |- *; tred.
  pose proof (bflat_ok kids (pre ++ bracket_open image)%string o1 H1 H2 Hk)
    as Hb.
  destruct (bflat kids (pre ++ bracket_open image)%string o1) as [txt o2];
    cbn [snd] in Hb |- *. exact Hb.
Qed.

Local Lemma bref_lit_ok :
  forall kids image label o,
    oscope_ok o = true -> wf_inlines kids = true ->
    oscope_ok (snd (bref_lit kids image label o)) = true
    /\ starts_str (ocur (snd (bref_lit kids image label o))) = false.
Proof.
  intros kids image label o Ho Hk. unfold bref_lit.
  pose proof (bclosed_lit_ok kids image o Ho Hk) as Hc.
  destruct (bclosed_lit kids image o). exact Hc.
Qed.

Local Lemma bspan_lit_ok :
  forall kids image src o,
    oscope_ok o = true -> wf_inlines kids = true ->
    oscope_ok (snd (bspan_lit kids image src o)) = true
    /\ starts_str (ocur (snd (bspan_lit kids image src o))) = false.
Proof.
  intros kids image src o Ho Hk. unfold bspan_lit.
  pose proof (bclosed_lit_ok kids image o Ho Hk) as Hc.
  destruct (bclosed_lit kids image o) as [txt o']; cbn [snd] in Hc |- *.
  destruct Hc as [H1 H2]. apply bsplit_nl_ok; assumption.
Qed.

Local Lemma battr_lit_ok :
  forall src txt o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    oscope_ok (snd (battr_lit src txt o)) = true
    /\ starts_str (ocur (snd (battr_lit src txt o))) = false.
Proof.
  intros src txt o Ho Hs. unfold battr_lit. apply bsplit_nl_ok; assumption.
Qed.

(* A marked open holds the state it was in: the push waits for the byte
   after the token, and it is that byte's arm that owes the scope
   condition. *)
Local Lemma idelim_marked_wf :
  forall k extra txt o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (idelim_marked k extra txt o) = true.
Proof.
  intros k extra txt o Ho Hs. unfold idelim_marked.
  cbn [iscan_wf]. rewrite Ho, hd_str_is_starts_str, Hs. reflexivity.
Qed.

(* And the push, which is exactly what `oscope_ok_push_at` covers. *)
Local Lemma oopen_marked_wf :
  forall k cm txt o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    oscope_ok (oopen_marked k cm txt o) = true
    /\ starts_str (ocur (oopen_marked k cm txt o)) = false.
Proof.
  intros k cm txt o Ho Hs. unfold oopen_marked.
  split; [apply oscope_ok_push_at, iscan_wf_flush; assumption | reflexivity].
Qed.

Local Lemma idelim_open_marked_wf :
  forall k cm txt o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (idelim_open_marked k cm txt o) = true.
Proof.
  intros k cm txt o Ho Hs. unfold idelim_open_marked.
  destruct (oopen_marked_wf k cm txt o Ho Hs) as [H1 H2].
  apply iscan_wf_text; assumption.
Qed.

(* The non-breaking space is a node, not text, so the branch that emits
   one restores the head condition rather than owing it; the branch that
   puts the backslash back does not touch the scopes at all. *)
Local Lemma iescws_resolve_wf :
  forall ws txt prev o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    let '(_, _, o') := iescws_resolve ws txt prev o in
    oscope_ok o' = true /\ starts_str (ocur o') = false.
Proof.
  intros [|c ws] txt prev o Ho Hs; cbn [iescws_resolve tval]; [split; assumption|].
  destruct (Ascii.eqb c " "%char); [|split; assumption].
  pose proof (iscan_wf_flush txt o Ho Hs) as Hf.
  split; [apply oscope_ok_emit; [exact Hf|reflexivity|apply andb_false_l]|].
  rewrite ocur_emit. reflexivity.
Qed.

(* Popping a frame keeps both halves of the scope invariant: the bottom
   scope is untouched and the rest of the stack was already well-formed. *)
Local Lemma oscope_ok_bunpush :
  forall o image open o',
    oscope_ok o = true -> bunpush o = Some (image, open, o') ->
    oscope_ok o' = true.
Proof.
  intros [out [|[[k|im|im|nm] m op [|n l]] stk] word] image open o' Ho H;
    try discriminate.
  injection H as _ _ <-. unfold oscope_ok in *;
    cbn [os_out os_stk frames_ok forallb] in *.
  apply andb_true_iff in Ho as [H1 H2]. apply andb_true_iff in H2 as [_ H3].
  rewrite H1, H3. reflexivity.
Qed.

Local Lemma ilead_wf :
  forall c txt prev o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (ilead c txt prev o) = true.
Proof.
  intros c txt prev o Ho Hs. unfold ilead.
  rewrite ?remember_word_start_semantic.
  destruct (is_bslash c); [apply (iscan_wf_text true txt prev o Ho Hs)|].
  destruct (is_tick c);
    [cbn [iscan_wf]; apply (iscan_wf_flush txt o Ho Hs)|].
  destruct (Ascii.eqb c dollar);
    [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity|].
  destruct (Ascii.eqb c period);
    [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity|].
  destruct (Ascii.eqb c hyphen);
    [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity|].
  destruct (Ascii.eqb c lbrace);
    [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity|].
  destruct (Ascii.eqb c bang);
    [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity|].
  destruct (Ascii.eqb c lt);
    [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity|].
  destruct (Ascii.eqb c ":"%char);
    [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity|].
  destruct (Ascii.eqb c lbrack).
  { assert (Hb : iscan_wf (IText false EmptyString (Some lbrack)
                  (bpush false (flush_text_at txt o))) = true)
      by (apply iscan_wf_text;
            [apply oscope_ok_bpush, iscan_wf_flush; assumption | reflexivity]).
    destruct (note_pos txt prev && wikilinks_enabled)%bool; [|exact Hb].
    destruct (bunpush o) as [[[image open] o']|] eqn:Eu; [|exact Hb].
    cbn [iscan_wf]. exact (oscope_ok_bunpush o image open o' Ho Eu). }
  destruct (Ascii.eqb c rbrack).
  { tred. destruct (if tags_enabled then tag_close (flush_text_at txt o) else None)
      as [[[[kids name] open] o']|] eqn:Et;
      [|cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity].
    destruct tags_enabled; [|discriminate Et].
    pose proof (tag_close_ok _ kids name open o' (iscan_wf_flush txt o Ho Hs) Et)
      as Hk.
    apply andb_true_iff in Hk as [Ho' Hk].
    unfold wf_inlines in Hk. apply andb_true_iff in Hk as [Hall Hadj].
    apply iscan_wf_text; [|rewrite ocur_emit; reflexivity].
    apply oscope_ok_emit; [exact Ho'| |reflexivity].
    rewrite imk_semantic. cbn [node_contents mk wf_inline].
    rewrite wf_ils_forallb, Hall, Hadj. reflexivity. }
  destruct (Ascii.eqb c hat && note_pos txt prev && notes_enabled)%bool;
    [destruct (bunpush o) as [[[image open] o']|] eqn:Eu;
       [cbn [iscan_wf]; exact (oscope_ok_bunpush o image open o' Ho Eu)|]|];
    destruct (dstyle_of c);
    cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity.
Qed.

Local Lemma idelim_done_wf :
  forall k txt bef marker next o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (idelim_done k txt bef marker next o) = true.
Proof.
  intros k txt bef marker next o Ho Hs. unfold idelim_done.
  destruct (dbare k bef && negb marker && nonspace_at next)%bool;
    [|apply iscan_wf_text; assumption].
  pose proof (iscan_wf_flush txt o Ho Hs) as Hf.
  apply iscan_wf_text; [apply oscope_ok_push, Hf | reflexivity].
Qed.

Local Lemma idelim_resolve_wf :
  forall k txt bef marker next o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (idelim_resolve k txt bef marker next o) = true.
Proof.
  intros k txt bef marker next o Ho Hs.
  unfold idelim_resolve; rewrite !oclose_guard; tred.
  sem_flush.
  destruct (nonspace_at bef || marker)%bool; [|apply idelim_done_wf; assumption].
  pose proof (iscan_wf_flush txt o Ho Hs) as Hf.
  destruct (sclose k marker (flush_text txt o)) as [o'|] eqn:Ec;
    [|destruct (oclose_barred k marker o);
        [apply iscan_wf_text; assumption
        |apply idelim_done_wf; assumption]].
  pose proof (oclose_ok k marker _ o' Hf Ec) as Hc.
  apply andb_true_iff in Hc as [Hc1 Hc2]. apply negb_true_iff in Hc2.
  apply iscan_wf_text; assumption.
Qed.

(* The span mode's step, shared by `istep` and the line break: both feed
   the machine one byte, and both dispositions -- literal fallback, or
   the `Span` the close builds -- preserve the invariant. *)
(* Flushing the decayed `!` keeps the scopes well-formed: the pop is the
   same one `bclosed_lit` does, so the text it re-emits is one `Str` and
   the tip it lands on is not one. *)
Local Lemma ospan_bang_ok :
  forall image o,
    oscope_ok o = true -> oscope_ok (ospan_bang image o) = true.
Proof.
  intros image o Ho. unfold ospan_bang. destruct image; [|exact Ho].
  destruct (opop_str_ok o Ho) as [H1 H2].
  destruct (opop_str o) as [pre o1]; cbn [snd] in H1, H2.
  apply iscan_wf_flush; assumption.
Qed.

(* Nothing has to be said about what attachment does to a scope:
   `iattr_mark` only pushes an item, and `oresolve` settles it once the
   scope is complete. *)
Local Lemma iattr_mark_wf :
  forall src a txt o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (iattr_mark src a txt o) = true.
Proof.
  intros src a txt o Ho Hs. unfold iattr_mark.
  change (@flush_text_at semantic_pos semantic_inline_cursor) with flush_text.
  apply iscan_wf_text.
  - apply oscope_ok_mark, iscan_wf_flush; assumption.
  - rewrite ocur_mark. reflexivity.
Qed.

Local Lemma islice_end_wf :
  forall st, iscan_wf st = true -> iscan_wf (islice_end st) = true.
Proof.
  induction st; intros H; try exact H.
  - destruct esc; exact H.
  - cbn [iscan_wf] in H. apply andb_true_iff in H as [_ Hsh].
    apply IHst, Hsh.
Qed.

Local Lemma iattr_feed_wf :
  forall c p src txt prev sh o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf sh = true ->
    iscan_wf (iattr_feed c p src txt prev sh o) = true.
Proof.
  intros c p src txt prev sh o Ho Hs Hsh. unfold iattr_feed.
  pose proof (islice_end_wf sh Hsh) as Hsl.
  destruct (ap_failed (astep p c)); [exact Hsh|].
  destruct (ap_done (astep p c));
    [apply iattr_mark_wf; [exact Ho | exact Hs]|].
  cbn [iscan_wf]. rewrite Ho, hd_str_is_starts_str, Hs, Hsl. reflexivity.
Qed.

Local Lemma ispan_feed_wf :
  forall c kids image open p src o,
    oscope_ok o = true -> wf_inlines kids = true ->
    iscan_wf (ispan_feed c kids image open p src o) = true.
Proof.
  intros c kids image open p src o Ho Hk. unfold ispan_feed. tred.
  destruct (ap_failed (astep p c)).
  - destruct (bspan_lit_ok kids image src o Ho Hk) as [H1 H2].
    destruct (bspan_lit kids image src o) as [txt o']; cbn [snd] in H1, H2.
    apply ilead_wf; assumption.
  - destruct (ap_done (astep p c));
      [|cbn [iscan_wf]; rewrite Ho, Hk; reflexivity].
    (* `starts_str` matches on the node's attributes before its payload,
       so the list has to be forced even though a `Span` is not a `Str`
       either way *)
    apply iscan_wf_text;
      [|rewrite ocur_emit; destruct (ap_attrs (astep p c)); reflexivity].
    apply oscope_ok_emit;
      [apply ospan_bang_ok, Ho| |destruct (ap_attrs (astep p c)); reflexivity].
    unfold wf_inlines in Hk. apply andb_true_iff in Hk as [Hall Hadj].
    rewrite ?add_inline_role_semantic.
    cbn [node_contents]. cbn [wf_inline].
    rewrite wf_ils_forallb, Hall, Hadj. reflexivity.
Qed.

Local Lemma iscan_wf_step_at :
  forall attrs_enabled c st,
    iscan_wf st = true -> iscan_wf (istep_at attrs_enabled c st) = true.
Proof.
  intros attrs_enabled c st. revert attrs_enabled c.
  induction st as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|mt me ms mx ml msh IHmsh mo|mct mcs mcx mcl mcsh IHmcsh mco|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img sopen sp ssrc sob|ap asrc atxt aprev ash IHash aob|kids img ropen label ob|nesc nimg nlab nopen nob|wesc wrb wimg wreg wopen wob|kids img dopen esc depth dst sh IHsh ob|asrc atxt aob|salias stxt sob IHsob o|rspec rtxt rob];
    intros attrs_enabled c H;
    cbn [istep_at];
    try (cbn [iscan_wf] in H; apply andb_true_iff in H as [Ho Hs];
         apply negb_true_iff in Hs;
         rewrite hd_str_is_starts_str in Hs); tred.
  - destruct (is_ws c);
      [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity
      |apply iscan_wf_text; [exact Ho | exact Hs]].
  - apply ilead_wf; [exact Ho | exact Hs].
  - destruct (is_ws c);
      [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity|].
    pose proof (iescws_resolve_wf ews etxt eprev eob Ho Hs) as Hr.
    destruct (iescws_resolve ews etxt eprev eob) as [[t p] o'].
    destruct Hr as [Ho' Hs']. apply ilead_wf; assumption.
  - unfold ibrace_step_at.
    destruct (dstyle_of c); [apply idelim_marked_wf; assumption|].
    destruct attrs_enabled.
    { apply iattr_feed_wf; [exact Ho|exact Hs|].
      apply ilead_wf; assumption. }
    destruct (battr_lit_ok EmptyString txt o Ho Hs) as [H1 H2].
    destruct (battr_lit EmptyString txt o) as [t o']; cbn [snd] in H1, H2.
    apply ilead_wf; assumption.
  - destruct (Nat.ltb (S seen) (dwidth k)).
    { destruct (Ascii.eqb c (dchar k));
        [|apply ilead_wf; assumption].
      destruct mrk;
        [apply idelim_marked_wf; assumption
        |cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity]; tred. }
    destruct mrk.
    { destruct (oopen_marked_wf k (Ascii.eqb c rbrace) txt o Ho Hs) as [H1 H2].
      apply ilead_wf; assumption. }
    destruct (Ascii.eqb c rbrace); [apply idelim_resolve_wf; assumption|].
    pose proof (idelim_resolve_wf k txt cc false (Some c) o Ho Hs) as Hr.
    destruct (idelim_resolve k txt cc false (Some c) o)
      as [[] txt' prev' o'|? ? ? ?|? ? ?|? ? ? ? ? ?|? ? ?|? ? ? ? ?|? ? ? ?|? ? ? ? ? ? ?|? ? ? ? ? ?|? ? ? ?|? ? ? ?|? ? ?|? ?|? ? ? ? ?|? ? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ? ? ?|? ? ? ? ? ?|? ? ?|? ? ?|? ? ?]; try exact Hr.
    cbn [iscan_wf] in Hr; tred. apply andb_true_iff in Hr as [Ho' Hs'].
    apply negb_true_iff in Hs'. rewrite hd_str_is_starts_str in Hs'.
    apply ilead_wf; assumption.
  - cbn [iscan_wf] in H |- *; tred. destruct (is_tick c); exact H.
  - cbn [iscan_wf] in H |- *. destruct (is_tick c); [exact H|].
    destruct (Nat.eqb run n); [|exact H].
    destruct vk as [|sty|prefix].
    + destruct (Ascii.eqb c lbrace && vkind_verb VVerb)%bool;
        [exact H|].
      rewrite ?imk_semantic. apply ilead_wf.
      * apply oscope_ok_emit;
          [exact H | apply wf_inline_vnode
          | rewrite plain_str_vnode; apply andb_false_l].
      * rewrite ocur_emit. apply starts_str_vnode.
    + destruct sty.
      * rewrite andb_false_r, ?imk_semantic. apply ilead_wf.
        -- apply oscope_ok_emit;
             [exact H | apply wf_inline_vnode
             | rewrite plain_str_vnode; apply andb_false_l].
        -- rewrite ocur_emit. apply starts_str_vnode.
      * destruct (Ascii.eqb c dollar && dollar_math_enabled)%bool.
        -- rewrite ?imk_semantic. apply iscan_wf_text.
           ++ apply oscope_ok_emit;
                [exact H|reflexivity|apply andb_false_l].
           ++ rewrite ocur_emit. reflexivity.
        -- rewrite ?imk_semantic. apply ilead_wf.
           ++ apply oscope_ok_emit;
                [exact H|reflexivity|apply andb_false_l].
           ++ rewrite ocur_emit. reflexivity.
    + destruct (Ascii.eqb c dollar).
      * destruct (opop_str_ok o H) as [Ho' Hs'].
        destruct (opop_str o) as [pre o']; cbn [fst snd] in Ho', Hs' |- *.
        apply iscan_wf_text.
        -- apply oscope_ok_emit;
             [sem_flush; apply iscan_wf_flush; assumption
             |reflexivity|apply andb_false_l].
        -- rewrite ocur_emit. reflexivity.
      * destruct (Ascii.eqb c lbrace); [exact H|].
        rewrite ?imk_semantic. apply ilead_wf.
        -- apply oscope_ok_emit;
             [exact H|reflexivity|apply andb_false_l].
        -- rewrite ocur_emit. reflexivity.
  - (* the dollars either grow, open a span, or become text *)
    unfold idollar_step. destruct (Ascii.eqb c dollar);
      [destruct dtwo;
         (cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity)|].
    destruct (is_tick c && math_enabled)%bool;
      [cbn [iscan_wf]; sem_flush; apply iscan_wf_flush; assumption
      |].
    destruct (is_tick c && dollar_math_enabled && negb dtwo)%bool;
      [cbn [iscan_wf]; sem_flush; apply iscan_wf_flush; assumption
      |].
    destruct (dollar_math_enabled &&
      (negb dtwo ||
       negb (match dprev with Some p => Ascii.eqb p dollar | None => false end))
      && (dtwo || (negb (is_ws_nl c) && negb (is_tick c))))%bool.
    + cbn [iscan_wf]. rewrite Ho, hd_str_is_starts_str, Hs.
      cbn. apply ilead_wf; assumption.
    + apply ilead_wf; assumption.
  - (* dollar-delimited math candidate *)
    assert (Hshadow : iscan_wf msh = true)
      by (cbn [iscan_wf] in H; apply andb_true_iff in H as [_ H]; exact H).
    pose proof (IHmsh attrs_enabled c Hshadow) as Hstep.
    cbn [iscan_wf] in H. rewrite Hshadow in H.
    destruct me; [|destruct (Ascii.eqb c dollar)];
      cbn [iscan_wf]; rewrite Hstep; exact H.
  - (* possible closing dollar *)
    cbn [iscan_wf] in H.
    apply andb_true_iff in H as [Hbase Hshadow].
    apply andb_true_iff in Hbase as [Ho Hs].
    rewrite hd_str_is_starts_str in Hs.
    pose proof (IHmcsh attrs_enabled c Hshadow) as Hstep.
    destruct mct.
    + destruct mcl as [p|];
        [destruct (Ascii.eqb p nl_char); destruct (Ascii.eqb c dollar)
        |destruct (Ascii.eqb c dollar)];
        try (cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hstep;
             apply negb_true_iff in Hs; rewrite Hs; reflexivity).
      apply ilead_wf.
      * apply oscope_ok_emit;
          [sem_flush; apply iscan_wf_flush;
             [exact Ho|apply negb_true_iff in Hs; exact Hs]
          |reflexivity|reflexivity].
      * rewrite ocur_emit. reflexivity.
    + destruct (match mcl with Some p => negb (is_ws_nl p)
                | None => false end
        && negb ((Nat.leb 48 (nat_of_ascii c))
                 && Nat.leb (nat_of_ascii c) 57))%bool;
        [|exact Hstep].
      apply ilead_wf.
      * apply oscope_ok_emit;
          [sem_flush; apply iscan_wf_flush;
             [exact Ho|apply negb_true_iff in Hs; exact Hs]
          |reflexivity|reflexivity].
      * rewrite ocur_emit. reflexivity.
  - (* and the periods either grow, complete an ellipsis, or become text;
       the ellipsis goes into the buffer, so the head condition is the
       one the state already carried *)
    unfold iperiod_step. destruct (Ascii.eqb c period);
      [destruct ptwo;
         (cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity)
      |apply ilead_wf; assumption].
  - (* a hyphen run keeps its buffer, and the close it may hand to the
       delete row is `idelim_resolve`'s business *)
    unfold idash_step. destruct (Ascii.eqb c hyphen);
      [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity|].
    destruct (Ascii.eqb c rbrace); [|apply ilead_wf; assumption].
    destruct (dstyle_of hyphen) as [k|];
      [destruct (Nat.leb (dwidth k) dn);
         [apply idelim_resolve_wf; assumption|]|];
      (apply iscan_wf_text; assumption).
  - unfold ibang_step. destruct (Ascii.eqb c lbrack);
      [apply iscan_wf_text;
         [apply oscope_ok_bpush, iscan_wf_flush; assumption | reflexivity]
      |apply ilead_wf; assumption].
  - (* the byte after a `]`: either it closes the bracket, and the three
       constructs inherit `bclose`'s obligation, or the `]` is text *)
    destruct ((Ascii.eqb c lparen || Ascii.eqb c lbrack
               || (Ascii.eqb c lbrace && attrs_enabled))%bool);
      [|apply ilead_wf; assumption].
    sem_flush.
    destruct (bclose (flush_text cltxt clob))
      as [[[[kids image] open] o']|] eqn:Eb;
      [|apply ilead_wf; assumption].
    pose proof (bclose_ok _ _ _ _ _ (iscan_wf_flush cltxt clob Ho Hs) Eb) as Hb.
    apply andb_true_iff in Hb as [Ho' Hk].
    destruct (Ascii.eqb c lparen);
      [cbn [iscan_wf];
       rewrite Ho', Hk, (idest_open_wf kids image open o' Ho' Hk);
       reflexivity|].
    destruct (Ascii.eqb c lbrack); cbn [iscan_wf]; rewrite Ho', Hk;
      reflexivity.
  - cbn [iscan_wf] in H. apply andb_true_iff in H as [Ho Hk].
    apply ispan_feed_wf; assumption.
  - cbn [iscan_wf] in H. apply andb_true_iff in H as [Hb Hsh].
    apply andb_true_iff in Hb as [Ho Hs].
    apply negb_true_iff in Hs. rewrite hd_str_is_starts_str in Hs.
    destruct (ap_failed (astep ap c)).
    + apply IHash, Hsh.
    + apply iattr_feed_wf; [exact Ho|exact Hs|apply IHash; exact Hsh].
  - cbn [iscan_wf] in H. apply andb_true_iff in H as [Ho Hk].
    destruct (Ascii.eqb c rbrack); [|cbn [iscan_wf]; rewrite Ho, Hk; reflexivity].
    apply iscan_wf_text; [|rewrite ocur_emit; destruct img; reflexivity].
    apply oscope_ok_emit; [exact Ho| |destruct img; reflexivity].
    unfold wf_inlines in Hk. apply andb_true_iff in Hk as [Hall Hadj].
    cbn [node_contents mk]. apply wf_inline_bnode;
      [rewrite wf_ils_forallb; exact Hall | exact Hadj].
  - (* the label discards its brackets, so the only obligation is the
       scope the emitted node lands in *)
    unfold inote_step. destruct nesc;
      [cbn [iscan_wf]; exact H|].
    destruct (is_bslash c); [cbn [iscan_wf]; exact H|].
    destruct (Ascii.eqb c rbrack); [|cbn [iscan_wf]; exact H].
    cbn [iscan_wf] in H |- *.
    apply (iscan_wf_text false EmptyString (Some rbrack));
      [apply oscope_ok_emit;
         [apply ospan_bang_ok, H | reflexivity | apply andb_false_l]
      |rewrite ocur_emit; reflexivity].
  - (* the region is source, so until the closer the only obligation is
       the scope the candidate took its bracket back from; an empty
       target is the bracket modes' literal, reabsorbing as they do *)
    cbn [iscan_wf] in H. unfold iwiki_step.
    destruct wesc; [cbn [iscan_wf]; exact H|].
    destruct (wrb && Ascii.eqb c rbrack)%bool.
    + unfold iwiki_close. tred. destruct (wiki_split wreg) as [[|x t] al].
      * unfold bwiki_lit. destruct (opop_str_ok wob H) as [H1 H2].
        destruct (opop_str wob) as [pre o1]; cbn [snd] in H1, H2.
        apply iscan_wf_text; assumption.
      * apply (iscan_wf_text false EmptyString (Some rbrack));
          [apply oscope_ok_emit; [exact H | reflexivity | apply andb_false_l]
          |rewrite ocur_emit; reflexivity].
    + destruct (is_bslash c); [cbn [iscan_wf]; exact H|].
      destruct (Ascii.eqb c rbrack); cbn [iscan_wf]; exact H.
  - (* both readings advance, so both obligations are carried; only the
       balanced close discharges one by dropping it *)
    cbn [iscan_wf] in H. apply andb_true_iff in H as [Hd0 Hsh].
    pose proof (IHsh attrs_enabled c Hsh) as Hsh'.
    assert (Hd : forall e d t,
               iscan_wf
                 (IDest kids img dopen e d t
                    (istep_at attrs_enabled c sh) ob) = true)
      by (intros; cbn [iscan_wf]; rewrite Hd0, Hsh'; reflexivity).
    destruct esc; [apply Hd|].
    destruct (is_bslash c); [apply Hd|].
    destruct (Ascii.eqb c lparen); [apply Hd|].
    destruct (Ascii.eqb c rparen); [|apply Hd].
    destruct depth as [|d]; [|apply Hd].
    apply andb_true_iff in Hd0 as [Ho Hk].
    (* the link or image node is the one thing the bracket modes build *)
    apply iscan_wf_text; [|rewrite ocur_emit; destruct img; reflexivity].
    apply oscope_ok_emit; [exact Ho| |destruct img; reflexivity].
    unfold wf_inlines in Hk. apply andb_true_iff in Hk as [Hall Hadj].
    cbn [node_contents mk]. apply wf_inline_bnode;
      [rewrite wf_ils_forallb; exact Hall | exact Hadj].
  (* a candidate either emits its link node over the flushed text, or
     hands the text back to `ilead` with the `<` on the end *)
  - unfold iauto_step. tred.
    destruct (Ascii.eqb c gt && auto_body_ok asrc && auto_kind_ok asrc)%bool.
    { apply iscan_wf_text;
        [apply oscope_ok_emit;
           [apply iscan_wf_flush; assumption
           |unfold auto_node; destruct (auto_email asrc); reflexivity
           |unfold auto_node; destruct (auto_email asrc); reflexivity]
        |rewrite ocur_emit; unfold auto_node;
         destruct (auto_email asrc); reflexivity]. }
    destruct (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt)%bool;
      [apply ilead_wf; assumption
      |cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity].
  - unfold isymbol_step. tred.
    cbn [iscan_wf] in H. apply andb_true_iff in H as [Hp Hsh].
    apply andb_true_iff in Hp as [Ho Hs].
    apply negb_true_iff in Hs. rewrite hd_str_is_starts_str in Hs.
    destruct (symbol_char c).
    + cbn [iscan_wf]. rewrite Ho, hd_str_is_starts_str, Hs,
        (IHsob attrs_enabled c Hsh). reflexivity.
    + destruct (Ascii.eqb c ":"%char && nonempty_str salias)%bool.
      * apply iscan_wf_text.
        -- apply oscope_ok_emit;
             [apply iscan_wf_flush; assumption | reflexivity | apply andb_false_l].
        -- rewrite ocur_emit. reflexivity.
      * destruct (Ascii.eqb c lbrack && nonempty_str salias && tags_enabled && tag_may_follow stxt)%bool;
          [|apply IHsob, Hsh].
        apply iscan_wf_text; [|reflexivity].
        apply oscope_ok_tag_push, iscan_wf_flush; assumption.
  (* the node the spec decides is not a `Str` either way, so the scope it
     lands in carries the head condition its own emission establishes *)
  - cbn [iscan_wf] in H. unfold iraw_step_at. tred.
    assert (Hv : oscope_ok (oemit (mk (Verbatim rtxt)) rob) = true /\
                 starts_str (ocur (oemit (mk (Verbatim rtxt)) rob)) = false).
    { split;
        [apply oscope_ok_emit; [exact H | reflexivity | apply andb_false_l]
        |rewrite ocur_emit; reflexivity]. }
    destruct Hv as [Hvo Hvs].
    destruct (Ascii.eqb c rbrace && raw_spec_ok rspec)%bool.
    { destruct raw_inline_enabled.
      - apply iscan_wf_text;
          [apply oscope_ok_emit; [exact H | reflexivity | apply andb_false_l]
          |rewrite ocur_emit; reflexivity].
      - apply ilead_wf; assumption. }
    destruct rspec as [|x rspec']; cbn [tnonempty nonempty_str].
    + destruct (negb (Ascii.eqb c eqchar)); [|cbn [iscan_wf]; exact H].
      unfold ibrace_step_at. destruct (dstyle_of c);
        [apply idelim_marked_wf; assumption|].
      destruct attrs_enabled.
      { apply iattr_feed_wf; [exact Hvo|exact Hvs|].
        apply ilead_wf; assumption. }
      destruct (battr_lit_ok EmptyString ""
                  (oemit (mk (Verbatim rtxt)) rob) Hvo Hvs) as [H1 H2].
      destruct (battr_lit EmptyString "" (oemit (mk (Verbatim rtxt)) rob))
        as [t o']; cbn [snd] in H1, H2.
      apply ilead_wf; assumption.
    + destruct (Ascii.eqb c rbrace || raw_stop c)%bool;
        [apply ilead_wf; assumption | cbn [iscan_wf]; exact H].
Qed.

Local Lemma iscan_wf_step :
  forall c st, iscan_wf st = true -> iscan_wf (istep c st) = true.
Proof.
  intros c st H. unfold istep. apply iscan_wf_step_at, H.
Qed.

Local Lemma iscan_wf_str :
  forall s st, iscan_wf st = true -> iscan_wf (iscan_str s st) = true.
Proof.
  induction s as [|c rest IH]; intros st H; [exact H|].
  cbn [iscan_str]. apply IH, iscan_wf_step, H.
Qed.

Local Lemma wf_inlines_of_rlist :
  forall out, rlist_ok out = true -> wf_inlines (List.rev out) = true.
Proof.
  intros out H. unfold rlist_ok in H. unfold wf_inlines.
  apply andb_true_iff in H as [Hall Hadj].
  rewrite forallb_rev, Hall, Hadj. reflexivity.
Qed.

(* Flattening abandons every open scope, splicing each into the level
   below with its opener as text -- the same `oapp` merge as closing,
   repeated to the bottom. *)
Local Lemma ilist_ok_oflatten :
  forall stk pend bottom,
    frames_ok stk = true -> ilist_ok pend = true -> ilist_ok bottom = true ->
    ilist_ok (oflatten pend stk bottom) = true.
Proof.
  induction stk as [|f stk IH]; intros pend bottom Hs Hp Hb; cbn [oflatten].
  - apply ilist_ok_oapp; assumption.
  - apply IH; [exact (frames_ok_tail f stk Hs) | | exact Hb].
    apply ilist_ok_oapp;
      [apply ilist_ok_oapp; [exact Hp | exact (frames_ok_head f stk Hs)]
      |apply ilist_ok_src].
Qed.

Local Lemma ilist_ok_oitems_of :
  forall o, oscope_ok o = true -> ilist_ok (oitems_of o) = true.
Proof.
  intros o H. apply andb_true_iff in H as [Hb Hs].
  rewrite oitems_of_spec.
  apply ilist_ok_oflatten; [exact Hs | reflexivity | exact Hb].
Qed.

Local Lemma rlist_ok_ofinish :
  forall o, oscope_ok o = true -> rlist_ok (ofinish o) = true.
Proof.
  intros o H. unfold ofinish. apply oresolve_ok, ilist_ok_oitems_of, H.
Qed.

Local Lemma iscan_wf_resolve :
  forall st, iscan_wf st = true -> iscan_wf (iresolve st) = true.
Proof.
  intros [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|mt me ms mx ml msh mo|mct mcs mcx mcl mcsh mco|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img sopen sp ssrc sob|ap asrc atxt aprev ash aob|kids img ropen label ob|nesc nimg nlab nopen nob|wesc wrb wimg wreg wopen wob|kids img dopen esc depth dst sh ob|asrc atxt aob|salias stxt sob|rspec rtxt rob] H;
    cbn [iresolve]; try exact H;
    cbn [iscan_wf] in H; apply andb_true_iff in H as [Ho Hs].
  (* `IBrace` is closed by `exact H` above: the invariant does not look
     at the text buffer, and resolving a brace only moves a byte into
     it, which is `IClosed`'s case too.  `IDelim` is the one that can
     close a scope. *)
  - apply negb_true_iff in Hs; rewrite hd_str_is_starts_str in Hs.
    destruct (Nat.ltb (S seen) (dwidth k));
      [apply iscan_wf_text; assumption|].
    destruct mrk;
      [apply idelim_open_marked_wf | apply idelim_resolve_wf]; assumption.
Qed.

Local Lemma iscan_wf_ostate_flat :
  forall st,
    iscan_wf st = true ->
    oscope_ok (ifinish_ostate_flat (iresolve st)) = true.
Proof.
  intros st H. pose proof (iscan_wf_resolve st H) as Hr.
  pose proof (iresolve_resolved st) as Hno.
  destruct (iresolve st) as
    [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|mt me ms mx ml msh mo|mct mcs mcx mcl mcsh mco|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img sopen sp ssrc sob|ap asrc atxt aprev ash aob|kids img ropen label ob|nesc nimg nlab nopen nob|wesc wrb wimg wreg wopen wob|kids img dopen esc depth dst sh ob|asrc atxt aob|salias stxt sob|rspec rtxt rob];
    try contradiction; cbn [ifinish_ostate_flat];
    try (cbn [iscan_wf] in Hr; apply andb_true_iff in Hr as [Ho Hs];
         apply negb_true_iff in Hs; rewrite hd_str_is_starts_str in Hs).
  1,3: unfold iesc_hard; apply oscope_ok_emit;
       [apply iscan_wf_flush; assumption | reflexivity | apply andb_false_l].
  - apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr. rewrite ?imk_semantic.
    apply oscope_ok_emit;
      [exact Hr | apply wf_inline_vnode
      | rewrite plain_str_vnode; apply andb_false_l].
  - cbn [iscan_wf] in Hr. rewrite ?imk_semantic.
    apply oscope_ok_emit;
      [exact Hr | apply wf_inline_vnode
      | rewrite plain_str_vnode; apply andb_false_l].
  - cbn [iscan_wf] in Hr.
    apply andb_true_iff in Hr as [Hb _].
    apply andb_true_iff in Hb as [Ho _]. exact Ho.
  - cbn [iscan_wf] in Hr.
    apply andb_true_iff in Hr as [Hb _].
    apply andb_true_iff in Hb as [Ho _]. exact Ho.
  - cbn [iscan_wf] in Hr. apply andb_true_iff in Hr as [Ho Hk].
    destruct (bspan_lit_ok kids img (tval ssrc) sob Ho Hk) as [H1 H2].
    destruct (bspan_lit kids img (tval ssrc) sob) as [txt o']; cbn [snd] in H1, H2.
    apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr. apply andb_true_iff in Hr as [Hb _].
    apply andb_true_iff in Hb as [Ho Hs].
    apply negb_true_iff in Hs. rewrite hd_str_is_starts_str in Hs.
    destruct (battr_lit_ok (tval asrc) atxt aob Ho Hs) as [H1 H2].
    destruct (battr_lit (tval asrc) atxt aob) as [t o']; cbn [snd] in H1, H2.
    apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr. apply andb_true_iff in Hr as [Ho Hk].
    destruct (bref_lit_ok kids img (tval label) ob Ho Hk) as [H1 H2].
    destruct (bref_lit kids img (tval label) ob) as [txt o']; cbn [snd] in H1, H2.
    apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr.
    destruct (opop_str_ok nob Hr) as [H1 H2].
    unfold bnote_lit. destruct (opop_str nob) as [pre o1]; cbn [snd] in H1, H2.
    apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr.
    destruct (opop_str_ok wob Hr) as [H1 H2].
    unfold bwiki_lit. destruct (opop_str wob) as [pre o1]; cbn [snd] in H1, H2.
    apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr.
    apply andb_true_iff in Hr as [Hr _]. apply andb_true_iff in Hr as [Hr _].
    exact Hr.
  - apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr. apply andb_true_iff in Hr as [Hp _].
    apply andb_true_iff in Hp as [Ho _]. exact Ho.
  - cbn [iscan_wf] in Hr. apply iscan_wf_flush;
      [apply oscope_ok_emit; [exact Hr | reflexivity | apply andb_false_l]
      |rewrite ocur_emit; reflexivity].
Qed.

(* A compound state hands the question to its ordinary shadow, which is
   where the last conjunct of its obligation was kept for. *)
Local Lemma iscan_wf_ostate :
  forall st, iscan_wf st = true -> oscope_ok (ifinish_ostate st) = true.
Proof.
  induction st; intros H;
    try (rewrite ifinish_ostate_flat_state by reflexivity;
         apply iscan_wf_ostate_flat, H).
  all: try (cbn [ifinish_ostate];
       match goal with
       | IH : iscan_wf _ = true -> _ |- _ => apply IH
       end;
       cbn [iscan_wf] in H; apply andb_true_iff in H as [_ H]; exact H).
  - cbn [ifinish_ostate iresolve ifinish_ostate_flat iscan_wf]
      in H |- *.
    apply andb_true_iff in H as [Ho Hs].
    apply negb_true_iff in Hs.
    rewrite hd_str_is_starts_str in Hs.
    apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in H.
  apply andb_true_iff in H as [Hb Hshadow].
  apply andb_true_iff in Hb as [Ho Hs].
  rewrite hd_str_is_starts_str in Hs.
  cbn [ifinish_ostate]. destruct two;
    [destruct last as [p|];
     [apply IHst, Hshadow
     |apply oscope_ok_emit;
       [sem_flush; apply iscan_wf_flush;
          [exact Ho|apply negb_true_iff in Hs; exact Hs]
       |reflexivity|reflexivity]]|].
  destruct (match last with Some p => negb (is_ws_nl p)
            | None => false end); [|apply IHst, Hshadow].
  apply oscope_ok_emit;
    [sem_flush; apply iscan_wf_flush;
       [exact Ho|apply negb_true_iff in Hs; exact Hs]
    |reflexivity|reflexivity].
Qed.

Local Lemma iscan_wf_finish_rev :
  forall st, iscan_wf st = true -> rlist_ok (ifinish_rev st) = true.
Proof.
  intros st H. unfold ifinish_rev.
  apply rlist_ok_ofinish, iscan_wf_ostate, H.
Qed.

Local Lemma iscan_wf_finish :
  forall st, iscan_wf st = true -> wf_inlines (ifinish st) = true.
Proof.
  intros st H. unfold ifinish.
  apply wf_inlines_of_rlist, iscan_wf_finish_rev, H.
Qed.

(* A line boundary pushes a `SoftBreak` into the innermost open scope,
   which leaves a head that is not a `Str` -- what the next line's text
   accumulation needs.  Open scopes survive the break: a span may cross
   it. *)
Local Lemma iscan_wf_break_flat :
  forall st, is_compound st = false -> iscan_wf st = true ->
    iscan_wf (ibreak_flat (iresolve st)) = true.
Proof.
  intros st Hcomp H. pose proof (iscan_wf_resolve st H) as Hr.
  pose proof (iresolve_resolved st) as Hno.
  assert (Hcomp' : is_compound (iresolve st) = false)
    by (destruct st as [| | |k extra txt before marked o
                       | | | | | | | | | | | | | | | | | |];
        cbn [is_compound iresolve] in *;
        try reflexivity; try discriminate Hcomp;
        destruct (Nat.ltb (S extra) (dwidth k)); [reflexivity|];
        destruct marked; [reflexivity|];
        destruct (idelim_resolve_text k txt before false None o)
          as [u [v [w E]]]; rewrite E; reflexivity).
  destruct (iresolve st) as
    [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|mt me ms mx ml msh mo|mct mcs mcx mcl mcsh mco|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img sopen sp ssrc sob|ap asrc atxt aprev ash aob|kids img ropen label ob|nesc nimg nlab nopen nob|wesc wrb wimg wreg wopen wob|kids img dopen esc depth dst sh ob|asrc atxt aob|salias stxt sob|rspec rtxt rob];
    try contradiction;
    try (cbn [is_compound] in Hcomp'; discriminate Hcomp');
    cbn [ibreak_flat];
    try (cbn [iscan_wf] in Hr; apply andb_true_iff in Hr as [Ho Hs];
         apply negb_true_iff in Hs; rewrite hd_str_is_starts_str in Hs).
  1,2,3: try unfold iesc_hard;
         apply (iscan_wf_text_reset false EmptyString None);
         [ apply oscope_ok_emit;
           [ apply iscan_wf_flush; assumption
           | reflexivity | apply andb_false_l ]
         | rewrite ocur_emit; reflexivity ].
  - cbn [iscan_wf] in Hr |- *. exact Hr.
  - cbn [iscan_wf] in Hr. destruct (Nat.eqb run n); [|exact Hr].
    rewrite ?imk_semantic.
    apply (iscan_wf_text_reset false EmptyString None).
    + apply oscope_ok_emit;
        [apply oscope_ok_emit;
           [exact Hr | apply wf_inline_vnode
           | rewrite plain_str_vnode; apply andb_false_l]
        |reflexivity | apply andb_false_l].
    + rewrite ocur_emit. reflexivity.
  - apply andb_true_iff in Hr as [Ho Hk]. apply ispan_feed_wf; assumption.
  - cbn [iscan_wf] in Hr |- *. exact Hr.
  (* a label and a destination both carry the break as a character, so
     nothing is emitted and the invariant is the one they arrived with *)
  - cbn [iscan_wf] in Hr |- *. exact Hr.
  (* a wikilink candidate decays to its literal, reabsorbing the text
     before its bracket, and the break is the soft one after it *)
  - cbn [iscan_wf] in Hr.
    destruct (opop_str_ok wob Hr) as [H1 H2].
    unfold bwiki_lit. destruct (opop_str wob) as [pre o1]; cbn [snd] in H1, H2.
    apply (iscan_wf_text_reset false EmptyString None);
      [apply oscope_ok_emit;
         [apply iscan_wf_flush; assumption | reflexivity | apply andb_false_l]
      |rewrite ocur_emit; reflexivity].
  (* a candidate does not: the region may not hold a break, so it decays
     to text and the break is the soft one after it *)
  - apply (iscan_wf_text_reset false EmptyString None);
      [apply oscope_ok_emit;
         [apply iscan_wf_flush; assumption | reflexivity | apply andb_false_l]
      |rewrite ocur_emit; reflexivity].
  - cbn [iscan_wf] in Hr.
    assert (Hvo : oscope_ok (oemit (mk (Verbatim rtxt)) rob) = true)
      by (apply oscope_ok_emit;
            [exact Hr | reflexivity | apply andb_false_l]).
    apply (iscan_wf_text_reset false EmptyString None);
      [apply oscope_ok_emit;
         [apply iscan_wf_flush;
            [exact Hvo | rewrite ocur_emit; reflexivity]
         |reflexivity | apply andb_false_l]
      |rewrite ocur_emit; reflexivity].
Qed.

(* A compound state takes the break in both readings at once. *)
Local Lemma iscan_wf_break_at :
  forall attrs_enabled st,
    iscan_wf st = true -> iscan_wf (ibreak_at attrs_enabled st) = true.
Proof.
  intros attrs_enabled st. revert attrs_enabled.
  induction st; intros attrs_enabled H;
    try (rewrite ibreak_at_flat_state by reflexivity;
         apply iscan_wf_break_flat; [reflexivity|exact H]).
  - cbn [ibreak_at].
    destruct (two && dollar_math_enabled &&
      negb (match prev with Some p => Ascii.eqb p dollar
            | None => false end))%bool eqn:E.
    + cbn [iscan_wf] in H |- *.
      apply andb_true_iff in H as [Ho Hs].
      rewrite Ho, Hs. cbn [andb].
      apply (iscan_wf_break_flat
        (IText false (tpush txt (InlineScan.dollars true)) (Some dollar) o));
        [reflexivity|].
      cbn [iscan_wf]. rewrite Ho, Hs. reflexivity.
    + apply iscan_wf_break_flat;
        [cbn [is_compound]; rewrite E; reflexivity|exact H].
  - cbn [ibreak_at iscan_wf] in H |- *.
    apply andb_true_iff in H as [Hb Hsh].
    apply andb_true_iff in Hb as [Ho Hs].
    rewrite Ho, Hs. apply IHst, Hsh.
  - cbn [iscan_wf] in H.
    apply andb_true_iff in H as [Hb Hsh].
    apply andb_true_iff in Hb as [Ho Hs].
    rewrite hd_str_is_starts_str in Hs.
    cbn [ibreak_at]. destruct two.
    + destruct last as [p|].
      * cbn [iscan_wf]. rewrite Ho, hd_str_is_starts_str.
        apply negb_true_iff in Hs. rewrite Hs. apply IHst, Hsh.
      * apply (iscan_wf_break_flat
          (IText false tnil (Some dollar)
            (oemit
              (imk (spot_before cursor_start
                      (InlineScan.dollars true ++ tval src ++
                       InlineScan.dollars true)) cursor_start
                   (Math DisplayMath (tval src)))
              (flush_text_to_at
                (spot_before cursor_start
                  (InlineScan.dollars true ++ tval src ++
                   InlineScan.dollars true)) (tval txt) o))));
          [reflexivity|].
        apply iscan_wf_text.
        -- apply oscope_ok_emit;
             [sem_flush; apply iscan_wf_flush;
                [exact Ho|apply negb_true_iff in Hs; exact Hs]
             |reflexivity|reflexivity].
        -- rewrite ocur_emit. reflexivity.
    + destruct (match last with Some p => negb (is_ws_nl p)
                | None => false end).
      * apply (iscan_wf_text_reset false EmptyString None).
        -- apply oscope_ok_emit;
             [apply oscope_ok_emit;
                [sem_flush; apply iscan_wf_flush;
                   [exact Ho|apply negb_true_iff in Hs; exact Hs]
                |reflexivity|reflexivity]
             |reflexivity|apply andb_false_l].
        -- rewrite ocur_emit. reflexivity.
      * apply IHst, Hsh.
  - cbn [ibreak_at iscan_wf] in H |- *.
    apply andb_true_iff in H as [Hb Hsh].
    apply andb_true_iff in Hb as [Ho Hs].
    apply negb_true_iff in Hs. rewrite hd_str_is_starts_str in Hs.
    apply iattr_feed_wf; [exact Ho|exact Hs|apply IHst; exact Hsh].
  - cbn [ibreak_at iscan_wf] in H |- *.
    apply andb_true_iff in H as [Ho Hsh]. rewrite Ho. cbn [andb].
    apply IHst, Hsh.
  - cbn [ibreak_at iscan_wf] in H |- *.
    apply andb_true_iff in H as [_ Hsh]. apply IHst, Hsh.
Qed.

Local Lemma iscan_wf_break :
  forall st, iscan_wf st = true -> iscan_wf (ibreak st) = true.
Proof.
  intros st H. unfold ibreak. apply iscan_wf_break_at, H.
Qed.

Local Lemma iscan_wf_lines :
  forall l st, iscan_wf st = true -> iscan_wf (iscan_lines l st) = true.
Proof.
  induction l as [|x [|y rest] IH]; intros st H; cbn [iscan_lines].
  - exact H.
  - apply iscan_wf_str, H.
  - apply IH, iscan_wf_break, iscan_wf_str, H.
Qed.

Local Lemma iscan_wf_str_off :
  forall s st, iscan_wf st = true -> iscan_wf (iscan_str_off s st) = true.
Proof.
  induction s as [|c rest IH]; intros st H; [exact H|].
  cbn [iscan_str_off]. apply IH, iscan_wf_step_at, H.
Qed.

(* The bit the frozen lines are read with is invisible to the invariant:
   `iscan_wf_step_at` and `iscan_wf_break_at` hold for either value. *)
Local Lemma iscan_wf_lines_off :
  forall k l st, iscan_wf st = true -> iscan_wf (iscan_lines_off k l st) = true.
Proof.
  induction k as [|k IH]; intros l st H; [apply iscan_wf_lines, H|].
  destruct l as [|x [|y rest]]; cbn [iscan_lines_off].
  - exact H.
  - apply iscan_wf_str_off, H.
  - apply IH, iscan_wf_break_at, iscan_wf_str_off, H.
Qed.

(** The parser's inline pass only ever emits a well-formed sequence. *)
Lemma parse_inline_line_wf :
  forall s, wf_inlines (parse_inline_line s) = true.
Proof.
  intros s. unfold parse_inline_line.
  apply iscan_wf_finish, iscan_wf_str. reflexivity.
Qed.

Local Lemma quote_block_wf :
  forall header bs,
    wf_blocks bs = true -> wf_block (quote_block header bs) = true.
Proof.
  intros header bs Hbs.
  destruct header as [[[kind fold] [line source]]|];
    cbn [quote_block callout_title semantic_pos pos_records].
  - rewrite wf_block_callout, parse_inline_line_wf, Hbs. reflexivity.
  - rewrite wf_block_quote. exact Hbs.
Qed.

(*
Paragraph assembly is well-formed
=================================
*)

(* No hypothesis: the scan's invariant does not care what the lines
   look like. *)
Local Lemma para_inlines_wf :
  forall ls, wf_inlines (para_inlines ls) = true.
Proof.
  intros ls. unfold para_inlines.
  apply iscan_wf_finish, iscan_wf_lines. reflexivity.
Qed.

Local Lemma para_inlines_off_wf :
  forall k ls, wf_inlines (para_inlines_off k ls) = true.
Proof.
  intros k ls. unfold para_inlines_off.
  apply iscan_wf_finish, iscan_wf_lines_off. reflexivity.
Qed.

Local Lemma flush_para_wf :
  forall cur k,
    wf_blocks k = true ->
    wf_blocks (mk (Para (para_inlines cur)) :: k) = true.
Proof.
  intros cur k Hk.
  rewrite wf_blocks_cons. cbn [node_contents mk wf_block].
  rewrite para_inlines_wf, Hk. reflexivity.
Qed.

(* What an open key closes to, either way.  With no block it is the
   paragraph the key line retracts to, which is `flush_para_wf` at a
   one-line accumulator; with one it is the key, whose only condition
   beyond its block's is that the label is a well-formed inline list. *)
Local Lemma flush_para_off_wf :
  forall n cur k,
    wf_blocks k = true ->
    wf_blocks (mk (Para (para_inlines_off n cur)) :: k) = true.
Proof.
  intros n cur k Hk.
  rewrite wf_blocks_cons. cbn [node_contents mk wf_block].
  rewrite para_inlines_off_wf, Hk. reflexivity.
Qed.

Local Lemma key_close_wf :
  forall start lbl src bs,
    wf_blocks bs = true -> wf_blocks (key_close start lbl src bs) = true.
Proof.
  intros start lbl src bs Hbs. destruct bs as [|b rest].
  - exact (flush_para_wf [src] [] eq_refl).
  - cbn [key_close key_label pos_records semantic_pos]. rewrite wf_blocks_cons in Hbs |- *.
    apply andb_true_iff in Hbs as [Hb Hrest].
    cbn [node_contents mk]. rewrite wf_block_keyed, para_inlines_wf, Hrest.
    rewrite wf_blocks_cons, Hb. reflexivity.
Qed.

(*
The parser produces well-formed output
======================================
*)

(* Fenced blocks are always well-formed, whatever the info and content. *)
Local Lemma fence_block_wf :
  forall f content, wf_block (node_contents (fence_block f content)) = true.
Proof.
  intros f content. unfold fence_block.
  destruct (f_info f) as [|c info]; [reflexivity|].
  destruct c as [[|] [|] [|] [|] [|] [|] [|] [|]];
    destruct braw_blocks; reflexivity.
Qed.

(* The fold's invariant: what a state has already closed is well-formed,
   recursively through its containers, and a heading carries its level.
   Paragraph and fence accumulators carry nothing: `para_inlines` is
   well-formed whatever the lines, and `CodeBlock`/`RawBlock` are
   unconditionally well-formed. *)
Local Fixpoint state_wf (st : pstate) : bool :=
  match st with
  (* A paragraph accumulator carries nothing: `wf_block` asks only that
     the inlines are well formed, and `para_inlines_wf` says they are
     whatever the lines look like. *)
  | PPara _ => true
  (* The recovery's paragraph carries nothing either: its count only
     changes how the lines are read, not what the reading may be. *)
  | PParaOff _ _ => true
  (* A heading carries its level, which `Heading` requires to be at
     least 1, and nothing else. *)
  | PHeading lvl _ _ => Nat.leb 1 lvl
  | PFence _ _ _ _ _ => true
  | PQuote _ _ done inner => wf_blocks done && state_wf inner
  (* A div carries no invariant its fence length or class could break:
     `Div` is well-formed for any block sequence, exactly as
     `BlockQuote` is. *)
  | PDiv _ _ _ _ done inner => wf_blocks done && state_wf inner
  (* The finished items, the current item's finished blocks, and its
     open state. *)
  | PList ls done inner =>
      forallb wf_blocks (ls_items ls) && wf_blocks done && state_wf inner
  (* The slices are the paragraph a failed spec becomes, and a paragraph
     accumulator carries nothing. *)
  | PAttr _ _ _ _ _ _ => true
  (* A definition's label and destination carry `wf_block (RefDef _ _)`
     itself: they are fixed when the state opens, and a continuation line
     only appends another whitespace-free run to the destination. *)
  | PRef _ _ lbl val =>
      no_char "]"%char lbl && negb (is_footnote_label lbl) && no_ws val
  | PFoot _ _ lbl done inner =>
      nonempty_str lbl && wf_blocks done && state_wf inner
  (* A table's rows carry no invariant: a cell's inlines come from
     `parse_inline_line`, which is well-formed for any string.  Its
     caption carries none either: it is a paragraph's inlines. *)
  | PTable _ _ _ => true
  (* Pending attributes add nothing of their own. *)
  | PPend _ _ inner => state_wf inner
  (* A key becomes one of two blocks and both are paragraphs' business,
     so it carries what a paragraph accumulator does: nothing. *)
  | PKey _ _ _ inner => state_wf inner
  end.

(* Every cell a table is built from is well-formed, whichever of the two
   builders made it: `cells_of` calls `parse_inline_line`, and `head_of`
   only re-labels cells that already exist. *)
Local Lemma cells_of_wf :
  forall ct aligns cs,
    forallb (fun c => match c with Cell _ _ ils => wf_inlines ils end)
      (cells_of ct aligns cs) = true.
Proof.
  intros ct aligns cs. revert aligns.
  induction cs as [|c cs IH]; intros aligns; [reflexivity|].
  destruct aligns as [|a als]; cbn [cells_of forallb];
    rewrite parse_inline_line_wf; apply IH.
Qed.

Local Lemma head_of_wf :
  forall aligns r,
    forallb (fun c => match c with Cell _ _ ils => wf_inlines ils end) r = true ->
    forallb (fun c => match c with Cell _ _ ils => wf_inlines ils end)
      (head_of aligns r) = true.
Proof.
  intros aligns r. revert aligns.
  induction r as [|[ct al ils] r IH]; intros aligns H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hc Hr].
  destruct aligns as [|a als]; cbn [head_of forallb]; rewrite Hc; apply IH, Hr.
Qed.

Local Lemma table_fold_wf :
  forall rows aligns acc,
    forallb (forallb (fun c => match c with Cell _ _ ils => wf_inlines ils end))
      acc = true ->
    forallb (forallb (fun c => match c with Cell _ _ ils => wf_inlines ils end))
      (table_fold rows aligns acc) = true.
Proof.
  induction rows as [|r rows IH]; intros aligns acc H.
  - cbn [table_fold]. rewrite forallb_rev. exact H.
  - destruct r as [als|cs]; cbn [table_fold]; apply IH.
    + destruct acc as [|row acc']; [reflexivity|].
      cbn [forallb] in H |- *. apply andb_true_iff in H as [Hrow Hacc].
      rewrite (head_of_wf _ _ Hrow). exact Hacc.
    + cbn [forallb]. rewrite cells_of_wf. exact H.
Qed.

(* A caption is a paragraph's inlines, or none. *)
Local Lemma caption_of_wf : forall c, wf_inlines (caption_of c) = true.
Proof.
  intros [rs|rs|rs start ls]; try reflexivity.
  cbn [caption_of]. sem_para. apply para_inlines_wf.
Qed.

(* The rows the parser builds are bare nodes of bare cells. *)
Local Lemma rows_mk_wf :
  forall X : list (list cell),
    forallb (fun row => forallb (fun c => match node_contents c with
                                          | Cell _ _ ils => wf_inlines ils end)
                          (node_contents row))
      (map (fun r => mk (map mk r)) X)
    = forallb (forallb (fun c => match c with Cell _ _ ils => wf_inlines ils end)) X.
Proof.
  induction X as [|r X IH]; [reflexivity|]. cbn [map forallb node_contents mk].
  rewrite (forallb_mk _ (fun c => match c with Cell _ _ ils => wf_inlines ils end)), IH.
  reflexivity.
Qed.

Local Lemma table_block_wf :
  forall rows c, wf_blocks [table_block rows c] = true.
Proof.
  intros rows c. unfold table_block.
  cbn [pos_records semantic_pos].
  rewrite wf_blocks_cons. cbn [node_contents mk wf_block].
  rewrite rows_mk_wf, table_fold_wf by reflexivity.
  rewrite andb_true_r, andb_true_r.
  apply caption_of_wf.
Qed.

(* Closing the stack at end of input preserves the invariant. *)
(* A heading block is well-formed as soon as its level is. *)
Local Lemma heading_block_wf :
  forall lvl cur,
    Nat.leb 1 lvl = true -> wf_blocks [heading_block lvl cur] = true.
Proof.
  intros lvl cur Hl. unfold heading_block.
  rewrite wf_blocks_cons. cbn [node_contents mk wf_block]. sem_para.
  rewrite Hl, para_inlines_wf.
  reflexivity.
Qed.

Local Lemma heading_block_off_wf :
  forall k lvl cur,
    Nat.leb 1 lvl = true -> wf_blocks [heading_block_off k lvl cur] = true.
Proof.
  intros k lvl cur Hl. unfold heading_block_off.
  rewrite wf_blocks_cons. cbn [node_contents mk wf_block]. sem_para.
  rewrite Hl, para_inlines_off_wf.
  reflexivity.
Qed.

Local Lemma finish_wf :
  forall st, state_wf st = true -> wf_blocks (finish st) = true.
Proof.
  induction st as [cur|lvl hrng hcur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H.
  - destruct cur as [|c cur']; [reflexivity|].
    cbn [finish]; nopos. apply flush_para_wf. reflexivity.
  - cbn [state_wf] in H. cbn [finish]; nopos. apply heading_block_wf, H.
  - cbn [finish]; nopos. rewrite wf_blocks_cons, fence_block_wf. reflexivity.
  - cbn [state_wf] in H. apply andb_true_iff in H as [Hd Hi].
    destruct qhead as [[[kind fold] [line source]]|];
      cbn [finish option_map quote_block callout_title semantic_pos pos_records]; nopos;
      rewrite wf_blocks_cons; cbn [node_contents mk].
    + rewrite wf_block_callout, parse_inline_line_wf,
        wf_blocks_app, wf_blocks_rev, Hd, (IH Hi). reflexivity.
    + rewrite wf_block_quote, wf_blocks_app, wf_blocks_rev, Hd, (IH Hi).
      reflexivity.
  - (* a div: as a quote, but through div_block's attribute wrapper *)
    cbn [state_wf] in H. apply andb_true_iff in H as [Hd Hi].
    cbn [finish]; nopos. apply div_block_wf.
    rewrite wf_blocks_app, wf_blocks_rev, Hd, (IH Hi). reflexivity.
  - (* a list: the item still open, plus the ones already closed *)
    cbn [state_wf] in H. apply andb_true_iff in H as [H1 Hi].
    apply andb_true_iff in H1 as [Hitems Hd].
    cbn [finish]; nopos. rewrite wf_blocks_cons, andb_true_r.
    apply wf_list_block.
    rewrite nonempty_rev, forallb_rev. cbn [nonempty forallb].
    rewrite wf_blocks_app, wf_blocks_rev, Hd, (IH Hi), Hitems.
    reflexivity.
  - (* an attribute spec: a finished one contributes nothing, an
       unfinished one the paragraph of the lines it ate *)
    cbn [finish]; nopos.
    destruct (ap_done aap); [reflexivity|].
    cbn [finish_para_recover]; nopos.
    destruct aslices as [|c cur']; [reflexivity|].
    apply flush_para_off_wf. reflexivity.
  - (* the recovery's paragraph: its lines are well formed however they
       are read *)
    cbn [finish]; nopos. apply flush_para_off_wf. reflexivity.
  - (* a reference definition: the state's invariant is the block's *)
    cbn [state_wf] in H. cbn [finish]; nopos.
    rewrite wf_blocks_cons. cbn [ref_block node_contents mk wf_block].
    rewrite H. reflexivity.
  - cbn [state_wf] in H. apply andb_true_iff in H as [Hboth Hinner].
    apply andb_true_iff in Hboth as [Hlbl Hdone].
    cbn [finish]; nopos. rewrite wf_blocks_cons.
    cbn [foot_block node_contents mk]. rewrite wf_block_footnote.
    rewrite Hlbl, wf_blocks_app, wf_blocks_rev, Hdone, (IH Hinner).
    reflexivity.
  - (* a table: its rows are well-formed by construction, and its
       caption by the state's invariant *)
    cbn [finish]; nopos. apply table_block_wf.
  - cbn [state_wf] in H. cbn [finish]; nopos.
    rewrite wf_blocks_decorate_head. exact (IH H).
  - cbn [state_wf] in H.
    rewrite finish_key; nopos. exact (key_close_wf _ _ _ _ (IH H)).
Qed.

(* A lazy line joins the innermost paragraph, which asks nothing of it. *)
Local Lemma feed_lazy_wf :
  forall l st, state_wf st = true -> state_wf (feed_lazy l st) = true.
Proof.
  induction st as [cur|lvl hrng hcur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H.
  - reflexivity.
  - cbn [feed_lazy state_wf] in *. exact H.
  - reflexivity.
  - cbn [feed_lazy state_wf] in *. apply andb_true_iff in H as [Hd Hi].
    rewrite Hd, (IH Hi). reflexivity.
  - cbn [feed_lazy state_wf] in *. apply andb_true_iff in H as [Hd Hi].
    rewrite Hd, (IH Hi). reflexivity.
  - cbn [feed_lazy state_wf list_content ls_items] in *.
    apply andb_true_iff in H as [H1 Hi].
    apply andb_true_iff in H1 as [Hitems Hd].
    rewrite Hitems, Hd, (IH Hi). reflexivity.
  - exact H.                            (* excluded by lazy_ok *)
  - reflexivity.                        (* the recovery's paragraph *)
  - exact H.                            (* excluded by lazy_ok *)
  - cbn [feed_lazy state_wf] in *. apply andb_true_iff in H as [Hfixed Hi].
    rewrite Hfixed, (IH Hi). reflexivity.
  - exact H.                            (* excluded by lazy_ok *)
  - cbn [feed_lazy state_wf] in *. exact (IH H).
  - cbn [feed_lazy state_wf] in *. exact (IH H).
Qed.

(* Opening a block from an idle state. *)
Local Lemma open_kind_wf :
  forall l k,
    classify l = k ->
    wf_blocks (fst (open_kind l k)) = true
    /\ state_wf (snd (open_kind l k)) = true.
Proof.
  intros l k H. destruct k; cbn [close_reopen open_quote finish app open_kind open_fence open_attr open_ref fst snd]; nopos; try (split; reflexivity).
  - (* KDiv: opens the container when enabled, otherwise literal text. *)
    destruct (@bdivs K); split; reflexivity.
  - (* KHeading: the level comes from the classifier, and is the only
       thing a heading state carries *)
    split; [reflexivity|].
    cbn [state_wf]. rewrite (classify_heading_level _ _ _ H). reflexivity.
  - (* KRow: either opens a table or becomes one paragraph line. *)
    destruct (@btables K); split; reflexivity.
  - (* KText: the accumulator gains a line, or the line opens a key --
       and neither state asks anything of it. *)
    unfold open_text.
    destruct (if @bkeyed K then key_split (drop_leading_ws l) else None)
      as [[lbl v]|]; split; reflexivity.
Qed.

(* One transition preserves the invariant and emits only well-formed
   blocks.  Proved on fuel, since that is what `step` recurses on. *)
(* Opening a list: a fresh list has no closed items yet, so all the
   invariant needs is what the descent already gives. *)
Local Lemma open_list_wf :
  forall l ind m chk bs inner,
    wf_blocks bs = true -> state_wf inner = true ->
    wf_blocks (fst (open_list l ind m chk (bs, inner))) = true
    /\ state_wf (snd (open_list l ind m chk (bs, inner))) = true.
Proof.
  intros l ind m chk bs inner Hb Hi.
  cbn [open_list list_opened fst snd state_wf ls_items forallb].
  split; [reflexivity|]. rewrite wf_blocks_rev, Hb, Hi. reflexivity.
Qed.

(* Opening an attribute spec: the recorded line carries no condition. *)
Local Lemma open_attr_wf :
  forall pend specs ind ap l,
    wf_blocks (fst (open_attr pend specs ind ap l)) = true
    /\ state_wf (snd (open_attr pend specs ind ap l)) = true.
Proof.
  intros pend specs ind ap l. unfold open_attr.
  destruct (@battrs K); cbn [fst snd state_wf]; split; reflexivity.
Qed.

(* Opening a code fence: it carries no invariant at all, its column
   least of all. *)
Local Lemma open_fence_wf :
  forall l ind f,
    wf_blocks (fst (open_fence l ind f)) = true
    /\ state_wf (snd (open_fence l ind f)) = true.
Proof. intros l ind f. split; reflexivity. Qed.

(* Opening a reference definition: the classifier's guarantees about the
   label and the destination are exactly the block's. *)
Local Lemma open_ref_wf :
  forall ind l lbl v,
    classify l = KRef lbl v ->
    wf_blocks (fst (open_ref l ind lbl v)) = true
    /\ state_wf (snd (open_ref l ind lbl v)) = true.
Proof.
  intros ind l lbl v H. apply classify_kref in H.
  cbn [open_ref fst snd state_wf]. split; [reflexivity|].
  rewrite (ref_open_label_ok l lbl v H), (ref_open_value_no_ws l lbl v H).
  reflexivity.
Qed.

Local Lemma open_foot_wf :
  forall ind l lbl rest bs inner,
    classify l = KFoot lbl rest ->
    wf_blocks bs = true -> state_wf inner = true ->
    wf_blocks (fst (open_foot l ind lbl (bs, inner))) = true /\
    state_wf (snd (open_foot l ind lbl (bs, inner))) = true.
Proof.
  intros ind l lbl rest bs inner Hclass Hbs Hinner.
  pose proof (foot_open_label_ok _ _ _ (classify_kfoot _ _ _ Hclass)) as Hlbl.
  apply andb_true_iff in Hlbl as [Hnonempty _].
  unfold open_foot. destruct (@bfootnotes K); cbn [fst snd state_wf];
    split; try reflexivity.
  rewrite Hnonempty, wf_blocks_rev, Hbs, Hinner. reflexivity.
Qed.

(* Pending attributes are invisible to the invariant: decoration touches
   only a head that was already well-formed, and a `PPend` carries the
   state under it unchanged. *)
Local Lemma pend_result_wf :
  forall pend specs r,
    wf_blocks (fst r) = true ->
    state_wf (snd r) = true ->
    wf_blocks (fst (pend_result pend specs r)) = true
    /\ state_wf (snd (pend_result pend specs r)) = true.
Proof.
  intros pend specs [bs st] Hb Hs. cbn [fst snd] in Hb, Hs.
  destruct bs; cbn [pend_result fst snd state_wf]; nopos;
    (split; [rewrite ?wf_blocks_decorate_head; exact Hb | exact Hs]).
Qed.

Local Lemma step_fuel_wf :
  forall n off l st,
    state_wf st = true ->
    wf_blocks (fst (step_fuel n off l st)) = true
    /\ state_wf (snd (step_fuel n off l st)) = true.
Proof.
  induction n as [|n IH]; intros off l st H; [split; [reflexivity | exact H]|].
  cbn [step_fuel open_line].
  destruct st as [cur|hlvl hrng hcur|f fnd crng cop acc|qrng qhead done inner|dlen dcls drng dop ddone dinner|ls done inner|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner|trng trows tcap|ppend pspecs pinner|krng klbl ksrc kinner].
  - (* idle, or an open paragraph *)
    destruct cur as [|c cur'].
    + destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy];
        try (apply open_kind_wf; exact E).
      * (* KFence: opens its own state, recording its column *)
        apply open_fence_wf.
      * (* KQuote: descend into the enclosed line *)
        destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner].
        destruct (quote_header rest)
          as [[[kind fold] title]|].
        -- cbn [open_callout fst snd state_wf]. split; reflexivity.
        -- cbn [open_quote fst snd] in Hb, Hs |- *.
           split; [reflexivity|].
           cbn [state_wf]. rewrite wf_blocks_rev, Hb. exact Hs.
      * (* KList: descend into the rest of the line *)
        destruct (IH (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara [])) as [bs inner].
        apply open_list_wf; assumption.
      * (* KAttr: opens its own state, not through open_kind *)
        apply open_attr_wf.
      * (* KFoot: descend into the first body line *)
        destruct (IH (off + consumed l frest) frest (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l frest) frest (PPara [])) as [bs inner].
        apply (open_foot_wf (off + indent_of l) l flbl frest); assumption.
      * (* KRef: opens its own state too *)
        apply (open_ref_wf _ l _ _ E).
    + destruct (bunderline_of l) as [ulvl|] eqn:Eu; cbn [fst snd].
      { (* an underline: the open paragraph becomes a heading, and its
           level is `S ulvl` precisely so that `1 <= lvl` is free *)
        split; [|reflexivity].
        apply heading_block_wf. reflexivity. }
      destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy]; cbn [fst snd].
      7: { (* list marker: interrupts the paragraph only when the setting says so *)
        destruct (binterrupt (KList m mc chk mr)) eqn:Ei; cbn [fst snd].
        - destruct (IH (off + consumed l (configured_list_rest chk mr))
                      (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
          destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                      (configured_list_rest chk mr) (PPara [])) as [bs inner].
          destruct (open_list_wf l (off + indent_of l)
                      (with_starts (configured_list_styles m chk) mc)
                      (configured_list_check chk) bs inner Hb Hs) as [Hob Hos].
          destruct (open_list l (off + indent_of l)
                      (with_starts (configured_list_styles m chk) mc)
                      (configured_list_check chk) (bs, inner)) as [obs ost].
          cbn [close_reopen finish app fst snd] in Hob, Hos |- *; nopos.
          split; [|exact Hos].
          apply flush_para_wf, Hob.
        - split; reflexivity. }
      1: (split; [|reflexivity]; apply flush_para_wf; reflexivity).
      (* every remaining kind reaches the same interrupt test, and
         `binterrupt` answers `false` on each of them definitionally --
         its type is what says only a list marker may interrupt. *)
      all: cbn [binterrupt fst snd]; split; reflexivity.
  - (* an open heading *)
    cbn [state_wf] in H. rename H into Hlv.
    assert (Hhb : wf_blocks [heading_block hlvl hcur] = true)
      by (apply heading_block_wf, Hlv).
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
    4: { (* div: close the heading, then obey the div capability. *)
      destruct (open_kind_wf l (KDiv dl dc) E) as [Hob Hos].
      unfold close_reopen. destruct (open_kind l (KDiv dl dc)) as [obs ost].
      cbn [finish fst snd] in Hob, Hos |- *; nopos. split; [|exact Hos].
      rewrite wf_blocks_app, Hhb, Hob. reflexivity. }
    6: { (* list marker: close the heading, then open the list *)
        destruct (IH (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara [])) as [bs inner].
      destruct (open_list_wf l (off + indent_of l)
        (with_starts (configured_list_styles m chk) mc)
        (configured_list_check chk) bs inner Hb Hs) as [Hob Hos].
      destruct (open_list l (off + indent_of l)
        (with_starts (configured_list_styles m chk) mc)
        (configured_list_check chk) (bs, inner)) as [obs ost].
      cbn [close_reopen finish app fst snd] in Hob, Hos |- *; nopos.
      split; [|exact Hos].
      rewrite wf_blocks_cons in Hhb |- *.
      apply andb_true_iff in Hhb as [Hhb _]. rewrite Hhb, Hob. reflexivity. }
    4: { (* quote: close the heading, then descend *)
      destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner].
      destruct (quote_header rest)
        as [[[kind fold] title]|].
      - cbn [close_reopen open_callout finish app fst snd]; nopos.
        split; [exact Hhb|reflexivity].
      - cbn [close_reopen open_quote finish app fst snd] in Hb, Hs |- *; nopos.
        split; [exact Hhb|].
        cbn [state_wf]. rewrite wf_blocks_rev, Hb. exact Hs. }
    4: { (* matching or differing level *)
      destruct bheading_continues eqn:Hcontinues.
      - destruct (Nat.eqb kl hlvl) eqn:Elv;
          cbn [close_reopen open_kind finish app fst snd]; nopos.
        + split; [reflexivity|]. cbn [state_wf]. exact Hlv.
        + split; [exact Hhb|].
          cbn [state_wf]. exact (classify_heading_level _ _ _ E).
      - cbn [close_reopen open_kind finish app fst snd]; nopos.
        split; [exact Hhb|].
        cbn [state_wf]. exact (classify_heading_level _ _ _ E). }
    4: { (* attribute spec: close the heading, then open the spec *)
      destruct (open_attr_wf [] [] (off + indent_of l) kap l) as [Hob Hos].
      rewrite close_reopen_attr. cbn [fst snd].
      split; [exact Hhb|exact Hos]. }
    4: { (* footnote definition: close the heading, then descend *)
      destruct (IH (off + consumed l frest) frest (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n (off + consumed l frest) frest (PPara [])) as [bs inner].
      destruct (open_foot_wf (off + indent_of l) l flbl frest bs inner E Hb Hs)
        as [Hob Hos].
      rewrite close_reopen_foot. cbn [fst snd].
      split; [exact Hhb|exact Hos]. }
    4: { (* reference definition: close the heading, then open it *)
      destruct (open_ref_wf (off + indent_of l) l rlbl rval E) as [Hob Hos].
      split; [|exact Hos].
      cbn [close_reopen open_ref finish fst snd]; nopos. rewrite app_nil_r. exact Hhb. }
    4: { (* row: close the heading, then open either table or paragraph *)
      destruct (open_kind_wf l (KRow krow) E) as [Hob Hos].
      unfold close_reopen. destruct (open_kind l (KRow krow)) as [obs ost].
      cbn [finish fst snd] in Hob, Hos |- *; nopos. split; [|exact Hos].
      rewrite wf_blocks_app, Hhb, Hob. reflexivity. }
    4: { (* lazy text *)
      destruct bheading_continues.
      - cbn [fst snd]. split; [reflexivity|]. cbn [state_wf]. exact Hlv.
      - destruct (open_kind_wf l KText E) as [Hob Hos].
        unfold close_reopen. destruct (open_kind l KText) as [obs ost].
        cbn [finish fst snd] in Hob, Hos |- *; nopos. split; [|exact Hos].
        rewrite wf_blocks_app, Hob, andb_true_r. exact Hhb. }
    (* blank, thematic, fence: close the heading and reopen outside it *)
    all: cbn [close_reopen open_quote finish app open_kind open_fence open_attr open_ref fst snd]; nopos; split;
         [ rewrite wf_blocks_cons in Hhb |- *;
           cbn [node_contents] in Hhb |- *;
           apply andb_true_iff in Hhb as [Hhb _]; rewrite Hhb; cbn [andb];
           reflexivity
         | reflexivity ].
  - (* inside a fence: only the close test *)
    destruct (fence_close f l); cbn [fst snd]; nopos.
    + rewrite wf_blocks_cons, fence_block_wf. split; reflexivity.
    + split; reflexivity.
  - (* inside a quote *)
    pose proof H as H0. cbn [state_wf] in H0.
    apply andb_true_iff in H0 as [Hd Hi].
    assert (Hbq : wf_block (quote_block qhead (rev done ++ finish inner)%list) = true).
    { apply quote_block_wf.
      rewrite wf_blocks_app, wf_blocks_rev, Hd, (finish_wf _ Hi).
      reflexivity. }
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
    7: { (* a list marker closes the quote and opens a list outside it *)
      destruct (IH (off + consumed l (configured_list_rest chk mr))
        (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
        (configured_list_rest chk mr) (PPara [])) as [bs inner'].
      destruct (open_list_wf l (off + indent_of l)
        (with_starts (configured_list_styles m chk) mc)
        (configured_list_check chk) bs inner' Hb Hs) as [Hob Hos].
      destruct (open_list l (off + indent_of l)
        (with_starts (configured_list_styles m chk) mc)
        (configured_list_check chk) (bs, inner')) as [obs ost].
      cbn [close_reopen finish app fst snd] in Hob, Hos |- *; nopos.
      split; [|exact Hos].
      rewrite wf_blocks_cons. cbn [node_contents mk].
      rewrite Hbq, Hob. reflexivity. }
    5: { (* quote prefix: descend into the enclosed line *)
      destruct (IH (off + consumed l rest) rest inner Hi) as [Hb Hs].
      destruct (step_fuel n (off + consumed l rest) rest inner) as [bs inner'].
      cbn [close_reopen open_quote finish app fst snd] in Hb, Hs |- *; nopos.
      split; [reflexivity|].
      cbn [state_wf]. rewrite wf_blocks_app, wf_blocks_rev, Hb, Hd. exact Hs. }
    6: { (* attribute spec: closes the quote and opens outside it *)
      destruct (open_attr_wf [] [] (off + indent_of l) kap l) as [Hob Hos].
      rewrite close_reopen_attr. cbn [fst snd]. split; [|exact Hos].
      cbn [finish]; nopos. rewrite wf_blocks_cons. cbn [node_contents mk].
      rewrite Hbq. reflexivity. }
    6: { (* footnote definition: closes the quote and opens outside it *)
      destruct (IH (off + consumed l frest) frest (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n (off + consumed l frest) frest (PPara [])) as [bs inner'].
      destruct (open_foot_wf (off + indent_of l) l flbl frest bs inner' E Hb Hs)
        as [Hob Hos].
      rewrite close_reopen_foot. cbn [fst snd]. split; [|exact Hos].
      cbn [finish]; nopos. rewrite wf_blocks_cons. cbn [node_contents mk].
      rewrite Hbq. reflexivity. }
    6: { (* reference definition: closes the quote and opens outside it *)
      destruct (open_ref_wf (off + indent_of l) l rlbl rval E) as [Hob Hos].
      split; [|exact Hos].
      cbn [close_reopen open_ref finish fst snd]; nopos. rewrite app_nil_r.
      rewrite wf_blocks_cons. cbn [node_contents mk]. rewrite Hbq. reflexivity. }
    (* KRow closes the quote and reopens outside it, which the `all:`
       below already covers. *)
    7: { (* text without the prefix: lazy continuation, or close *)
      cbn [is_lazy]. destruct (lazy_ok inner) eqn:El.
      - cbn [close_reopen open_quote finish app open_fence open_attr open_ref fst snd]; nopos.
        split; [reflexivity|].
        cbn [state_wf]. rewrite Hd. cbn [andb].
        apply feed_lazy_wf, Hi.
      - destruct (open_kind_wf l KText E) as [Hob Hos].
        unfold close_reopen. destruct (open_kind l KText) as [obs ost].
        cbn [finish fst snd] in Hob, Hos |- *; nopos. split; [|exact Hos].
        rewrite wf_blocks_app, Hob, andb_true_r, wf_blocks_cons.
        cbn [node_contents mk]. rewrite Hbq. reflexivity. }
    (* a fence opens through open_fence, and every other kind closes the
       quote and reopens outside it on exactly the transition
       open_kind_wf already describes *)
    all: first
         [ cbn [close_reopen open_fence finish app fst snd]; nopos;
           split;
           [ rewrite wf_blocks_cons; cbn [node_contents mk]; rewrite Hbq;
             cbn [andb]; reflexivity
           | reflexivity ]
         | destruct (open_kind_wf l _ E) as [Hob Hos];
           cbn [is_lazy];
           destruct (open_kind l _) as [obs ost] eqn:Eo;
           cbn [close_reopen open_quote finish app fst snd] in Hob, Hos |- *;
           nopos; split;
           [ rewrite wf_blocks_cons; cbn [node_contents mk]; rewrite Hbq;
             cbn [andb]; exact Hob
           | exact Hos ] ].
  - (* inside a div: the close test decides, and neither side classifies
       the line, so there are two goals here rather than seven *)
    pose proof H as H0. cbn [state_wf] in H0.
    apply andb_true_iff in H0 as [Hd Hi].
    destruct (negb (in_fence dinner) && div_close dlen l)%bool; cbn [fst snd]; nopos.
    + split; [|reflexivity].
      apply div_block_wf.
      rewrite wf_blocks_app, wf_blocks_rev, Hd, (finish_wf _ Hi). reflexivity.
    + destruct (IH off l dinner Hi) as [Hb Hs].
      destruct (step_fuel n off l dinner) as [bs inner'].
      cbn [fst snd] in Hb, Hs |- *.
      split; [reflexivity|].
      cbn [state_wf]. rewrite wf_blocks_app, wf_blocks_rev, Hb, Hd. exact Hs.
  - (* inside a list *)
    pose proof H as H0. cbn [state_wf] in H0.
    apply andb_true_iff in H0 as [H1 Hi].
    apply andb_true_iff in H1 as [Hitems Hd].
    assert (Hitem : wf_blocks (rev done ++ finish inner)%list = true).
    { rewrite wf_blocks_app, wf_blocks_rev, Hd, (finish_wf _ Hi). reflexivity. }
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
    7: { (* a bullet marker *)
      destruct (list_takes ls off l inner).
      - (* indented past the marker: contents of the current item *)
        destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        cbn [state_wf ls_items list_content];
          rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs.
      - destruct (narrow (ls_styles ls) (configured_list_styles m chk)).
        + (* no style survives: close this list, open another *)
          destruct (IH (off + consumed l (configured_list_rest chk mr))
            (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
          destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
            (configured_list_rest chk mr) (PPara [])) as [bs inner'].
          destruct (open_list_wf l (off + indent_of l)
            (with_starts (configured_list_styles m chk) mc)
            (configured_list_check chk) bs inner' Hb Hs) as [Hob Hos].
          destruct (open_list l (off + indent_of l)
            (with_starts (configured_list_styles m chk) mc)
            (configured_list_check chk) (bs, inner')) as [obs ost].
          cbn [close_reopen fst snd] in Hob, Hos |- *.
          split; [|exact Hos].
          rewrite wf_blocks_app, Hob, andb_true_r. apply finish_wf. exact H.
        + (* a sibling item: the closed one joins ls_items *)
          destruct (IH (off + consumed l (configured_list_rest chk mr))
            (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
          destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
            (configured_list_rest chk mr) (PPara [])) as [bs inner'].
          cbn [fst snd] in Hb, Hs |- *.
          split; [reflexivity|].
          cbn [state_wf]. unfold list_next, list_narrow.
          destruct (is_blank (configured_list_rest chk mr)); cbn [ls_items forallb];
            rewrite Hitem, Hitems, wf_blocks_rev, Hb; exact Hs. }
    1: { (* a blank line goes to the item's contents *)
      destruct (IH off l inner Hi) as [Hb Hs].
      destruct (step_fuel n off l inner) as [bs inner'].
      cbn [fst snd] in Hb, Hs |- *.
      split; [reflexivity|].
      cbn [state_wf].
      (* the blank either leaves the list state alone or only arms
         `ls_blanks`; either way `ls_items` is untouched *)
      destruct (blank_absorbed inner); cbn [ls_items list_blank];
        rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs. }
    6: { (* attribute spec: item contents when indented, else close *)
      destruct (list_takes ls off l inner).
      - destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        cbn [state_wf ls_items list_content];
          rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs.
      - destruct (open_attr_wf [] [] (off + indent_of l) kap l) as [Hob Hos].
        rewrite close_reopen_attr. cbn [fst snd]. split; [|exact Hos].
        apply finish_wf. exact H. }
    6: { (* footnote definition: item contents when indented, else close *)
      destruct (list_takes ls off l inner).
      - destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        cbn [state_wf ls_items list_content];
          rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs.
      - destruct (IH (off + consumed l frest) frest (PPara []) eq_refl)
          as [Hb Hs].
        destruct (step_fuel n (off + consumed l frest) frest (PPara []))
          as [bs inner'].
        destruct (open_foot_wf (off + indent_of l) l flbl frest bs inner'
                    E Hb Hs) as [Hob Hos].
        rewrite close_reopen_foot. cbn [fst snd]. split; [|exact Hos].
        apply finish_wf. exact H. }
    6: { (* reference definition: item contents when indented, else close *)
      destruct (list_takes ls off l inner).
      - destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        cbn [state_wf ls_items list_content];
          rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs.
      - destruct (open_ref_wf (off + indent_of l) l rlbl rval E) as [Hob Hos].
        split; [|exact Hos].
        cbn [close_reopen open_ref fst snd]. rewrite app_nil_r.
        apply finish_wf. exact H. }
    (* KRow is an ordinary close-and-reopen kind: the `all:` below. *)
    7: { (* text: lazy continuation into the item, or close the list *)
      destruct (list_takes ls off l inner).
      - destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        cbn [state_wf ls_items list_content];
          rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs.
      - cbn [is_lazy]. destruct (lazy_ok inner) eqn:El; cbn [fst snd].
        + split; [reflexivity|].
          cbn [state_wf list_content ls_items]. rewrite Hitems, Hd. cbn [andb].
          apply feed_lazy_wf, Hi.
        + destruct (open_kind_wf l _ E) as [Hob Hos].
          destruct (open_kind l _) as [obs ost] eqn:Eo.
          cbn [close_reopen fst snd] in Hob, Hos |- *.
          split; [|exact Hos].
          rewrite wf_blocks_app, Hob, andb_true_r.
          apply finish_wf. exact H. }
    4: { (* a quote either belongs to the item or opens after the list *)
      destruct (list_takes ls off l inner).
      - destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        cbn [state_wf ls_items list_content];
          rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs.
      - destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner'].
        cbn [fst snd] in Hb, Hs.
        destruct (quote_header rest)
          as [[[kind fold] title]|].
        + cbn [close_reopen open_callout fst snd]. split.
          * rewrite app_nil_r. apply finish_wf. exact H.
          * reflexivity.
        + cbn [close_reopen open_quote fst snd]. split.
          * try rewrite app_nil_r. apply finish_wf. exact H.
          * cbn [state_wf]. rewrite wf_blocks_rev, Hb. exact Hs. }
    (* every other kind: item contents when indented, else close the
       list and reopen outside it *)
    all: destruct (list_takes ls off l inner);
         [ destruct (IH off l inner Hi) as [Hb Hs];
           destruct (step_fuel n off l inner) as [bs inner'];
           cbn [fst snd] in Hb, Hs |- *;
           split; [reflexivity|];
           cbn [state_wf ls_items list_content];
           rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs
         | first
           [ cbn [close_reopen open_fence fst snd];
             split;
             [ rewrite app_nil_r; apply finish_wf; exact H | reflexivity ]
           | cbn [is_lazy];
             destruct (open_kind_wf l _ E) as [Hob Hos];
             destruct (open_kind l _) as [obs ost] eqn:Eo;
             cbn [close_reopen fst snd] in Hob, Hos |- *;
             split;
             [ rewrite wf_blocks_app, Hob, andb_true_r; apply finish_wf; exact H
             | exact Hos ] ] ].
  - (* an open attribute spec: every branch either hands the line to a
       state this invariant already covers, or records one more line *)
    destruct (ap_done aap); [apply IH; reflexivity|].
    destruct (Nat.ltb aind (off + indent_of l));
      [destruct (ap_failed (attr_feed l aap))|].
    + destruct (IH off l (para_recover 1 aslices) eq_refl) as [Hb Hs].
      exact (pend_result_wf _ _ _ Hb Hs).
    + cbn [fst snd]. split; reflexivity.
    + destruct (is_blank l); [cbn [fst snd state_wf]; split; reflexivity|].
      destruct (IH off l (para_recover 0 aslices) eq_refl) as [Hb Hs].
      exact (pend_result_wf _ _ _ Hb Hs).
  - (* the recovery's paragraph: the branches an open paragraph has, with
       its own flush *)
    destruct (bunderline_of l) as [ulvl|] eqn:Eu; cbn [fst snd].
    { split; [|reflexivity]. apply heading_block_off_wf. reflexivity. }
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy]; cbn [fst snd].
    7: { destruct (binterrupt (KList m mc chk mr)) eqn:Ei; cbn [fst snd].
      - destruct (IH (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara [])) as [bs inner].
        destruct (open_list_wf l (off + indent_of l)
                    (with_starts (configured_list_styles m chk) mc)
                    (configured_list_check chk) bs inner Hb Hs) as [Hob Hos].
        destruct (open_list l (off + indent_of l)
                    (with_starts (configured_list_styles m chk) mc)
                    (configured_list_check chk) (bs, inner)) as [obs ost].
        cbn [close_reopen finish app fst snd] in Hob, Hos |- *; nopos.
        split; [|exact Hos].
        apply flush_para_off_wf, Hob.
      - split; reflexivity. }
    1: (split; [|reflexivity]; apply flush_para_off_wf; reflexivity).
    all: cbn [binterrupt fst snd]; split; reflexivity.
  - (* an open reference definition: a continuation line appends another
       whitespace-free run, and closing emits the block the invariant
       already describes *)
    cbn [state_wf] in H.
    destruct (if Nat.ltb rind (off + indent_of l) then ref_cont l else None)
      as [t|] eqn:Ec.
    + cbn [fst snd]. split; [reflexivity|]. cbn [state_wf].
      apply andb_true_iff in H as [Hlbl Hval]. rewrite Hlbl. cbn [andb].
      apply no_ws_append; [exact Hval|].
      destruct (Nat.ltb rind (off + indent_of l)); [|discriminate Ec].
      apply (ref_cont_no_ws l t Ec).
    + destruct (IH off l (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n off l (PPara [])) as [bs st'].
      cbn [fst snd] in Hb, Hs |- *; nopos. split; [|exact Hs].
      rewrite wf_blocks_cons. cbn [ref_block node_contents mk wf_block].
      rewrite H, Hb. reflexivity.
  - (* an open footnote definition: body lines preserve the accumulated
       blocks; closing emits one well-formed metadata block *)
    cbn [state_wf] in H. apply andb_true_iff in H as [Hfixed Hinner].
    apply andb_true_iff in Hfixed as [Hlbl Hdone].
    assert (Hbody : wf_blocks (rev fdone ++ finish finner)%list = true).
    { rewrite wf_blocks_app, wf_blocks_rev, Hdone, (finish_wf _ Hinner).
      reflexivity. }
    destruct (is_blank l).
    + destruct (IH off l finner Hinner) as [Hb Hs].
      destruct (step_fuel n off l finner) as [bs inner'].
      cbn [fst snd] in Hb, Hs |- *. split; [reflexivity|].
      cbn [state_wf]. rewrite Hlbl, wf_blocks_app, wf_blocks_rev, Hb, Hdone, Hs.
      reflexivity.
    + destruct (foot_takes find off l finner).
      * destruct (IH off l finner Hinner) as [Hb Hs].
        destruct (step_fuel n off l finner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *. split; [reflexivity|].
        cbn [state_wf]. rewrite Hlbl, wf_blocks_app, wf_blocks_rev, Hb, Hdone, Hs.
        reflexivity.
      * destruct (is_lazy (classify l) finner).
        { cbn [fst snd]. split; [reflexivity|].
          cbn [state_wf]. rewrite Hlbl, Hdone, (feed_lazy_wf l finner Hinner).
          reflexivity. }
        destruct (IH off l (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n off l (PPara [])) as [bs st'].
        cbn [fst snd] in Hb, Hs |- *; nopos. split; [|exact Hs].
        rewrite wf_blocks_cons. cbn [foot_block node_contents mk].
        rewrite wf_block_footnote, Hlbl, Hbody, Hb.
        reflexivity.
  - (* a table: a row line extends it, a caption opener starts one, a
       blank leaves it waiting, and anything else emits it and
       reprocesses the line from idle *)
    assert (Htb : wf_blocks [table_block (rev trows) tcap] = true)
      by apply table_block_wf.
    destruct tcap as [| |ls].
    3: { destruct (is_blank l) eqn:Eb; cbn [fst snd].
         - split; [exact Htb | reflexivity].
         - split; reflexivity. }
    all: destruct (caption_open l) as [rest|] eqn:Ec;
         [ split; reflexivity
         | destruct (is_blank l) eqn:Eb; [split; reflexivity|] ].
    { destruct (classify l) eqn:E; cbn [open_line is_lazy]; try (split; reflexivity);
        (destruct (IH off l (PPara []) eq_refl) as [Hb Hs];
         destruct (step_fuel n off l (PPara [])) as [bs st'];
         cbn [fst snd] in Hb, Hs |- *; split; [|exact Hs];
         rewrite wf_blocks_cons; cbn [node_contents];
         rewrite Hb, andb_true_r;
         rewrite wf_blocks_cons in Htb; cbn [node_contents] in Htb;
         rewrite andb_true_r in Htb; exact Htb). }
    { destruct (classify l) eqn:E; cbn [open_line is_lazy];
        (destruct (IH off l (PPara []) eq_refl) as [Hb Hs];
         destruct (step_fuel n off l (PPara [])) as [bs st'];
         cbn [fst snd] in Hb, Hs |- *; split; [|exact Hs];
         rewrite wf_blocks_cons; cbn [node_contents];
         rewrite Hb, andb_true_r;
         rewrite wf_blocks_cons in Htb; cbn [node_contents] in Htb;
         rewrite andb_true_r in Htb; exact Htb). }
  - (* pending attributes: decoration is invisible to wf, and the state
       under them carries the invariant *)
    cbn [state_wf] in H.
    destruct (classify l) eqn:E; cbn [open_line is_lazy];
      try (destruct (is_idle pinner);
           [ solve [ split; reflexivity | apply open_attr_wf ] |]);
      destruct (IH off l pinner H) as [Hb Hs];
      destruct (step_fuel n off l pinner) as [bs st'] eqn:Ed;
      cbn [fst snd] in Hb, Hs;
      destruct bs; cbn [pend_result fst snd state_wf]; nopos;
      (split; [rewrite ?wf_blocks_decorate_head; exact Hb | exact Hs]).
  - (* an open key: the retraction is a paragraph of the line it kept,
       and otherwise `key_close` wraps whatever comes back *)
    cbn [state_wf] in H. rename H into Hi.
    cbn [step_fuel]. destruct (is_blank l && is_idle kinner)%bool.
    { cbn [fst snd]. split; [|reflexivity].
      exact (flush_para_wf [ksrc] [] eq_refl). }
    destruct (IH off l kinner Hi) as [Hb Hs].
    destruct (step_fuel n off l kinner) as [bs st'] eqn:Ed.
    cbn [fst snd] in Hb, Hs.
    destruct bs as [|b bs']; cbn [key_result fst snd state_wf].
    + split; [reflexivity | exact Hs].
    + split; [exact (key_close_wf _ _ _ _ Hb) | exact Hs].
Qed.

Local Lemma step_wf :
  forall l st,
    state_wf st = true ->
    wf_blocks (fst (step l st)) = true /\ state_wf (snd (step l st)) = true.
Proof. intros l st H. apply step_fuel_wf. exact H. Qed.

Local Lemma parse_lines_wf :
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

(** The line fold cannot produce a malformed block list. *)
Theorem wf_parse : forall s, wf_blocks (parse_blocks s) = true.
Proof.
  intros s. unfold parse_blocks. apply parse_lines_wf. reflexivity.
Qed.

(*
Completeness
============
*)

(** wf = image(parse_blocks): the converse of wf_parse, which alone permits
   any weaker predicate.  Asserted nowhere: false as stated, see
   wf_complete_false. *)
Definition wf_complete : Prop :=
  forall bs, wf_blocks bs = true -> exists s, parse_blocks s = bs.

(* The block constructs Parser.v has a rule for.  One is left without:
   `Section` is the document pass's, not the line fold's.  Recursive, so
   a quote whose contents are unreachable is itself unreachable. *)
Local Fixpoint supported (b : block) : bool :=
  let sup_bs :=
    fix go (ns : list (node block)) : bool :=
      match ns with
      | [] => true
      | Node _ _ x :: rest => supported x && go rest
      end in
  let sup_items :=
    fix goi (its : list (node (list (node block)))) : bool :=
      match its with
      | [] => true
      | Node _ _ it :: rest => sup_bs it && goi rest
      end in
  match b with
  | Para _ | ThematicBreak | CodeBlock _ _ | RawBlock _ _ | Heading _ _
  | RefDef _ _ => true
  (* A table's cells and caption hold inlines, so it recurses into
     nothing. *)
  | Table _ _ => true
  | FootnoteDef _ bs => sup_bs bs
  | BlockQuote bs | Div _ bs | Ext_callout _ _ _ bs => sup_bs bs
  (* A label holds inlines, so only the block is recursed into. *)
  | Ext_keyed _ b => sup_bs [b]
  | BulletList _ _ items => sup_items items
  | OrderedList _ _ items => sup_items items
  (* A term holds inlines, so only the definition is recursed into. *)
  | DefinitionList _ items =>
      (fix god (its : list (node (node inlines * node (list (node block))))) : bool :=
         match its with
         | [] => true
         | Node _ _ (_, Node _ _ it) :: rest => sup_bs it && god rest
         end) items
  (* A status is a leaf, so a task item recurses like a definition's. *)
  | TaskList _ items =>
      (fix got (its : list (node (task_status * list (node block)))) : bool :=
         match its with
         | [] => true
         | Node _ _ (_, it) :: rest => sup_bs it && got rest
         end) items
  | _ => false
  end.

Local Definition supported_blocks (bs : blocks) : bool :=
  forallb (fun n => supported (node_contents n)) bs.

Local Lemma supported_footnote :
  forall label bs, supported (FootnoteDef label bs) = supported_blocks bs.
Proof.
  intros label bs. cbn [supported].
  induction bs as [|[p a b] rest IH]; [reflexivity|].
  cbn [supported_blocks forallb node_contents]. rewrite IH. reflexivity.
Qed.

Local Lemma supported_blocks_cons :
  forall n bs,
    supported_blocks (n :: bs)
    = (supported (node_contents n) && supported_blocks bs)%bool.
Proof. reflexivity. Qed.

Local Lemma supported_blocks_app :
  forall bs1 bs2,
    supported_blocks (bs1 ++ bs2)%list
    = (supported_blocks bs1 && supported_blocks bs2)%bool.
Proof. intros bs1 bs2. unfold supported_blocks. apply forallb_app. Qed.

Local Lemma supported_blocks_rev :
  forall bs, supported_blocks (rev bs) = supported_blocks bs.
Proof. intros bs. unfold supported_blocks. apply forallb_rev. Qed.

Local Lemma supported_keyed :
  forall label b, supported (Ext_keyed label b) = supported (node_contents b).
Proof. intros label [q a x]. cbn [supported]. apply andb_true_r. Qed.

Local Lemma supported_quote :
  forall bs, supported (BlockQuote bs) = supported_blocks bs.
Proof.
  induction bs as [|n bs IH]; [reflexivity|].
  destruct n as [p a x].
  change (supported (BlockQuote (Node p a x :: bs)))
    with (supported x && supported (BlockQuote bs))%bool.
  rewrite IH. reflexivity.
Qed.

Local Lemma supported_quote_block :
  forall header bs,
    supported (quote_block header bs) = supported_blocks bs.
Proof.
  intros header bs. destruct header as [[[kind fold] source]|];
    cbn [quote_block];
    change (supported (BlockQuote bs) = supported_blocks bs);
    apply supported_quote.
Qed.

Local Lemma supported_div :
  forall name bs, supported (Div name bs) = supported_blocks bs.
Proof.
  intros name.
  induction bs as [|n bs IH]; [reflexivity|].
  destruct n as [p a x].
  change (supported (Div name (Node p a x :: bs)))
    with (supported x && supported (Div name bs))%bool.
  rewrite IH. reflexivity.
Qed.

Local Lemma div_block_supported :
  forall cls bs,
    supported_blocks bs = true -> supported_blocks [div_block cls bs] = true.
Proof.
  intros cls bs H. unfold div_block.
  destruct bdiv_names; [|destruct (String.eqb cls EmptyString)];
    rewrite supported_blocks_cons; cbn [node_contents mk];
    rewrite supported_div, H; reflexivity.
Qed.

Local Lemma supported_bullet :
  forall bc sp items,
    supported (BulletList bc sp items)
    = forallb (fun it => supported_blocks (node_contents it)) items.
Proof.
  intros bc sp items.
  assert (H : forall its,
             (fix goi (l : list (node (list (node block)))) : bool :=
                match l with
                | [] => true
                | Node _ _ it :: rest => (supported (BlockQuote it) && goi rest)%bool
                end) its = forallb (fun it => supported_blocks (node_contents it)) its).
  { induction its as [|[ip ia it] rest IH]; [reflexivity|].
    cbn [forallb node_contents]. rewrite supported_quote, IH. reflexivity. }
  change (supported (BulletList bc sp items))
    with ((fix goi (l : list (node (list (node block)))) : bool :=
             match l with
             | [] => true
             | Node _ _ it :: rest => (supported (BlockQuote it) && goi rest)%bool
             end) items).
  apply H.
Qed.

Local Lemma supported_olist :
  forall oa sp items,
    supported (OrderedList oa sp items)
    = forallb (fun it => supported_blocks (node_contents it)) items.
Proof.
  intros oa sp items.
  assert (H : forall its,
             (fix goi (l : list (node (list (node block)))) : bool :=
                match l with
                | [] => true
                | Node _ _ it :: rest => (supported (BlockQuote it) && goi rest)%bool
                end) its = forallb (fun it => supported_blocks (node_contents it)) its).
  { induction its as [|[ip ia it] rest IH]; [reflexivity|].
    cbn [forallb node_contents]. rewrite supported_quote, IH. reflexivity. }
  change (supported (OrderedList oa sp items))
    with ((fix goi (l : list (node (list (node block)))) : bool :=
             match l with
             | [] => true
             | Node _ _ it :: rest => (supported (BlockQuote it) && goi rest)%bool
             end) items).
  apply H.
Qed.

Local Lemma supported_deflist :
  forall sp items,
    supported (DefinitionList sp items)
    = forallb (fun ti => supported_blocks (node_contents (snd (node_contents ti)))) items.
Proof.
  intros sp items.
  assert (Hb : forall bs,
             (fix go (ns : list (node block)) : bool :=
                match ns with
                | [] => true
                | Node _ _ x :: rest => (supported x && go rest)%bool
                end) bs = supported_blocks bs).
  { induction bs as [|[p a b] rest IH]; [reflexivity|].
    cbn [supported_blocks forallb node_contents]. rewrite IH. reflexivity. }
  cbn [supported]. induction items as [|[ip ia [term [dp da it]]] rest IH]; [reflexivity|].
  cbn [forallb snd node_contents]. rewrite IH, Hb. reflexivity.
Qed.

(* Unlike `wf_list_block`, this one stays an equation: the blocks the
   split removes are a paragraph, which `supported` answers `true` for,
   and the definitions it steps over stay in the list. *)
Local Lemma supported_def_split :
  forall bs ils def,
    def_split bs = Some (ils, def) ->
    supported_blocks def = supported_blocks bs.
Proof.
  induction bs as [|[q a x] rest IH]; intros ils def E; [discriminate|].
  cbn [def_split] in E. destruct x; try discriminate E.
  - injection E as <- <-.
    rewrite supported_blocks_cons. cbn [node_contents supported]. reflexivity.
  - destruct (def_split rest) as [[ils' more]|] eqn:Es; [|discriminate E].
    injection E as <- <-.
    rewrite !supported_blocks_cons, (IH ils' more eq_refl). reflexivity.
  - destruct (def_split rest) as [[ils' more]|] eqn:Es; [|discriminate E].
    injection E as <- <-.
    rewrite !supported_blocks_cons, (IH ils' more eq_refl). reflexivity.
Qed.

Local Lemma supported_def_items :
  forall its,
    forallb (fun ti => supported_blocks (node_contents (snd (node_contents ti))))
      (def_items its)
    = forallb supported_blocks its.
Proof.
  unfold def_items. induction its as [|it rest IH]; [reflexivity|].
  cbn [forallb map]. rewrite IH. f_equal. unfold def_node.
  destruct (def_split it) as [[ils def]|] eqn:E.
  - rewrite (def_item_some it _ E). cbn [snd node_contents mk].
    exact (supported_def_split it ils def E).
  - rewrite (def_item_none it E). reflexivity.
Qed.

Local Lemma supported_tasklist :
  forall sp items,
    supported (TaskList sp items)
    = forallb (fun ti => supported_blocks (snd (node_contents ti))) items.
Proof.
  intros sp items.
  assert (Hb : forall bs,
             (fix go (ns : list (node block)) : bool :=
                match ns with
                | [] => true
                | Node _ _ x :: rest => (supported x && go rest)%bool
                end) bs = supported_blocks bs).
  { induction bs as [|[p a b] rest IH]; [reflexivity|].
    cbn [supported_blocks forallb node_contents]. rewrite IH. reflexivity. }
  cbn [supported]. induction items as [|[ip ia [st it]] rest IH]; [reflexivity|].
  cbn [forallb snd node_contents]. rewrite IH, Hb. reflexivity.
Qed.

(* Pairing statuses onto items is invisible to `supported`. *)
Local Lemma supported_task_items :
  forall (chks : list task_status) its,
    forallb (fun ti => supported_blocks (snd (node_contents ti))) (task_items chks its)
    = forallb supported_blocks its.
Proof.
  intros chks its. revert chks.
  induction its as [|it rest IH]; intros chks; [reflexivity|].
  destruct chks as [|c cs]; cbn [task_items forallb snd node_contents mk]; rewrite IH;
    reflexivity.
Qed.

(* `supported` cannot tell the list flavours apart, so
   `finish_supported` stays one case. *)
Local Lemma supported_list_block :
  forall ls last,
    supported (node_contents (list_block ls last))
    = forallb supported_blocks (rev (last :: ls_items ls)).
Proof.
  intros ls last. unfold list_block, styles_list_checked, styles_list.
  destruct (ls_styles ls) as [|[[c|c|n d] st] ss].
  - cbn [node_contents mk]. rewrite supported_bullet. apply forallb_mk.
  - destruct (Ascii.eqb c ":" && bdeflists)%bool; cbn [node_contents mk].
    + rewrite supported_deflist. apply supported_def_items.
    + rewrite supported_bullet. apply forallb_mk.
  - cbn [node_contents mk].
    rewrite supported_tasklist. apply supported_task_items.
  - cbn [node_contents mk]. rewrite supported_olist. apply forallb_mk.
Qed.

Local Lemma fence_block_supported :
  forall f content, supported (node_contents (fence_block f content)) = true.
Proof.
  intros f content. unfold fence_block.
  destruct (f_info f) as [|c info]; [reflexivity|].
  destruct c as [[|] [|] [|] [|] [|] [|] [|] [|]];
    destruct braw_blocks; reflexivity.
Qed.

(* The same shape as state_wf: only a quote's closed blocks carry an
   obligation. *)
Local Fixpoint state_supported (st : pstate) : bool :=
  match st with
  | PPara _ | PParaOff _ _ | PHeading _ _ _ | PFence _ _ _ _ _ => true
  | PQuote _ _ done inner => supported_blocks done && state_supported inner
  | PDiv _ _ _ _ done inner => supported_blocks done && state_supported inner
  | PList ls done inner =>
      forallb supported_blocks (ls_items ls) && supported_blocks done
      && state_supported inner
  (* A spec emits at most a paragraph, a definition emits a RefDef, and
     pending attributes emit nothing of their own. *)
  | PAttr _ _ _ _ _ _ | PRef _ _ _ _ | PTable _ _ _ => true
  | PFoot _ _ _ done inner => supported_blocks done && state_supported inner
  | PPend _ _ inner => state_supported inner
  (* A key emits either a paragraph or an `Ext_keyed` over what is under it. *)
  | PKey _ _ _ inner => state_supported inner
  end.

Local Lemma supported_blocks_decorate_head :
  forall a bs, supported_blocks (decorate_head a bs) = supported_blocks bs.
Proof. intros a bs. destruct bs as [|[q a' x] rest]; reflexivity. Qed.

Local Lemma finish_supported :
  forall st, state_supported st = true -> supported_blocks (finish st) = true.
Proof.
  induction st as [cur|lvl hrng hcur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H.
  - destruct cur as [|c cur']; reflexivity.
  - reflexivity.
  - cbn [finish]; nopos. rewrite supported_blocks_cons, fence_block_supported.
    reflexivity.
  - cbn [state_supported] in H. apply andb_true_iff in H as [Hd Hi].
    cbn [finish]; nopos. rewrite supported_blocks_cons. cbn [node_contents mk].
    rewrite supported_quote_block, supported_blocks_app, supported_blocks_rev, Hd,
      (IH Hi).
    reflexivity.
  - cbn [state_supported] in H. apply andb_true_iff in H as [Hd Hi].
    cbn [finish]; nopos. apply div_block_supported.
    rewrite supported_blocks_app, supported_blocks_rev, Hd, (IH Hi).
    reflexivity.
  - cbn [state_supported] in H. apply andb_true_iff in H as [H1 Hi].
    apply andb_true_iff in H1 as [Hitems Hd].
    cbn [finish]; nopos. rewrite supported_blocks_cons.
    rewrite supported_list_block, forallb_rev. cbn [forallb].
    rewrite supported_blocks_app, supported_blocks_rev, Hd, (IH Hi), Hitems.
    reflexivity.
  - cbn [finish]; nopos. destruct (ap_done aap); [reflexivity|].
    cbn [finish_para_recover]; nopos. destruct aslices; reflexivity.
  - reflexivity.                        (* the recovery's paragraph *)
  - reflexivity.
  - cbn [state_supported] in H. apply andb_true_iff in H as [Hd Hi].
    cbn [finish]; nopos. rewrite supported_blocks_cons. cbn [foot_block node_contents mk].
    rewrite supported_footnote.
    rewrite supported_blocks_app, supported_blocks_rev, Hd, (IH Hi).
    reflexivity.
  - reflexivity.                        (* a table recurses into nothing *)
  - cbn [state_supported] in H. cbn [finish]; nopos.
    rewrite supported_blocks_decorate_head. exact (IH H).
  - cbn [state_supported] in H. rewrite finish_key; nopos.
    pose proof (IH H) as Hi.
    destruct (finish kinner) as [|b rest]; [reflexivity|].
    cbn [key_close]. rewrite supported_blocks_cons in Hi |- *.
    cbn [node_contents mk]. rewrite supported_keyed. exact Hi.
Qed.

Local Lemma feed_lazy_supported :
  forall l st,
    state_supported st = true -> state_supported (feed_lazy l st) = true.
Proof.
  induction st as [cur|lvl hrng hcur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH
    |ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
    |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros H;
    [reflexivity | reflexivity | reflexivity | | | | reflexivity | reflexivity
    | reflexivity | | reflexivity | | ].
  5: { cbn [feed_lazy state_supported] in *. exact (IH H). }
  5: { cbn [feed_lazy state_supported] in *. exact (IH H). }
  - cbn [feed_lazy state_supported] in *.
    apply andb_true_iff in H as [Hd Hi]. rewrite Hd, (IH Hi). reflexivity.
  - cbn [feed_lazy state_supported] in *.
    apply andb_true_iff in H as [Hd Hi]. rewrite Hd, (IH Hi). reflexivity.
  - cbn [feed_lazy state_supported list_content ls_items] in *.
    apply andb_true_iff in H as [H1 Hi]. apply andb_true_iff in H1 as [Ht Hd].
    rewrite Ht, Hd, (IH Hi). reflexivity.
  - cbn [feed_lazy state_supported] in *.
    apply andb_true_iff in H as [Hd Hi]. rewrite Hd, (IH Hi). reflexivity.
Qed.

Local Lemma open_list_supported :
  forall l ind m chk bs inner,
    supported_blocks bs = true -> state_supported inner = true ->
    supported_blocks (fst (open_list l ind m chk (bs, inner))) = true
    /\ state_supported (snd (open_list l ind m chk (bs, inner))) = true.
Proof.
  intros l ind m chk bs inner Hb Hi.
  cbn [open_list list_opened fst snd state_supported ls_items forallb].
  split; [reflexivity|]. rewrite supported_blocks_rev, Hb, Hi. reflexivity.
Qed.

(* Same case analysis as step_fuel_wf: the emitted constructors are
   supported unconditionally, so only the container accumulators are
   threaded. *)
(* `pend_result_wf` for the support invariant, and for the same reason. *)
Local Lemma pend_result_supported :
  forall pend specs r,
    supported_blocks (fst r) = true ->
    state_supported (snd r) = true ->
    supported_blocks (fst (pend_result pend specs r)) = true
    /\ state_supported (snd (pend_result pend specs r)) = true.
Proof.
  intros pend specs [bs st] Hb Hs. cbn [fst snd] in Hb, Hs.
  destruct bs; cbn [pend_result fst snd state_supported]; nopos;
    (split; [rewrite ?supported_blocks_decorate_head; exact Hb | exact Hs]).
Qed.

Local Lemma step_fuel_supported :
  forall n off l st,
    state_supported st = true ->
    supported_blocks (fst (step_fuel n off l st)) = true
    /\ state_supported (snd (step_fuel n off l st)) = true.
Proof.
  induction n as [|n IH]; intros off l st H; [split; [reflexivity | exact H]|].
  cbn [step_fuel open_line].
  destruct st as [cur|hlvl hrng hcur|f fnd crng cop acc|qrng qhead done inner|dlen dcls drng dop ddone dinner|ls done inner|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner|trng trows tcap|ppend pspecs pinner|krng klbl ksrc kinner].
  - destruct cur as [|c cur'].
    + destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy];
        try (cbn [close_reopen open_quote finish app open_kind open_fence open_attr open_ref fst snd]; nopos; split; reflexivity).
      * cbn [open_kind fst snd]. destruct (@bdivs K); cbn [fst snd];
          split; reflexivity.
      * destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner].
        destruct (quote_header rest)
          as [[[kind fold] title]|].
        -- cbn [open_callout fst snd state_supported]. split; reflexivity.
        -- cbn [close_reopen open_quote finish app fst snd] in Hb, Hs |- *; nopos.
           split; [reflexivity|].
           cbn [state_supported]. rewrite supported_blocks_rev, Hb. exact Hs.
      * destruct (IH (off + consumed l (configured_list_rest chk mr))
          (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
          (configured_list_rest chk mr) (PPara [])) as [bs inner].
        apply open_list_supported; assumption.
      * unfold open_attr. destruct (@battrs K);
          cbn [close_reopen finish app fst snd state_supported]; nopos;
          split; reflexivity.
      * destruct (IH (off + consumed l frest) frest (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l frest) frest (PPara [])) as [bs inner].
        cbn [fst snd] in Hb, Hs.
        unfold open_foot. destruct (@bfootnotes K);
          cbn [fst snd state_supported]; split; try reflexivity.
        rewrite supported_blocks_rev, Hb. exact Hs.
      * cbn [open_kind fst snd]. destruct (@btables K); split; reflexivity.
      * cbn [open_kind]. unfold open_text.
        destruct (if @bkeyed K then key_split (drop_leading_ws l) else None)
          as [[lbl v]|]; cbn [fst snd state_supported]; split; reflexivity.
    + destruct (bunderline_of l) as [ulvl|] eqn:Eu;
        [cbn [fst snd]; split; reflexivity|].
      destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
      7: { destruct (binterrupt (KList m mc chk mr)) eqn:Ei;
             [|cbn [fst snd]; split; reflexivity].
        destruct (IH (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara [])) as [bs inner].
           destruct (open_list_supported l (off + indent_of l)
                       (with_starts (configured_list_styles m chk) mc)
                       (configured_list_check chk) bs inner Hb Hs) as [Hob Hos].
           destruct (open_list l (off + indent_of l)
                       (with_starts (configured_list_styles m chk) mc)
                       (configured_list_check chk) (bs, inner)) as [obs ost].
           cbn [close_reopen finish app fst snd] in Hob, Hos |- *; nopos.
           rewrite supported_blocks_cons. cbn [node_contents].
           rewrite Hob. split; [reflexivity | exact Hos]. }
      all: cbn [binterrupt fst snd]; split; reflexivity.
  - (* an open heading: Heading is supported, so only the quote branch
       carries anything to prove *)
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
    4: { cbn [open_kind close_reopen finish app fst snd]; nopos.
         destruct (@bdivs K); cbn [fst snd]; split; reflexivity. }
    6: { destruct (IH (off + consumed l (configured_list_rest chk mr))
           (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
         destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
           (configured_list_rest chk mr) (PPara [])) as [bs inner].
         destruct (open_list_supported l (off + indent_of l)
           (with_starts (configured_list_styles m chk) mc)
           (configured_list_check chk) bs inner Hb Hs)
           as [Hob Hos].
         destruct (open_list l (off + indent_of l)
           (with_starts (configured_list_styles m chk) mc)
           (configured_list_check chk) (bs, inner)) as [obs ost].
         cbn [close_reopen finish app fst snd] in Hob, Hos |- *; nopos.
         rewrite supported_blocks_cons. cbn [node_contents].
         rewrite Hob. split; [reflexivity | exact Hos]. }
    4: { destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
         destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner].
         destruct (quote_header rest)
           as [[[kind fold] title]|].
         - cbn [close_reopen open_callout finish app fst snd]; nopos.
           split; reflexivity.
         - cbn [close_reopen open_quote finish app fst snd] in Hb, Hs |- *; nopos.
           split; [reflexivity|].
           cbn [state_supported]. rewrite supported_blocks_rev, Hb. exact Hs. }
    4: { destruct bheading_continues;
           [destruct (Nat.eqb kl hlvl)|];
           cbn [close_reopen open_kind finish app fst snd]; nopos;
           split; reflexivity. }
    5: { destruct (IH (off + consumed l frest) frest (PPara []) eq_refl)
           as [Hb Hs].
         destruct (step_fuel n (off + consumed l frest) frest (PPara []))
           as [bs inner].
         cbn [fst snd] in Hb, Hs.
         unfold open_foot. destruct (@bfootnotes K);
           cbn [close_reopen finish app fst snd]; nopos; split; try reflexivity;
           cbn [state_supported]; rewrite supported_blocks_rev, Hb; exact Hs. }
    6: { cbn [close_reopen open_kind finish app fst snd]; nopos.
         destruct (@btables K); split; reflexivity. }
    all: destruct bheading_continues; unfold open_attr;
         try destruct (@battrs K);
         cbn [open_kind];
         try (unfold open_text;
              destruct (if @bkeyed K then key_split (drop_leading_ws l) else None)
                as [[?klb ?kv]|]);
         cbn [close_reopen open_quote finish app open_fence open_ref fst snd]; nopos;
         split; reflexivity.
  - destruct (fence_close f l); cbn [fst snd]; nopos.
    + rewrite supported_blocks_cons, fence_block_supported. split; reflexivity.
    + split; reflexivity.
  - pose proof H as H0. cbn [state_supported] in H0.
    apply andb_true_iff in H0 as [Hd Hi].
    assert (Hbq : supported (quote_block qhead (rev done ++ finish inner)%list) = true).
    { rewrite supported_quote_block, supported_blocks_app, supported_blocks_rev, Hd,
        (finish_supported _ Hi).
      reflexivity. }
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
    4: { cbn [is_lazy open_kind]. destruct (@bdivs K);
         cbn [close_reopen finish app fst snd]; nopos; split; try reflexivity;
         rewrite supported_blocks_cons; cbn [node_contents mk];
         rewrite Hbq; reflexivity. }
    6: { destruct (IH (off + consumed l (configured_list_rest chk mr))
           (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
         destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
           (configured_list_rest chk mr) (PPara [])) as [bs inner'].
         destruct (open_list_supported l (off + indent_of l)
           (with_starts (configured_list_styles m chk) mc)
           (configured_list_check chk) bs inner' Hb Hs)
           as [Hob Hos].
         destruct (open_list l (off + indent_of l)
           (with_starts (configured_list_styles m chk) mc)
           (configured_list_check chk) (bs, inner')) as [obs ost].
         cbn [close_reopen finish app fst snd] in Hob, Hos |- *; nopos.
         split; [|exact Hos].
         rewrite supported_blocks_cons. cbn [node_contents mk].
         rewrite Hbq, Hob. reflexivity. }
    4: { destruct (IH (off + consumed l rest) rest inner Hi) as [Hb Hs].
         destruct (step_fuel n (off + consumed l rest) rest inner) as [bs inner'].
         cbn [close_reopen open_quote finish app fst snd] in Hb, Hs |- *; nopos.
         split; [reflexivity|].
         cbn [state_supported].
         rewrite supported_blocks_app, supported_blocks_rev, Hb, Hd. exact Hs. }
    6: { destruct (IH (off + consumed l frest) frest (PPara []) eq_refl)
           as [Hb Hs].
         destruct (step_fuel n (off + consumed l frest) frest (PPara []))
           as [bs inner'].
         cbn [fst snd] in Hb, Hs.
         unfold open_foot. destruct (@bfootnotes K);
           cbn [close_reopen finish app fst snd]; nopos; split;
           try (rewrite supported_blocks_cons; cbn [node_contents mk];
                rewrite Hbq; reflexivity);
           try reflexivity;
           cbn [state_supported]; rewrite supported_blocks_rev, Hb; exact Hs. }
    7: { cbn [is_lazy open_kind]. destruct (@btables K);
         cbn [close_reopen finish app fst snd]; nopos; split; try reflexivity;
         rewrite supported_blocks_cons; cbn [node_contents mk];
         rewrite Hbq; reflexivity. }
    7: { cbn [is_lazy]. destruct (lazy_ok inner).
         - cbn [close_reopen open_quote finish app open_fence open_attr open_ref fst snd]; nopos.
           split; [reflexivity|].
           cbn [state_supported]. rewrite Hd. cbn [andb].
           apply feed_lazy_supported. exact Hi.
         - cbn [open_kind]. unfold open_text.
           destruct (if @bkeyed K then key_split (drop_leading_ws l) else None)
             as [[klb kv]|];
             cbn [close_reopen finish app fst snd]; nopos; split; try reflexivity;
             rewrite supported_blocks_cons; cbn [node_contents mk];
             rewrite Hbq; cbn [andb]; reflexivity. }
    all: unfold open_attr; try destruct (@battrs K);
         cbn [is_lazy close_reopen open_quote finish app open_kind open_fence
              open_ref fst snd]; nopos; split; try reflexivity;
         rewrite supported_blocks_cons; cbn [node_contents mk]; rewrite Hbq;
         cbn [andb]; reflexivity.
  - (* a div: close, or descend; the same two goals as in step_fuel_wf *)
    pose proof H as H0. cbn [state_supported] in H0.
    apply andb_true_iff in H0 as [Hd Hi].
    destruct (negb (in_fence dinner) && div_close dlen l)%bool; cbn [fst snd].
    + split; [|reflexivity].
      apply div_block_supported.
      rewrite supported_blocks_app, supported_blocks_rev, Hd,
        (finish_supported _ Hi).
      reflexivity.
    + destruct (IH off l dinner Hi) as [Hb Hs].
      destruct (step_fuel n off l dinner) as [bs inner'].
      cbn [fst snd] in Hb, Hs |- *.
      split; [reflexivity|].
      cbn [state_supported].
      rewrite supported_blocks_app, supported_blocks_rev, Hb, Hd. exact Hs.
  - (* inside a list *)
    pose proof H as H0. cbn [state_supported] in H0.
    apply andb_true_iff in H0 as [H1 Hi].
    apply andb_true_iff in H1 as [Hitems Hd].
    assert (Hitem : supported_blocks (rev done ++ finish inner)%list = true).
    { rewrite supported_blocks_app, supported_blocks_rev, Hd,
        (finish_supported _ Hi). reflexivity. }
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
    4: { destruct (list_takes ls off l inner).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *. split; [reflexivity|].
           cbn [state_supported ls_items list_content];
             rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
             exact Hs.
         - cbn [is_lazy open_kind]. destruct (@bdivs K);
             cbn [close_reopen fst snd]; split; try reflexivity;
             rewrite supported_blocks_app, (finish_supported _ H);
             reflexivity. }
    6: { destruct (list_takes ls off l inner).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *.
           split; [reflexivity|].
           cbn [state_supported ls_items list_content];
             rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
             exact Hs.
         - destruct (narrow (ls_styles ls) (configured_list_styles m chk)).
           + destruct (IH (off + consumed l (configured_list_rest chk mr))
               (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
             destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
               (configured_list_rest chk mr) (PPara [])) as [bs inner'].
             destruct (open_list_supported l (off + indent_of l)
               (with_starts (configured_list_styles m chk) mc)
               (configured_list_check chk) bs inner' Hb Hs)
               as [Hob Hos].
             destruct (open_list l (off + indent_of l)
               (with_starts (configured_list_styles m chk) mc)
               (configured_list_check chk) (bs, inner')) as [obs ost].
             cbn [close_reopen fst snd] in Hob, Hos |- *.
             split; [|exact Hos].
             rewrite supported_blocks_app, Hob, andb_true_r.
             apply finish_supported. exact H.
           + destruct (IH (off + consumed l (configured_list_rest chk mr))
               (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
             destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
               (configured_list_rest chk mr) (PPara [])) as [bs inner'].
             cbn [fst snd] in Hb, Hs |- *.
             split; [reflexivity|].
             cbn [state_supported]. unfold list_next, list_narrow.
             destruct (is_blank (configured_list_rest chk mr)); cbn [ls_items forallb];
               rewrite Hitem, Hitems, supported_blocks_rev, Hb; exact Hs. }
    1: { destruct (IH off l inner Hi) as [Hb Hs].
         destruct (step_fuel n off l inner) as [bs inner'].
         cbn [fst snd] in Hb, Hs |- *.
         split; [reflexivity|].
         cbn [state_supported].
         destruct (blank_absorbed inner); cbn [ls_items list_blank];
           rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
           exact Hs. }
    6: { destruct (list_takes ls off l inner).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *.
           split; [reflexivity|].
           cbn [state_supported ls_items list_content];
             rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
             exact Hs.
         - destruct (IH (off + consumed l frest) frest (PPara []) eq_refl)
             as [Hb Hs].
           destruct (step_fuel n (off + consumed l frest) frest (PPara []))
             as [bs inner'].
           cbn [fst snd] in Hb, Hs.
           rewrite close_reopen_foot. cbn [fst snd]. split.
           + apply finish_supported. exact H.
           + unfold open_foot in *. destruct (@bfootnotes K);
               cbn [snd state_supported]; try reflexivity.
             rewrite supported_blocks_rev, Hb. exact Hs. }
    7: { destruct (list_takes ls off l inner).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *. split; [reflexivity|].
           cbn [state_supported ls_items list_content];
             rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
             exact Hs.
         - cbn [is_lazy open_kind]. destruct (@btables K);
             cbn [close_reopen fst snd]; split; try reflexivity;
             rewrite supported_blocks_app, (finish_supported _ H);
             reflexivity. }
    7: { destruct (list_takes ls off l inner).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *.
           split; [reflexivity|].
           cbn [state_supported ls_items list_content];
             rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
             exact Hs.
         - cbn [is_lazy]. destruct (lazy_ok inner); cbn [fst snd].
           + split; [reflexivity|].
             cbn [state_supported list_content ls_items]. rewrite Hitems, Hd. cbn [andb].
             apply feed_lazy_supported. exact Hi.
           + cbn [open_kind]. unfold open_text.
             destruct (if @bkeyed K then key_split (drop_leading_ws l) else None)
               as [[klb kv]|];
               cbn [close_reopen open_attr open_ref fst snd];
               (split; [|reflexivity]);
               rewrite supported_blocks_app, (finish_supported _ H);
               reflexivity. }
    3: { destruct (list_takes ls off l inner).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *.
           split; [reflexivity|].
           cbn [state_supported ls_items list_content];
             rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
             exact Hs.
         - destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
           destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner'].
           cbn [fst snd] in Hb, Hs.
           destruct (quote_header rest)
             as [[[kind fold] title]|].
           + cbn [close_reopen open_callout fst snd]. split.
             * rewrite app_nil_r. apply finish_supported. exact H.
             * reflexivity.
           + cbn [close_reopen open_quote fst snd]. split.
             * try rewrite app_nil_r. apply finish_supported. exact H.
             * cbn [state_supported]. rewrite supported_blocks_rev, Hb. exact Hs. }
    all: destruct (list_takes ls off l inner);
         [ destruct (IH off l inner Hi) as [Hb Hs];
           destruct (step_fuel n off l inner) as [bs inner'];
           cbn [fst snd] in Hb, Hs |- *;
           split; [reflexivity|];
           cbn [state_supported ls_items list_content];
           rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
           exact Hs
         | unfold open_attr; try destruct (@battrs K);
           cbn [is_lazy close_reopen open_kind open_fence open_ref fst snd];
           split; try reflexivity;
           rewrite supported_blocks_app, (finish_supported _ H);
           reflexivity ].
  - (* an attribute spec emits nothing until it resolves *)
    destruct (ap_done aap); [apply IH; reflexivity|].
    destruct (Nat.ltb aind (off + indent_of l));
      [destruct (ap_failed (attr_feed l aap))|];
      [ destruct (IH off l (para_recover 1 aslices) eq_refl) as [Hb Hs];
        exact (pend_result_supported _ _ _ Hb Hs)
      | split; reflexivity
      | destruct (is_blank l);
        [ cbn [fst snd state_supported]; split; reflexivity
        | destruct (IH off l (para_recover 0 aslices) eq_refl) as [Hb Hs];
          exact (pend_result_supported _ _ _ Hb Hs) ] ].
  - (* the recovery's paragraph: Para and Heading are both supported, so
       only the list branch carries anything *)
    destruct (bunderline_of l) as [ulvl|] eqn:Eu;
      [cbn [fst snd]; split; reflexivity|].
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
    7: { destruct (binterrupt (KList m mc chk mr)) eqn:Ei;
           [|cbn [fst snd]; split; reflexivity].
      destruct (IH (off + consumed l (configured_list_rest chk mr))
                  (configured_list_rest chk mr) (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                  (configured_list_rest chk mr) (PPara [])) as [bs inner].
      destruct (open_list_supported l (off + indent_of l)
                  (with_starts (configured_list_styles m chk) mc)
                  (configured_list_check chk) bs inner Hb Hs) as [Hob Hos].
      destruct (open_list l (off + indent_of l)
                  (with_starts (configured_list_styles m chk) mc)
                  (configured_list_check chk) (bs, inner)) as [obs ost].
      cbn [close_reopen finish app fst snd] in Hob, Hos |- *; nopos.
      rewrite supported_blocks_cons. cbn [node_contents].
      rewrite Hob. split; [reflexivity | exact Hos]. }
    all: cbn [binterrupt fst snd]; split; reflexivity.
  - (* a reference definition: it emits a RefDef, which is supported *)
    destruct (if Nat.ltb rind (off + indent_of l) then ref_cont l else None);
      [split; reflexivity|].
    destruct (IH off l (PPara []) eq_refl) as [Hb Hs].
    destruct (step_fuel n off l (PPara [])) as [bs st'].
    cbn [fst snd] in Hb, Hs |- *; nopos.
    rewrite supported_blocks_cons, Hb. split; [reflexivity|exact Hs].
  - cbn [state_supported] in H. apply andb_true_iff in H as [Hd Hi].
    assert (Hbody : supported_blocks (rev fdone ++ finish finner)%list = true).
    { rewrite supported_blocks_app, supported_blocks_rev, Hd,
        (finish_supported _ Hi). reflexivity. }
    destruct (is_blank l).
    + destruct (IH off l finner Hi) as [Hb Hs].
      destruct (step_fuel n off l finner) as [bs inner'].
      cbn [fst snd] in Hb, Hs |- *. split; [reflexivity|].
      cbn [state_supported].
      rewrite supported_blocks_app, supported_blocks_rev, Hb, Hd, Hs.
      reflexivity.
    + destruct (foot_takes find off l finner).
      * destruct (IH off l finner Hi) as [Hb Hs].
        destruct (step_fuel n off l finner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *. split; [reflexivity|].
        cbn [state_supported].
        rewrite supported_blocks_app, supported_blocks_rev, Hb, Hd, Hs.
        reflexivity.
      * destruct (is_lazy (classify l) finner).
        { cbn [fst snd]. split; [reflexivity|].
          cbn [state_supported]. rewrite Hd, (feed_lazy_supported l finner Hi).
          reflexivity. }
        destruct (IH off l (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n off l (PPara [])) as [bs st'].
        cbn [fst snd] in Hb, Hs |- *; nopos. split; [|exact Hs].
        rewrite supported_blocks_cons. cbn [foot_block node_contents mk].
        rewrite supported_footnote, Hbody, Hb. reflexivity.
  - (* a table: what it emits is supported, and so is what the line
       reopens *)
    destruct tcap as [| |ls].
    3: { destruct (is_blank l); cbn [fst snd]; split; reflexivity. }
    all: destruct (caption_open l) as [rest|] eqn:Ec; [split; reflexivity|];
         destruct (is_blank l) eqn:Eb; [split; reflexivity|];
         destruct (classify l) eqn:E; cbn [open_line is_lazy]; try (split; reflexivity);
         (destruct (IH off l (PPara []) eq_refl) as [Hb Hs];
          destruct (step_fuel n off l (PPara [])) as [bs st'];
          cbn [fst snd] in Hb, Hs |- *; nopos; split; [|exact Hs];
          rewrite supported_blocks_cons; cbn [table_block node_contents mk];
          exact Hb).
  - cbn [state_supported] in H.
    destruct (classify l) eqn:E; cbn [open_line is_lazy];
      try (destruct (is_idle pinner);
           [try unfold open_attr; try destruct (@battrs K);
            split; reflexivity|]);
      destruct (IH off l pinner H) as [Hb Hs];
      destruct (step_fuel n off l pinner) as [bs st'] eqn:Ed;
      cbn [fst snd] in Hb, Hs;
      destruct bs; cbn [pend_result fst snd state_supported]; nopos;
      (split; [rewrite ?supported_blocks_decorate_head; exact Hb | exact Hs]).
  - (* an open key: a paragraph, or an `Ext_keyed` over a block that already
       carried the invariant *)
    cbn [state_supported] in H.
    destruct (is_blank l && is_idle kinner)%bool; [split; reflexivity|].
    destruct (IH off l kinner H) as [Hb Hs].
    destruct (step_fuel n off l kinner) as [bs st'] eqn:Ed.
    cbn [fst snd] in Hb, Hs.
    destruct bs as [|b rest]; cbn [key_result fst snd state_supported].
    + split; [reflexivity | exact Hs].
    + split; [|exact Hs]. cbn [key_close]; nopos.
      rewrite supported_blocks_cons in Hb |- *. cbn [node_contents mk].
      rewrite supported_keyed. exact Hb.
Qed.

Local Lemma parse_lines_supported :
  forall lines st,
    state_supported st = true ->
    supported_blocks (parse_lines lines st) = true.
Proof.
  induction lines as [|l rest IH]; intros st Hst.
  - apply finish_supported. exact Hst.
  - destruct (step_fuel_supported (S (String.length l + pstate_depth st))
                0 l st Hst) as [Hb Hs].
    change (step_fuel (S (String.length l + pstate_depth st)) 0 l st)
      with (step l st) in Hb, Hs.
    destruct (step l st) as [bs st'] eqn:Es.
    cbn [fst snd] in Hb, Hs.
    rewrite (parse_lines_step _ _ _ _ _ Es), supported_blocks_app, Hb.
    apply IH. exact Hs.
Qed.

(* Counterexample: a `Section`, well-formed and unreachable from the line
   fold: sections only ever come from `Document.sectionize`, which runs
   after it.  The gap is coverage, not a missing wf condition, so
   completeness has to be restated over the parser's fragment in
   canonical form, i.e. Render.v's cb_ok cblocks. *)
Theorem wf_complete_false : ~ wf_complete.
Proof.
  intros Hc.
  destruct (Hc [mk (Section [mk ThematicBreak])] eq_refl) as [s Hs].
  pose proof (parse_lines_supported (split_lines s) (PPara []) eq_refl) as Hsup.
  change (parse_lines (split_lines s) (PPara []))
    with (parse_blocks s) in Hsup.
  rewrite Hs in Hsup. discriminate.
Qed.

(*
The whole-document pass
=======================

wf_parse is about the line fold alone.  Document.parse_doc runs the
whole-document pass on top of it, so well-formedness has to survive that
too, or the guarantee no longer covers the parser's actual entry point.

Two obligations, one per half of the pass:
- assigning identifiers rewrites attributes and nothing else, and wf_block
  never inspects a block's attributes;
- sectionize introduces `Section` nodes, which do carry a nonempty
  obligation, discharged because every section starts with the heading
  that opened it.
*)

Local Lemma wf_block_section :
  forall bs, wf_block (Section bs) = (nonempty bs && wf_blocks bs)%bool.
Proof.
  intros bs.
  change (wf_block (Section bs))
    with (nonempty bs && wf_block (BlockQuote bs))%bool.
  rewrite wf_block_quote. reflexivity.
Qed.

(*
Identifiers
-----------
*)

Local Lemma assign_ids_wf :
  forall b p a st,
    wf_block b = true ->
    wf_block (node_contents (snd (Ids.of_block b p a st))) = true.
Proof.
  intros b.
  induction b using block_ind2 with
    (Q := fun bs => forall st,
            wf_blocks bs = true ->
            wf_blocks (snd (Ids.of_list bs st)) = true)
    (R := fun its => forall st,
            forallb (fun it => wf_blocks (node_contents it)) its = true ->
            forallb (fun it => wf_blocks (node_contents it)) (snd (Ids.of_items its st)) = true)
    (D := fun its => forall st,
            forallb wf_def_entry its
            = true ->
            forallb wf_def_entry (snd (Ids.of_def_items its st)) = true)
    (K := fun its => forall st,
            forallb (fun ti => wf_blocks (snd (node_contents ti))) its = true ->
            forallb (fun ti => wf_blocks (snd (node_contents ti)))
              (snd (Ids.of_task_items its st)) = true);
    intros; try exact H.
  (* A `Section` is unreachable from the line fold, but the lemma is
     stated for every block, so it is discharged by the identity branch
     of Ids.of_block above. *)
  - (* Heading *)
    unfold Ids.of_block, assign_heading_id.
    destruct (alist_lookup "id" a) as [v|]; exact H.
  - (* BlockQuote *)
    rewrite Ids.quote.
    destruct (Ids.of_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd node_contents].
    rewrite wf_block_quote in H |- *.
    change bs' with (snd (st', bs')). rewrite <- E.
    apply IHb. exact H.
  - (* Div *)
    rewrite Ids.div.
    destruct (Ids.of_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd node_contents].
    rewrite wf_block_div in H |- *.
    change bs' with (snd (st', bs')). rewrite <- E.
    apply IHb. exact H.
  - (* OrderedList: as the bullet case below *)
    rewrite Ids.olist.
    destruct (Ids.of_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd node_contents].
    rewrite wf_block_olist in H |- *.
    apply andb_true_iff in H as [Hne Hits].
    apply andb_true_iff. split.
    + replace its' with (snd (Ids.of_items items (register_id a st)))
        by (rewrite E; reflexivity).
      rewrite Ids.items_nonempty. exact Hne.
    + change its' with (snd (st', its')). rewrite <- E.
      apply IHb. exact Hits.
  - (* BulletList: the id pass rewrites items, so the nonempty conjunct
       has to survive the traversal too *)
    rewrite Ids.blist.
    destruct (Ids.of_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd node_contents].
    rewrite wf_block_bullet in H |- *.
    apply andb_true_iff in H as [Hne Hits].
    apply andb_true_iff. split.
    + replace its' with (snd (Ids.of_items items (register_id a st)))
        by (rewrite E; reflexivity).
      rewrite Ids.items_nonempty. exact Hne.
    + change its' with (snd (st', its')). rewrite <- E.
      apply IHb. exact Hits.
  - (* TaskList: as the bullet case, over pairs *)
    rewrite Ids.tasklist.
    destruct (Ids.of_task_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd node_contents].
    rewrite wf_block_tasklist in H |- *.
    apply andb_true_iff in H as [Hne Hits].
    apply andb_true_iff. split.
    + replace its' with (snd (Ids.of_task_items items (register_id a st)))
        by (rewrite E; reflexivity).
      rewrite Ids.task_items_nonempty. exact Hne.
    + change its' with (snd (st', its')). rewrite <- E.
      apply IHb. exact Hits.
  - (* DefinitionList: as the bullet case, over pairs *)
    rewrite Ids.deflist.
    destruct (Ids.of_def_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd node_contents].
    rewrite wf_block_deflist in H |- *.
    apply andb_true_iff in H as [Hne Hits].
    apply andb_true_iff. split.
    + replace its' with (snd (Ids.of_def_items items (register_id a st)))
        by (rewrite E; reflexivity).
      rewrite Ids.def_items_nonempty. exact Hne.
    + change its' with (snd (st', its')). rewrite <- E.
      apply IHb. exact Hits.
  - (* FootnoteDef: identifiers recurse through its body. *)
    rewrite Ids.foot.
    destruct (Ids.of_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd node_contents]. rewrite wf_block_footnote in H |- *.
    apply andb_true_iff in H as [Hlbl Hbs].
    apply andb_true_iff. split; [exact Hlbl|].
    change bs' with (snd (st', bs')). rewrite <- E. apply IHb. exact Hbs.
  - (* Ext_keyed: the label is untouched and the block is `Q` at a
       singleton. *)
    rewrite wf_block_keyed in H. apply andb_true_iff in H as [Hlbl Hb].
    destruct b as [p' a' x].
    cbn [Ids.of_block] in *.
    destruct (Ids.of_block x p' a' (register_id a st)) as [st1 n1] eqn:E1.
    cbn [snd node_contents]. rewrite wf_block_keyed.
    apply andb_true_iff. split; [exact Hlbl|].
    specialize (IHb (register_id a st) Hb).
    cbn [Ids.of_list Ids.of_node] in IHb. rewrite E1 in IHb.
    cbn [snd] in IHb. exact IHb.
  - (* Ext_callout: the title is unchanged; identifiers traverse the body. *)
    rewrite Ids.callout.
    destruct (Ids.of_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd node_contents]. rewrite wf_block_callout in H |- *.
    apply andb_true_iff in H as [Htitle Hbs].
    apply andb_true_iff. split; [exact Htitle|].
    change bs' with (snd (st', bs')). rewrite <- E.
    apply IHb. exact Hbs.
  - (* Node p a b :: rest *)
    rewrite wf_blocks_cons in H. apply andb_true_iff in H as [Hx Hrest].
    cbn [Ids.of_list Ids.of_node].
    destruct (Ids.of_block b p a st) as [st1 n1] eqn:E1.
    destruct (Ids.of_list rest st1) as [st2 rest1] eqn:E2.
    cbn [snd]. rewrite wf_blocks_cons.
    apply andb_true_iff. split.
    + change n1 with (snd (st1, n1)). rewrite <- E1. apply IHb. exact Hx.
    + change rest1 with (snd (st2, rest1)). rewrite <- E2.
      apply IHb0. exact Hrest.
  - (* R's cons *)
    cbn [forallb node_contents wf_def_entry] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [Ids.of_items].
    destruct (Ids.of_list it st) as [s1 it1] eqn:E1.
    destruct (Ids.of_items rest s1) as [s2 rest1] eqn:E2.
    cbn [snd forallb node_contents wf_def_entry]. apply andb_true_iff. split.
    + change it1 with (snd (s1, it1)). rewrite <- E1. apply IHb. exact Hit.
    + change rest1 with (snd (s2, rest1)). rewrite <- E2.
      apply IHb0. exact Hrest.
  - (* D's cons: the term is carried, so only the definition moves *)
    cbn [forallb fst snd node_contents wf_def_entry] in H. apply andb_true_iff in H as [Hit Hrest].
    apply andb_true_iff in Hit as [Hterm Hit].
    cbn [Ids.of_def_items].
    destruct (Ids.of_list it st) as [s1 it1] eqn:E1.
    destruct (Ids.of_def_items rest s1) as [s2 rest1] eqn:E2.
    cbn [snd forallb fst node_contents wf_def_entry]. apply andb_true_iff. split.
    + apply andb_true_iff. split; [exact Hterm|].
      change it1 with (snd (s1, it1)). rewrite <- E1. apply IHb. exact Hit.
    + change rest1 with (snd (s2, rest1)). rewrite <- E2.
      apply IHb0. exact Hrest.
  - (* K's cons: the status is carried the same way *)
    cbn [forallb snd node_contents wf_def_entry] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [Ids.of_task_items].
    destruct (Ids.of_list it st) as [s1 it1] eqn:E1.
    destruct (Ids.of_task_items rest s1) as [s2 rest1] eqn:E2.
    cbn [snd forallb node_contents wf_def_entry]. apply andb_true_iff. split.
    + change it1 with (snd (s1, it1)). rewrite <- E1. apply IHb. exact Hit.
    + change rest1 with (snd (s2, rest1)). rewrite <- E2.
      apply IHb0. exact Hrest.
Qed.

Local Lemma assign_ids_list_wf :
  forall bs st,
    wf_blocks bs = true -> wf_blocks (snd (Ids.of_list bs st)) = true.
Proof.
  induction bs as [|[p a x] rest IH]; intros st H; [reflexivity|].
  rewrite wf_blocks_cons in H. apply andb_true_iff in H as [Hx Hrest].
  cbn [Ids.of_list Ids.of_node].
  destruct (Ids.of_block x p a st) as [st1 n1] eqn:E1.
  destruct (Ids.of_list rest st1) as [st2 rest1] eqn:E2.
  cbn [snd]. rewrite wf_blocks_cons. apply andb_true_iff. split.
  - change n1 with (snd (st1, n1)). rewrite <- E1.
    apply assign_ids_wf. exact Hx.
  - change rest1 with (snd (st2, rest1)). rewrite <- E2.
    apply IH. exact Hrest.
Qed.

(*
Sections
--------
*)

(* The invariant the section stack maintains: every accumulator is
   well-formed, and every entry above the document's has a nonempty one,
   which discharges Section's nonempty obligation on close.  The bottom
   entry may be empty: an empty document is well-formed. *)
Local Fixpoint sect_state_wf (stk : sect_state) : bool :=
  match stk with
  | [] => false                      (* the document entry is never popped *)
  | [(_, _, acc)] => wf_blocks acc
  | (_, _, acc) :: outer => nonempty acc && wf_blocks acc && sect_state_wf outer
  end.

Local Lemma close_ge_wf :
  forall stk lvl pending,
    wf_blocks pending = true ->
    sect_state_wf stk = true ->
    sect_state_wf (close_ge lvl pending stk) = true.
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros lvl pending Hp Hs;
    [discriminate|].
  destruct outer as [|e outer'].
  - cbn in Hs |- *. rewrite wf_blocks_app, Hp, Hs. reflexivity.
  - cbn [sect_state_wf] in Hs.
    apply andb_true_iff in Hs as [Hhd Houter].
    apply andb_true_iff in Hhd as [Hne Hacc].
    cbn [close_ge]. destruct (Nat.leb lvl l).
    + apply IH; [|exact Houter].
      rewrite wf_blocks_cons, section_node_nopos. cbn [node_contents].
      rewrite wf_block_section, wf_blocks_rev, wf_blocks_app, Hp, Hacc.
      cbn [andb]. rewrite andb_true_r.
      (* the closed section is nonempty: its accumulator already was *)
      rewrite nonempty_rev, andb_true_r. apply nonempty_app_r. exact Hne.
    + cbn [sect_state_wf].
      rewrite wf_blocks_app, Hp, Hacc, Houter, andb_true_r.
      cbn [andb]. rewrite andb_true_r.
      destruct pending as [|q pending']; [exact Hne|reflexivity].
Qed.

(* Same shape as close_ge_wf, minus the level test. *)
Local Lemma close_all_wf :
  forall stk pending,
    wf_blocks pending = true ->
    sect_state_wf stk = true ->
    sect_state_wf (close_all pending stk) = true.
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros pending Hp Hs;
    [discriminate|].
  destruct outer as [|e outer'].
  - cbn [close_all sect_state_wf] in Hs |- *.
    rewrite wf_blocks_app, Hp, Hs. reflexivity.
  - cbn [sect_state_wf] in Hs.
    apply andb_true_iff in Hs as [Hhd Houter].
    apply andb_true_iff in Hhd as [Hne Hacc].
    rewrite close_all_cons by discriminate.
    apply IH; [|exact Houter].
    rewrite wf_blocks_cons, section_node_nopos. cbn [node_contents].
    rewrite wf_block_section, wf_blocks_rev, wf_blocks_app, Hp, Hacc.
    cbn [andb]. rewrite andb_true_r.
    rewrite nonempty_rev, andb_true_r. apply nonempty_app_r. exact Hne.
Qed.

Local Lemma sect_push_wf :
  forall stk n,
    wf_block (node_contents n) = true ->
    sect_state_wf stk = true ->
    sect_state_wf (sect_push n stk) = true.
Proof.
  intros [|[[l a] acc] outer] n Hn Hs; [discriminate|].
  cbn [sect_push]. destruct outer as [|e outer'];
    cbn [sect_state_wf] in Hs |- *.
  - rewrite wf_blocks_cons, Hn, Hs. reflexivity.
  - apply andb_true_iff in Hs as [Hhd Houter].
    apply andb_true_iff in Hhd as [_ Hacc].
    rewrite wf_blocks_cons, Hn, Hacc, Houter. reflexivity.
Qed.

(* Stated separately because sect_state_wf's two list patterns make `cbn`
   unfold one step too many: it reduces the recursive call as well, and
   the induction hypothesis then no longer matches. *)
Local Lemma sect_state_wf_cons :
  forall l a acc stk,
    nonempty acc = true -> wf_blocks acc = true -> sect_state_wf stk = true ->
    sect_state_wf ((l, a, acc) :: stk) = true.
Proof.
  intros l a acc [|e outer] Hne Hacc Hstk; [discriminate|].
  change (sect_state_wf ((l, a, acc) :: e :: outer))
    with (nonempty acc && wf_blocks acc && sect_state_wf (e :: outer))%bool.
  rewrite Hne, Hacc, Hstk. reflexivity.
Qed.

Local Lemma sect_step_wf :
  forall stk n,
    wf_block (node_contents n) = true ->
    sect_state_wf stk = true ->
    sect_state_wf (sect_step stk n) = true.
Proof.
  intros stk [p a b] Hn Hs. destruct b; try (apply sect_push_wf; assumption).
  (* A heading opens a section whose accumulator already holds it, so the
     nonempty half of the invariant holds by construction. *)
  cbn [sect_step]. cbn [node_contents] in Hn.
  apply sect_state_wf_cons.
  - reflexivity.
  - unfold wf_blocks. cbn [forallb node_contents node_contents wf_def_entry].
    rewrite andb_true_r. exact Hn.
  - apply close_ge_wf; [reflexivity | exact Hs].
Qed.

Local Lemma sect_bottom_wf :
  forall stk, sect_state_wf stk = true -> wf_blocks (sect_bottom stk) = true.
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros Hs; [discriminate|].
  destruct outer as [|e outer'].
  - cbn [sect_state_wf sect_bottom] in Hs |- *.
    rewrite wf_blocks_rev. exact Hs.
  - cbn [sect_state_wf] in Hs. apply andb_true_iff in Hs as [_ Houter].
    apply IH. exact Houter.
Qed.

(* The fold that drives the stack, carrying the invariant. *)
Local Lemma fold_sect_step_wf :
  forall bs stk,
    wf_blocks bs = true ->
    sect_state_wf stk = true ->
    sect_state_wf (fold_left sect_step bs stk) = true.
Proof.
  induction bs as [|n rest IH]; intros stk H Hstk; [exact Hstk|].
  rewrite wf_blocks_cons in H. apply andb_true_iff in H as [Hn Hrest].
  cbn [fold_left]. apply IH; [exact Hrest|].
  apply sect_step_wf; assumption.
Qed.

Local Lemma sectionize_wf :
  forall bs, wf_blocks bs = true -> wf_blocks (sectionize bs) = true.
Proof.
  intros bs H. unfold sectionize.
  apply sect_bottom_wf, close_all_wf; [reflexivity|].
  apply fold_sect_step_wf; [exact H | reflexivity].
Qed.

Local Definition wf_note_map (m : note_map) : bool :=
  forallb (fun p : string * blocks => wf_blocks (snd p)) m.

Local Lemma wf_note_map_set :
  forall label bs m,
    wf_blocks bs = true -> wf_note_map m = true ->
    wf_note_map (alist_set label bs m) = true.
Proof.
  intros label bs m Hbs. induction m as [|[label' bs'] rest IH]; intros Hm.
  - cbn [alist_set wf_note_map forallb snd node_contents wf_def_entry]. rewrite Hbs. reflexivity.
  - cbn [wf_note_map forallb snd node_contents wf_def_entry] in Hm.
    apply andb_true_iff in Hm as [Hhead Hrest]. cbn [alist_set].
    destruct (String.eqb label label').
    + cbn [wf_note_map forallb snd node_contents wf_def_entry]. rewrite Hbs, Hrest. reflexivity.
    + change (wf_blocks bs' && wf_note_map (alist_set label bs rest) = true)%bool.
      rewrite Hhead, (IH Hrest). reflexivity.
Qed.

(* The pass enters only well-formed bodies, so every body it records is
   well formed. *)
Local Lemma collect_notes_block_wf :
  forall b m,
    wf_block b = true -> wf_note_map m = true ->
    wf_note_map (Notes.of_block b m) = true.
Proof.
  intros b. induction b using block_ind2 with
      (Q := fun bs => forall m,
          wf_blocks bs = true -> wf_note_map m = true ->
          wf_note_map (Notes.of_list bs m) = true)
      (R := fun its => forall m,
          forallb (fun it => wf_blocks (node_contents it)) its = true ->
          wf_note_map m = true ->
          wf_note_map
            (fold_left (fun acc it => Notes.of_list (node_contents it) acc) its m)
          = true)
      (D := fun its => forall m,
          forallb wf_def_entry its = true -> wf_note_map m = true ->
          wf_note_map
            (fold_left
               (fun acc kv =>
                  Notes.of_list (node_contents (snd (node_contents kv))) acc)
               its m)
          = true)
      (K := fun its => forall m,
          forallb (fun ti => wf_blocks (snd (node_contents ti))) its = true ->
          wf_note_map m = true ->
          wf_note_map
            (fold_left (fun acc kv => Notes.of_list (snd (node_contents kv)) acc)
               its m)
          = true);
    intros; try assumption.
  - (* Section *)
    rewrite wf_block_section in H. apply andb_true_iff in H as [_ Hbs].
    cbn [Notes.of_block]. rewrite Notes.inner_go. apply IHb; assumption.
  - (* BlockQuote *)
    rewrite wf_block_quote in H.
    cbn [Notes.of_block]. rewrite Notes.inner_go. apply IHb; assumption.
  - (* Div *)
    rewrite wf_block_div in H.
    cbn [Notes.of_block]. rewrite Notes.inner_go. apply IHb; assumption.
  - (* OrderedList *)
    rewrite wf_block_olist in H. apply andb_true_iff in H as [_ Hits].
    cbn [Notes.of_block]. rewrite Notes.inner_goit. apply IHb; assumption.
  - (* BulletList *)
    rewrite wf_block_bullet in H. apply andb_true_iff in H as [_ Hits].
    cbn [Notes.of_block]. rewrite Notes.inner_goit. apply IHb; assumption.
  - (* TaskList *)
    rewrite wf_block_tasklist in H. apply andb_true_iff in H as [_ Hits].
    cbn [Notes.of_block]. rewrite Notes.inner_got. apply IHb; assumption.
  - (* DefinitionList *)
    rewrite wf_block_deflist in H. apply andb_true_iff in H as [_ Hits].
    cbn [Notes.of_block]. rewrite Notes.inner_god. apply IHb; assumption.
  - (* FootnoteDef: the one arm that writes an entry *)
    rewrite wf_block_footnote in H. apply andb_true_iff in H as [_ Hbs].
    cbn [Notes.of_block]. rewrite Notes.inner_go.
    apply wf_note_map_set; [exact Hbs|apply IHb; assumption].
  - (* Ext_keyed: its one block, through Q at the singleton *)
    rewrite wf_block_keyed in H. apply andb_true_iff in H as [_ Hb].
    destruct b as [p' a' x]. exact (IHb m Hb H0).
  - (* Ext_callout *)
    rewrite wf_block_callout in H. apply andb_true_iff in H as [_ Hbs].
    cbn [Notes.of_block]. rewrite Notes.inner_go. apply IHb; assumption.
  - rewrite wf_blocks_cons in H. apply andb_true_iff in H as [Hb Hrest].
    cbn [Notes.of_list]. apply IHb0; [exact Hrest|apply IHb; assumption].
  - cbn [forallb node_contents] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [fold_left node_contents]. apply IHb0; [exact Hrest|apply IHb; assumption].
  - cbn [forallb] in H. apply andb_true_iff in H as [Hit Hrest].
    apply andb_true_iff in Hit as [_ Hit].
    cbn [fold_left node_contents snd]. apply IHb0; [exact Hrest|apply IHb; assumption].
  - cbn [forallb node_contents snd] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [fold_left node_contents snd]. apply IHb0; [exact Hrest|apply IHb; assumption].
Qed.

Local Lemma collect_notes_list_wf :
  forall bs m,
    wf_blocks bs = true -> wf_note_map m = true ->
    wf_note_map (Notes.of_list bs m) = true.
Proof.
  induction bs as [|[p a b] rest IH]; intros m Hbs Hm; [exact Hm|].
  rewrite wf_blocks_cons in Hbs. apply andb_true_iff in Hbs as [Hb Hrest].
  cbn [Notes.of_list]. apply IH; [exact Hrest|].
  apply collect_notes_block_wf; assumption.
Qed.

(*
The theorem
-----------
*)

(** The whole-document pass cannot turn a well-formed block list into a
    malformed document. *)
Theorem wf_doc_pass :
  forall bs, wf_blocks bs = true -> wf_doc (doc_pass bs) = true.
Proof.
  intros bs H. unfold wf_doc, doc_pass.
  destruct (Ids.of_list bs id_state_init) as [st bs'] eqn:E.
  assert (Hbs' : wf_blocks bs' = true).
  { change bs' with (snd (st, bs')). rewrite <- E.
    apply assign_ids_list_wf. exact H. }
  cbn [doc_blocks doc_footnotes]. apply andb_true_iff. split.
  - apply sectionize_wf. exact Hbs'.
  - exact (collect_notes_list_wf bs' [] Hbs' eq_refl).
Qed.

(** The parser cannot produce a malformed document. *)
Theorem wf_parse_doc : forall s, wf_doc (parse_doc s) = true.
Proof. intros s. apply wf_doc_pass, wf_parse. Qed.

End WithTable.
