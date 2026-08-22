(* ai-disclosure: autonomous *)

(* Well-formedness of the djot AST, as a decidable boolean predicate,
   plus the theorem that the parser only produces well-formed output.

   Two kinds of condition:
   - Structural: no empty containers, no empty containers, no empty lists
     - record what the parser can emit
   - Canonicality: _
*)

From Stdlib Require Import String Ascii List Bool PeanoNat.
From DjotV Require Import Strings Line Ast Attributes Parser Document.
Import ListNotations.

Local Open Scope string_scope.

(* The delimiter table this file is read at.  Implicit, so nothing below
   mentions it: what it buys is that the statements quantify over the
   family rather than over djot's spelling. *)
Section WithTable.
Context {T : dtable}.

(*
Canonicality of inline sequences
================================

Two adjacent attribute-less Str nodes should have been merged into one
(djoths's Inlines Semigroup does this on append). *)

(* `plain_str` (an attribute-less `Str`, the kind that would have been
   merged with a neighbour) and `no_adjacent_str` (no two of them side by
   side) are defined in `Inline.v`: `oresolve` is the identity exactly on
   lists satisfying the second, so the scanner has to name it too. *)

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
  | Superscript ns | Subscript ns | Quoted _ ns =>
      wf_container ns
  | Link ns _ | Image ns _ | Span ns =>
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
Fixpoint wf_block (b : block) : bool :=
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
    fix goi (its : list (list (node block))) : bool :=
      match its with
      | [] => true
      | it :: rest => wf_bs it && goi rest
      end in
  let wf_task_items :=
    fix got (its : list (task_status * list (node block))) : bool :=
      match its with
      | [] => true
      (* No nonemptiness: `- [ ]` alone is a task item with no content,
         which djot.js renders as `<li><input/></li>`.  Same evidence as
         the bullet item's, one construct over. *)
      | (_, it) :: rest => wf_bs it && got rest
      end in
  let wf_def_items :=
    fix god (its : list (inlines * list (node block))) : bool :=
      match its with
      | [] => true
      | (term, it) :: rest => wf_inlines term && wf_bs it && god rest
      end in
  match b with
  | Para ils => nonempty ils && wf_inlines ils
  | Section bs => nonempty bs && wf_bs bs
  (* A block quote may be empty: a bare ">" line is a valid, contentless
     quote (djot.js emits <blockquote></blockquote> for it).  A div may be
     empty for the same reason and on the same evidence — `:::` then
     `:::` renders as `<div>\n</div>` in *both* oracles — so these are the
     two containers without a nonempty obligation. *)
  | BlockQuote bs | Div bs => wf_bs bs
  | Heading level ils => Nat.leb 1 level && wf_inlines ils
  | CodeBlock _ _ => true
  | OrderedList _ _ items => nonempty items && wf_items items
  | BulletList _ items => nonempty items && wf_items items
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
  (* A caption is nonempty when present: `^ ` with nothing after it opens
     a caption with no content, and djot.js renders that as no caption at
     all, so `Some []` would be a second spelling of `None`.  The parser
     owes the collapse. *)
  | Table caption rows =>
      match caption with
      | Some ils => nonempty ils && wf_inlines ils
      | None => true
      end
      && forallb
           (fun row =>
              forallb (fun c => match c with Cell _ _ ils => wf_inlines ils end)
                row)
           rows
  | RawBlock _ _ => true
  end.

Definition wf_blocks (bs : blocks) : bool :=
  forallb (fun n => wf_block (node_contents n)) bs.

Lemma wf_block_footnote :
  forall label bs,
    wf_block (FootnoteDef label bs) = (nonempty_str label && wf_blocks bs)%bool.
Proof.
  intros label bs. cbn [wf_block]. f_equal.
  induction bs as [|[p a b] rest IH]; [reflexivity|].
  cbn [wf_blocks forallb node_contents]. rewrite IH. reflexivity.
Qed.

(* Well-formedness reads payloads, never attributes, so hanging block
   attributes on a node is invisible to it. *)
Lemma wf_blocks_decorate_head :
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

(* Divs share BlockQuote's clause, so they share its lemma's shape. *)
Lemma wf_block_div :
  forall bs, wf_block (Div bs) = wf_blocks bs.
Proof.
  induction bs as [|n bs IH]; [reflexivity|].
  destruct n as [p a x].
  change (wf_block (Div (Node p a x :: bs)))
    with (wf_block x && wf_block (Div bs))%bool.
  rewrite IH. reflexivity.
Qed.

(* A div's node carries a class attribute when it has one; `wf_block`
   reads only the payload, so the wrapper is irrelevant to it. *)
Lemma div_block_wf :
  forall cls bs,
    wf_blocks bs = true -> wf_blocks [div_block cls bs] = true.
Proof.
  intros cls bs H. unfold div_block.
  destruct (String.eqb cls EmptyString);
    rewrite wf_blocks_cons; cbn [node_contents mk];
    rewrite wf_block_div, H; reflexivity.
Qed.

(* wf_block's hand-inlined item-list fixpoint, named for the same reason
   as wf_block_quote. *)
Lemma wf_block_bullet :
  forall sp items,
    wf_block (BulletList sp items)
    = (nonempty items && forallb wf_blocks items)%bool.
Proof.
  intros sp items.
  assert (H : forall its,
             (fix goi (l : list (list (node block))) : bool :=
                match l with
                | [] => true
                | it :: rest => (wf_block (BlockQuote it) && goi rest)%bool
                end) its = forallb wf_blocks its).
  { induction its as [|it rest IH]; [reflexivity|].
    cbn [forallb]. rewrite wf_block_quote, IH. reflexivity. }
  change (wf_block (BulletList sp items))
    with (nonempty items
          && (fix goi (l : list (list (node block))) : bool :=
                match l with
                | [] => true
                | it :: rest => (wf_block (BlockQuote it) && goi rest)%bool
                end) items)%bool.
  rewrite H. reflexivity.
Qed.

(* The ordered flavour asks for exactly the same thing, which is what
   lets `finish_wf` stay one case: `list_block` chooses the wrapper, and
   `wf_block` cannot tell the two apart. *)
Lemma wf_block_olist :
  forall oa sp items,
    wf_block (OrderedList oa sp items)
    = (nonempty items && forallb wf_blocks items)%bool.
Proof.
  intros oa sp items.
  assert (H : forall its,
             (fix goi (l : list (list (node block))) : bool :=
                match l with
                | [] => true
                | it :: rest => (wf_block (BlockQuote it) && goi rest)%bool
                end) its = forallb wf_blocks its).
  { induction its as [|it rest IH]; [reflexivity|].
    cbn [forallb]. rewrite wf_block_quote, IH. reflexivity. }
  change (wf_block (OrderedList oa sp items))
    with (nonempty items
          && (fix goi (l : list (list (node block))) : bool :=
                match l with
                | [] => true
                | it :: rest => (wf_block (BlockQuote it) && goi rest)%bool
                end) items)%bool.
  rewrite H. reflexivity.
Qed.

(* The definition flavour asks *less*: `wf_def_items` has no nonemptiness
   obligation on a term, so an item that was a lone empty paragraph —
   ill-formed as a bullet item — is well-formed once the term is split
   off.  That is why `wf_list_block` below is an implication where the
   other two are equations. *)
Lemma wf_block_deflist :
  forall sp items,
    wf_block (DefinitionList sp items)
    = (nonempty items
       && forallb (fun ti => wf_inlines (fst ti) && wf_blocks (snd ti))
            items)%bool.
Proof.
  intros sp items.
  assert (H : forall its,
             (fix god (l : list (inlines * list (node block))) : bool :=
                match l with
                | [] => true
                | (term, it) :: rest =>
                    (wf_inlines term && wf_block (BlockQuote it) && god rest)%bool
                end) its
             = forallb (fun ti => wf_inlines (fst ti) && wf_blocks (snd ti)) its).
  { induction its as [|[term it] rest IH]; [reflexivity|].
    cbn [forallb fst snd]. rewrite wf_block_quote, IH. reflexivity. }
  change (wf_block (DefinitionList sp items))
    with (nonempty items
          && (fix god (l : list (inlines * list (node block))) : bool :=
                match l with
                | [] => true
                | (term, it) :: rest =>
                    (wf_inlines term && wf_block (BlockQuote it) && god rest)%bool
                end) items)%bool.
  rewrite H. reflexivity.
Qed.

(* Splitting the term off an item keeps it well-formed: the term's
   inlines are the leading paragraph's, which `wf_blocks` already
   checked, and the definition is the rest of a list it checked. *)
Lemma wf_def_split :
  forall bs ils def,
    wf_blocks bs = true ->
    def_split bs = Some (ils, def) ->
    (wf_inlines ils && wf_blocks def)%bool = true.
Proof.
  induction bs as [|[q a x] rest IH]; intros ils def H E; [discriminate|].
  rewrite wf_blocks_cons in H. apply andb_true_iff in H as [Hx Hrest].
  cbn [def_split] in E. destruct x; try discriminate E.
  - injection E as <- <-.
    cbn [node_contents wf_block] in Hx. apply andb_true_iff in Hx as [_ Hi].
    rewrite Hi, Hrest. reflexivity.
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

Lemma wf_def_item :
  forall bs,
    wf_blocks bs = true ->
    (wf_inlines (fst (def_item bs)) && wf_blocks (snd (def_item bs)))%bool
    = true.
Proof.
  intros bs H. destruct (def_split bs) as [[ils def]|] eqn:E.
  - rewrite (def_item_some bs _ E). cbn [fst snd].
    exact (wf_def_split bs ils def H E).
  - rewrite (def_item_none bs E). cbn [fst snd]. rewrite H. reflexivity.
Qed.

Lemma wf_def_items :
  forall its,
    forallb wf_blocks its = true ->
    forallb (fun ti => wf_inlines (fst ti) && wf_blocks (snd ti))
      (def_items its) = true.
Proof.
  unfold def_items. induction its as [|it rest IH]; [reflexivity|].
  cbn [forallb map]. intros H.
  apply andb_true_iff in H as [Hit Hrest].
  rewrite (wf_def_item it Hit), (IH Hrest). reflexivity.
Qed.

Lemma nonempty_def_items :
  forall its, nonempty (def_items its) = nonempty its.
Proof. intros [|it rest]; reflexivity. Qed.

(* An implication, not an equation, for the reason `wf_block_deflist`
   gives.  Its one user needs only this direction. *)
(* As `wf_block_bullet`, for the flavour whose items carry a status. *)
Lemma wf_block_tasklist :
  forall sp items,
    wf_block (TaskList sp items)
    = (nonempty items && forallb (fun ti => wf_blocks (snd ti)) items)%bool.
Proof.
  intros sp items.
  assert (H : forall its,
             (fix got (l : list (task_status * list (node block))) : bool :=
                match l with
                | [] => true
                | (_, it) :: rest => (wf_block (BlockQuote it) && got rest)%bool
                end) its = forallb (fun ti => wf_blocks (snd ti)) its).
  { induction its as [|[st it] rest IH]; [reflexivity|].
    cbn [forallb snd]. rewrite wf_block_quote, IH. reflexivity. }
  change (wf_block (TaskList sp items))
    with (nonempty items
          && (fix got (l : list (task_status * list (node block))) : bool :=
                match l with
                | [] => true
                | (_, it) :: rest => (wf_block (BlockQuote it) && got rest)%bool
                end) items)%bool.
  rewrite H. reflexivity.
Qed.

Lemma nonempty_task_items :
  forall chks its, nonempty (task_items chks its) = nonempty its.
Proof. intros chks [|it rest]; [reflexivity|destruct chks; reflexivity]. Qed.

(* Pairing the statuses onto the items is invisible to `wf_block`. *)
Lemma wf_task_items :
  forall (chks : list task_status) its,
    forallb wf_blocks its = true ->
    forallb (fun ti => wf_blocks (snd ti)) (task_items chks its) = true.
Proof.
  intros chks its. revert chks.
  induction its as [|it rest IH]; intros chks H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hit Hrest].
  destruct chks as [|c cs]; cbn [task_items forallb snd];
    rewrite Hit; apply IH, Hrest.
Qed.

Lemma wf_list_block :
  forall ls last,
    (nonempty (rev (last :: ls_items ls))
     && forallb wf_blocks (rev (last :: ls_items ls)))%bool = true ->
    wf_block (node_contents (list_block ls last)) = true.
Proof.
  intros ls last H. apply andb_true_iff in H as [Hne Hall].
  unfold list_block.
  destruct (ls_styles ls) as [|[[c|c|n d] st] ss].
  - cbn [node_contents mk].
    rewrite wf_block_bullet. apply andb_true_iff. split; assumption.
  - destruct (Ascii.eqb c ":"); cbn [node_contents mk].
    + rewrite wf_block_deflist. apply andb_true_iff. split.
      * rewrite nonempty_def_items. exact Hne.
      * apply wf_def_items, Hall.
    + rewrite wf_block_bullet. apply andb_true_iff. split; assumption.
  - cbn [node_contents mk].
    rewrite wf_block_tasklist. apply andb_true_iff. split.
    + rewrite nonempty_task_items. exact Hne.
    + apply wf_task_items, Hall.
  - cbn [node_contents mk].
    rewrite wf_block_olist. apply andb_true_iff. split; assumption.
Qed.

Lemma nonempty_rev :
  forall (A : Type) (l : list A), nonempty (rev l) = nonempty l.
Proof.
  intros A l. destruct l as [|x l']; [reflexivity|].
  cbn [rev nonempty]. destruct (rev l') as [|y r]; reflexivity.
Qed.

Lemma nonempty_app_r :
  forall (A : Type) (l1 l2 : list A),
    nonempty l2 = true -> nonempty (l1 ++ l2)%list = true.
Proof. intros A [|x l1] l2 H; [exact H|reflexivity]. Qed.

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
The inline scan emits a well-formed sequence
============================================

`no_adjacent_str` recurses from the front while `Inline.iscan` accumulates
at the front of a *reversed* list, so the invariant needs one snoc lemma
and then reads off the four scanner states.

Why it holds: `flush_text` is the only thing that pushes a `Str`, and it
runs exactly on the transition into `IOpen`, whose own next push is a
`Verbatim`.  So a `Str` is never pushed onto a `Str`.  That is what
`iscan_wf`'s `IText` case records, by asserting the head is not a `Str`
whenever text is still being accumulated. *)

Lemma no_adjacent_str_app2 :
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

Lemma no_adjacent_str_app2_l :
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

Lemma no_adjacent_str_app2_pair :
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
Definition plain_item (i : oitem) : bool :=
  match i with OIn n => plain_str n | OMark _ _ => false end.

Fixpoint no_adjacent_item (l : oitems) : bool :=
  match l with
  | i1 :: ((i2 :: _) as rest) =>
      negb (plain_item i1 && plain_item i2) && no_adjacent_item rest
  | _ => true
  end.

Definition oitem_ok (i : oitem) : bool :=
  match i with
  | OIn n => wf_inline (node_contents n)
  | OMark _ src => nonempty_str src
  end.

Definition hd_str (out : oitems) : bool :=
  match out with i :: _ => plain_item i | [] => false end.

(* What a scope carries.  What a *resolved* list carries is `rlist_ok`
   below; `oresolve_ok` is the bridge. *)
Definition ilist_ok (out : oitems) : bool :=
  (forallb oitem_ok out && no_adjacent_item (List.rev out))%bool.

Definition rlist_ok (out : inlines) : bool :=
  (forallb (fun n => wf_inline (node_contents n)) out
   && no_adjacent_str (List.rev out))%bool.

(* `no_adjacent_item` is `no_adjacent_str` over a wider element type, so
   the three list facts it needs are proved again rather than reused. *)
Lemma no_adjacent_item_app2 :
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

Lemma no_adjacent_item_app2_l :
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

Lemma no_adjacent_item_app2_pair :
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

Lemma ilist_ok_push :
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

Every scope's list carries the same invariant as the flat one did, and
the two operations that move inlines between scopes -- closing, which
turns a scope into a node, and abandoning, which splices it into the
level below as text -- are where it has to be re-established.  Abandoning
is the interesting one: it is the only place two `Str` nodes can meet,
which is why `oapp` merges its seam rather than concatenating. *)

Lemma no_adjacent_str_last_subst :
  forall l a b,
    plain_str a = plain_str b ->
    no_adjacent_str (l ++ [a])%list = no_adjacent_str (l ++ [b])%list.
Proof.
  induction l as [|x l IH]; intros a b H; [reflexivity|].
  destruct l as [|y l'].
  - cbn [app no_adjacent_str]. rewrite H. reflexivity.
  - cbn [app no_adjacent_str] in IH |- *. rewrite (IH a b H). reflexivity.
Qed.

Lemma hd_str_is_starts_str : forall l, hd_str l = starts_str l.
Proof. intros [|[[? [|? ?] ?]|? ?] ?]; reflexivity. Qed.

Lemma no_adjacent_item_snoc_ext :
  forall l n m,
    plain_item n = plain_item m ->
    no_adjacent_item (l ++ [n])%list = no_adjacent_item (l ++ [m])%list.
Proof.
  induction l as [|x l IH]; intros n m H; [reflexivity|].
  destruct l as [|y l']; cbn [app no_adjacent_item].
  - rewrite H. reflexivity.
  - f_equal. exact (IH n m H).
Qed.

Lemma no_adjacent_item_last_subst :
  forall l a b,
    plain_item a = plain_item b ->
    no_adjacent_item (l ++ [a])%list = no_adjacent_item (l ++ [b])%list.
Proof. exact no_adjacent_item_snoc_ext. Qed.

(* `no_adjacent_str` reads nothing but `plain_str` of each node, so the
   element at the end may be swapped for any other with the same verdict.
   `oattach_list` is the one writer that replaces a node in place. *)
Lemma no_adjacent_str_snoc_ext :
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
Lemma ilist_ok_reattr :
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

Lemma ilist_ok_osnoc :
  forall n out,
    ilist_ok out = true ->
    oitem_ok n = true ->
    ilist_ok (osnoc n out) = true.
Proof.
  intros n out Ho Hn. destruct (plain_item n) eqn:Hpn.
  - (* n is a plain `Str`: the head of `out` decides whether they merge *)
    destruct n as [[c [|q qs] j]|na ns]; [|discriminate|discriminate].
    destruct j; try discriminate.
    destruct out as [|[[a [|p ps] i]|ma ms] out'];
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
                 (OIn (Node a [] (Str (s0 ++ s)))) (OIn (Node a [] (Str s0))));
        [exact Hadj | reflexivity].
  - (* n is not a plain `Str`: no merge, and nothing to check *)
    replace (osnoc n out) with (n :: out)%list;
      [apply ilist_ok_push;
        [exact Ho | exact Hn | rewrite Hpn; reflexivity]|].
    destruct out as [|[[a [|p ps] i]|ma ms] out']; try reflexivity.
    destruct i; try reflexivity.
    destruct n as [[c [|q qs] j]|na ns]; try reflexivity.
    destruct j; try reflexivity. discriminate.
Qed.

Lemma hd_str_oapp :
  forall cur out, nonempty cur = true -> hd_str (oapp cur out) = hd_str cur.
Proof.
  intros [|n [|m cur']] out H; [discriminate| |rewrite oapp_cons2; reflexivity].
  rewrite oapp_one. destruct out as [|[[a [|p ps] i]|ma ms] out'];
    try (unfold osnoc; destruct n as [[c d j]|na ns]; reflexivity).
  unfold osnoc. destruct i;
    try (destruct n as [[c d j]|na ns]; reflexivity).
  destruct n as [[c [|q qs] j]|na ns]; try reflexivity.
  destruct j; reflexivity.
Qed.

Lemma ilist_ok_oapp :
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

Lemma plain_str_reattr :
  forall p a' v a,
    plain_str (Node p a' v) = false ->
    plain_str (Node p (attr_merge a a') v) = false.
Proof.
  intros p [|kv a'] v a H;
    [|destruct (attr_merge_cons a kv a') as [x [r E]]; rewrite E; reflexivity].
  destruct (attr_merge a []) as [|z r];
    [destruct v; try reflexivity; discriminate H|reflexivity].
Qed.

Lemma istarts_str_cons :
  forall m out, istarts_str (m :: out)%list = plain_str m.
Proof.
  intros [q [|kv b] w] out; [destruct w; reflexivity|reflexivity].
Qed.

Lemma rlist_ok_push :
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

Lemma rlist_ok_tail :
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

Lemma rlist_ok_reattr :
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

Lemma istarts_str_isnoc :
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

Lemma rlist_ok_isnoc :
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
                 (Node a [] (Str (s0 ++ s))) (Node a [] (Str s0)));
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
   Every disposition either leaves the list alone, replaces its head by a
   node with the same payload, or snocs a `Str` that is nonempty by
   construction. *)
Lemma rlist_ok_attach :
  forall a src out,
    rlist_ok out = true -> nonempty_str src = true ->
    rlist_ok (oattach_list a src out) = true.
Proof.
  intros a src out Ho Hsrc. unfold oattach_list.
  destruct out as [|[p a' v] out].
  - apply rlist_ok_isnoc; [exact Ho | exact Hsrc].
  - assert (Hre : plain_str (Node p a' v) = false ->
                  rlist_ok (Node p (attr_merge a a') v :: out) = true).
    { intros Hp. apply rlist_ok_reattr with (n := Node p a' v);
        [exact Ho | reflexivity | apply plain_str_reattr, Hp | exact Hp]. }
    destruct a' as [|kv a'']; destruct v;
      try (apply Hre; reflexivity);
      try (apply rlist_ok_isnoc; [exact Ho | exact Hsrc]).
    (* the one case left: a plain `Str` head, which the spec splits *)
    destruct (last_ws_split s) as [pre w] eqn:Es.
    destruct (nonempty_str w) eqn:Ew; [|exact Ho].
    destruct a as [|ka a2]; [exact Ho|].
    assert (Hrest : rlist_ok out = true) by exact (rlist_ok_tail _ _ Ho).
    apply rlist_ok_isnoc; [|cbn [node_contents]; exact Ew].
    destruct (nonempty_str pre) eqn:Ep; [|exact Hrest].
    apply rlist_ok_isnoc; [exact Hrest|cbn [node_contents]; exact Ep].
Qed.

(* The bridge.  Note what the input invariant does *not* say: it allows
   two plain `Str` items with a spec between them, because that spec may
   vanish -- and when it does, `oresolve_go`'s flag makes the next node
   merge rather than sit adjacent. *)
Lemma oresolve_go_ok :
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
  destruct i as [n|a src].
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

Lemma oresolve_ok :
  forall l, ilist_ok l = true -> rlist_ok (oresolve l) = true.
Proof. intros l H. apply (proj1 (oresolve_go_ok l H)). Qed.

Definition frames_ok (stk : list frame) : bool :=
  forallb (fun f => ilist_ok (fr_out f)) stk.

Definition oscope_ok (o : ostate) : bool :=
  (ilist_ok (os_out o) && frames_ok (os_stk o))%bool.

Definition iscan_wf (st : iscan) : bool :=
  match st with
  | IText _ _ _ o | IEscWs _ _ _ o | IBrace _ _ o | IAttr _ _ _ _ o
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
     text states' head condition and nothing else. *)
  | IBang _ _ o | IAuto _ _ o => (oscope_ok o && negb (hd_str (ocur o)))%bool
  | IClosed kids _ o | ISpan kids _ _ _ o | IReference kids _ _ o
  | IDest kids _ _ _ _ o =>
      (oscope_ok o && wf_inlines kids)%bool
  (* A footnote label carries no children -- it discards what the
     brackets would have held -- and no head condition either, for the
     bracket modes' reason: `bnote_lit` reabsorbs the flushed `Str`
     through `opop_str` before it writes. *)
  | INote _ _ _ o => oscope_ok o
  end.

(* `wf_inline`'s inline-list check, as a global fixpoint with the same
   body: the local one is not nameable, and every container obligation
   below needs to talk about it. *)
Fixpoint wf_ils (ns : list (node inline)) : bool :=
  match ns with
  | [] => true
  | Node _ _ x :: rest => wf_inline x && wf_ils rest
  end.

Lemma wf_ils_forallb :
  forall ns, wf_ils ns = forallb (fun n => wf_inline (node_contents n)) ns.
Proof.
  induction ns as [|[p a x] ns IH]; [reflexivity|].
  cbn [wf_ils forallb node_contents]. rewrite IH. reflexivity.
Qed.

Lemma wf_inline_dnode :
  forall k ns, nonempty ns = true -> rlist_ok (List.rev ns) = true ->
  wf_inline (dnode k ns) = true.
Proof.
  intros k ns Hne Hok. unfold rlist_ok in Hok.
  apply andb_true_iff in Hok as [Hall Hadj].
  rewrite forallb_rev in Hall. rewrite List.rev_involutive in Hadj.
  rewrite <- wf_ils_forallb in Hall.
  destruct k; cbn [dnode];
    match goal with
    | |- wf_inline ?X = true =>
        change (wf_inline X)
          with (nonempty ns && wf_ils ns && no_adjacent_str ns)%bool
    end;
    rewrite Hne, Hall, Hadj; reflexivity.
Qed.

(* The bracket node, both spellings.  A link's or image's text may be
   empty -- `[](u)` is a link -- so there is no nonemptiness conjunct
   here, which is the one way this differs from `wf_inline_dnode`. *)
Lemma wf_inline_bnode :
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

Lemma ocur_emit : forall n o, ocur (oemit n o) = (OIn n :: ocur o)%list.
Proof. intros n [out [|f stk]]; reflexivity. Qed.

Lemma ocur_mark :
  forall a src o, ocur (omark a src o) = (OMark a src :: ocur o)%list.
Proof. intros a src [out [|f stk]]; reflexivity. Qed.

(* A closed backtick run emits a `Verbatim` or a `Math`, and neither is
   a container or a plain `Str` -- which is all the scope invariant asks
   of it. *)
Lemma wf_inline_vnode : forall vk s, wf_inline (vnode vk s) = true.
Proof. intros [|st] s; reflexivity. Qed.

Lemma plain_str_vnode : forall vk s, plain_str (mk (vnode vk s)) = false.
Proof. intros [|st] s; reflexivity. Qed.

Lemma starts_str_vnode :
  forall vk s out, starts_str (OIn (mk (vnode vk s)) :: out) = false.
Proof. intros [|st] s out; reflexivity. Qed.

Lemma oscope_ok_emit :
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
Lemma oscope_ok_mark :
  forall a src o,
    oscope_ok o = true -> nonempty_str src = true ->
    oscope_ok (omark a src o) = true.
Proof.
  intros a src [out [|f stk]] Ho Hs; unfold oscope_ok, omark in *;
    cbn [os_out os_stk frames_ok forallb fr_out fr_kind fr_marked] in *.
  - apply andb_true_iff in Ho as [Ho _]. rewrite andb_true_r.
    apply (ilist_ok_push (OMark a src)); [exact Ho | exact Hs | reflexivity].
  - apply andb_true_iff in Ho as [Hb Hf].
    apply andb_true_iff in Hf as [Hff Hf].
    rewrite Hb, Hf, !andb_true_r.
    apply (ilist_ok_push (OMark a src)); [exact Hff | exact Hs | reflexivity].
Qed.

Lemma oscope_ok_emit_merge :
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

Lemma oscope_ok_emit_all_merge :
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

Lemma oscope_ok_push :
  forall k m o, oscope_ok o = true -> oscope_ok (opush k m o) = true.
Proof.
  intros k m [out stk] H. unfold oscope_ok, opush in *;
    cbn [os_out os_stk frames_ok forallb fr_out] in *.
  change (ilist_ok []) with true. rewrite andb_true_l. exact H.
Qed.

Lemma oscope_ok_bpush :
  forall image o, oscope_ok o = true -> oscope_ok (bpush image o) = true.
Proof.
  intros image [out stk] H. unfold oscope_ok, bpush in *;
    cbn [os_out os_stk frames_ok forallb fr_out] in *.
  change (ilist_ok []) with true. rewrite andb_true_l. exact H.
Qed.

Lemma frames_ok_tail :
  forall f stk, frames_ok (f :: stk) = true -> frames_ok stk = true.
Proof.
  intros f stk H. unfold frames_ok in *. cbn [forallb] in H.
  apply andb_true_iff in H as [_ H]. exact H.
Qed.

Lemma frames_ok_head :
  forall f stk, frames_ok (f :: stk) = true -> ilist_ok (fr_out f) = true.
Proof.
  intros f stk H. unfold frames_ok in *. cbn [forallb] in H.
  apply andb_true_iff in H as [H _]. exact H.
Qed.

(* An abandoned opener decays to a `Str` of its own source text, which is
   nonempty by construction -- a bracket writes its own byte, and a
   delimiter writes its row's token, which an admissible table never
   leaves empty. *)
Lemma fr_src_nonempty : forall f, nonempty_str (fr_src f) = true.
Proof.
  intros [kind marked out]. unfold fr_src; cbn [fr_kind fr_marked].
  destruct kind as [k|image].
  - apply ddecay_str_nonempty.
  - destruct image; reflexivity.
Qed.

Lemma ilist_ok_src : forall f, ilist_ok [OIn (mk (Str (fr_src f)))] = true.
Proof.
  intros f. unfold ilist_ok.
  cbn [forallb oitem_ok node_contents mk List.rev].
  cbn [wf_inline no_adjacent_item]. rewrite (fr_src_nonempty f). reflexivity.
Qed.

Lemma oclose_go_ok :
  forall stk k m pend content rest,
    frames_ok stk = true -> ilist_ok pend = true ->
    oclose_go k m pend stk = Some (content, rest) ->
    (ilist_ok content && frames_ok rest)%bool = true.
Proof.
  induction stk as [|f stk IH]; intros k m pend content rest Hs Hp E;
    [discriminate|].
  cbn [oclose_go] in E.
  destruct (dmatch k m f) eqn:Em.
  { destruct (nonempty (oapp pend (fr_out f))); [|discriminate].
    injection E as <- <-. rewrite (frames_ok_tail f stk Hs), andb_true_r.
    apply ilist_ok_oapp; [exact Hp | exact (frames_ok_head f stk Hs)]. }
  apply (IH k m (oapp (oapp pend (fr_out f)) [OIn (mk (Str (fr_src f)))])
           content rest (frames_ok_tail f stk Hs)); [|exact E].
  apply ilist_ok_oapp;
    [apply ilist_ok_oapp; [exact Hp | exact (frames_ok_head f stk Hs)]
    |apply ilist_ok_src].
Qed.

Lemma oclose_go_nonempty :
  forall stk k m pend content rest,
    oclose_go k m pend stk = Some (content, rest) -> nonempty content = true.
Proof.
  induction stk as [|f stk IH]; intros k m pend content rest E; [discriminate|].
  cbn [oclose_go] in E.
  destruct (dmatch k m f) eqn:Em.
  { destruct (nonempty (oapp pend (fr_out f))) eqn:En; [|discriminate].
    injection E as <- <-. exact En. }
  exact (IH k m (oapp (oapp pend (fr_out f)) [OIn (mk (Str (fr_src f)))])
           content rest E).
Qed.

Lemma oclose_ok :
  forall k m o o',
    oscope_ok o = true -> oclose k m o = Some o' ->
    (oscope_ok o' && negb (starts_str (ocur o')))%bool = true.
Proof.
  intros k m o o' Ho E. unfold oclose in E.
  destruct (oclose_go k m [] (os_stk o)) as [[content rest]|] eqn:Eg;
    [|discriminate].
  injection E as <-.
  apply andb_true_iff in Ho as [Hb Hs].
  pose proof (oclose_go_ok (os_stk o) k m [] content rest Hs eq_refl Eg) as Hcr.
  apply andb_true_iff in Hcr as [Hc Hr].
  assert (Hnode :
    wf_inline (node_contents (mk (dnode k (List.rev (oresolve content)))))
    = true).
  { cbn [node_contents mk]. apply wf_inline_dnode.
    - rewrite nonempty_rev. apply nonempty_oresolve.
      exact (oclose_go_nonempty (os_stk o) k m [] content rest Eg).
    - rewrite List.rev_involutive. exact (oresolve_ok content Hc). }
  rewrite ocur_emit.
  assert (Hplain :
    plain_str (mk (dnode k (List.rev (oresolve content)))) = false)
    by (destruct k; reflexivity).
  assert (Hstart :
    starts_str (OIn (mk (dnode k (List.rev (oresolve content))))
                 :: ocur (OState (os_out o) rest)) = false)
    by (destruct k; reflexivity).
  rewrite Hstart, andb_true_r.
  apply oscope_ok_emit;
    [|exact Hnode | rewrite Hplain; reflexivity].
  unfold oscope_ok; cbn [os_out os_stk]. rewrite Hb, Hr. reflexivity.
Qed.

(*
The transitions preserve it
---------------------------
*)

Lemma iscan_wf_text :
  forall esc txt prev o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (IText esc txt prev o) = true.
Proof.
  intros esc txt prev o Ho Hs. cbn [iscan_wf].
  rewrite Ho, hd_str_is_starts_str, Hs. reflexivity.
Qed.

(* Only the scopes stay well-formed: after a flush the current head *is*
   a `Str`, which is exactly why the head condition is attached to the
   states that still have text pending and not to `IOpen` and `IVerb` --
   a flush happens only on the way into a verbatim, whose own next
   emission is a `Verbatim`. *)
Lemma iscan_wf_flush :
  forall txt o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    oscope_ok (flush_text txt o) = true.
Proof.
  intros txt o Ho Hs. unfold flush_text.
  destruct (nonempty_str txt) eqn:Ht; [|exact Ho].
  apply oscope_ok_emit; [exact Ho | exact Ht | rewrite Hs; apply andb_false_r].
Qed.

(* Closing a bracket is `oclose` without the node: it abandons the
   delimiter scopes above the bracket the same way, and hands back the
   label rather than wrapping it, so the label carries the list
   invariant and the restored state carries the scope one. *)
Lemma bclose_go_ok :
  forall stk pend content image rest,
    frames_ok stk = true -> ilist_ok pend = true ->
    bclose_go pend stk = Some (content, image, rest) ->
    (ilist_ok content && frames_ok rest)%bool = true.
Proof.
  induction stk as [|f stk IH]; intros pend content image rest Hs Hp E;
    [discriminate|].
  cbn [bclose_go] in E. destruct (fr_kind f).
  - apply (IH (oapp (oapp pend (fr_out f)) [OIn (mk (Str (fr_src f)))])
            content image rest (frames_ok_tail f stk Hs)); [|exact E].
    apply ilist_ok_oapp;
      [apply ilist_ok_oapp; [exact Hp | exact (frames_ok_head f stk Hs)]
      |apply ilist_ok_src].
  - injection E as <- <- <-. rewrite (frames_ok_tail f stk Hs), andb_true_r.
    apply ilist_ok_oapp; [exact Hp | exact (frames_ok_head f stk Hs)].
Qed.

Lemma bclose_ok :
  forall o kids image o',
    oscope_ok o = true -> bclose o = Some (kids, image, o') ->
    (oscope_ok o' && wf_inlines kids)%bool = true.
Proof.
  intros o kids image o' Ho E. unfold bclose in E.
  destruct (bclose_go [] (os_stk o)) as [[[content im] rest]|] eqn:Eg;
    [|discriminate].
  injection E as <- <- <-.
  apply andb_true_iff in Ho as [Hb Hs].
  pose proof (bclose_go_ok (os_stk o) [] content im rest Hs eq_refl Eg) as Hcr.
  apply andb_true_iff in Hcr as [Hc Hr].
  pose proof (oresolve_ok content Hc) as Hres.
  unfold rlist_ok in Hres. apply andb_true_iff in Hres as [Hall Hadj].
  apply andb_true_iff. split.
  - unfold oscope_ok; cbn [os_out os_stk]. rewrite Hb, Hr. reflexivity.
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

Lemma ilist_ok_tail :
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

Lemma ilist_ok_head_pop :
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

Lemma opop_str_ok :
  forall o,
    oscope_ok o = true ->
    oscope_ok (snd (opop_str o)) = true
    /\ starts_str (ocur (snd (opop_str o))) = false.
Proof.
  intros [out stk] H. unfold opop_str, ocur; cbn [os_out os_stk].
  destruct stk as [|f fs].
  - destruct out as [|[[a [|p ps] i]|ma ms] rest]; cbn [snd os_out os_stk];
      try (split; [exact H | reflexivity]).
    destruct i; cbn [snd os_out os_stk];
      try (split; [exact H | reflexivity]).
    unfold oscope_ok in H |- *; cbn [os_out os_stk frames_ok] in H |- *.
    rewrite andb_true_r in H |- *.
    split; [exact (ilist_ok_tail _ _ H)|].
    rewrite <- hd_str_is_starts_str.
    exact (ilist_ok_head_pop _ _ H eq_refl).
  - destruct f as [kind marked fout]; cbn [fr_out fr_kind fr_marked].
    destruct fout as [|[[a [|p ps] i]|ma ms] rest];
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

Lemma bflat_ok :
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

Lemma bsplit_nl_ok :
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

Lemma bclosed_lit_ok :
  forall kids image o,
    oscope_ok o = true -> wf_inlines kids = true ->
    oscope_ok (snd (bclosed_lit kids image o)) = true
    /\ starts_str (ocur (snd (bclosed_lit kids image o))) = false.
Proof.
  intros kids image o Ho Hk. unfold bclosed_lit.
  destruct (opop_str_ok o Ho) as [H1 H2].
  destruct (opop_str o) as [pre o1]; cbn [snd] in H1, H2 |- *.
  pose proof (bflat_ok kids (pre ++ bracket_open image)%string o1 H1 H2 Hk)
    as Hb.
  destruct (bflat kids (pre ++ bracket_open image)%string o1) as [txt o2];
    cbn [snd] in Hb |- *. exact Hb.
Qed.

Lemma bdest_lit_ok :
  forall kids image esc dst o,
    oscope_ok o = true -> wf_inlines kids = true ->
    oscope_ok (snd (bdest_lit kids image esc dst o)) = true
    /\ starts_str (ocur (snd (bdest_lit kids image esc dst o))) = false.
Proof.
  intros kids image esc dst o Ho Hk. unfold bdest_lit.
  pose proof (bclosed_lit_ok kids image o Ho Hk) as Hc.
  destruct (bclosed_lit kids image o) as [txt o']; cbn [snd] in Hc |- *.
  destruct Hc as [H1 H2]. apply bsplit_nl_ok; assumption.
Qed.

Lemma bref_lit_ok :
  forall kids image label o,
    oscope_ok o = true -> wf_inlines kids = true ->
    oscope_ok (snd (bref_lit kids image label o)) = true
    /\ starts_str (ocur (snd (bref_lit kids image label o))) = false.
Proof.
  intros kids image label o Ho Hk. unfold bref_lit.
  pose proof (bclosed_lit_ok kids image o Ho Hk) as Hc.
  destruct (bclosed_lit kids image o). exact Hc.
Qed.

Lemma bspan_lit_ok :
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

Lemma battr_lit_ok :
  forall src txt o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    oscope_ok (snd (battr_lit src txt o)) = true
    /\ starts_str (ocur (snd (battr_lit src txt o))) = false.
Proof.
  intros src txt o Ho Hs. unfold battr_lit. apply bsplit_nl_ok; assumption.
Qed.

(* A marked open either waits for the rest of its token, holding the
   state it was in, or pushes -- and a push is exactly what
   `oscope_ok_push` covers. *)
Lemma idelim_marked_wf :
  forall k extra txt o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (idelim_marked k extra txt o) = true.
Proof.
  intros k extra txt o Ho Hs. unfold idelim_marked.
  destruct (Nat.ltb (S extra) (dwidth k));
    [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity|].
  apply iscan_wf_text;
    [apply oscope_ok_push, iscan_wf_flush; assumption | reflexivity].
Qed.

(* The non-breaking space is a node, not text, so the branch that emits
   one restores the head condition rather than owing it; the branch that
   puts the backslash back does not touch the scopes at all. *)
Lemma iescws_resolve_wf :
  forall ws txt prev o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    let '(_, _, o') := iescws_resolve ws txt prev o in
    oscope_ok o' = true /\ starts_str (ocur o') = false.
Proof.
  intros [|c ws] txt prev o Ho Hs; cbn [iescws_resolve]; [split; assumption|].
  destruct (Ascii.eqb c " "%char); [|split; assumption].
  pose proof (iscan_wf_flush txt o Ho Hs) as Hf.
  split; [apply oscope_ok_emit; [exact Hf|reflexivity|apply andb_false_l]|].
  rewrite ocur_emit. reflexivity.
Qed.

(* Popping a frame keeps both halves of the scope invariant: the bottom
   scope is untouched and the rest of the stack was already well-formed. *)
Lemma oscope_ok_bunpush :
  forall o image o',
    oscope_ok o = true -> bunpush o = Some (image, o') -> oscope_ok o' = true.
Proof.
  intros [out [|[[k|im] m [|n l]] stk]] image o' Ho H; try discriminate.
  injection H as _ <-. unfold oscope_ok in *;
    cbn [os_out os_stk frames_ok forallb] in *.
  apply andb_true_iff in Ho as [H1 H2]. apply andb_true_iff in H2 as [_ H3].
  rewrite H1, H3. reflexivity.
Qed.

Lemma ilead_wf :
  forall c txt prev o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (ilead c txt prev o) = true.
Proof.
  intros c txt prev o Ho Hs. unfold ilead.
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
  destruct (Ascii.eqb c lbrack);
    [apply iscan_wf_text;
       [apply oscope_ok_bpush, iscan_wf_flush; assumption | reflexivity]|].
  destruct (Ascii.eqb c rbrack).
  { destruct (bclose (flush_text txt o)) as [[[kids image] o']|] eqn:Eb;
      [|apply iscan_wf_text; assumption].
    cbn [iscan_wf].
    exact (bclose_ok _ _ _ _ (iscan_wf_flush txt o Ho Hs) Eb). }
  destruct (Ascii.eqb c hat && note_pos txt prev)%bool;
    [destruct (bunpush o) as [[image o']|] eqn:Eu;
       [cbn [iscan_wf]; exact (oscope_ok_bunpush o image o' Ho Eu)|]|];
    destruct (dstyle_of c);
    cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity.
Qed.

Lemma idelim_done_wf :
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

Lemma idelim_resolve_wf :
  forall k txt bef marker next o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (idelim_resolve k txt bef marker next o) = true.
Proof.
  intros k txt bef marker next o Ho Hs. unfold idelim_resolve.
  destruct (nonspace_at bef || marker)%bool; [|apply idelim_done_wf; assumption].
  pose proof (iscan_wf_flush txt o Ho Hs) as Hf.
  destruct (oclose k marker (flush_text txt o)) as [o'|] eqn:Ec;
    [|apply idelim_done_wf; assumption].
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
Lemma ospan_bang_ok :
  forall image o,
    oscope_ok o = true -> oscope_ok (ospan_bang image o) = true.
Proof.
  intros image o Ho. unfold ospan_bang. destruct image; [|exact Ho].
  destruct (opop_str_ok o Ho) as [H1 H2].
  destruct (opop_str o) as [pre o1]; cbn [snd] in H1, H2.
  apply iscan_wf_flush; assumption.
Qed.

(* Merging attributes onto a node cannot turn it into a plain `Str`:
   either it already carried some, and `attr_merge_cons` says it still
   does, or it carried none and its payload was not a `Str`. *)

(* Attachment no longer happens here, so nothing has to be said about
   what it does to a scope: `iattr_mark` only pushes an item, and
   `oresolve` settles it once the scope is complete. *)
Lemma iattr_mark_wf :
  forall a src txt o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (iattr_mark a src txt o) = true.
Proof.
  intros a src txt o Ho Hs. unfold iattr_mark.
  apply iscan_wf_text.
  - apply oscope_ok_mark;
      [apply iscan_wf_flush; assumption
      |apply nonempty_str_app_r; reflexivity].
  - rewrite ocur_mark. reflexivity.
Qed.

Lemma iattr_feed_wf :
  forall c p src txt prev o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (iattr_feed c p src txt prev o) = true.
Proof.
  intros c p src txt prev o Ho Hs. unfold iattr_feed.
  destruct (ap_failed (astep p c)).
  { destruct (battr_lit_ok src txt o Ho Hs) as [H1 H2].
    destruct (battr_lit src txt o) as [t o']; cbn [snd] in H1, H2.
    apply ilead_wf; assumption. }
  destruct (ap_done (astep p c));
    [apply iattr_mark_wf; [exact Ho | exact Hs]|].
  cbn [iscan_wf]. rewrite Ho, hd_str_is_starts_str, Hs. reflexivity.
Qed.

Lemma ispan_feed_wf :
  forall c kids image p src o,
    oscope_ok o = true -> wf_inlines kids = true ->
    iscan_wf (ispan_feed c kids image p src o) = true.
Proof.
  intros c kids image p src o Ho Hk. unfold ispan_feed.
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
    cbn [node_contents]. cbn [wf_inline].
    rewrite wf_ils_forallb, Hall, Hadj. reflexivity.
Qed.

Lemma iscan_wf_step :
  forall c st, iscan_wf st = true -> iscan_wf (istep c st) = true.
Proof.
  intros c [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob|rspec rtxt rob] H;
    cbn [istep];
    try (cbn [iscan_wf] in H; apply andb_true_iff in H as [Ho Hs];
         apply negb_true_iff in Hs;
         rewrite hd_str_is_starts_str in Hs).
  - destruct (is_ws c);
      [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity
      |apply (iscan_wf_text false _ prev o Ho Hs)].
  - apply ilead_wf; [exact Ho | exact Hs].
  - destruct (is_ws c);
      [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity|].
    pose proof (iescws_resolve_wf ews etxt eprev eob Ho Hs) as Hr.
    destruct (iescws_resolve ews etxt eprev eob) as [[t p] o'].
    destruct Hr as [Ho' Hs']. apply ilead_wf; assumption.
  - unfold ibrace_step.
    destruct (dstyle_of c);
      [apply idelim_marked_wf; assumption|apply iattr_feed_wf; assumption].
  - destruct (Nat.ltb (S seen) (dwidth k)).
    { destruct (Ascii.eqb c (dchar k));
        [|apply ilead_wf; assumption].
      destruct mrk;
        [apply idelim_marked_wf; assumption
        |cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity]. }
    destruct (Ascii.eqb c rbrace); [apply idelim_resolve_wf; assumption|].
    pose proof (idelim_resolve_wf k txt cc false (Some c) o Ho Hs) as Hr.
    destruct (idelim_resolve k txt cc false (Some c) o)
      as [[] txt' prev' o'|? ? ? ?|? ? ?|? ? ? ? ? ?|? ? ?|? ? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ?|? ? ?|? ? ? ? ?|? ? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ? ? ?|? ? ?|? ? ?]; try exact Hr.
    cbn [iscan_wf] in Hr. apply andb_true_iff in Hr as [Ho' Hs'].
    apply negb_true_iff in Hs'. rewrite hd_str_is_starts_str in Hs'.
    apply ilead_wf; assumption.
  - cbn [iscan_wf] in H |- *. destruct (is_tick c); exact H.
  - cbn [iscan_wf] in H |- *. destruct (is_tick c); [exact H|].
    destruct (Nat.eqb run n); [|exact H].
    destruct (Ascii.eqb c lbrace && vkind_verb vk)%bool;
      [cbn [iscan_wf]; exact H|].
    apply ilead_wf.
    + apply oscope_ok_emit;
        [exact H | apply wf_inline_vnode
        | rewrite plain_str_vnode; apply andb_false_l].
    + rewrite ocur_emit. apply starts_str_vnode.
  - (* the dollars either grow, open a span, or become text *)
    unfold idollar_step. destruct (Ascii.eqb c dollar);
      [destruct dtwo;
         (cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity)|].
    destruct (is_tick c);
      [cbn [iscan_wf]; apply iscan_wf_flush; assumption
      |apply ilead_wf; assumption].
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
  - cbn [iscan_wf] in H. apply andb_true_iff in H as [Ho Hk].
    destruct (Ascii.eqb c lparen);
      [cbn [iscan_wf]; rewrite Ho, Hk; reflexivity|].
    destruct (Ascii.eqb c lbrack);
      [cbn [iscan_wf]; rewrite Ho, Hk; reflexivity|].
    destruct (Ascii.eqb c lbrace);
      [cbn [iscan_wf]; rewrite Ho, Hk; reflexivity|].
    destruct (bclosed_lit_ok kids img ob Ho Hk) as [H1 H2].
    destruct (bclosed_lit kids img ob) as [txt o']; cbn [snd] in H1, H2.
    apply ilead_wf; assumption.
  - cbn [iscan_wf] in H. apply andb_true_iff in H as [Ho Hk].
    apply ispan_feed_wf; assumption.
  - apply iattr_feed_wf; assumption.
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
  - cbn [iscan_wf] in H. apply andb_true_iff in H as [Ho Hk].
    assert (Hd : forall e d t, iscan_wf (IDest kids img e d t ob) = true)
      by (intros; cbn [iscan_wf]; rewrite Ho, Hk; reflexivity).
    destruct esc; [apply Hd|].
    destruct (is_bslash c); [apply Hd|].
    destruct (Ascii.eqb c lparen); [apply Hd|].
    destruct (Ascii.eqb c rparen); [|apply Hd].
    destruct depth as [|d]; [|apply Hd].
    (* the link or image node is the one thing the bracket modes build *)
    apply iscan_wf_text; [|rewrite ocur_emit; destruct img; reflexivity].
    apply oscope_ok_emit; [exact Ho| |destruct img; reflexivity].
    unfold wf_inlines in Hk. apply andb_true_iff in Hk as [Hall Hadj].
    cbn [node_contents mk]. apply wf_inline_bnode;
      [rewrite wf_ils_forallb; exact Hall | exact Hadj].
  (* a candidate either emits its link node over the flushed text, or
     hands the text back to `ilead` with the `<` on the end *)
  - unfold iauto_step.
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
  (* the node the spec decides is not a `Str` either way, so the scope it
     lands in carries the head condition its own emission establishes *)
  - cbn [iscan_wf] in H. unfold iraw_step.
    assert (Hv : oscope_ok (oemit (mk (Verbatim rtxt)) rob) = true /\
                 starts_str (ocur (oemit (mk (Verbatim rtxt)) rob)) = false).
    { split;
        [apply oscope_ok_emit; [exact H | reflexivity | apply andb_false_l]
        |rewrite ocur_emit; reflexivity]. }
    destruct Hv as [Hvo Hvs].
    destruct (Ascii.eqb c rbrace && raw_spec_ok rspec)%bool.
    { apply iscan_wf_text;
        [apply oscope_ok_emit; [exact H | reflexivity | apply andb_false_l]
        |rewrite ocur_emit; reflexivity]. }
    destruct rspec as [|x rspec'].
    + destruct (negb (Ascii.eqb c eqchar)); [|cbn [iscan_wf]; exact H].
      unfold ibrace_step. destruct (dstyle_of c);
        [apply idelim_marked_wf; assumption | apply iattr_feed_wf; assumption].
    + destruct (Ascii.eqb c rbrace || raw_stop c)%bool;
        [apply ilead_wf; assumption | cbn [iscan_wf]; exact H].
Qed.

Lemma iscan_wf_str :
  forall s st, iscan_wf st = true -> iscan_wf (iscan_str s st) = true.
Proof.
  induction s as [|c rest IH]; intros st H; [exact H|].
  cbn [iscan_str]. apply IH, iscan_wf_step, H.
Qed.

Lemma wf_inlines_of_rlist :
  forall out, rlist_ok out = true -> wf_inlines (List.rev out) = true.
Proof.
  intros out H. unfold rlist_ok in H. unfold wf_inlines.
  apply andb_true_iff in H as [Hall Hadj].
  rewrite forallb_rev, Hall, Hadj. reflexivity.
Qed.

(* Flattening abandons every open scope, splicing each into the level
   below with its opener as text -- the same `oapp` merge as closing,
   repeated to the bottom. *)
Lemma ilist_ok_oflatten :
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

Lemma ilist_ok_oitems_of :
  forall o, oscope_ok o = true -> ilist_ok (oitems_of o) = true.
Proof.
  intros o H. apply andb_true_iff in H as [Hb Hs].
  unfold oitems_of.
  apply ilist_ok_oflatten; [exact Hs | reflexivity | exact Hb].
Qed.

Lemma rlist_ok_ofinish :
  forall o, oscope_ok o = true -> rlist_ok (ofinish o) = true.
Proof.
  intros o H. unfold ofinish. apply oresolve_ok, ilist_ok_oitems_of, H.
Qed.

Lemma iscan_wf_resolve :
  forall st, iscan_wf st = true -> iscan_wf (iresolve st) = true.
Proof.
  intros [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob|rspec rtxt rob] H;
    cbn [iresolve]; try exact H;
    cbn [iscan_wf] in H; apply andb_true_iff in H as [Ho Hs].
  (* `IBrace` is closed by `exact H` above: the invariant does not look
     at the text buffer, and resolving a brace only moves a byte into
     it.  `IDelim` is the one that can close a scope, and `IClosed` the
     one that puts a bracket back as text. *)
  - apply negb_true_iff in Hs; rewrite hd_str_is_starts_str in Hs.
    destruct (Nat.ltb (S seen) (dwidth k));
      [apply iscan_wf_text; assumption|apply idelim_resolve_wf; assumption].
  - destruct (bclosed_lit_ok kids img ob Ho Hs) as [H1 H2].
    destruct (bclosed_lit kids img ob) as [txt o']; cbn [snd] in H1, H2.
    apply iscan_wf_text; assumption.
Qed.

Lemma iscan_wf_ostate :
  forall st, iscan_wf st = true -> oscope_ok (ifinish_ostate st) = true.
Proof.
  intros st H. pose proof (iscan_wf_resolve st H) as Hr.
  pose proof (iresolve_resolved st) as Hno.
  unfold ifinish_ostate.
  destruct (iresolve st) as
    [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob|rspec rtxt rob];
    try contradiction;
    try (cbn [iscan_wf] in Hr; apply andb_true_iff in Hr as [Ho Hs];
         apply negb_true_iff in Hs; rewrite hd_str_is_starts_str in Hs).
  1,3: unfold iesc_hard; apply oscope_ok_emit;
       [apply iscan_wf_flush; assumption | reflexivity | apply andb_false_l].
  - apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr.
    apply oscope_ok_emit;
      [exact Hr | apply wf_inline_vnode
      | rewrite plain_str_vnode; apply andb_false_l].
  - cbn [iscan_wf] in Hr.
    apply oscope_ok_emit;
      [exact Hr | apply wf_inline_vnode
      | rewrite plain_str_vnode; apply andb_false_l].
  - cbn [iscan_wf] in Hr. apply andb_true_iff in Hr as [Ho Hk].
    destruct (bspan_lit_ok kids img ssrc sob Ho Hk) as [H1 H2].
    destruct (bspan_lit kids img ssrc sob) as [txt o']; cbn [snd] in H1, H2.
    apply iscan_wf_flush; assumption.
  - destruct (battr_lit_ok asrc atxt aob Ho Hs) as [H1 H2].
    destruct (battr_lit asrc atxt aob) as [t o']; cbn [snd] in H1, H2.
    apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr. apply andb_true_iff in Hr as [Ho Hk].
    destruct (bref_lit_ok kids img label ob Ho Hk) as [H1 H2].
    destruct (bref_lit kids img label ob) as [txt o']; cbn [snd] in H1, H2.
    apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr.
    destruct (opop_str_ok nob Hr) as [H1 H2].
    unfold bnote_lit. destruct (opop_str nob) as [pre o1]; cbn [snd] in H1, H2.
    apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr. apply andb_true_iff in Hr as [Ho Hk].
    destruct (bdest_lit_ok kids img esc dst ob Ho Hk) as [H1 H2].
    destruct (bdest_lit kids img esc dst ob) as [txt o']; cbn [snd] in H1, H2.
    apply iscan_wf_flush; assumption.
  - apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr. apply iscan_wf_flush;
      [apply oscope_ok_emit; [exact Hr | reflexivity | apply andb_false_l]
      |rewrite ocur_emit; reflexivity].
Qed.

Lemma iscan_wf_finish_rev :
  forall st, iscan_wf st = true -> rlist_ok (ifinish_rev st) = true.
Proof.
  intros st H. unfold ifinish_rev.
  apply rlist_ok_ofinish, iscan_wf_ostate, H.
Qed.

Lemma iscan_wf_finish :
  forall st, iscan_wf st = true -> wf_inlines (ifinish st) = true.
Proof.
  intros st H. unfold ifinish.
  apply wf_inlines_of_rlist, iscan_wf_finish_rev, H.
Qed.

(* A line boundary pushes a `SoftBreak` into the innermost open scope,
   which leaves a head that is not a `Str` -- what the next line's text
   accumulation needs.  Open scopes survive the break: a span may cross
   it. *)
Lemma iscan_wf_break :
  forall st, iscan_wf st = true -> iscan_wf (ibreak st) = true.
Proof.
  intros st H. pose proof (iscan_wf_resolve st H) as Hr.
  pose proof (iresolve_resolved st) as Hno.
  unfold ibreak.
  destruct (iresolve st) as
    [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob|rspec rtxt rob];
    try contradiction;
    try (cbn [iscan_wf] in Hr; apply andb_true_iff in Hr as [Ho Hs];
         apply negb_true_iff in Hs; rewrite hd_str_is_starts_str in Hs).
  1,2,3: try unfold iesc_hard;
         apply (iscan_wf_text false EmptyString None);
         [ apply oscope_ok_emit;
           [ apply iscan_wf_flush; assumption
           | reflexivity | apply andb_false_l ]
         | rewrite ocur_emit; reflexivity ].
  - cbn [iscan_wf] in Hr |- *. exact Hr.
  - cbn [iscan_wf] in Hr. destruct (Nat.eqb run n); [|exact Hr].
    apply (iscan_wf_text false EmptyString None).
    + apply oscope_ok_emit;
        [apply oscope_ok_emit;
           [exact Hr | apply wf_inline_vnode
           | rewrite plain_str_vnode; apply andb_false_l]
        |reflexivity | apply andb_false_l].
    + rewrite ocur_emit. reflexivity.
  - apply andb_true_iff in Hr as [Ho Hk]. apply ispan_feed_wf; assumption.
  - apply iattr_feed_wf; assumption.
  - cbn [iscan_wf] in Hr |- *. exact Hr.
  (* a label and a destination both carry the break as a character, so
     nothing is emitted and the invariant is the one they arrived with *)
  - cbn [iscan_wf] in Hr |- *. exact Hr.
  - cbn [iscan_wf] in Hr |- *. exact Hr.
  (* a candidate does not: the region may not hold a break, so it decays
     to text and the break is the soft one after it *)
  - apply (iscan_wf_text false EmptyString None);
      [apply oscope_ok_emit;
         [apply iscan_wf_flush; assumption | reflexivity | apply andb_false_l]
      |rewrite ocur_emit; reflexivity].
  - cbn [iscan_wf] in Hr.
    assert (Hvo : oscope_ok (oemit (mk (Verbatim rtxt)) rob) = true)
      by (apply oscope_ok_emit;
            [exact Hr | reflexivity | apply andb_false_l]).
    apply (iscan_wf_text false EmptyString None);
      [apply oscope_ok_emit;
         [apply iscan_wf_flush;
            [exact Hvo | rewrite ocur_emit; reflexivity]
         |reflexivity | apply andb_false_l]
      |rewrite ocur_emit; reflexivity].
Qed.

Lemma iscan_wf_lines :
  forall l st, iscan_wf st = true -> iscan_wf (iscan_lines l st) = true.
Proof.
  induction l as [|x [|y rest] IH]; intros st H; cbn [iscan_lines].
  - exact H.
  - apply iscan_wf_str, H.
  - apply IH, iscan_wf_break, iscan_wf_str, H.
Qed.

(** The parser's inline pass only ever emits a well-formed sequence. *)
Lemma parse_inline_line_wf :
  forall s, wf_inlines (parse_inline_line s) = true.
Proof.
  intros s. unfold parse_inline_line.
  apply iscan_wf_finish, iscan_wf_str. reflexivity.
Qed.

(*
Paragraph assembly is well-formed
=================================
*)

Lemma para_inlines_nonempty :
  forall ls, forallb nonblank ls = true -> ls <> [] ->
  nonempty (para_inlines ls) = true.
Proof.
  intros [|x [|y r]] Hnb H; [congruence| |].
  - cbn [forallb] in Hnb. apply andb_true_iff in Hnb as [Hx _].
    rewrite para_inlines_one. apply parse_inline_line_nonempty.
    apply strip_trailing_ws_nonempty.
    unfold nonblank in Hx. apply negb_true_iff in Hx. exact Hx.
  - unfold para_inlines. rewrite iscan_lines_cons2.
    apply iscan_productive_finish, iscan_productive_lines,
          iscan_productive_break.
Qed.

(* No hypothesis: the scan's invariant does not care what the lines look
   like, and the blankness the callers carry was only ever needed for
   nonemptiness. *)
Lemma para_inlines_wf :
  forall ls, wf_inlines (para_inlines ls) = true.
Proof.
  intros ls. unfold para_inlines.
  apply iscan_wf_finish, iscan_wf_lines. reflexivity.
Qed.

Lemma flush_para_wf :
  forall c cur' k,
    forallb nonblank (c :: cur') = true ->
    wf_blocks k = true ->
    wf_blocks (mk (Para (para_inlines (rev (c :: cur')))) :: k) = true.
Proof.
  intros c cur' k Hcur Hk.
  rewrite wf_blocks_cons. cbn [node_contents mk wf_block].
  rewrite para_inlines_wf.
  rewrite Hk.
  rewrite para_inlines_nonempty;
    [reflexivity | rewrite forallb_rev; exact Hcur |].
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
  (* A heading additionally carries its level, which `Heading` requires
     to be at least 1. *)
  | PHeading lvl cur => Nat.leb 1 lvl && forallb nonblank cur
  | PFence _ _ _ => true
  | PQuote done inner => wf_blocks done && state_wf inner
  (* A div carries no invariant its fence length or class could break:
     `Div` is well-formed for any block sequence, exactly as
     `BlockQuote` is. *)
  | PDiv _ _ done inner => wf_blocks done && state_wf inner
  (* The finished items, the current item's finished blocks, and its
     open state. *)
  | PList ls done inner =>
      forallb wf_blocks (ls_items ls) && wf_blocks done && state_wf inner
  (* The slices are the paragraph a failed spec becomes, so they carry
     the paragraph accumulator's invariant.  `push_text` is what keeps
     it: a blank continuation line is fed to the machine but not
     recorded. *)
  | PAttr _ _ _ slices => forallb nonblank slices
  (* A definition's label and destination carry `wf_block (RefDef _ _)`
     itself: they are fixed when the state opens, and a continuation line
     only appends another whitespace-free run to the destination. *)
  | PRef _ lbl val =>
      no_char "]"%char lbl && negb (is_footnote_label lbl) && no_ws val
  | PFoot _ lbl done inner =>
      nonempty_str lbl && wf_blocks done && state_wf inner
  (* A table's rows carry no invariant: a cell's inlines come from
     `parse_inline_line`, which is well-formed for any string.  Its
     caption is a paragraph accumulator, and carries the same condition
     one does -- which is what makes the caption `wf_block` asks for
     nonempty. *)
  | PTable _ cap => forallb nonblank (cap_lines cap)
  (* Pending attributes add nothing of their own. *)
  | PPend _ inner => state_wf inner
  end.

(* Every cell a table is built from is well-formed, whichever of the two
   builders made it: `cells_of` calls `parse_inline_line`, and `head_of`
   only re-labels cells that already exist. *)
Lemma cells_of_wf :
  forall ct aligns cs,
    forallb (fun c => match c with Cell _ _ ils => wf_inlines ils end)
      (cells_of ct aligns cs) = true.
Proof.
  intros ct aligns cs. revert aligns.
  induction cs as [|c cs IH]; intros aligns; [reflexivity|].
  destruct aligns as [|a als]; cbn [cells_of forallb];
    rewrite parse_inline_line_wf; apply IH.
Qed.

Lemma head_of_wf :
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

Lemma table_fold_wf :
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

(* A caption is well-formed when it is present at all: `caption_of`
   answers `None` for an empty accumulator, so the `nonempty` half of
   `wf_block`'s clause is exactly `para_inlines_nonempty` on a list of
   lines the state only ever pushes nonblank. *)
Lemma caption_of_wf :
  forall c,
    forallb nonblank (cap_lines c) = true ->
    match caption_of c with
    | Some ils => (nonempty ils && wf_inlines ils)%bool
    | None => true
    end = true.
Proof.
  intros [| |ls] H; try reflexivity.
  destruct ls as [|x ls']; [reflexivity|].
  cbn [caption_of]. rewrite para_inlines_wf, andb_true_r.
  apply para_inlines_nonempty.
  - rewrite forallb_rev. exact H.
  - intros Hcontra. apply (f_equal (@List.length string)) in Hcontra.
    rewrite List.length_rev in Hcontra. discriminate.
Qed.

Lemma table_block_wf :
  forall rows c,
    forallb nonblank (cap_lines c) = true ->
    wf_blocks [table_block rows c] = true.
Proof.
  intros rows c H. unfold table_block.
  rewrite wf_blocks_cons. cbn [node_contents mk wf_block].
  rewrite table_fold_wf by reflexivity.
  rewrite andb_true_r, andb_true_r.
  pose proof (caption_of_wf c H) as Hc.
  destruct (caption_of c); [exact Hc | reflexivity].
Qed.

(* Closing the stack at end of input preserves the invariant. *)
(* A heading block is well-formed as soon as its level is and its lines
   are nonblank; unlike a paragraph it may be empty. *)
Lemma heading_block_wf :
  forall lvl cur,
    Nat.leb 1 lvl = true -> forallb nonblank cur = true ->
    wf_blocks [heading_block lvl cur] = true.
Proof.
  intros lvl cur Hl Hc. unfold heading_block.
  rewrite wf_blocks_cons. cbn [node_contents mk wf_block].
  rewrite Hl, para_inlines_wf.
  reflexivity.
Qed.

Lemma finish_wf :
  forall st, state_wf st = true -> wf_blocks (finish st) = true.
Proof.
  induction st as [cur|lvl hcur|f fnd acc|done inner IH|dlen dcls ddone dinner IH
    |ls done inner IH|apend aind aap aslices|rind rlbl rval
    |find flbl fdone finner IH|trows tcap|ppend pinner IH];
    intros H.
  - destruct cur as [|c cur']; [reflexivity|].
    cbn [finish]. apply flush_para_wf; [exact H | reflexivity].
  - cbn [state_wf] in H. apply andb_true_iff in H as [Hl Hc].
    cbn [finish]. apply heading_block_wf; assumption.
  - cbn [finish]. rewrite wf_blocks_cons, fence_block_wf. reflexivity.
  - cbn [state_wf] in H. apply andb_true_iff in H as [Hd Hi].
    cbn [finish]. rewrite wf_blocks_cons. cbn [node_contents mk].
    rewrite wf_block_quote, wf_blocks_app, wf_blocks_rev, Hd, (IH Hi).
    reflexivity.
  - (* a div: as a quote, but through div_block's attribute wrapper *)
    cbn [state_wf] in H. apply andb_true_iff in H as [Hd Hi].
    cbn [finish]. apply div_block_wf.
    rewrite wf_blocks_app, wf_blocks_rev, Hd, (IH Hi). reflexivity.
  - (* a list: the item still open, plus the ones already closed *)
    cbn [state_wf] in H. apply andb_true_iff in H as [H1 Hi].
    apply andb_true_iff in H1 as [Hitems Hd].
    cbn [finish]. rewrite wf_blocks_cons, andb_true_r.
    apply wf_list_block.
    rewrite nonempty_rev, forallb_rev. cbn [nonempty forallb].
    rewrite wf_blocks_app, wf_blocks_rev, Hd, (IH Hi), Hitems.
    reflexivity.
  - (* an attribute spec: a finished one contributes nothing, an
       unfinished one the paragraph of the lines it ate *)
    cbn [state_wf] in H. cbn [finish].
    destruct (ap_done aap); [reflexivity|].
    destruct aslices as [|c cur']; [reflexivity|].
    apply (flush_para_wf c cur' [] H eq_refl).
  - (* a reference definition: the state's invariant is the block's *)
    cbn [state_wf] in H. cbn [finish].
    rewrite wf_blocks_cons. cbn [ref_block node_contents mk wf_block].
    rewrite H. reflexivity.
  - cbn [state_wf] in H. apply andb_true_iff in H as [Hboth Hinner].
    apply andb_true_iff in Hboth as [Hlbl Hdone].
    cbn [finish]. rewrite wf_blocks_cons.
    cbn [foot_block node_contents mk]. rewrite wf_block_footnote.
    rewrite Hlbl, wf_blocks_app, wf_blocks_rev, Hdone, (IH Hinner).
    reflexivity.
  - (* a table: its rows are well-formed by construction, and its
       caption by the state's invariant *)
    cbn [finish]. apply table_block_wf. exact H.
  - cbn [state_wf] in H. cbn [finish].
    rewrite wf_blocks_decorate_head. exact (IH H).
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

(* An attribute spec's opening line is nonblank -- it has a brace on it.
   `open_attr` records that line, so this is what keeps the slices'
   invariant true from the start. *)
Lemma classify_kattr_nonblank :
  forall l p, classify l = KAttr p -> is_blank l = false.
Proof.
  intros l p H. apply classify_not_kblank_nonblank. rewrite H. discriminate.
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
  induction st as [cur|lvl hcur|f fnd acc|done inner IH|dlen dcls ddone dinner IH
    |ls done inner IH|apend aind aap aslices|rind rlbl rval
    |find flbl fdone finner IH|trows tcap|ppend pinner IH];
    intros Hl H;
    (* feed_lazy strips the line's leading whitespace, which cannot turn a
       nonblank line blank *)
    assert (Hnb : is_blank (drop_leading_ws l) = false)
      by (rewrite is_blank_drop_leading_ws; exact Hl).
  - cbn [feed_lazy state_wf] in *. rewrite forallb_nonblank_cons by exact Hnb.
    exact H.
  - cbn [feed_lazy state_wf] in *. apply andb_true_iff in H as [Hlv Hc].
    apply andb_true_iff. split; [exact Hlv|].
    rewrite forallb_nonblank_cons by exact Hnb. exact Hc.
  - reflexivity.
  - cbn [feed_lazy state_wf] in *. apply andb_true_iff in H as [Hd Hi].
    rewrite Hd, (IH Hl Hi). reflexivity.
  - cbn [feed_lazy state_wf] in *. apply andb_true_iff in H as [Hd Hi].
    rewrite Hd, (IH Hl Hi). reflexivity.
  - cbn [feed_lazy state_wf] in *. apply andb_true_iff in H as [H1 Hi].
    apply andb_true_iff in H1 as [Hitems Hd].
    rewrite Hitems, Hd, (IH Hl Hi). reflexivity.
  - exact H.                            (* excluded by lazy_ok *)
  - exact H.                            (* excluded by lazy_ok *)
  - cbn [feed_lazy state_wf] in *. apply andb_true_iff in H as [Hfixed Hi].
    rewrite Hfixed, (IH Hl Hi). reflexivity.
  - exact H.                            (* excluded by lazy_ok *)
  - cbn [feed_lazy state_wf] in *. exact (IH Hl H).
Qed.

(* push_text only ever adds a nonblank line, by construction. *)
Lemma forallb_nonblank_push_text :
  forall txt cur,
    forallb nonblank cur = true ->
    forallb nonblank (push_text txt cur) = true.
Proof.
  intros txt cur H. unfold push_text.
  destruct (is_blank txt) eqn:E; [exact H|].
  rewrite forallb_nonblank_cons
    by (rewrite is_blank_drop_leading_ws; exact E).
  exact H.
Qed.

(* Opening a block from an idle state. *)
Lemma open_kind_wf :
  forall l k,
    classify l = k ->
    wf_blocks (fst (open_kind l k)) = true
    /\ state_wf (snd (open_kind l k)) = true.
Proof.
  intros l k H. destruct k; cbn [close_reopen open_quote finish app open_kind open_fence open_attr open_ref fst snd]; try (split; reflexivity).
  - (* KHeading: the level comes from the classifier *)
    split; [reflexivity|].
    cbn [state_wf]. rewrite (classify_heading_level _ _ _ H). cbn [andb].
    apply forallb_nonblank_push_text. reflexivity.
  - (* KText: the accumulator gains one line, which must be nonblank *)
    split; [reflexivity|].
    cbn [state_wf].
    rewrite forallb_nonblank_cons
      by (rewrite is_blank_drop_leading_ws; apply classify_ktext_nonblank; exact H).
    reflexivity.
Qed.

(* One transition preserves the invariant and emits only well-formed
   blocks.  Proved on fuel, since that is what `step` recurses on. *)
(* Opening a list: a fresh list has no closed items yet, so all the
   invariant needs is what the descent already gives. *)
Lemma open_list_wf :
  forall ind m chk bs inner,
    wf_blocks bs = true -> state_wf inner = true ->
    wf_blocks (fst (open_list ind m chk (bs, inner))) = true
    /\ state_wf (snd (open_list ind m chk (bs, inner))) = true.
Proof.
  intros ind m chk bs inner Hb Hi.
  cbn [open_list fst snd state_wf ls_items forallb].
  split; [reflexivity|]. rewrite wf_blocks_rev, Hb, Hi. reflexivity.
Qed.

(* Opening an attribute spec: one recorded line, and it is nonblank. *)
Lemma open_attr_wf :
  forall pend ind ap l,
    is_blank l = false ->
    wf_blocks (fst (open_attr pend ind ap l)) = true
    /\ state_wf (snd (open_attr pend ind ap l)) = true.
Proof.
  intros pend ind ap l Hl. cbn [open_attr fst snd state_wf].
  split; [reflexivity|].
  rewrite forallb_nonblank_cons
    by (rewrite is_blank_drop_leading_ws; exact Hl).
  reflexivity.
Qed.

(* Opening a code fence: it carries no invariant at all, its column
   least of all. *)
Lemma open_fence_wf :
  forall ind f,
    wf_blocks (fst (open_fence ind f)) = true
    /\ state_wf (snd (open_fence ind f)) = true.
Proof. intros ind f. split; reflexivity. Qed.

(* Opening a reference definition: the classifier's guarantees about the
   label and the destination are exactly the block's. *)
Lemma open_ref_wf :
  forall ind l lbl v,
    classify l = KRef lbl v ->
    wf_blocks (fst (open_ref ind lbl v)) = true
    /\ state_wf (snd (open_ref ind lbl v)) = true.
Proof.
  intros ind l lbl v H. apply classify_kref in H.
  cbn [open_ref fst snd state_wf]. split; [reflexivity|].
  rewrite (ref_open_label_ok l lbl v H), (ref_open_value_no_ws l lbl v H).
  reflexivity.
Qed.

Lemma open_foot_wf :
  forall ind l lbl rest bs inner,
    classify l = KFoot lbl rest ->
    wf_blocks bs = true -> state_wf inner = true ->
    wf_blocks (fst (open_foot ind lbl (bs, inner))) = true /\
    state_wf (snd (open_foot ind lbl (bs, inner))) = true.
Proof.
  intros ind l lbl rest bs inner Hclass Hbs Hinner.
  pose proof (foot_open_label_ok _ _ _ (classify_kfoot _ _ _ Hclass)) as Hlbl.
  apply andb_true_iff in Hlbl as [Hnonempty _].
  cbn [open_foot fst snd state_wf]. split; [reflexivity|].
  rewrite Hnonempty, wf_blocks_rev, Hbs, Hinner. reflexivity.
Qed.

Lemma step_fuel_wf :
  forall n off l st,
    state_wf st = true ->
    wf_blocks (fst (step_fuel n off l st)) = true
    /\ state_wf (snd (step_fuel n off l st)) = true.
Proof.
  induction n as [|n IH]; intros off l st H; [split; [reflexivity | exact H]|].
  cbn [step_fuel].
  destruct st as [cur|hlvl hcur|f fnd acc|done inner|dlen dcls ddone dinner|ls done inner|apend aind aap aslices|rind rlbl rval|find flbl fdone finner|trows tcap|ppend pinner].
  - (* idle, or an open paragraph *)
    destruct cur as [|c cur'].
    + destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E;
        try (apply open_kind_wf; exact E).
      * (* KFence: opens its own state, recording its column *)
        apply open_fence_wf.
      * (* KQuote: descend into the enclosed line *)
        destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner].
        cbn [open_quote fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        cbn [state_wf]. rewrite wf_blocks_rev, Hb. exact Hs.
      * (* KList: descend into the rest of the line *)
        destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner].
        apply open_list_wf; assumption.
      * (* KAttr: opens its own state, not through open_kind *)
        apply open_attr_wf, (classify_kattr_nonblank l kap E).
      * (* KFoot: descend into the first body line *)
        destruct (IH (off + consumed l frest) frest (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l frest) frest (PPara [])) as [bs inner].
        apply (open_foot_wf (off + indent_of l) l flbl frest); assumption.
      * (* KRef: opens its own state too *)
        apply (open_ref_wf _ l _ _ E).
    + destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [fst snd].
      1: (split; [| reflexivity];
          apply flush_para_wf; [exact H | reflexivity]).
      all: split; [reflexivity|];
           cbn [state_wf];
           rewrite forallb_nonblank_cons
             by (rewrite is_blank_drop_leading_ws;
                 apply classify_not_kblank_nonblank; rewrite E; discriminate);
           exact H.
  - (* an open heading *)
    cbn [state_wf] in H. apply andb_true_iff in H as [Hlv Hc].
    assert (Hhb : wf_blocks [heading_block hlvl hcur] = true)
      by (apply heading_block_wf; assumption).
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E.
    7: { (* list marker: close the heading, then open the list *)
      destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner].
      destruct (open_list_wf (off + indent_of l) (with_starts m mc) (chk_status chk) bs inner Hb Hs) as [Hob Hos].
      destruct (open_list (off + indent_of l) (with_starts m mc) (chk_status chk) (bs, inner)) as [obs ost].
      cbn [close_reopen finish app fst snd] in Hob, Hos |- *.
      split; [|exact Hos].
      rewrite wf_blocks_cons in Hhb |- *.
      apply andb_true_iff in Hhb as [Hhb _]. rewrite Hhb, Hob. reflexivity. }
    5: { (* quote: close the heading, then descend *)
      destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner].
      cbn [close_reopen open_quote finish app fst snd] in Hb, Hs |- *.
      split; [exact Hhb|].
      cbn [state_wf]. rewrite wf_blocks_rev, Hb. exact Hs. }
    5: { (* matching or differing level *)
      destruct (Nat.eqb kl hlvl) eqn:Elv;
        cbn [close_reopen open_kind finish app fst snd].
      - split; [reflexivity|].
        cbn [state_wf]. rewrite Hlv. cbn [andb].
        apply forallb_nonblank_push_text. exact Hc.
      - split; [exact Hhb|].
        cbn [state_wf]. rewrite (classify_heading_level _ _ _ E). cbn [andb].
        apply forallb_nonblank_push_text. reflexivity. }
    5: { (* attribute spec: close the heading, then open the spec *)
      destruct (open_attr_wf [] (off + indent_of l) kap l
                  (classify_kattr_nonblank l kap E)) as [Hob Hos].
      split; [|exact Hos].
      cbn [close_reopen open_attr finish fst snd]. rewrite app_nil_r. exact Hhb. }
    5: { (* footnote definition: close the heading, then descend *)
      destruct (IH (off + consumed l frest) frest (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n (off + consumed l frest) frest (PPara [])) as [bs inner].
      destruct (open_foot_wf (off + indent_of l) l flbl frest bs inner E Hb Hs)
        as [Hob Hos].
      split; [|exact Hos].
      cbn [close_reopen open_foot finish fst snd]. rewrite app_nil_r. exact Hhb. }
    5: { (* reference definition: close the heading, then open it *)
      destruct (open_ref_wf (off + indent_of l) l rlbl rval E) as [Hob Hos].
      split; [|exact Hos].
      cbn [close_reopen open_ref finish fst snd]. rewrite app_nil_r. exact Hhb. }
    (* KRow now sits between KRef and KText, and closing a heading in
       front of a table is the same as closing it in front of a thematic
       break: the `all:` below covers it. *)
    6: { (* lazy text *)
      cbn [fst snd]. split; [reflexivity|].
      cbn [state_wf]. rewrite Hlv. cbn [andb].
      rewrite forallb_nonblank_cons
        by (rewrite is_blank_drop_leading_ws;
            apply classify_ktext_nonblank; exact E).
      exact Hc. }
    (* blank, thematic, fence: close the heading and reopen outside it *)
    all: cbn [close_reopen open_quote finish app open_kind open_fence open_attr open_ref fst snd]; split;
         [ rewrite wf_blocks_cons in Hhb |- *;
           cbn [node_contents] in Hhb |- *;
           apply andb_true_iff in Hhb as [Hhb _]; rewrite Hhb; cbn [andb];
           reflexivity
         | reflexivity ].
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
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E.
    7: { (* a list marker closes the quote and opens a list outside it *)
      destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner'].
      destruct (open_list_wf (off + indent_of l) (with_starts m mc) (chk_status chk) bs inner' Hb Hs) as [Hob Hos].
      destruct (open_list (off + indent_of l) (with_starts m mc) (chk_status chk) (bs, inner')) as [obs ost].
      cbn [close_reopen finish app fst snd] in Hob, Hos |- *.
      split; [|exact Hos].
      rewrite wf_blocks_cons. cbn [node_contents mk].
      rewrite Hbq, Hob. reflexivity. }
    5: { (* quote prefix: descend into the enclosed line *)
      destruct (IH (off + consumed l rest) rest inner Hi) as [Hb Hs].
      destruct (step_fuel n (off + consumed l rest) rest inner) as [bs inner'].
      cbn [close_reopen open_quote finish app fst snd] in Hb, Hs |- *.
      split; [reflexivity|].
      cbn [state_wf]. rewrite wf_blocks_app, wf_blocks_rev, Hb, Hd. exact Hs. }
    6: { (* attribute spec: closes the quote and opens outside it *)
      destruct (open_attr_wf [] (off + indent_of l) kap l
                  (classify_kattr_nonblank l kap E)) as [Hob Hos].
      split; [|exact Hos].
      cbn [close_reopen open_attr finish fst snd]. rewrite app_nil_r.
      rewrite wf_blocks_cons. cbn [node_contents mk]. rewrite Hbq. reflexivity. }
    6: { (* footnote definition: closes the quote and opens outside it *)
      destruct (IH (off + consumed l frest) frest (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n (off + consumed l frest) frest (PPara [])) as [bs inner'].
      destruct (open_foot_wf (off + indent_of l) l flbl frest bs inner' E Hb Hs)
        as [Hob Hos].
      split; [|exact Hos].
      cbn [close_reopen open_foot finish fst snd]. rewrite app_nil_r.
      rewrite wf_blocks_cons. cbn [node_contents mk]. rewrite Hbq. reflexivity. }
    6: { (* reference definition: closes the quote and opens outside it *)
      destruct (open_ref_wf (off + indent_of l) l rlbl rval E) as [Hob Hos].
      split; [|exact Hos].
      cbn [close_reopen open_ref finish fst snd]. rewrite app_nil_r.
      rewrite wf_blocks_cons. cbn [node_contents mk]. rewrite Hbq. reflexivity. }
    (* KRow closes the quote and reopens outside it, which the `all:`
       below already covers. *)
    7: { (* text without the prefix: lazy continuation, or close *)
      cbn [is_lazy]. destruct (lazy_ok inner) eqn:El; cbn [close_reopen open_quote finish app open_kind open_fence open_attr open_ref fst snd].
      - split; [reflexivity|].
        cbn [state_wf]. rewrite Hd. cbn [andb].
        apply feed_lazy_wf;
          [apply classify_ktext_nonblank; exact E | exact Hi].
      - split.
        + rewrite wf_blocks_cons. cbn [node_contents mk]. rewrite Hbq.
          cbn [andb]. reflexivity.
        + cbn [state_wf].
          rewrite forallb_nonblank_cons
            by (rewrite is_blank_drop_leading_ws;
                apply classify_ktext_nonblank; exact E).
          reflexivity. }
    (* a fence opens through open_fence, and every other kind closes the
       quote and reopens outside it on exactly the transition
       open_kind_wf already describes *)
    all: first
         [ cbn [close_reopen open_fence finish app fst snd];
           split;
           [ rewrite wf_blocks_cons; cbn [node_contents mk]; rewrite Hbq;
             cbn [andb]; reflexivity
           | reflexivity ]
         | destruct (open_kind_wf l _ E) as [Hob Hos];
           cbn [is_lazy];
           destruct (open_kind l _) as [obs ost] eqn:Eo;
           cbn [close_reopen open_quote finish app fst snd] in Hob, Hos |- *;
           split;
           [ rewrite wf_blocks_cons; cbn [node_contents mk]; rewrite Hbq;
             cbn [andb]; exact Hob
           | exact Hos ] ].
  - (* inside a div: the close test decides, and neither side classifies
       the line, so there are two goals here rather than seven *)
    pose proof H as H0. cbn [state_wf] in H0.
    apply andb_true_iff in H0 as [Hd Hi].
    destruct (negb (in_fence dinner) && div_close dlen l)%bool; cbn [fst snd].
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
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E.
    7: { (* a bullet marker *)
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - (* indented past the marker: contents of the current item *)
        destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        destruct (div_closer l inner);
          cbn [state_wf ls_items list_content list_blank];
          rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs.
      - destruct (narrow (ls_styles ls) m).
        + (* no style survives: close this list, open another *)
          destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
          destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner'].
          destruct (open_list_wf (off + indent_of l) (with_starts m mc) (chk_status chk) bs inner' Hb Hs) as [Hob Hos].
          destruct (open_list (off + indent_of l) (with_starts m mc) (chk_status chk) (bs, inner')) as [obs ost].
          cbn [close_reopen fst snd] in Hob, Hos |- *.
          split; [|exact Hos].
          rewrite wf_blocks_app, Hob, andb_true_r. apply finish_wf. exact H.
        + (* a sibling item: the closed one joins ls_items *)
          destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
          destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner'].
          cbn [fst snd] in Hb, Hs |- *.
          split; [reflexivity|].
          cbn [state_wf]. unfold list_next, list_narrow.
          destruct (is_blank mr); cbn [ls_items forallb];
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
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        destruct (div_closer l inner);
          cbn [state_wf ls_items list_content list_blank];
          rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs.
      - destruct (open_attr_wf [] (off + indent_of l) kap l
                    (classify_kattr_nonblank l kap E)) as [Hob Hos].
        split; [|exact Hos].
        cbn [close_reopen open_attr fst snd]. rewrite app_nil_r.
        apply finish_wf. exact H. }
    6: { (* footnote definition: item contents when indented, else close *)
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        destruct (div_closer l inner);
          cbn [state_wf ls_items list_content list_blank];
          rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs.
      - destruct (IH (off + consumed l frest) frest (PPara []) eq_refl)
          as [Hb Hs].
        destruct (step_fuel n (off + consumed l frest) frest (PPara []))
          as [bs inner'].
        destruct (open_foot_wf (off + indent_of l) l flbl frest bs inner'
                    E Hb Hs) as [Hob Hos].
        split; [|exact Hos].
        cbn [close_reopen open_foot fst snd]. rewrite app_nil_r.
        apply finish_wf. exact H. }
    6: { (* reference definition: item contents when indented, else close *)
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        destruct (div_closer l inner);
          cbn [state_wf ls_items list_content list_blank];
          rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs.
      - destruct (open_ref_wf (off + indent_of l) l rlbl rval E) as [Hob Hos].
        split; [|exact Hos].
        cbn [close_reopen open_ref fst snd]. rewrite app_nil_r.
        apply finish_wf. exact H. }
    (* KRow is an ordinary close-and-reopen kind: the `all:` below. *)
    7: { (* text: lazy continuation into the item, or close the list *)
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        destruct (div_closer l inner);
          cbn [state_wf ls_items list_content list_blank];
          rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs.
      - cbn [is_lazy]. destruct (lazy_ok inner) eqn:El; cbn [fst snd].
        + split; [reflexivity|].
          cbn [state_wf]. rewrite Hitems, Hd. cbn [andb].
          apply feed_lazy_wf;
            [apply classify_ktext_nonblank; exact E | exact Hi].
        + destruct (open_kind_wf l _ E) as [Hob Hos].
          destruct (open_kind l _) as [obs ost] eqn:Eo.
          cbn [close_reopen fst snd] in Hob, Hos |- *.
          split; [|exact Hos].
          rewrite wf_blocks_app, Hob, andb_true_r.
          apply finish_wf. exact H. }
    4: { (* a quote either belongs to the item or opens after the list *)
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        destruct (div_closer l inner);
          cbn [state_wf ls_items list_content list_blank];
          rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs.
      - destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner'].
        cbn [fst snd] in Hb, Hs.
        cbn [close_reopen open_quote fst snd]. split.
        + rewrite app_nil_r. apply finish_wf. exact H.
        + cbn [state_wf]. rewrite wf_blocks_rev, Hb. exact Hs. }
    (* every other kind: item contents when indented, else close the
       list and reopen outside it *)
    all: destruct (Nat.ltb (ls_indent ls) (off + indent_of l));
         [ destruct (IH off l inner Hi) as [Hb Hs];
           destruct (step_fuel n off l inner) as [bs inner'];
           cbn [fst snd] in Hb, Hs |- *;
           split; [reflexivity|];
           destruct (div_closer l inner);
           cbn [state_wf ls_items list_content list_blank];
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
       state this invariant already covers, or records a nonblank line *)
    cbn [state_wf] in H.
    destruct (ap_done aap); [apply IH; reflexivity|].
    destruct (Nat.ltb aind (off + indent_of l));
      [destruct (ap_failed (attr_feed l aap))|].
    + apply IH. cbn [state_wf]. exact H.
    + cbn [fst snd]. split; [reflexivity|].
      cbn [state_wf]. apply forallb_nonblank_push_text. exact H.
    + apply IH. cbn [state_wf]. exact H.
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
      cbn [fst snd] in Hb, Hs |- *. split; [|exact Hs].
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
    + destruct (Nat.ltb find (off + indent_of l)).
      * destruct (IH off l finner Hinner) as [Hb Hs].
        destruct (step_fuel n off l finner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *. split; [reflexivity|].
        cbn [state_wf]. rewrite Hlbl, wf_blocks_app, wf_blocks_rev, Hb, Hdone, Hs.
        reflexivity.
      * destruct (IH off l (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n off l (PPara [])) as [bs st'].
        cbn [fst snd] in Hb, Hs |- *. split; [|exact Hs].
        rewrite wf_blocks_cons. cbn [foot_block node_contents mk].
        rewrite wf_block_footnote, Hlbl, Hbody, Hb.
        reflexivity.
  - (* a table: a row line extends it, a caption opener starts one, a
       blank leaves it waiting, and anything else emits it and
       reprocesses the line from idle *)
    assert (Htb : wf_blocks [table_block (rev trows) tcap] = true)
      by (apply table_block_wf; exact H).
    destruct tcap as [| |ls].
    3: { destruct (is_blank l) eqn:Eb; cbn [fst snd].
         - split; [exact Htb | reflexivity].
         - split; [reflexivity|]. cbn [state_wf cap_lines] in H |- *.
           rewrite forallb_nonblank_cons
             by (rewrite is_blank_drop_leading_ws; exact Eb).
           exact H. }
    all: destruct (caption_open l) as [rest|] eqn:Ec;
         [ split; [reflexivity|];
           cbn [state_wf cap_lines]; apply forallb_nonblank_push_text;
           reflexivity
         | destruct (is_blank l) eqn:Eb; [split; reflexivity|] ].
    { destruct (classify l) eqn:E; try (split; reflexivity);
        (destruct (IH off l (PPara []) eq_refl) as [Hb Hs];
         destruct (step_fuel n off l (PPara [])) as [bs st'];
         cbn [fst snd] in Hb, Hs |- *; split; [|exact Hs];
         rewrite wf_blocks_cons; cbn [node_contents];
         rewrite Hb, andb_true_r;
         rewrite wf_blocks_cons in Htb; cbn [node_contents] in Htb;
         rewrite andb_true_r in Htb; exact Htb). }
    { destruct (classify l) eqn:E;
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
    destruct (classify l) eqn:E;
      try (destruct (is_idle pinner);
           [ solve [ split; reflexivity
                   | apply open_attr_wf, (classify_kattr_nonblank l _ E) ] |]);
      destruct (IH off l pinner H) as [Hb Hs];
      destruct (step_fuel n off l pinner) as [bs st'] eqn:Ed;
      cbn [fst snd] in Hb, Hs;
      destruct bs; cbn [pend_result fst snd state_wf];
      (split; [rewrite ?wf_blocks_decorate_head; exact Hb | exact Hs]).
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

(* The block constructs Parser.v has a rule for.  `Section` is the only
   one left without: it is the document pass's, not the line fold's.
   Recursive, so a quote whose contents are unreachable is itself
   unreachable. *)
Fixpoint supported (b : block) : bool :=
  let sup_bs :=
    fix go (ns : list (node block)) : bool :=
      match ns with
      | [] => true
      | Node _ _ x :: rest => supported x && go rest
      end in
  let sup_items :=
    fix goi (its : list (list (node block))) : bool :=
      match its with
      | [] => true
      | it :: rest => sup_bs it && goi rest
      end in
  match b with
  | Para _ | ThematicBreak | CodeBlock _ _ | RawBlock _ _ | Heading _ _
  | RefDef _ _ => true
  (* A table's cells and caption hold inlines, so it recurses into
     nothing. *)
  | Table _ _ => true
  | FootnoteDef _ bs => sup_bs bs
  | BlockQuote bs | Div bs => sup_bs bs
  | BulletList _ items => sup_items items
  | OrderedList _ _ items => sup_items items
  (* A term holds inlines, so only the definition is recursed into. *)
  | DefinitionList _ items =>
      (fix god (its : list (inlines * list (node block))) : bool :=
         match its with
         | [] => true
         | (_, it) :: rest => sup_bs it && god rest
         end) items
  (* A status is a leaf, so a task item recurses like a definition's. *)
  | TaskList _ items =>
      (fix got (its : list (task_status * list (node block))) : bool :=
         match its with
         | [] => true
         | (_, it) :: rest => sup_bs it && got rest
         end) items
  | _ => false
  end.

Definition supported_blocks (bs : blocks) : bool :=
  forallb (fun n => supported (node_contents n)) bs.

Lemma supported_footnote :
  forall label bs, supported (FootnoteDef label bs) = supported_blocks bs.
Proof.
  intros label bs. cbn [supported].
  induction bs as [|[p a b] rest IH]; [reflexivity|].
  cbn [supported_blocks forallb node_contents]. rewrite IH. reflexivity.
Qed.

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

Lemma supported_div :
  forall bs, supported (Div bs) = supported_blocks bs.
Proof.
  induction bs as [|n bs IH]; [reflexivity|].
  destruct n as [p a x].
  change (supported (Div (Node p a x :: bs)))
    with (supported x && supported (Div bs))%bool.
  rewrite IH. reflexivity.
Qed.

Lemma div_block_supported :
  forall cls bs,
    supported_blocks bs = true -> supported_blocks [div_block cls bs] = true.
Proof.
  intros cls bs H. unfold div_block.
  destruct (String.eqb cls EmptyString);
    rewrite supported_blocks_cons; cbn [node_contents mk];
    rewrite supported_div, H; reflexivity.
Qed.

Lemma supported_bullet :
  forall sp items,
    supported (BulletList sp items) = forallb supported_blocks items.
Proof.
  intros sp items.
  assert (H : forall its,
             (fix goi (l : list (list (node block))) : bool :=
                match l with
                | [] => true
                | it :: rest => (supported (BlockQuote it) && goi rest)%bool
                end) its = forallb supported_blocks its).
  { induction its as [|it rest IH]; [reflexivity|].
    cbn [forallb]. rewrite supported_quote, IH. reflexivity. }
  change (supported (BulletList sp items))
    with ((fix goi (l : list (list (node block))) : bool :=
             match l with
             | [] => true
             | it :: rest => (supported (BlockQuote it) && goi rest)%bool
             end) items).
  apply H.
Qed.

Lemma supported_olist :
  forall oa sp items,
    supported (OrderedList oa sp items) = forallb supported_blocks items.
Proof.
  intros oa sp items.
  assert (H : forall its,
             (fix goi (l : list (list (node block))) : bool :=
                match l with
                | [] => true
                | it :: rest => (supported (BlockQuote it) && goi rest)%bool
                end) its = forallb supported_blocks its).
  { induction its as [|it rest IH]; [reflexivity|].
    cbn [forallb]. rewrite supported_quote, IH. reflexivity. }
  change (supported (OrderedList oa sp items))
    with ((fix goi (l : list (list (node block))) : bool :=
             match l with
             | [] => true
             | it :: rest => (supported (BlockQuote it) && goi rest)%bool
             end) items).
  apply H.
Qed.

Lemma supported_deflist :
  forall sp items,
    supported (DefinitionList sp items)
    = forallb (fun ti => supported_blocks (snd ti)) items.
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
  cbn [supported]. induction items as [|[term it] rest IH]; [reflexivity|].
  cbn [forallb snd]. rewrite IH, Hb. reflexivity.
Qed.

(* Unlike `wf_list_block`, this one stays an equation: the blocks the
   split removes are a paragraph, which `supported` answers `true` for,
   and the definitions it steps over stay in the list. *)
Lemma supported_def_split :
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

Lemma supported_def_items :
  forall its,
    forallb (fun ti => supported_blocks (snd ti)) (def_items its)
    = forallb supported_blocks its.
Proof.
  unfold def_items. induction its as [|it rest IH]; [reflexivity|].
  cbn [forallb map]. rewrite IH. f_equal.
  destruct (def_split it) as [[ils def]|] eqn:E.
  - rewrite (def_item_some it _ E). cbn [snd].
    exact (supported_def_split it ils def E).
  - rewrite (def_item_none it E). reflexivity.
Qed.

Lemma supported_tasklist :
  forall sp items,
    supported (TaskList sp items)
    = forallb (fun ti => supported_blocks (snd ti)) items.
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
  cbn [supported]. induction items as [|[st it] rest IH]; [reflexivity|].
  cbn [forallb snd]. rewrite IH, Hb. reflexivity.
Qed.

(* Pairing statuses onto items is invisible to `supported`. *)
Lemma supported_task_items :
  forall (chks : list task_status) its,
    forallb (fun ti => supported_blocks (snd ti)) (task_items chks its)
    = forallb supported_blocks its.
Proof.
  intros chks its. revert chks.
  induction its as [|it rest IH]; intros chks; [reflexivity|].
  destruct chks as [|c cs]; cbn [task_items forallb snd]; rewrite IH;
    reflexivity.
Qed.

(* `supported` cannot tell the list flavours apart, so
   `finish_supported` stays one case. *)
Lemma supported_list_block :
  forall ls last,
    supported (node_contents (list_block ls last))
    = forallb supported_blocks (rev (last :: ls_items ls)).
Proof.
  intros ls last. unfold list_block.
  destruct (ls_styles ls) as [|[[c|c|n d] st] ss].
  - cbn [node_contents mk]. apply supported_bullet.
  - destruct (Ascii.eqb c ":"); cbn [node_contents mk].
    + rewrite supported_deflist. apply supported_def_items.
    + apply supported_bullet.
  - cbn [node_contents mk].
    rewrite supported_tasklist. apply supported_task_items.
  - cbn [node_contents mk]. apply supported_olist.
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
  | PPara _ | PHeading _ _ | PFence _ _ _ => true
  | PQuote done inner => supported_blocks done && state_supported inner
  | PDiv _ _ done inner => supported_blocks done && state_supported inner
  | PList ls done inner =>
      forallb supported_blocks (ls_items ls) && supported_blocks done
      && state_supported inner
  (* A spec emits at most a paragraph, a definition emits a RefDef, and
     pending attributes emit nothing of their own. *)
  | PAttr _ _ _ _ | PRef _ _ _ | PTable _ _ => true
  | PFoot _ _ done inner => supported_blocks done && state_supported inner
  | PPend _ inner => state_supported inner
  end.

Lemma supported_blocks_decorate_head :
  forall a bs, supported_blocks (decorate_head a bs) = supported_blocks bs.
Proof. intros a bs. destruct bs as [|[q a' x] rest]; reflexivity. Qed.

Lemma finish_supported :
  forall st, state_supported st = true -> supported_blocks (finish st) = true.
Proof.
  induction st as [cur|lvl hcur|f fnd acc|done inner IH|dlen dcls ddone dinner IH
    |ls done inner IH|apend aind aap aslices|rind rlbl rval
    |find flbl fdone finner IH|trows tcap|ppend pinner IH];
    intros H.
  - destruct cur as [|c cur']; reflexivity.
  - reflexivity.
  - cbn [finish]. rewrite supported_blocks_cons, fence_block_supported.
    reflexivity.
  - cbn [state_supported] in H. apply andb_true_iff in H as [Hd Hi].
    cbn [finish]. rewrite supported_blocks_cons. cbn [node_contents mk].
    rewrite supported_quote, supported_blocks_app, supported_blocks_rev, Hd,
      (IH Hi).
    reflexivity.
  - cbn [state_supported] in H. apply andb_true_iff in H as [Hd Hi].
    cbn [finish]. apply div_block_supported.
    rewrite supported_blocks_app, supported_blocks_rev, Hd, (IH Hi).
    reflexivity.
  - cbn [state_supported] in H. apply andb_true_iff in H as [H1 Hi].
    apply andb_true_iff in H1 as [Hitems Hd].
    cbn [finish]. rewrite supported_blocks_cons.
    rewrite supported_list_block, forallb_rev. cbn [forallb].
    rewrite supported_blocks_app, supported_blocks_rev, Hd, (IH Hi), Hitems.
    reflexivity.
  - cbn [finish]. destruct (ap_done aap); [reflexivity|].
    destruct aslices; reflexivity.
  - reflexivity.
  - cbn [state_supported] in H. apply andb_true_iff in H as [Hd Hi].
    cbn [finish]. rewrite supported_blocks_cons. cbn [foot_block node_contents mk].
    rewrite supported_footnote.
    rewrite supported_blocks_app, supported_blocks_rev, Hd, (IH Hi).
    reflexivity.
  - reflexivity.                        (* a table recurses into nothing *)
  - cbn [state_supported] in H. cbn [finish].
    rewrite supported_blocks_decorate_head. exact (IH H).
Qed.

Lemma feed_lazy_supported :
  forall l st,
    state_supported st = true -> state_supported (feed_lazy l st) = true.
Proof.
  induction st as [cur|lvl hcur|f fnd acc|done inner IH|dlen dcls ddone dinner IH
    |ls done inner IH|apend aind aap aslices|rind rlbl rval
    |find flbl fdone finner IH|trows tcap|ppend pinner IH];
    intros H;
    [reflexivity | reflexivity | reflexivity | | | | reflexivity | reflexivity
    | | reflexivity | ].
  5: { cbn [feed_lazy state_supported] in *. exact (IH H). }
  - cbn [feed_lazy state_supported] in *.
    apply andb_true_iff in H as [Hd Hi]. rewrite Hd, (IH Hi). reflexivity.
  - cbn [feed_lazy state_supported] in *.
    apply andb_true_iff in H as [Hd Hi]. rewrite Hd, (IH Hi). reflexivity.
  - cbn [feed_lazy state_supported] in *.
    apply andb_true_iff in H as [H1 Hi]. apply andb_true_iff in H1 as [Ht Hd].
    rewrite Ht, Hd, (IH Hi). reflexivity.
  - cbn [feed_lazy state_supported] in *.
    apply andb_true_iff in H as [Hd Hi]. rewrite Hd, (IH Hi). reflexivity.
Qed.

Lemma open_list_supported :
  forall ind m chk bs inner,
    supported_blocks bs = true -> state_supported inner = true ->
    supported_blocks (fst (open_list ind m chk (bs, inner))) = true
    /\ state_supported (snd (open_list ind m chk (bs, inner))) = true.
Proof.
  intros ind m chk bs inner Hb Hi.
  cbn [open_list fst snd state_supported ls_items forallb].
  split; [reflexivity|]. rewrite supported_blocks_rev, Hb, Hi. reflexivity.
Qed.

(* Same case analysis as step_fuel_wf: the emitted constructors are
   supported unconditionally, so only the container accumulators are
   threaded. *)
Lemma step_fuel_supported :
  forall n off l st,
    state_supported st = true ->
    supported_blocks (fst (step_fuel n off l st)) = true
    /\ state_supported (snd (step_fuel n off l st)) = true.
Proof.
  induction n as [|n IH]; intros off l st H; [split; [reflexivity | exact H]|].
  cbn [step_fuel].
  destruct st as [cur|hlvl hcur|f fnd acc|done inner|dlen dcls ddone dinner|ls done inner|apend aind aap aslices|rind rlbl rval|find flbl fdone finner|trows tcap|ppend pinner].
  - destruct cur as [|c cur'].
    + destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E;
        try (cbn [close_reopen open_quote finish app open_kind open_fence open_attr open_ref fst snd]; split; reflexivity).
      * destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner].
        cbn [close_reopen open_quote finish app fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        cbn [state_supported]. rewrite supported_blocks_rev, Hb. exact Hs.
      * destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner].
        apply open_list_supported; assumption.
      * destruct (IH (off + consumed l frest) frest (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l frest) frest (PPara [])) as [bs inner].
        cbn [fst snd] in Hb, Hs.
        cbn [open_foot fst snd state_supported]. split; [reflexivity|].
        rewrite supported_blocks_rev, Hb. exact Hs.
    + destruct (classify l); cbn [fst snd]; split; reflexivity.
  - (* an open heading: Heading is supported, so only the quote branch
       carries anything to prove *)
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E.
    7: { destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
         destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner].
         destruct (open_list_supported (off + indent_of l) (with_starts m mc) (chk_status chk) bs inner Hb Hs)
           as [Hob Hos].
         destruct (open_list (off + indent_of l) (with_starts m mc) (chk_status chk) (bs, inner)) as [obs ost].
         cbn [close_reopen finish app fst snd] in Hob, Hos |- *.
         rewrite supported_blocks_cons. cbn [node_contents].
         rewrite Hob. split; [reflexivity | exact Hos]. }
    5: { destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
         destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner].
         cbn [close_reopen open_quote finish app fst snd] in Hb, Hs |- *.
         split; [reflexivity|].
         cbn [state_supported]. rewrite supported_blocks_rev, Hb. exact Hs. }
    5: { destruct (Nat.eqb kl hlvl); cbn [fst snd]; split; reflexivity. }
    6: { destruct (IH (off + consumed l frest) frest (PPara []) eq_refl)
           as [Hb Hs].
         destruct (step_fuel n (off + consumed l frest) frest (PPara []))
           as [bs inner].
         cbn [fst snd] in Hb, Hs.
         cbn [close_reopen open_foot finish app fst snd]. split; [reflexivity|].
         cbn [state_supported]. rewrite supported_blocks_rev, Hb. exact Hs. }
    all: cbn [close_reopen open_quote finish app open_kind open_fence open_attr open_ref fst snd]; split; reflexivity.
  - destruct (fence_close f l); cbn [fst snd].
    + rewrite supported_blocks_cons, fence_block_supported. split; reflexivity.
    + split; reflexivity.
  - pose proof H as H0. cbn [state_supported] in H0.
    apply andb_true_iff in H0 as [Hd Hi].
    assert (Hbq : supported (BlockQuote (rev done ++ finish inner)%list) = true).
    { rewrite supported_quote, supported_blocks_app, supported_blocks_rev, Hd,
        (finish_supported _ Hi).
      reflexivity. }
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E.
    7: { destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
         destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner'].
         destruct (open_list_supported (off + indent_of l) (with_starts m mc) (chk_status chk) bs inner' Hb Hs)
           as [Hob Hos].
         destruct (open_list (off + indent_of l) (with_starts m mc) (chk_status chk) (bs, inner')) as [obs ost].
         cbn [close_reopen finish app fst snd] in Hob, Hos |- *.
         split; [|exact Hos].
         rewrite supported_blocks_cons. cbn [node_contents mk].
         rewrite Hbq, Hob. reflexivity. }
    5: { destruct (IH (off + consumed l rest) rest inner Hi) as [Hb Hs].
         destruct (step_fuel n (off + consumed l rest) rest inner) as [bs inner'].
         cbn [close_reopen open_quote finish app fst snd] in Hb, Hs |- *.
         split; [reflexivity|].
         cbn [state_supported].
         rewrite supported_blocks_app, supported_blocks_rev, Hb, Hd. exact Hs. }
    7: { destruct (IH (off + consumed l frest) frest (PPara []) eq_refl)
           as [Hb Hs].
         destruct (step_fuel n (off + consumed l frest) frest (PPara []))
           as [bs inner'].
         cbn [fst snd] in Hb, Hs.
         cbn [close_reopen open_foot finish app fst snd]. split.
         - rewrite supported_blocks_cons. cbn [node_contents mk].
           rewrite Hbq. reflexivity.
         - cbn [state_supported]. rewrite supported_blocks_rev, Hb. exact Hs. }
    9: { cbn [is_lazy]. destruct (lazy_ok inner); cbn [close_reopen open_quote finish app open_kind open_fence open_attr open_ref fst snd].
         - split; [reflexivity|].
           cbn [state_supported]. rewrite Hd. cbn [andb].
           apply feed_lazy_supported. exact Hi.
         - split; [| reflexivity].
           rewrite supported_blocks_cons. cbn [node_contents mk].
           rewrite Hbq. cbn [andb]. reflexivity. }
    all: cbn [is_lazy close_reopen open_quote finish app open_kind open_fence
              open_attr open_ref fst snd]; split;
         [ rewrite supported_blocks_cons; cbn [node_contents mk]; rewrite Hbq;
           cbn [andb]; reflexivity
         | reflexivity ].
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
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E.
    7: { destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *.
           split; [reflexivity|].
           destruct (div_closer l inner);
             cbn [state_supported ls_items list_content list_blank];
             rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
             exact Hs.
         - destruct (narrow (ls_styles ls) m).
           + destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
             destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner'].
             destruct (open_list_supported (off + indent_of l) (with_starts m mc) (chk_status chk) bs inner' Hb Hs)
               as [Hob Hos].
             destruct (open_list (off + indent_of l) (with_starts m mc) (chk_status chk) (bs, inner')) as [obs ost].
             cbn [close_reopen fst snd] in Hob, Hos |- *.
             split; [|exact Hos].
             rewrite supported_blocks_app, Hob, andb_true_r.
             apply finish_supported. exact H.
           + destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
             destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner'].
             cbn [fst snd] in Hb, Hs |- *.
             split; [reflexivity|].
             cbn [state_supported]. unfold list_next, list_narrow.
             destruct (is_blank mr); cbn [ls_items forallb];
               rewrite Hitem, Hitems, supported_blocks_rev, Hb; exact Hs. }
    1: { destruct (IH off l inner Hi) as [Hb Hs].
         destruct (step_fuel n off l inner) as [bs inner'].
         cbn [fst snd] in Hb, Hs |- *.
         split; [reflexivity|].
         cbn [state_supported].
         destruct (blank_absorbed inner); cbn [ls_items list_blank];
           rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
           exact Hs. }
    7: { destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *.
           split; [reflexivity|].
           destruct (div_closer l inner);
             cbn [state_supported ls_items list_content list_blank];
             rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
             exact Hs.
         - destruct (IH (off + consumed l frest) frest (PPara []) eq_refl)
             as [Hb Hs].
           destruct (step_fuel n (off + consumed l frest) frest (PPara []))
             as [bs inner'].
           cbn [fst snd] in Hb, Hs.
           cbn [close_reopen open_foot fst snd]. split.
           + rewrite app_nil_r. apply finish_supported. exact H.
           + cbn [state_supported]. rewrite supported_blocks_rev, Hb. exact Hs. }
    9: { destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *.
           split; [reflexivity|].
           destruct (div_closer l inner);
             cbn [state_supported ls_items list_content list_blank];
             rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
             exact Hs.
         - cbn [is_lazy]. destruct (lazy_ok inner); cbn [fst snd].
           + split; [reflexivity|].
             cbn [state_supported]. rewrite Hitems, Hd. cbn [andb].
             apply feed_lazy_supported. exact Hi.
           + cbn [close_reopen open_kind open_attr open_ref fst snd]. split; [|reflexivity].
             rewrite supported_blocks_app, (finish_supported _ H).
             reflexivity. }
    4: { destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *.
           split; [reflexivity|].
           destruct (div_closer l inner);
             cbn [state_supported ls_items list_content list_blank];
             rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
             exact Hs.
         - destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
           destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner'].
           cbn [fst snd] in Hb, Hs.
           cbn [close_reopen open_quote fst snd]. split.
           + rewrite app_nil_r. apply finish_supported. exact H.
           + cbn [state_supported]. rewrite supported_blocks_rev, Hb. exact Hs. }
    all: destruct (Nat.ltb (ls_indent ls) (off + indent_of l));
         [ destruct (IH off l inner Hi) as [Hb Hs];
           destruct (step_fuel n off l inner) as [bs inner'];
           cbn [fst snd] in Hb, Hs |- *;
           split; [reflexivity|];
           destruct (div_closer l inner);
           cbn [state_supported ls_items list_content list_blank];
           rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
           exact Hs
         | cbn [is_lazy close_reopen open_kind open_fence open_attr open_ref
                fst snd];
           split; [|reflexivity];
           rewrite supported_blocks_app, (finish_supported _ H);
           reflexivity ].
  - (* an attribute spec emits nothing until it resolves *)
    destruct (ap_done aap); [apply IH; reflexivity|].
    destruct (Nat.ltb aind (off + indent_of l));
      [destruct (ap_failed (attr_feed l aap))|];
      [apply IH; reflexivity | split; reflexivity | apply IH; reflexivity].
  - (* a reference definition: it emits a RefDef, which is supported *)
    destruct (if Nat.ltb rind (off + indent_of l) then ref_cont l else None);
      [split; reflexivity|].
    destruct (IH off l (PPara []) eq_refl) as [Hb Hs].
    destruct (step_fuel n off l (PPara [])) as [bs st'].
    cbn [fst snd] in Hb, Hs |- *.
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
    + destruct (Nat.ltb find (off + indent_of l)).
      * destruct (IH off l finner Hi) as [Hb Hs].
        destruct (step_fuel n off l finner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *. split; [reflexivity|].
        cbn [state_supported].
        rewrite supported_blocks_app, supported_blocks_rev, Hb, Hd, Hs.
        reflexivity.
      * destruct (IH off l (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n off l (PPara [])) as [bs st'].
        cbn [fst snd] in Hb, Hs |- *. split; [|exact Hs].
        rewrite supported_blocks_cons. cbn [foot_block node_contents mk].
        rewrite supported_footnote, Hbody, Hb. reflexivity.
  - (* a table: what it emits is supported, and so is what the line
       reopens *)
    destruct tcap as [| |ls].
    3: { destruct (is_blank l); cbn [fst snd]; split; reflexivity. }
    all: destruct (caption_open l) as [rest|] eqn:Ec; [split; reflexivity|];
         destruct (is_blank l) eqn:Eb; [split; reflexivity|];
         destruct (classify l) eqn:E; try (split; reflexivity);
         (destruct (IH off l (PPara []) eq_refl) as [Hb Hs];
          destruct (step_fuel n off l (PPara [])) as [bs st'];
          cbn [fst snd] in Hb, Hs |- *; split; [|exact Hs];
          rewrite supported_blocks_cons; cbn [table_block node_contents mk];
          exact Hb).
  - cbn [state_supported] in H.
    destruct (classify l) eqn:E;
      try (destruct (is_idle pinner); [split; reflexivity|]);
      destruct (IH off l pinner H) as [Hb Hs];
      destruct (step_fuel n off l pinner) as [bs st'] eqn:Ed;
      cbn [fst snd] in Hb, Hs;
      destruct bs; cbn [pend_result fst snd state_supported];
      (split; [rewrite ?supported_blocks_decorate_head; exact Hb | exact Hs]).
Qed.

Lemma parse_lines_supported :
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
   fold — sections only ever come from Document.sectionize, which runs
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
  obligation — discharged because every section starts with the heading
  that opened it.
*)

Lemma wf_block_section :
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

Lemma assign_ids_wf :
  forall b p a st,
    wf_block b = true ->
    wf_block (node_contents (snd (assign_ids b p a st))) = true.
Proof.
  intros b.
  induction b using block_ind2 with
    (Q := fun bs => forall st,
            wf_blocks bs = true ->
            wf_blocks (snd (assign_ids_list bs st)) = true)
    (R := fun its => forall st,
            forallb wf_blocks its = true ->
            forallb wf_blocks (snd (assign_ids_items its st)) = true)
    (D := fun its => forall st,
            forallb (fun ti => wf_inlines (fst ti) && wf_blocks (snd ti)) its
            = true ->
            forallb (fun ti => wf_inlines (fst ti) && wf_blocks (snd ti))
              (snd (assign_ids_def_items its st)) = true)
    (K := fun its => forall st,
            forallb (fun ti => wf_blocks (snd ti)) its = true ->
            forallb (fun ti => wf_blocks (snd ti))
              (snd (assign_ids_task_items its st)) = true);
    intros; try exact H.
  (* A `Section` is unreachable from the line fold, but the lemma is
     stated for every block, so it is discharged by the identity branch
     of assign_ids above. *)
  - (* Heading *)
    unfold assign_ids, assign_heading_id.
    destruct (lookup_attr "id" a) as [v|]; exact H.
  - (* BlockQuote *)
    rewrite assign_ids_quote.
    destruct (assign_ids_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd node_contents].
    rewrite wf_block_quote in H |- *.
    change bs' with (snd (st', bs')). rewrite <- E.
    apply IHb. exact H.
  - (* Div *)
    rewrite assign_ids_div.
    destruct (assign_ids_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd node_contents].
    rewrite wf_block_div in H |- *.
    change bs' with (snd (st', bs')). rewrite <- E.
    apply IHb. exact H.
  - (* OrderedList: as the bullet case below *)
    rewrite assign_ids_olist.
    destruct (assign_ids_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd node_contents].
    rewrite wf_block_olist in H |- *.
    apply andb_true_iff in H as [Hne Hits].
    apply andb_true_iff. split.
    + replace its' with (snd (assign_ids_items items (register_id a st)))
        by (rewrite E; reflexivity).
      rewrite assign_ids_items_nonempty. exact Hne.
    + change its' with (snd (st', its')). rewrite <- E.
      apply IHb. exact Hits.
  - (* BulletList: the id pass rewrites items, so the nonempty conjunct
       has to survive the traversal too *)
    rewrite assign_ids_blist.
    destruct (assign_ids_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd node_contents].
    rewrite wf_block_bullet in H |- *.
    apply andb_true_iff in H as [Hne Hits].
    apply andb_true_iff. split.
    + replace its' with (snd (assign_ids_items items (register_id a st)))
        by (rewrite E; reflexivity).
      rewrite assign_ids_items_nonempty. exact Hne.
    + change its' with (snd (st', its')). rewrite <- E.
      apply IHb. exact Hits.
  - (* TaskList: as the bullet case, over pairs *)
    rewrite assign_ids_tasklist.
    destruct (assign_ids_task_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd node_contents].
    rewrite wf_block_tasklist in H |- *.
    apply andb_true_iff in H as [Hne Hits].
    apply andb_true_iff. split.
    + replace its' with (snd (assign_ids_task_items items (register_id a st)))
        by (rewrite E; reflexivity).
      rewrite assign_ids_task_items_nonempty. exact Hne.
    + change its' with (snd (st', its')). rewrite <- E.
      apply IHb. exact Hits.
  - (* DefinitionList: as the bullet case, over pairs *)
    rewrite assign_ids_deflist.
    destruct (assign_ids_def_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd node_contents].
    rewrite wf_block_deflist in H |- *.
    apply andb_true_iff in H as [Hne Hits].
    apply andb_true_iff. split.
    + replace its' with (snd (assign_ids_def_items items (register_id a st)))
        by (rewrite E; reflexivity).
      rewrite assign_ids_def_items_nonempty. exact Hne.
    + change its' with (snd (st', its')). rewrite <- E.
      apply IHb. exact Hits.
  - (* FootnoteDef: identifiers recurse through its body. *)
    rewrite assign_ids_foot.
    destruct (assign_ids_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd node_contents]. rewrite wf_block_footnote in H |- *.
    apply andb_true_iff in H as [Hlbl Hbs].
    apply andb_true_iff. split; [exact Hlbl|].
    change bs' with (snd (st', bs')). rewrite <- E. apply IHb. exact Hbs.
  - (* Node p a b :: rest *)
    rewrite wf_blocks_cons in H. apply andb_true_iff in H as [Hx Hrest].
    cbn [assign_ids_list assign_ids_node].
    destruct (assign_ids b p a st) as [st1 n1] eqn:E1.
    destruct (assign_ids_list rest st1) as [st2 rest1] eqn:E2.
    cbn [snd]. rewrite wf_blocks_cons.
    apply andb_true_iff. split.
    + change n1 with (snd (st1, n1)). rewrite <- E1. apply IHb. exact Hx.
    + change rest1 with (snd (st2, rest1)). rewrite <- E2.
      apply IHb0. exact Hrest.
  - (* R's cons *)
    cbn [forallb] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [assign_ids_items].
    destruct (assign_ids_list it st) as [s1 it1] eqn:E1.
    destruct (assign_ids_items rest s1) as [s2 rest1] eqn:E2.
    cbn [snd forallb]. apply andb_true_iff. split.
    + change it1 with (snd (s1, it1)). rewrite <- E1. apply IHb. exact Hit.
    + change rest1 with (snd (s2, rest1)). rewrite <- E2.
      apply IHb0. exact Hrest.
  - (* D's cons: the term is carried, so only the definition moves *)
    cbn [forallb fst snd] in H. apply andb_true_iff in H as [Hit Hrest].
    apply andb_true_iff in Hit as [Hterm Hit].
    cbn [assign_ids_def_items].
    destruct (assign_ids_list it st) as [s1 it1] eqn:E1.
    destruct (assign_ids_def_items rest s1) as [s2 rest1] eqn:E2.
    cbn [snd forallb fst]. apply andb_true_iff. split.
    + apply andb_true_iff. split; [exact Hterm|].
      change it1 with (snd (s1, it1)). rewrite <- E1. apply IHb. exact Hit.
    + change rest1 with (snd (s2, rest1)). rewrite <- E2.
      apply IHb0. exact Hrest.
  - (* K's cons: the status is carried the same way *)
    cbn [forallb snd] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [assign_ids_task_items].
    destruct (assign_ids_list it st) as [s1 it1] eqn:E1.
    destruct (assign_ids_task_items rest s1) as [s2 rest1] eqn:E2.
    cbn [snd forallb]. apply andb_true_iff. split.
    + change it1 with (snd (s1, it1)). rewrite <- E1. apply IHb. exact Hit.
    + change rest1 with (snd (s2, rest1)). rewrite <- E2.
      apply IHb0. exact Hrest.
Qed.

Lemma assign_ids_list_wf :
  forall bs st,
    wf_blocks bs = true -> wf_blocks (snd (assign_ids_list bs st)) = true.
Proof.
  induction bs as [|[p a x] rest IH]; intros st H; [reflexivity|].
  rewrite wf_blocks_cons in H. apply andb_true_iff in H as [Hx Hrest].
  cbn [assign_ids_list assign_ids_node].
  destruct (assign_ids x p a st) as [st1 n1] eqn:E1.
  destruct (assign_ids_list rest st1) as [st2 rest1] eqn:E2.
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
   well-formed, and every entry above the document's has a nonempty one —
   which is what discharges Section's nonempty obligation on close.  The
   bottom entry may be empty: an empty document is well-formed. *)
Fixpoint sect_state_wf (stk : sect_state) : bool :=
  match stk with
  | [] => false                      (* the document entry is never popped *)
  | [(_, _, acc)] => wf_blocks acc
  | (_, _, acc) :: outer => nonempty acc && wf_blocks acc && sect_state_wf outer
  end.

Lemma close_ge_wf :
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
      rewrite wf_blocks_cons. cbn [node_contents].
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
Lemma close_all_wf :
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
    rewrite wf_blocks_cons. cbn [node_contents].
    rewrite wf_block_section, wf_blocks_rev, wf_blocks_app, Hp, Hacc.
    cbn [andb]. rewrite andb_true_r.
    rewrite nonempty_rev, andb_true_r. apply nonempty_app_r. exact Hne.
Qed.

Lemma sect_push_wf :
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
Lemma sect_state_wf_cons :
  forall l a acc stk,
    nonempty acc = true -> wf_blocks acc = true -> sect_state_wf stk = true ->
    sect_state_wf ((l, a, acc) :: stk) = true.
Proof.
  intros l a acc [|e outer] Hne Hacc Hstk; [discriminate|].
  change (sect_state_wf ((l, a, acc) :: e :: outer))
    with (nonempty acc && wf_blocks acc && sect_state_wf (e :: outer))%bool.
  rewrite Hne, Hacc, Hstk. reflexivity.
Qed.

Lemma sect_step_wf :
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
  - unfold wf_blocks. cbn [forallb node_contents].
    rewrite andb_true_r. exact Hn.
  - apply close_ge_wf; [reflexivity | exact Hs].
Qed.

Lemma sect_bottom_wf :
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
Lemma fold_sect_step_wf :
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

Lemma sectionize_wf :
  forall bs, wf_blocks bs = true -> wf_blocks (sectionize bs) = true.
Proof.
  intros bs H. unfold sectionize.
  apply sect_bottom_wf, close_all_wf; [reflexivity|].
  apply fold_sect_step_wf; [exact H | reflexivity].
Qed.

Definition wf_note_map (m : note_map) : bool :=
  forallb (fun p : string * blocks => wf_blocks (snd p)) m.

Lemma wf_note_map_set :
  forall label bs m,
    wf_blocks bs = true -> wf_note_map m = true ->
    wf_note_map (alist_set label bs m) = true.
Proof.
  intros label bs m Hbs. induction m as [|[label' bs'] rest IH]; intros Hm.
  - cbn [alist_set wf_note_map forallb snd]. rewrite Hbs. reflexivity.
  - cbn [wf_note_map forallb snd] in Hm.
    apply andb_true_iff in Hm as [Hhead Hrest]. cbn [alist_set].
    destruct (String.eqb label label').
    + cbn [wf_note_map forallb snd]. rewrite Hbs, Hrest. reflexivity.
    + change (wf_blocks bs' && wf_note_map (alist_set label bs rest) = true)%bool.
      rewrite Hhead, (IH Hrest). reflexivity.
Qed.

Lemma collect_notes_block_wf :
  forall b p a m,
    wf_block b = true -> wf_note_map m = true ->
    let r := collect_notes b p a m in
    wf_note_map (fst r) = true /\
    match snd r with
    | Some n => wf_block (node_contents n) = true
    | None => True
    end.
Proof.
  intros b. induction b using block_ind2 with
      (Q := fun bs => forall m,
          wf_blocks bs = true -> wf_note_map m = true ->
          let r := collect_notes_list bs m in
          wf_note_map (fst r) = true /\ wf_blocks (snd r) = true)
      (R := fun its => forall m,
          forallb wf_blocks its = true -> wf_note_map m = true ->
          let r := collect_notes_items its m in
          wf_note_map (fst r) = true /\ forallb wf_blocks (snd r) = true)
      (D := fun its => forall m,
          forallb (fun ti => wf_inlines (fst ti) && wf_blocks (snd ti)) its
          = true -> wf_note_map m = true ->
          let r := collect_notes_def_items its m in
          wf_note_map (fst r) = true /\
          forallb (fun ti => wf_inlines (fst ti) && wf_blocks (snd ti))
            (snd r) = true)
      (K := fun its => forall m,
          forallb (fun ti => wf_blocks (snd ti)) its = true ->
          wf_note_map m = true ->
          let r := collect_notes_task_items its m in
          wf_note_map (fst r) = true /\
          forallb (fun ti => wf_blocks (snd ti)) (snd r) = true);
    intros; try (split; assumption).
  - unfold r. rewrite wf_block_quote in H. rewrite collect_notes_quote.
    destruct (collect_notes_list bs m) as [m' bs'] eqn:E.
    specialize (IHb m H H0). rewrite E in IHb. cbn [fst snd] in IHb |- *.
    destruct IHb as [Hm Hbs]. split; [exact Hm|].
    cbn [node_contents]. rewrite wf_block_quote. exact Hbs.
  - unfold r. rewrite wf_block_div in H. rewrite collect_notes_div.
    destruct (collect_notes_list bs m) as [m' bs'] eqn:E.
    specialize (IHb m H H0). rewrite E in IHb. cbn [fst snd] in IHb |- *.
    destruct IHb as [Hm Hbs]. split; [exact Hm|].
    cbn [node_contents]. rewrite wf_block_div. exact Hbs.
  - unfold r. rewrite wf_block_olist in H. apply andb_true_iff in H as [Hne Hits].
    rewrite collect_notes_olist.
    destruct (collect_notes_items items m) as [m' items'] eqn:E.
    specialize (IHb m Hits H0). rewrite E in IHb. cbn [fst snd] in IHb |- *.
    destruct IHb as [Hm Hits']. split; [exact Hm|]. cbn [node_contents].
    rewrite wf_block_olist. apply andb_true_iff. split; [|exact Hits'].
    change items' with (snd (m', items')). rewrite <- E.
    rewrite collect_notes_items_nonempty. exact Hne.
  - unfold r. rewrite wf_block_bullet in H. apply andb_true_iff in H as [Hne Hits].
    rewrite collect_notes_blist.
    destruct (collect_notes_items items m) as [m' items'] eqn:E.
    specialize (IHb m Hits H0). rewrite E in IHb. cbn [fst snd] in IHb |- *.
    destruct IHb as [Hm Hits']. split; [exact Hm|]. cbn [node_contents].
    rewrite wf_block_bullet. apply andb_true_iff. split; [|exact Hits'].
    change items' with (snd (m', items')). rewrite <- E.
    rewrite collect_notes_items_nonempty. exact Hne.
  - unfold r. rewrite wf_block_tasklist in H.
    apply andb_true_iff in H as [Hne Hits].
    rewrite collect_notes_tasklist.
    destruct (collect_notes_task_items items m) as [m' items'] eqn:E.
    specialize (IHb m Hits H0). rewrite E in IHb. cbn [fst snd] in IHb |- *.
    destruct IHb as [Hm Hits']. split; [exact Hm|]. cbn [node_contents].
    rewrite wf_block_tasklist. apply andb_true_iff. split; [|exact Hits'].
    change items' with (snd (m', items')). rewrite <- E.
    rewrite collect_notes_task_items_nonempty. exact Hne.
  - unfold r. rewrite wf_block_deflist in H.
    apply andb_true_iff in H as [Hne Hits].
    rewrite collect_notes_deflist.
    destruct (collect_notes_def_items items m) as [m' items'] eqn:E.
    specialize (IHb m Hits H0). rewrite E in IHb. cbn [fst snd] in IHb |- *.
    destruct IHb as [Hm Hits']. split; [exact Hm|]. cbn [node_contents].
    rewrite wf_block_deflist. apply andb_true_iff. split; [|exact Hits'].
    change items' with (snd (m', items')). rewrite <- E.
    rewrite collect_notes_def_items_nonempty. exact Hne.
  - unfold r. rewrite wf_block_footnote in H. apply andb_true_iff in H as [_ Hbs].
    rewrite collect_notes_foot.
    destruct (collect_notes_list bs m) as [m' bs'] eqn:E.
    specialize (IHb m Hbs H0). rewrite E in IHb. cbn [fst snd] in IHb |- *.
    destruct IHb as [Hm Hbs']. split; [|exact I].
    apply wf_note_map_set; assumption.
  - unfold r. rewrite wf_blocks_cons in H. apply andb_true_iff in H as [Hb Hrest].
    cbn [collect_notes_list].
    destruct (collect_notes b p a m) as [m1 [n|]] eqn:E1.
    + specialize (IHb p a m Hb H0). rewrite E1 in IHb.
      cbn [fst snd] in IHb. destruct IHb as [Hm1 Hn].
      destruct (collect_notes_list rest m1) as [m2 rest'] eqn:E2.
      specialize (IHb0 m1 Hrest Hm1). rewrite E2 in IHb0.
      cbn [fst snd] in IHb0 |- *. destruct IHb0 as [Hm2 Hr].
      split; [exact Hm2|]. rewrite wf_blocks_cons, Hn, Hr. reflexivity.
    + specialize (IHb p a m Hb H0). rewrite E1 in IHb.
      cbn [fst snd] in IHb. destruct IHb as [Hm1 _].
      destruct (collect_notes_list rest m1) as [m2 rest'] eqn:E2.
      specialize (IHb0 m1 Hrest Hm1). rewrite E2 in IHb0.
      cbn [fst snd] in IHb0 |- *. exact IHb0.
  - unfold r. cbn [forallb] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [collect_notes_items].
    destruct (collect_notes_list it m) as [m1 it'] eqn:E1.
    specialize (IHb m Hit H0). rewrite E1 in IHb.
    cbn [fst snd] in IHb. destruct IHb as [Hm1 Hit'].
    destruct (collect_notes_items rest m1) as [m2 rest'] eqn:E2.
    specialize (IHb0 m1 Hrest Hm1). rewrite E2 in IHb0.
    cbn [fst snd forallb] in IHb0 |- *. destruct IHb0 as [Hm2 Hrest'].
    split; [exact Hm2|]. rewrite Hit', Hrest'. reflexivity.
  - unfold r. cbn [forallb fst snd] in H. apply andb_true_iff in H as [Hit Hrest].
    apply andb_true_iff in Hit as [Hterm Hit].
    cbn [collect_notes_def_items].
    destruct (collect_notes_list it m) as [m1 it'] eqn:E1.
    specialize (IHb m Hit H0). rewrite E1 in IHb.
    cbn [fst snd] in IHb. destruct IHb as [Hm1 Hit'].
    destruct (collect_notes_def_items rest m1) as [m2 rest'] eqn:E2.
    specialize (IHb0 m1 Hrest Hm1). rewrite E2 in IHb0.
    cbn [fst snd forallb] in IHb0 |- *. destruct IHb0 as [Hm2 Hrest'].
    split; [exact Hm2|]. rewrite Hterm, Hit', Hrest'. reflexivity.
  - unfold r. cbn [forallb snd] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [collect_notes_task_items].
    destruct (collect_notes_list it m) as [m1 it'] eqn:E1.
    specialize (IHb m Hit H0). rewrite E1 in IHb.
    cbn [fst snd] in IHb. destruct IHb as [Hm1 Hit'].
    destruct (collect_notes_task_items rest m1) as [m2 rest'] eqn:E2.
    specialize (IHb0 m1 Hrest Hm1). rewrite E2 in IHb0.
    cbn [fst snd forallb] in IHb0 |- *. destruct IHb0 as [Hm2 Hrest'].
    split; [exact Hm2|]. rewrite Hit', Hrest'. reflexivity.
Qed.

Lemma collect_notes_list_wf :
  forall bs m,
    wf_blocks bs = true -> wf_note_map m = true ->
    wf_note_map (fst (collect_notes_list bs m)) = true /\
    wf_blocks (snd (collect_notes_list bs m)) = true.
Proof.
  induction bs as [|[p a b] rest IH]; intros m Hbs Hm.
  - split; assumption.
  - rewrite wf_blocks_cons in Hbs. apply andb_true_iff in Hbs as [Hb Hrest].
    cbn [collect_notes_list].
    destruct (collect_notes b p a m) as [m1 [n|]] eqn:E1.
    + pose proof (collect_notes_block_wf b p a m Hb Hm) as Hhead.
      rewrite E1 in Hhead. cbn [fst snd] in Hhead.
      destruct Hhead as [Hm1 Hn].
      destruct (collect_notes_list rest m1) as [m2 rest'] eqn:E2.
      specialize (IH m1 Hrest Hm1). cbn [fst snd] in IH |- *.
      destruct IH as [Hm2 Hr]. rewrite E2 in Hm2, Hr. cbn [fst snd] in Hm2, Hr.
      split; [exact Hm2|].
      rewrite wf_blocks_cons, Hn, Hr. reflexivity.
    + pose proof (collect_notes_block_wf b p a m Hb Hm) as Hhead.
      rewrite E1 in Hhead. cbn [fst snd] in Hhead.
      destruct Hhead as [Hm1 _].
      destruct (collect_notes_list rest m1) as [m2 rest'] eqn:E2.
      specialize (IH m1 Hrest Hm1). destruct IH as [Hm2 Hr].
      rewrite E2 in Hm2, Hr. cbn [fst snd] in Hm2, Hr |- *.
      split; assumption.
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
  destruct (assign_ids_list bs id_state_init) as [st bs'] eqn:E.
  assert (Hbs' : wf_blocks bs' = true).
  { change bs' with (snd (st, bs')). rewrite <- E.
    apply assign_ids_list_wf. exact H. }
  destruct (collect_notes_list bs' []) as [notes visible] eqn:En.
  pose proof (collect_notes_list_wf bs' [] Hbs' eq_refl) as Hcollect.
  cbn [fst snd] in Hcollect.
  destruct Hcollect as [Hnotes Hvisible].
  rewrite En in Hnotes, Hvisible. cbn [fst snd] in Hnotes, Hvisible.
  cbn [doc_blocks doc_footnotes]. apply andb_true_iff. split.
  - apply sectionize_wf. exact Hvisible.
  - change (wf_note_map notes = true). exact Hnotes.
Qed.

(** The parser cannot produce a malformed document. *)
Theorem wf_parse_doc : forall s, wf_doc (parse_doc s) = true.
Proof. intros s. apply wf_doc_pass, wf_parse. Qed.

End WithTable.
