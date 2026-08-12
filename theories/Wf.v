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

Lemma wf_list_block :
  forall ls last,
    wf_block (node_contents (list_block ls last))
    = (nonempty (rev (last :: ls_items ls))
       && forallb wf_blocks (rev (last :: ls_items ls)))%bool.
Proof.
  intros ls last. unfold list_block.
  destruct (ls_styles ls) as [|[[c|n d] st] ss];
    cbn [node_contents mk];
    solve [ apply wf_block_bullet | apply wf_block_olist ].
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

Definition hd_str (out : inlines) : bool :=
  match out with n :: _ => plain_str n | [] => false end.

Definition ilist_ok (out : inlines) : bool :=
  (forallb (fun n => wf_inline (node_contents n)) out
   && no_adjacent_str (List.rev out))%bool.

Lemma ilist_ok_push :
  forall n out,
    ilist_ok out = true ->
    wf_inline (node_contents n) = true ->
    (plain_str n && hd_str out)%bool = false ->
    ilist_ok (n :: out) = true.
Proof.
  intros n out H Hn Hc. unfold ilist_ok in *.
  apply andb_true_iff in H as [Hall Hadj].
  apply andb_true_iff. split; [cbn [forallb]; rewrite Hn, Hall; reflexivity|].
  cbn [List.rev]. destruct out as [|m out'].
  - reflexivity.
  - cbn [List.rev] in Hadj |- *. rewrite <- app_assoc. cbn [app].
    apply no_adjacent_str_app2; [exact Hadj|].
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
Proof. intros [|[? [|? ?] ?] ?]; reflexivity. Qed.

Lemma ilist_ok_osnoc :
  forall n out,
    ilist_ok out = true ->
    wf_inline (node_contents n) = true ->
    ilist_ok (osnoc n out) = true.
Proof.
  intros n out Ho Hn. destruct (plain_str n) eqn:Hpn.
  - (* n is a plain `Str`: the head of `out` decides whether they merge *)
    destruct n as [c [|q qs] j]; [|discriminate].
    destruct j; try discriminate.
    destruct out as [|[a [|p ps] i] out'];
      [unfold osnoc; apply ilist_ok_push;
        [exact Ho | exact Hn | reflexivity] | |].
    2: { unfold osnoc. apply ilist_ok_push;
           [exact Ho | exact Hn | reflexivity]. }
    destruct i;
      try (unfold osnoc; apply ilist_ok_push;
           [exact Ho | exact Hn | reflexivity]).
    (* the one merging case: two plain `Str` nodes become one *)
    unfold osnoc, ilist_ok in *. cbn [node_contents wf_inline] in Hn.
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
  - (* n is not a plain `Str`: no merge, and nothing to check *)
    replace (osnoc n out) with (n :: out)%list;
      [apply ilist_ok_push;
        [exact Ho | exact Hn | rewrite Hpn; reflexivity]|].
    destruct out as [|[a [|p ps] i] out']; try reflexivity.
    destruct i; try reflexivity.
    destruct n as [c [|q qs] j]; [|reflexivity].
    destruct j; try reflexivity. discriminate.
Qed.

Lemma hd_str_oapp :
  forall cur out, nonempty cur = true -> hd_str (oapp cur out) = hd_str cur.
Proof.
  intros [|n [|m cur']] out H; [discriminate| |rewrite oapp_cons2; reflexivity].
  rewrite oapp_one. destruct out as [|[a [|p ps] i] out'];
    try (unfold osnoc; destruct n as [c d j]; reflexivity).
  unfold osnoc. destruct i;
    try (destruct n as [c d j]; reflexivity).
  destruct n as [c [|q qs] j]; [|reflexivity].
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
      exact (no_adjacent_str_app2_l _ _ _ Hadj). }
    rewrite oapp_cons2.
    apply ilist_ok_push; [apply IH; assumption | exact Hn |].
    rewrite (hd_str_oapp (m :: cur') out eq_refl). cbn [hd_str].
    rewrite andb_comm. exact (no_adjacent_str_app2_pair _ _ _ Hadj).
Qed.

Definition frames_ok (stk : list frame) : bool :=
  forallb (fun f => ilist_ok (fr_out f)) stk.

Definition oscope_ok (o : ostate) : bool :=
  (ilist_ok (os_out o) && frames_ok (os_stk o))%bool.

(* The scope emissions land in: the innermost open one, or the bottom. *)
Definition ocur (o : ostate) : inlines :=
  match os_stk o with [] => os_out o | f :: _ => fr_out f end.

Definition iscan_wf (st : iscan) : bool :=
  match st with
  | IText _ _ _ o | IBrace _ _ o | IDelim _ _ _ o =>
      (oscope_ok o && negb (hd_str (ocur o)))%bool
  | IOpen _ o => oscope_ok o
  | IVerb _ _ _ o => oscope_ok o
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
  forall k ns, nonempty ns = true -> ilist_ok (List.rev ns) = true ->
  wf_inline (dnode k ns) = true.
Proof.
  intros k ns Hne Hok. unfold ilist_ok in Hok.
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

(*
The scope operations preserve it
--------------------------------
*)

Lemma ocur_emit : forall n o, ocur (oemit n o) = (n :: ocur o)%list.
Proof. intros n [out [|f stk]]; reflexivity. Qed.

Lemma oscope_ok_emit :
  forall n o,
    oscope_ok o = true ->
    wf_inline (node_contents n) = true ->
    (plain_str n && starts_str (ocur o))%bool = false ->
    oscope_ok (oemit n o) = true.
Proof.
  intros n [out [|f stk]] Ho Hn Hc; unfold oscope_ok, oemit, ocur in *;
    cbn [os_out os_stk frames_ok forallb fr_out fr_style fr_marked] in *.
  - apply andb_true_iff in Ho as [Ho _]. rewrite andb_true_r.
    apply ilist_ok_push; [exact Ho | exact Hn |].
    rewrite hd_str_is_starts_str. exact Hc.
  - apply andb_true_iff in Ho as [Hb Hf].
    apply andb_true_iff in Hf as [Hff Hf].
    rewrite Hb, Hf, !andb_true_r.
    apply ilist_ok_push; [exact Hff | exact Hn |].
    rewrite hd_str_is_starts_str. exact Hc.
Qed.

Lemma oscope_ok_push :
  forall k m o, oscope_ok o = true -> oscope_ok (opush k m o) = true.
Proof.
  intros k m [out stk] H. unfold oscope_ok, opush in *;
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
   nonempty by construction, so it is well-formed. *)
Lemma ilist_ok_src : forall f, ilist_ok [mk (Str (fr_src f))] = true.
Proof.
  intros [k [|] out]; reflexivity.
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
  destruct (dmatch k m f && nonempty (oapp pend (fr_out f)))%bool eqn:Em.
  - injection E as <- <-. rewrite (frames_ok_tail f stk Hs), andb_true_r.
    apply ilist_ok_oapp; [exact Hp | exact (frames_ok_head f stk Hs)].
  - apply (IH k m (oapp (oapp pend (fr_out f)) [mk (Str (fr_src f))])
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
  destruct (dmatch k m f && nonempty (oapp pend (fr_out f)))%bool eqn:Em.
  - injection E as <- <-. apply andb_true_iff in Em as [_ Em]. exact Em.
  - exact (IH k m (oapp (oapp pend (fr_out f)) [mk (Str (fr_src f))])
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
  assert (Hnode : wf_inline (node_contents (mk (dnode k (List.rev content))))
                  = true).
  { cbn [node_contents mk]. apply wf_inline_dnode.
    - rewrite nonempty_rev.
      exact (oclose_go_nonempty (os_stk o) k m [] content rest Eg).
    - rewrite List.rev_involutive. exact Hc. }
  rewrite ocur_emit.
  assert (Hplain : plain_str (mk (dnode k (List.rev content))) = false)
    by (destruct k; reflexivity).
  assert (Hstart : starts_str (mk (dnode k (List.rev content))
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

Lemma ilead_wf :
  forall c txt prev o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (ilead c txt prev o) = true.
Proof.
  intros c txt prev o Ho Hs. unfold ilead.
  destruct (is_bslash c); [apply (iscan_wf_text true txt prev o Ho Hs)|].
  destruct (is_tick c);
    [cbn [iscan_wf]; apply (iscan_wf_flush txt o Ho Hs)|].
  destruct (Ascii.eqb c lbrace);
    [cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity|].
  destruct (dstyle_of c);
    cbn [iscan_wf]; rewrite Ho, hd_str_is_starts_str, Hs; reflexivity.
Qed.

Lemma idelim_done_wf :
  forall k txt marker next o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (idelim_done k txt marker next o) = true.
Proof.
  intros k txt marker next o Ho Hs. unfold idelim_done.
  destruct (dbare k && negb marker && nonspace_at next)%bool;
    [|apply iscan_wf_text; assumption].
  pose proof (iscan_wf_flush txt o Ho Hs) as Hf.
  apply iscan_wf_text; [apply oscope_ok_push, Hf | reflexivity].
Qed.

Lemma idelim_resolve_wf :
  forall k txt cc marker next o,
    oscope_ok o = true -> starts_str (ocur o) = false ->
    iscan_wf (idelim_resolve k txt cc marker next o) = true.
Proof.
  intros k txt cc marker next o Ho Hs. unfold idelim_resolve.
  destruct (cc || marker)%bool; [|apply idelim_done_wf; assumption].
  pose proof (iscan_wf_flush txt o Ho Hs) as Hf.
  destruct (oclose k marker (flush_text txt o)) as [o'|] eqn:Ec;
    [|apply idelim_done_wf; assumption].
  pose proof (oclose_ok k marker _ o' Hf Ec) as Hc.
  apply andb_true_iff in Hc as [Hc1 Hc2]. apply negb_true_iff in Hc2.
  apply iscan_wf_text; assumption.
Qed.

Lemma iscan_wf_step :
  forall c st, iscan_wf st = true -> iscan_wf (istep c st) = true.
Proof.
  intros c [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o] H;
    cbn [istep];
    try (cbn [iscan_wf] in H; apply andb_true_iff in H as [Ho Hs];
         apply negb_true_iff in Hs;
         rewrite hd_str_is_starts_str in Hs).
  - apply (iscan_wf_text false _ prev o Ho Hs).
  - apply ilead_wf; [exact Ho | exact Hs].
  - unfold ibrace_step.
    destruct (dstyle_of c); [|apply ilead_wf; assumption].
    pose proof (iscan_wf_flush txt o Ho Hs) as Hf.
    apply (iscan_wf_text false EmptyString (Some (dchar d))
             (opush d true (flush_text txt o)));
      [apply oscope_ok_push, Hf | reflexivity].
  - destruct (Ascii.eqb c rbrace); [apply idelim_resolve_wf; assumption|].
    pose proof (idelim_resolve_wf k txt cc false (Some c) o Ho Hs) as Hr.
    destruct (idelim_resolve k txt cc false (Some c) o)
      as [[] txt' prev' o'|? ? ?|? ? ? ?|? ?|? ? ? ?]; try exact Hr.
    cbn [iscan_wf] in Hr. apply andb_true_iff in Hr as [Ho' Hs'].
    apply negb_true_iff in Hs'. rewrite hd_str_is_starts_str in Hs'.
    apply ilead_wf; assumption.
  - cbn [iscan_wf] in H |- *. destruct (is_tick c); exact H.
  - cbn [iscan_wf] in H |- *. destruct (is_tick c); [exact H|].
    destruct (Nat.eqb run n); [|exact H].
    apply ilead_wf.
    + apply oscope_ok_emit; [exact H | reflexivity | apply andb_false_l].
    + rewrite ocur_emit. reflexivity.
Qed.

Lemma iscan_wf_str :
  forall s st, iscan_wf st = true -> iscan_wf (iscan_str s st) = true.
Proof.
  induction s as [|c rest IH]; intros st H; [exact H|].
  cbn [iscan_str]. apply IH, iscan_wf_step, H.
Qed.

Lemma wf_inlines_of_ilist :
  forall out, ilist_ok out = true -> wf_inlines (List.rev out) = true.
Proof.
  intros out H. unfold ilist_ok in H. unfold wf_inlines.
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

Lemma ilist_ok_ofinish :
  forall o, oscope_ok o = true -> ilist_ok (ofinish o) = true.
Proof.
  intros o H. apply andb_true_iff in H as [Hb Hs].
  unfold ofinish. apply ilist_ok_oflatten; [exact Hs | reflexivity | exact Hb].
Qed.

Lemma iscan_wf_resolve :
  forall st, iscan_wf st = true -> iscan_wf (iresolve st) = true.
Proof.
  intros [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o] H;
    cbn [iresolve]; try exact H;
    cbn [iscan_wf] in H; apply andb_true_iff in H as [Ho Hs];
    apply negb_true_iff in Hs; rewrite hd_str_is_starts_str in Hs.
  (* `IBrace` is closed by `exact H` above: the invariant does not look
     at the text buffer, and resolving a brace only moves a byte into
     it.  `IDelim` is the one that can close a scope. *)
  apply idelim_resolve_wf; assumption.
Qed.

Lemma iscan_wf_ostate :
  forall st, iscan_wf st = true -> oscope_ok (ifinish_ostate st) = true.
Proof.
  intros st H. pose proof (iscan_wf_resolve st H) as Hr.
  pose proof (iresolve_resolved st) as Hno.
  unfold ifinish_ostate.
  destruct (iresolve st) as
    [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o];
    try contradiction;
    try (cbn [iscan_wf] in Hr; apply andb_true_iff in Hr as [Ho Hs];
         apply negb_true_iff in Hs; rewrite hd_str_is_starts_str in Hs).
  - apply iscan_wf_flush; assumption.
  - apply iscan_wf_flush; assumption.
  - cbn [iscan_wf] in Hr.
    apply oscope_ok_emit; [exact Hr | reflexivity | apply andb_false_l].
  - cbn [iscan_wf] in Hr.
    apply oscope_ok_emit; [exact Hr | reflexivity | apply andb_false_l].
Qed.

Lemma iscan_wf_finish_rev :
  forall st, iscan_wf st = true -> ilist_ok (ifinish_rev st) = true.
Proof.
  intros st H. unfold ifinish_rev.
  apply ilist_ok_ofinish, iscan_wf_ostate, H.
Qed.

Lemma iscan_wf_finish :
  forall st, iscan_wf st = true -> wf_inlines (ifinish st) = true.
Proof.
  intros st H. unfold ifinish.
  apply wf_inlines_of_ilist, iscan_wf_finish_rev, H.
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
    [[] txt prev o|txt prev o|k txt cc o|n o|n run txt o];
    try contradiction;
    try (cbn [iscan_wf] in Hr; apply andb_true_iff in Hr as [Ho Hs];
         apply negb_true_iff in Hs; rewrite hd_str_is_starts_str in Hs).
  1,2: apply (iscan_wf_text false EmptyString None);
         [ apply oscope_ok_emit;
           [ apply iscan_wf_flush; assumption
           | reflexivity | apply andb_false_l ]
         | rewrite ocur_emit; reflexivity ].
  - cbn [iscan_wf] in Hr |- *. exact Hr.
  - cbn [iscan_wf] in Hr. destruct (Nat.eqb run n); [|exact Hr].
    apply (iscan_wf_text false EmptyString None).
    + apply oscope_ok_emit;
        [apply oscope_ok_emit; [exact Hr | reflexivity | apply andb_false_l]
        |reflexivity | apply andb_false_l].
    + rewrite ocur_emit. reflexivity.
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
  | PFence _ _ => true
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
  (* Pending attributes add nothing of their own. *)
  | PPend _ inner => state_wf inner
  end.

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
  induction st as [cur|lvl hcur|f acc|done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|ppend pinner IH];
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
    cbn [finish]. rewrite wf_blocks_cons.
    rewrite wf_list_block, andb_true_r.
    rewrite nonempty_rev, forallb_rev. cbn [nonempty forallb].
    rewrite wf_blocks_app, wf_blocks_rev, Hd, (IH Hi), Hitems.
    reflexivity.
  - (* an attribute spec: a finished one contributes nothing, an
       unfinished one the paragraph of the lines it ate *)
    cbn [state_wf] in H. cbn [finish].
    destruct (ap_done aap); [reflexivity|].
    destruct aslices as [|c cur']; [reflexivity|].
    apply (flush_para_wf c cur' [] H eq_refl).
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
  induction st as [cur|lvl hcur|f acc|done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|ppend pinner IH];
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
  intros l k H. destruct k; cbn [close_reopen open_quote finish app open_kind open_attr fst snd]; try (split; reflexivity).
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
  forall ind m bs inner,
    wf_blocks bs = true -> state_wf inner = true ->
    wf_blocks (fst (open_list ind m (bs, inner))) = true
    /\ state_wf (snd (open_list ind m (bs, inner))) = true.
Proof.
  intros ind m bs inner Hb Hi.
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

Lemma step_fuel_wf :
  forall n off l st,
    state_wf st = true ->
    wf_blocks (fst (step_fuel n off l st)) = true
    /\ state_wf (snd (step_fuel n off l st)) = true.
Proof.
  induction n as [|n IH]; intros off l st H; [split; [reflexivity | exact H]|].
  cbn [step_fuel].
  destruct st as [cur|hlvl hcur|f acc|done inner|dlen dcls ddone dinner|ls done inner|apend aind aap aslices|ppend pinner].
  - (* idle, or an open paragraph *)
    destruct cur as [|c cur'].
    + destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc mr|kap|] eqn:E;
        try (apply open_kind_wf; exact E).
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
    + destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc mr|kap|] eqn:E; cbn [fst snd].
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
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc mr|kap|] eqn:E.
    7: { (* list marker: close the heading, then open the list *)
      destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner].
      destruct (open_list_wf (off + indent_of l) (with_starts m mc) bs inner Hb Hs) as [Hob Hos].
      destruct (open_list (off + indent_of l) (with_starts m mc) (bs, inner)) as [obs ost].
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
    5: { (* lazy text *)
      cbn [fst snd]. split; [reflexivity|].
      cbn [state_wf]. rewrite Hlv. cbn [andb].
      rewrite forallb_nonblank_cons
        by (rewrite is_blank_drop_leading_ws;
            apply classify_ktext_nonblank; exact E).
      exact Hc. }
    (* blank, thematic, fence: close the heading and reopen outside it *)
    all: cbn [close_reopen open_quote finish app open_kind open_attr fst snd]; split;
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
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc mr|kap|] eqn:E.
    7: { (* a list marker closes the quote and opens a list outside it *)
      destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
      destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner'].
      destruct (open_list_wf (off + indent_of l) (with_starts m mc) bs inner' Hb Hs) as [Hob Hos].
      destruct (open_list (off + indent_of l) (with_starts m mc) (bs, inner')) as [obs ost].
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
    6: { (* text without the prefix: lazy continuation, or close *)
      cbn [is_lazy]. destruct (lazy_ok inner) eqn:El; cbn [close_reopen open_quote finish app open_kind open_attr fst snd].
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
    (* every other kind closes the quote and reopens outside it, on
       exactly the transition open_kind_wf already describes *)
    all: destruct (open_kind_wf l _ E) as [Hob Hos];
         cbn [is_lazy];
         destruct (open_kind l _) as [obs ost] eqn:Eo;
         cbn [close_reopen open_quote finish app fst snd] in Hob, Hos |- *;
         split;
         [ rewrite wf_blocks_cons; cbn [node_contents mk]; rewrite Hbq;
           cbn [andb]; exact Hob
         | exact Hos ].
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
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc mr|kap|] eqn:E.
    7: { (* a bullet marker *)
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - (* indented past the marker: contents of the current item *)
        destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        cbn [state_wf ls_items list_content].
        rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd. exact Hs.
      - destruct (narrow (ls_styles ls) m).
        + (* no style survives: close this list, open another *)
          destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
          destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner'].
          destruct (open_list_wf (off + indent_of l) (with_starts m mc) bs inner' Hb Hs) as [Hob Hos].
          destruct (open_list (off + indent_of l) (with_starts m mc) (bs, inner')) as [obs ost].
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
      destruct (list_open inner); cbn [ls_items list_blank];
        rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs. }
    6: { (* attribute spec: item contents when indented, else close *)
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        cbn [state_wf ls_items list_content].
        rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd. exact Hs.
      - destruct (open_attr_wf [] (off + indent_of l) kap l
                    (classify_kattr_nonblank l kap E)) as [Hob Hos].
        split; [|exact Hos].
        cbn [close_reopen open_attr fst snd]. rewrite app_nil_r.
        apply finish_wf. exact H. }
    6: { (* text: lazy continuation into the item, or close the list *)
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - destruct (IH off l inner Hi) as [Hb Hs].
        destruct (step_fuel n off l inner) as [bs inner'].
        cbn [fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        cbn [state_wf ls_items list_content].
        rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd. exact Hs.
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
        cbn [state_wf ls_items list_content].
        rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd. exact Hs.
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
           cbn [state_wf ls_items list_content];
           rewrite Hitems, wf_blocks_app, wf_blocks_rev, Hb, Hd; exact Hs
         | cbn [is_lazy];
           destruct (open_kind_wf l _ E) as [Hob Hos];
           destruct (open_kind l _) as [obs ost] eqn:Eo;
           cbn [close_reopen fst snd] in Hob, Hos |- *;
           split;
           [ rewrite wf_blocks_app, Hob, andb_true_r; apply finish_wf; exact H
           | exact Hos ] ].
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
  let sup_items :=
    fix goi (its : list (list (node block))) : bool :=
      match its with
      | [] => true
      | it :: rest => sup_bs it && goi rest
      end in
  match b with
  | Para _ | ThematicBreak | CodeBlock _ _ | RawBlock _ _ | Heading _ _ => true
  | BlockQuote bs | Div bs => sup_bs bs
  | BulletList _ items => sup_items items
  | OrderedList _ _ items => sup_items items
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

(* As `wf_list_block`: `supported` cannot tell the two list flavours
   apart either, so `finish_supported` stays one case. *)
Lemma supported_list_block :
  forall ls last,
    supported (node_contents (list_block ls last))
    = forallb supported_blocks (rev (last :: ls_items ls)).
Proof.
  intros ls last. unfold list_block.
  destruct (ls_styles ls) as [|[[c|n d] st] ss];
    cbn [node_contents mk];
    solve [ apply supported_bullet | apply supported_olist ].
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
  | PPara _ | PHeading _ _ | PFence _ _ => true
  | PQuote done inner => supported_blocks done && state_supported inner
  | PDiv _ _ done inner => supported_blocks done && state_supported inner
  | PList ls done inner =>
      forallb supported_blocks (ls_items ls) && supported_blocks done
      && state_supported inner
  (* A spec emits at most a paragraph, and pending attributes emit
     nothing of their own. *)
  | PAttr _ _ _ _ => true
  | PPend _ inner => state_supported inner
  end.

Lemma supported_blocks_decorate_head :
  forall a bs, supported_blocks (decorate_head a bs) = supported_blocks bs.
Proof. intros a bs. destruct bs as [|[q a' x] rest]; reflexivity. Qed.

Lemma finish_supported :
  forall st, state_supported st = true -> supported_blocks (finish st) = true.
Proof.
  induction st as [cur|lvl hcur|f acc|done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|ppend pinner IH];
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
  - cbn [state_supported] in H. cbn [finish].
    rewrite supported_blocks_decorate_head. exact (IH H).
Qed.

Lemma feed_lazy_supported :
  forall l st,
    state_supported st = true -> state_supported (feed_lazy l st) = true.
Proof.
  induction st as [cur|lvl hcur|f acc|done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|ppend pinner IH];
    intros H; [reflexivity | reflexivity | reflexivity | | | | reflexivity |].
  4: { cbn [feed_lazy state_supported] in *. exact (IH H). }
  - cbn [feed_lazy state_supported] in *.
    apply andb_true_iff in H as [Hd Hi]. rewrite Hd, (IH Hi). reflexivity.
  - cbn [feed_lazy state_supported] in *.
    apply andb_true_iff in H as [Hd Hi]. rewrite Hd, (IH Hi). reflexivity.
  - cbn [feed_lazy state_supported] in *.
    apply andb_true_iff in H as [H1 Hi]. apply andb_true_iff in H1 as [Ht Hd].
    rewrite Ht, Hd, (IH Hi). reflexivity.
Qed.

Lemma open_list_supported :
  forall ind m bs inner,
    supported_blocks bs = true -> state_supported inner = true ->
    supported_blocks (fst (open_list ind m (bs, inner))) = true
    /\ state_supported (snd (open_list ind m (bs, inner))) = true.
Proof.
  intros ind m bs inner Hb Hi.
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
  destruct st as [cur|hlvl hcur|f acc|done inner|dlen dcls ddone dinner|ls done inner|apend aind aap aslices|ppend pinner].
  - destruct cur as [|c cur'].
    + destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc mr|kap|] eqn:E;
        try (cbn [close_reopen open_quote finish app open_kind open_attr fst snd]; split; reflexivity).
      * destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner].
        cbn [close_reopen open_quote finish app fst snd] in Hb, Hs |- *.
        split; [reflexivity|].
        cbn [state_supported]. rewrite supported_blocks_rev, Hb. exact Hs.
      * destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
        destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner].
        apply open_list_supported; assumption.
    + destruct (classify l); cbn [fst snd]; split; reflexivity.
  - (* an open heading: Heading is supported, so only the quote branch
       carries anything to prove *)
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc mr|kap|] eqn:E.
    7: { destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
         destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner].
         destruct (open_list_supported (off + indent_of l) (with_starts m mc) bs inner Hb Hs)
           as [Hob Hos].
         destruct (open_list (off + indent_of l) (with_starts m mc) (bs, inner)) as [obs ost].
         cbn [close_reopen finish app fst snd] in Hob, Hos |- *.
         rewrite supported_blocks_cons. cbn [node_contents].
         rewrite Hob. split; [reflexivity | exact Hos]. }
    5: { destruct (IH (off + consumed l rest) rest (PPara []) eq_refl) as [Hb Hs].
         destruct (step_fuel n (off + consumed l rest) rest (PPara [])) as [bs inner].
         cbn [close_reopen open_quote finish app fst snd] in Hb, Hs |- *.
         split; [reflexivity|].
         cbn [state_supported]. rewrite supported_blocks_rev, Hb. exact Hs. }
    5: { destruct (Nat.eqb kl hlvl); cbn [fst snd]; split; reflexivity. }
    all: cbn [close_reopen open_quote finish app open_kind open_attr fst snd]; split; reflexivity.
  - destruct (fence_close f l); cbn [fst snd].
    + rewrite supported_blocks_cons, fence_block_supported. split; reflexivity.
    + split; reflexivity.
  - pose proof H as H0. cbn [state_supported] in H0.
    apply andb_true_iff in H0 as [Hd Hi].
    assert (Hbq : supported (BlockQuote (rev done ++ finish inner)%list) = true).
    { rewrite supported_quote, supported_blocks_app, supported_blocks_rev, Hd,
        (finish_supported _ Hi).
      reflexivity. }
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc mr|kap|] eqn:E.
    7: { destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
         destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner'].
         destruct (open_list_supported (off + indent_of l) (with_starts m mc) bs inner' Hb Hs)
           as [Hob Hos].
         destruct (open_list (off + indent_of l) (with_starts m mc) (bs, inner')) as [obs ost].
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
    7: { cbn [is_lazy]. destruct (lazy_ok inner); cbn [close_reopen open_quote finish app open_kind open_attr fst snd].
         - split; [reflexivity|].
           cbn [state_supported]. rewrite Hd. cbn [andb].
           apply feed_lazy_supported. exact Hi.
         - split; [| reflexivity].
           rewrite supported_blocks_cons. cbn [node_contents mk].
           rewrite Hbq. cbn [andb]. reflexivity. }
    all: cbn [is_lazy close_reopen open_quote finish app open_kind open_attr fst snd]; split;
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
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc mr|kap|] eqn:E.
    7: { destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *.
           split; [reflexivity|].
           cbn [state_supported ls_items list_content].
           rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd.
           exact Hs.
         - destruct (narrow (ls_styles ls) m).
           + destruct (IH (off + consumed l mr) mr (PPara []) eq_refl) as [Hb Hs].
             destruct (step_fuel n (off + consumed l mr) mr (PPara [])) as [bs inner'].
             destruct (open_list_supported (off + indent_of l) (with_starts m mc) bs inner' Hb Hs)
               as [Hob Hos].
             destruct (open_list (off + indent_of l) (with_starts m mc) (bs, inner')) as [obs ost].
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
         destruct (list_open inner); cbn [ls_items list_blank];
           rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
           exact Hs. }
    7: { destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *.
           split; [reflexivity|].
           cbn [state_supported ls_items list_content].
           rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd.
           exact Hs.
         - cbn [is_lazy]. destruct (lazy_ok inner); cbn [fst snd].
           + split; [reflexivity|].
             cbn [state_supported]. rewrite Hitems, Hd. cbn [andb].
             apply feed_lazy_supported. exact Hi.
           + cbn [close_reopen open_kind open_attr fst snd]. split; [|reflexivity].
             rewrite supported_blocks_app, (finish_supported _ H).
             reflexivity. }
    4: { destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
         - destruct (IH off l inner Hi) as [Hb Hs].
           destruct (step_fuel n off l inner) as [bs inner'].
           cbn [fst snd] in Hb, Hs |- *.
           split; [reflexivity|].
           cbn [state_supported ls_items list_content].
           rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd.
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
           cbn [state_supported ls_items list_content];
           rewrite Hitems, supported_blocks_app, supported_blocks_rev, Hb, Hd;
           exact Hs
         | cbn [is_lazy close_reopen open_kind open_attr fst snd];
           split; [|reflexivity];
           rewrite supported_blocks_app, (finish_supported _ H);
           reflexivity ].
  - (* an attribute spec emits nothing until it resolves *)
    destruct (ap_done aap); [apply IH; reflexivity|].
    destruct (Nat.ltb aind (off + indent_of l));
      [destruct (ap_failed (attr_feed l aap))|];
      [apply IH; reflexivity | split; reflexivity | apply IH; reflexivity].
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
            forallb wf_blocks (snd (assign_ids_items its st)) = true);
    intros; try exact H.
  (* Section and the remaining list/table constructors are unreachable
     from the line fold, but the lemma is stated for every block, so they
     are discharged by the identity branch of assign_ids above. *)
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
  cbn [doc_blocks doc_footnotes]. rewrite andb_true_r.
  apply sectionize_wf.
  change bs' with (snd (st, bs')). rewrite <- E.
  apply assign_ids_list_wf. exact H.
Qed.

(** The parser cannot produce a malformed document. *)
Theorem wf_parse_doc : forall s, wf_doc (parse_doc s) = true.
Proof. intros s. apply wf_doc_pass, wf_parse. Qed.
