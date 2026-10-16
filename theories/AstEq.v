(* ai-disclosure: autonomous *)

(** * Equality of trees, decided

   `blocks_eqb` decides equality of block trees, positions and attributes
   included (`blocks_eqb_eq`).  `Scheme Equality` stops at the nested
   lists, so each type has its test written here. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Setoid.
From DjotV Require Import Ast.
Import ListNotations.

Local Open Scope bool_scope.

(* A test decides equality. *)
Notation eqb_spec f := (forall x y, f x y = true <-> x = y).

(* The constructor cases once the tests are rewritten to equalities:
   equal fields on the left, equal trees on the right. *)
Local Ltac ctor_iff :=
  split;
  [ intros; repeat match goal with H : _ /\ _ |- _ => destruct H end;
    subst; reflexivity
  | intros H; injection H; intros; subst; repeat split ].

Local Ltac mismatch := split; [discriminate | intros H; discriminate H].

(*
Lists, pairs and nodes
======================
*)

Fixpoint list_eqb {A : Type} (f : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => f x y && list_eqb f xs' ys'
  | _, _ => false
  end.

Lemma list_eqb_nil : forall {A} (f : A -> A -> bool) ys,
  list_eqb f [] ys = true <-> [] = ys.
Proof. intros A f [|y ys]; cbn; [tauto | mismatch]. Qed.

Lemma list_eqb_cons : forall {A} (f : A -> A -> bool) x xs,
  (forall y, f x y = true <-> x = y) ->
  (forall ys, list_eqb f xs ys = true <-> xs = ys) ->
  forall ys, list_eqb f (x :: xs) ys = true <-> x :: xs = ys.
Proof.
  intros A f x xs Hx Hxs [|y ys]; cbn; [mismatch|].
  rewrite andb_true_iff, Hx, Hxs. ctor_iff.
Qed.

Lemma list_eqb_spec : forall {A} (f : A -> A -> bool),
  eqb_spec f -> eqb_spec (list_eqb f).
Proof.
  intros A f Hf xs. induction xs as [|x xs IH].
  - apply list_eqb_nil.
  - apply list_eqb_cons; [apply Hf | exact IH].
Qed.

Definition pair_eqb {A B : Type} (f : A -> A -> bool) (g : B -> B -> bool)
  (p q : A * B) : bool :=
  let '(a, b) := p in let '(c, d) := q in f a c && g b d.

Lemma pair_eqb_spec : forall {A B} (f : A -> A -> bool) (g : B -> B -> bool),
  eqb_spec f -> eqb_spec g -> eqb_spec (pair_eqb f g).
Proof.
  intros A B f g Hf Hg [a b] [c d]; cbn.
  rewrite andb_true_iff, Hf, Hg. ctor_iff.
Qed.

Definition option_eqb {A : Type} (f : A -> A -> bool) (x y : option A) : bool :=
  match x, y with
  | Some a, Some b => f a b
  | None, None => true
  | _, _ => false
  end.

Lemma option_eqb_spec : forall {A} (f : A -> A -> bool),
  eqb_spec f -> eqb_spec (option_eqb f).
Proof.
  intros A f Hf [a|] [b|]; cbn; try mismatch; [rewrite Hf; ctor_iff | tauto].
Qed.

(*
Positions and attributes
========================
*)

Definition spot_eqb (p q : spot) : bool :=
  Nat.eqb (spot_line p) (spot_line q) && Nat.eqb (spot_rem p) (spot_rem q).

Lemma spot_eqb_spec : eqb_spec spot_eqb.
Proof.
  intros [a b] [c d]; unfold spot_eqb; cbn.
  rewrite andb_true_iff, !Nat.eqb_eq. ctor_iff.
Qed.

Definition span_eqb (r t : span) : bool :=
  spot_eqb (span_start r) (span_start t) && spot_eqb (span_stop r) (span_stop t).

Lemma span_eqb_spec : eqb_spec span_eqb.
Proof.
  intros [a b] [c d]; unfold span_eqb; cbn.
  rewrite andb_true_iff, !spot_eqb_spec. ctor_iff.
Qed.

Definition role_eqb (r t : syntax_role) : bool :=
  match r, t with
  | RAttrSpec, RAttrSpec | ROpenFence, ROpenFence | RCloseFence, RCloseFence => true
  | _, _ => false
  end.

Lemma role_eqb_spec : eqb_spec role_eqb.
Proof. intros [] []; cbn; (tauto || mismatch). Qed.

Definition pos_eqb (p q : pos) : bool :=
  match p, q with
  | NoPos, NoPos => true
  | SomePos (Provenance r rs), SomePos (Provenance t ts) =>
      span_eqb r t && list_eqb (pair_eqb role_eqb span_eqb) rs ts
  | _, _ => false
  end.

Lemma pos_eqb_spec : eqb_spec pos_eqb.
Proof.
  intros [|[r rs]] [|[t ts]]; cbn; try mismatch; [tauto|].
  rewrite andb_true_iff, span_eqb_spec,
    (list_eqb_spec _ (pair_eqb_spec _ _ role_eqb_spec span_eqb_spec)).
  ctor_iff.
Qed.

Definition attr_eqb : attr -> attr -> bool := list_eqb (pair_eqb String.eqb String.eqb).

Lemma attr_eqb_spec : eqb_spec attr_eqb.
Proof. apply list_eqb_spec, pair_eqb_spec; intros ? ?; apply String.eqb_eq. Qed.

Definition node_eqb {A : Type} (f : A -> A -> bool) (m n : node A) : bool :=
  match m, n with Node p a x, Node q b y => pos_eqb p q && attr_eqb a b && f x y end.

Lemma node_eqb_at : forall {A} (f : A -> A -> bool) p a x,
  (forall y, f x y = true <-> x = y) ->
  forall n, node_eqb f (Node p a x) n = true <-> Node p a x = n.
Proof.
  intros A f p a x Hx [q b y]; cbn.
  rewrite !andb_true_iff, pos_eqb_spec, attr_eqb_spec, Hx. ctor_iff.
Qed.

Lemma node_eqb_spec : forall {A} (f : A -> A -> bool),
  eqb_spec f -> eqb_spec (node_eqb f).
Proof. intros A f Hf [p a x]. apply node_eqb_at, Hf. Qed.

(*
Inlines
=======
*)

Definition math_style_eqb (x y : math_style) : bool :=
  match x, y with
  | DisplayMath, DisplayMath | InlineMath, InlineMath => true
  | _, _ => false
  end.

Lemma math_style_eqb_spec : eqb_spec math_style_eqb.
Proof. intros [] []; cbn; (tauto || mismatch). Qed.

Definition quote_type_eqb (x y : quote_type) : bool :=
  match x, y with
  | SingleQuotes, SingleQuotes | DoubleQuotes, DoubleQuotes => true
  | _, _ => false
  end.

Lemma quote_type_eqb_spec : eqb_spec quote_type_eqb.
Proof. intros [] []; cbn; (tauto || mismatch). Qed.

Definition target_eqb (x y : target) : bool :=
  match x, y with
  | Direct s, Direct t | Reference s, Reference t => String.eqb s t
  | _, _ => false
  end.

Lemma target_eqb_spec : eqb_spec target_eqb.
Proof. intros [s|s] [t|t]; cbn; try mismatch; rewrite String.eqb_eq; ctor_iff. Qed.

Fixpoint inline_eqb (x y : inline) : bool :=
  match x, y with
  | Str s, Str t | Verbatim s, Verbatim t | Symbol s, Symbol t
  | FootnoteReference s, FootnoteReference t | UrlLink s, UrlLink t
  | EmailLink s, EmailLink t | Hole s, Hole t => String.eqb s t
  | Emph a, Emph b | Strong a, Strong b | Highlight a, Highlight b
  | Insert a, Insert b | Delete a, Delete b
  | Superscript a, Superscript b | Subscript a, Subscript b =>
      list_eqb (node_eqb inline_eqb) a b
  | Math m s, Math n t => math_style_eqb m n && String.eqb s t
  | Link a u, Link b v | Image a u, Image b v =>
      list_eqb (node_eqb inline_eqb) a b && target_eqb u v
  | Span m a, Span n b => String.eqb m n && list_eqb (node_eqb inline_eqb) a b
  | RawInline f s, RawInline g t => String.eqb f g && String.eqb s t
  | Quoted q a, Quoted r b => quote_type_eqb q r && list_eqb (node_eqb inline_eqb) a b
  | NonBreakingSpace, NonBreakingSpace | SoftBreak, SoftBreak
  | HardBreak, HardBreak => true
  | Ext_wikilink e s a, Ext_wikilink f t b =>
      Bool.eqb e f && String.eqb s t && option_eqb String.eqb a b
  | _, _ => false
  end.

Definition inlines_eqb : inlines -> inlines -> bool := list_eqb (node_eqb inline_eqb).

Lemma inline_eqb_spec : eqb_spec inline_eqb.
Proof.
  intros x.
  induction x using inline_ind2 with
    (Q := fun ils => forall ys, list_eqb (node_eqb inline_eqb) ils ys = true <-> ils = ys);
    try (intros y; destruct y; cbn [inline_eqb]; try mismatch;
         rewrite ?andb_true_iff, ?String.eqb_eq, ?math_style_eqb_spec,
           ?target_eqb_spec, ?quote_type_eqb_spec, ?Bool.eqb_true_iff,
           ?(option_eqb_spec _ (fun a b => String.eqb_eq a b)), ?IHx;
         first [tauto | ctor_iff]).
  all: first [ apply list_eqb_nil
             | apply list_eqb_cons; [apply node_eqb_at; assumption | assumption] ].
Qed.

Lemma inlines_eqb_spec : eqb_spec inlines_eqb.
Proof. apply list_eqb_spec, node_eqb_spec, inline_eqb_spec. Qed.

(*
Blocks
======
*)

Definition spacing_eqb (x y : list_spacing) : bool :=
  match x, y with Tight, Tight | Loose, Loose => true | _, _ => false end.

Lemma spacing_eqb_spec : eqb_spec spacing_eqb.
Proof. intros [] []; cbn; (tauto || mismatch). Qed.

Definition ol_style_eqb (x y : ordered_list_style) : bool :=
  match x, y with
  | Decimal, Decimal | LetterUpper, LetterUpper | LetterLower, LetterLower
  | RomanUpper, RomanUpper | RomanLower, RomanLower => true
  | _, _ => false
  end.

Definition ol_delim_eqb (x y : ordered_list_delim) : bool :=
  match x, y with
  | RightPeriod, RightPeriod | RightParen, RightParen
  | LeftRightParen, LeftRightParen => true
  | _, _ => false
  end.

Lemma ol_style_eqb_spec : eqb_spec ol_style_eqb.
Proof. intros [] []; cbn; (tauto || mismatch). Qed.

Lemma ol_delim_eqb_spec : eqb_spec ol_delim_eqb.
Proof. intros [] []; cbn; (tauto || mismatch). Qed.

Definition ol_attrs_eqb (x y : ordered_list_attributes) : bool :=
  ol_style_eqb (ol_style x) (ol_style y) && ol_delim_eqb (ol_delim x) (ol_delim y)
  && Nat.eqb (ol_start x) (ol_start y).

Lemma ol_attrs_eqb_spec : eqb_spec ol_attrs_eqb.
Proof.
  intros [s d n] [t e m]; unfold ol_attrs_eqb; cbn.
  rewrite !andb_true_iff, ol_style_eqb_spec, ol_delim_eqb_spec, Nat.eqb_eq.
  ctor_iff.
Qed.

Definition task_eqb (x y : task_status) : bool :=
  match x, y with
  | Complete, Complete | Incomplete, Incomplete => true
  | _, _ => false
  end.

Lemma task_eqb_spec : eqb_spec task_eqb.
Proof. intros [] []; cbn; (tauto || mismatch). Qed.

Definition cell_type_eqb (x y : cell_type) : bool :=
  match x, y with HeadCell, HeadCell | BodyCell, BodyCell => true | _, _ => false end.

Lemma cell_type_eqb_spec : eqb_spec cell_type_eqb.
Proof. intros [] []; cbn; (tauto || mismatch). Qed.

Lemma align_eqb_spec : eqb_spec align_eqb.
Proof. intros [] []; cbn; (tauto || mismatch). Qed.

Definition cell_eqb (x y : cell) : bool :=
  match x, y with
  | Cell t a ils, Cell u b jls =>
      cell_type_eqb t u && align_eqb a b && inlines_eqb ils jls
  end.

Lemma cell_eqb_spec : eqb_spec cell_eqb.
Proof.
  intros [t a ils] [u b jls]; cbn.
  rewrite !andb_true_iff, cell_type_eqb_spec, align_eqb_spec, inlines_eqb_spec.
  ctor_iff.
Qed.

Definition fold_eqb (x y : callout_fold) : bool :=
  match x, y with
  | FoldExpanded, FoldExpanded | FoldCollapsed, FoldCollapsed => true
  | _, _ => false
  end.

Lemma fold_eqb_spec : eqb_spec fold_eqb.
Proof. intros [] []; cbn; (tauto || mismatch). Qed.

Fixpoint block_eqb (x y : block) : bool :=
  match x, y with
  | Para a, Para b => inlines_eqb a b
  | Section a, Section b | BlockQuote a, BlockQuote b =>
      list_eqb (node_eqb block_eqb) a b
  | Heading m a, Heading n b => Nat.eqb m n && inlines_eqb a b
  | CodeBlock f s, CodeBlock g t | RawBlock f s, RawBlock g t =>
      String.eqb f g && String.eqb s t
  | Div m a, Div n b | FootnoteDef m a, FootnoteDef n b =>
      String.eqb m n && list_eqb (node_eqb block_eqb) a b
  | OrderedList o s a, OrderedList p t b =>
      ol_attrs_eqb o p && spacing_eqb s t
      && list_eqb (node_eqb (list_eqb (node_eqb block_eqb))) a b
  | BulletList c s a, BulletList d t b =>
      Ascii.eqb c d && spacing_eqb s t
      && list_eqb (node_eqb (list_eqb (node_eqb block_eqb))) a b
  | TaskList s a, TaskList t b =>
      spacing_eqb s t
      && list_eqb (node_eqb (pair_eqb task_eqb (list_eqb (node_eqb block_eqb)))) a b
  | DefinitionList s a, DefinitionList t b =>
      spacing_eqb s t
      && list_eqb (node_eqb (pair_eqb (node_eqb inlines_eqb)
                                      (node_eqb (list_eqb (node_eqb block_eqb))))) a b
  | ThematicBreak, ThematicBreak | AttrBlock, AttrBlock => true
  | Table c r, Table d t =>
      node_eqb inlines_eqb c d && list_eqb (node_eqb (list_eqb (node_eqb cell_eqb))) r t
  | RefDef l s, RefDef m t => String.eqb l m && String.eqb s t
  | Ext_keyed l a, Ext_keyed m b => inlines_eqb l m && node_eqb block_eqb a b
  | Ext_callout k f t a, Ext_callout l g u b =>
      String.eqb k l
      && option_eqb fold_eqb f g
      && inlines_eqb t u && list_eqb (node_eqb block_eqb) a b
  | _, _ => false
  end.

Definition blocks_eqb : blocks -> blocks -> bool := list_eqb (node_eqb block_eqb).

Lemma block_eqb_spec : eqb_spec block_eqb.
Proof.
  intros x.
  induction x using block_ind2 with
    (Q := fun bs => forall ys, list_eqb (node_eqb block_eqb) bs ys = true <-> bs = ys)
    (R := fun its => forall ys,
       list_eqb (node_eqb (list_eqb (node_eqb block_eqb))) its ys = true <-> its = ys)
    (D := fun its => forall ys,
       list_eqb (node_eqb (pair_eqb (node_eqb inlines_eqb)
                                    (node_eqb (list_eqb (node_eqb block_eqb))))) its ys = true
       <-> its = ys)
    (K := fun its => forall ys,
       list_eqb (node_eqb (pair_eqb task_eqb (list_eqb (node_eqb block_eqb)))) its ys = true
       <-> its = ys).
  all: try (intros y; destruct y; cbn [block_eqb]; try mismatch).
  all: try (rewrite ?andb_true_iff, ?String.eqb_eq, ?Nat.eqb_eq, ?Ascii.eqb_eq,
             ?inlines_eqb_spec, ?ol_attrs_eqb_spec, ?spacing_eqb_spec,
             ?(option_eqb_spec _ fold_eqb_spec),
             ?(node_eqb_spec _ inlines_eqb_spec),
             ?(list_eqb_spec _ (node_eqb_spec _ (list_eqb_spec _ (node_eqb_spec _ cell_eqb_spec))));
           repeat match goal with H : forall _, _ <-> _ |- _ => rewrite H end;
           first [tauto | ctor_iff]).
  (* Left: a key's one block, which reaches here as a singleton list, and
     the cons cases of the four list shapes. *)
  - rewrite andb_true_iff, inlines_eqb_spec.
    specialize (IHx [b0]). cbn [list_eqb] in IHx. rewrite andb_true_r in IHx.
    rewrite IHx. split; [intros [-> E]; injection E; intros ->; reflexivity
                        | intros E; injection E; intros -> ->; split; reflexivity].
  - refine (list_eqb_cons _ _ _ (node_eqb_at _ _ _ _ IHx) IHx0 (n :: y)).
  - refine (list_eqb_cons _ _ _ (node_eqb_at _ _ _ _ IHx) IHx0 (n :: y)).
  - refine (list_eqb_cons _ _ _ (node_eqb_at _ _ _ _ _) IHx0 (n :: y)).
    intros [t m]; cbn [pair_eqb].
    rewrite andb_true_iff, (node_eqb_spec _ inlines_eqb_spec), (node_eqb_at _ _ _ _ IHx).
    ctor_iff.
  - refine (list_eqb_cons _ _ _ (node_eqb_at _ _ _ _ _) IHx0 (n :: y)).
    intros [t m]; cbn [pair_eqb].
    rewrite andb_true_iff, task_eqb_spec, IHx. ctor_iff.
Qed.

Theorem blocks_eqb_eq : forall x y, blocks_eqb x y = true <-> x = y.
Proof. apply list_eqb_spec, node_eqb_spec, block_eqb_spec. Qed.
