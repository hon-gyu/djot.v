(* ai-disclosure: autonomous *)

(** * Whole-document resolution

   The part of parsing that is a function of the finished block list
   rather than of a single line.  It runs after `Parser.parse_blocks`,
   never inside the fold, so inline classification cannot depend on the
   reference and note maps.

   - Auto-identifiers and implicit heading references, assigned in
     document order because uniqueness suffixes depend on what came
     before.
   - Section nesting: a level-driven container stack over the top-level
     block list, moving each heading's id onto the section that wraps it.
   - Footnote collection: definition containers are removed from the
     visible block sequences, and their cleaned bodies assigned into the
     note map.
   - Reference definitions: read into the reference map without being
     removed from the tree.

   Sectioning is top-level only: a section opens only where the enclosing
   container tracks a heading level, which the document does and a block
   quote does not, so `> # h` yields a bare `<h1 id="h">`.  Identifiers
   are assigned everywhere and share one counter. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From Stdlib Require MSetAVL FMapAVL OrdersEx OrderedTypeEx.
From DjotV Require Import Strings Ast Parser.
Import ListNotations.

(* Balanced trees over strings, for the identifier pass: the identifiers
   taken so far, the labels that already have an implicit reference, and
   each base's next candidate index.  Declared here because a module
   cannot be declared inside a section. *)
Module StrSet := MSetAVL.Make OrdersEx.String_as_OT.
Module StrMap := FMapAVL.Make OrderedTypeEx.String_as_OT.

Local Open Scope string_scope.

(* The delimiter table this file is read at.  Implicit, so nothing below
   mentions it: what it buys is that the statements quantify over the
   family rather than over djot's spelling. *)
Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
Heading text
============
*)

(* The string an element contributes to its heading's identifier:
   text-carrying leaves give their text, breaks give a newline,
   containers concatenate their children, and footnote references
   contribute nothing, so a heading's marker does not leak into its id.
   A symbol carries only its alias and contributes nothing, as in
   djot.js. *)
Fixpoint inline_text (il : inline) : string :=
  let go :=
    fix go (ns : list (node inline)) : string :=
      match ns with
      | [] => ""
      | Node _ _ x :: rest => inline_text x ++ go rest
      end in
  match il with
  | Str s => s
  | Verbatim s => s
  | Math _ s => s
  | RawInline _ s => s
  | SoftBreak | HardBreak => nl
  | FootnoteReference _ => ""
  | Emph ils | Strong ils | Highlight ils | Insert ils | Delete ils
  | Superscript ils | Subscript ils | Span ils
  | Link ils _ | Image ils _ | Quoted _ ils => go ils
  (* an autolink contributes its region, so it reaches a heading id and
     an image `alt` *)
  | UrlLink s | EmailLink s => s
  (* the text a wikilink displays, as its desugared link would push it *)
  | Wikilink _ t al => wiki_display t al
  | Symbol _ | NonBreakingSpace => ""
  end.

Local Definition inlines_text (ils : inlines) : string :=
  String.concat "" (map (fun n => inline_text (node_contents n)) ils).

(*
Auto-identifiers
================
*)

(* The characters an identifier drops.  Runs of them separate words,
   which are joined with "-": `words` over the class, where collapsing
   and trimming are what dropping empty tokens already does. *)
Local Definition is_id_sep (c : ascii) : bool :=
  (* JavaScript \s, ASCII part: HT VT FF CR LF and space *)
  ((Ascii.eqb c "009" || Ascii.eqb c "010" || Ascii.eqb c "011"
    || Ascii.eqb c "012" || Ascii.eqb c "013" || Ascii.eqb c " ")
   || (Ascii.eqb c "[" || Ascii.eqb c "]" || Ascii.eqb c "~"
       || Ascii.eqb c "!" || Ascii.eqb c "@" || Ascii.eqb c "#"
       || Ascii.eqb c "$" || Ascii.eqb c "%" || Ascii.eqb c "^"
       || Ascii.eqb c "&" || Ascii.eqb c "*" || Ascii.eqb c "("
       || Ascii.eqb c ")" || Ascii.eqb c "{" || Ascii.eqb c "}"
       || Ascii.eqb c "096" (* backquote *)
       || Ascii.eqb c "," || Ascii.eqb c "." || Ascii.eqb c "<"
       || Ascii.eqb c ">" || Ascii.eqb c "092" (* backslash *)
       || Ascii.eqb c "|" || Ascii.eqb c "=" || Ascii.eqb c "+"
       || Ascii.eqb c "/" || Ascii.eqb c "?"))%char%bool.

Local Definition id_base (s : string) : string :=
  String.concat "-" (words is_id_sep s).

Local Definition id_taken (used : list string) (s : string) : bool :=
  existsb (String.eqb s) used.

(* Candidate i: the base itself at 0, then base-1, base-2, ...  An empty
   base is rejected at 0 and becomes "s-1", "s-2", ... *)
Local Definition id_candidate (base : string) (i : nat) : string :=
  if Nat.eqb i 0 then base
  else (match base with EmptyString => "s" | _ => base end)
       ++ "-" ++ nat_str i.

(* The specification: the first free candidate.  Fuel, fixed by
   `unique_id` below.  With n identifiers taken, candidates 0..n+1 are
   n+2 distinct strings, so one of them is free and the O branch is
   unreachable.  Argued, not proved: the discharge lemma (compare
   `Step.step_fuel_enough`) needs pigeonhole plus injectivity of
   `nat_str`.  Nothing depends on it: `assign_heading_id_spec` relates the
   pass to this definition whatever the O branch returns. *)
Local Fixpoint unique_id_from (fuel i : nat) (used : list string) (base : string)
  : string :=
  let cand := id_candidate base i in
  match fuel with
  | O => cand
  | S f =>
      if nonempty_str cand && negb (id_taken used cand)
      then cand
      else unique_id_from f (S i) used base
  end.

Definition unique_id (used : list string) (base : string) : string :=
  unique_id_from (S (S (length used))) 0 used base.

(*
The identifier pass
-------------------
*)

(* Threaded through the block tree in document order.  Both lists hold
   their entries newest-first; `doc_pass` reverses them.

   Run as written, `unique_id` rescans every candidate from 0 against the
   whole list, which is cubic in the number of headings sharing a text.
   The pass keeps three more fields so that it need not: the taken set,
   the labels with an implicit reference, and per base the index below
   which every candidate is known to be taken.  `id_inv` says the fields
   agree with the lists, and `assign_heading_id_spec` says the pass then
   assigns `unique_id` exactly. *)
Record id_state : Type := IdSt
  { id_used : list string
  ; id_refs : reference_map
  ; id_count : nat
  ; id_used_set : StrSet.t
  ; id_ref_labels : StrSet.t
  ; id_next : StrMap.t nat }.

Definition id_state_init : id_state :=
  IdSt [] [] 0 StrSet.empty StrSet.empty (@StrMap.empty nat).

Local Definition take_id (ident : string) (st : id_state) : id_state :=
  IdSt (ident :: id_used st) (id_refs st) (S (id_count st))
       (StrSet.add ident (id_used_set st)) (id_ref_labels st) (id_next st).

(* An implicit reference from the heading's text to its own id, unless
   that label already has an implicit one.  Explicit references are not
   consulted: `Html.doc_refs` appends the implicit map after the explicit
   one and lookup takes the first match, so an explicit definition wins
   at lookup. *)
Local Definition add_auto_ref (label ident : string) (st : id_state) : id_state :=
  if StrSet.mem label (id_ref_labels st)
  then st
  else IdSt (id_used st) ((label, ("#" ++ ident, [])) :: id_refs st)
            (id_count st) (id_used_set st)
            (StrSet.add label (id_ref_labels st)) (id_next st).

(* An identifier a block attribute spec supplied is taken, and a later
   heading's auto-identifier steps around it.  Every id present in the
   tree at this point came from a spec, since this pass adds the
   others. *)
Definition register_id (a : attr) (st : id_state) : id_state :=
  match alist_lookup "id" a with
  | None => st
  | Some ident => take_id ident st
  end.

(* `unique_id_from` with the taken test on the set, returning the index. *)
Local Fixpoint fresh_index (taken : StrSet.t) (base : string) (fuel i : nat)
  : nat :=
  match fuel with
  | O => i
  | S f =>
      let cand := id_candidate base i in
      if nonempty_str cand && negb (StrSet.mem cand taken)
      then i
      else fresh_index taken base f (S i)
  end.

(* The index to search from, and the fuel that makes the search end where
   `unique_id`'s does. *)
Local Definition fresh_for (st : id_state) (base : string) : nat :=
  let start := match StrMap.find base (id_next st) with
               | Some n => n
               | None => 0
               end in
  fresh_index (id_used_set st) base (S (S (id_count st)) - start) start.

Definition assign_heading_id (p : pos) (a : attr) (lvl : nat) (ils : inlines)
  (st : id_state) : id_state * node block :=
  let text := inlines_text ils in
  match alist_lookup "id" a with
  (* An explicit id wins, and takes its slot.  The implicit reference is
     registered either way and points at that id, so `{#foo}` over
     `# Introduction` makes `[Introduction][]` a link to `#foo`. *)
  | Some ident =>
      (add_auto_ref (normalize_label text) ident (register_id a st),
       Node p a (Heading lvl ils))
  | None =>
      let base := id_base text in
      let i := fresh_for st base in
      let ident := id_candidate base i in
      let st1 := take_id ident st in
      let st' := IdSt (id_used st1) (id_refs st1) (id_count st1)
                      (id_used_set st1) (id_ref_labels st1)
                      (StrMap.add base (S i) (id_next st1)) in
      (add_auto_ref (normalize_label text) ident st',
       Node p (("id", ident) :: a) (Heading lvl ils))
  end.

(*
Agreement with the specification
---------------------------------
*)

Local Definition id_free (used : list string) (base : string) (j : nat) : bool :=
  nonempty_str (id_candidate base j)
  && negb (id_taken used (id_candidate base j)).

Definition id_inv (st : id_state) : Prop :=
  (forall s, StrSet.In s (id_used_set st) <-> In s (id_used st))
  /\ (forall l, StrSet.In l (id_ref_labels st) <-> In l (map fst (id_refs st)))
  /\ id_count st = length (id_used st)
  /\ (forall base n, StrMap.MapsTo base n (id_next st) ->
        n <= S (S (length (id_used st)))
        /\ forall j, j < n -> id_free (id_used st) base j = false).

Lemma id_inv_init : id_inv id_state_init.
Proof.
  split; [|split; [|split]]; cbn.
  - intros s. split; [intros H; apply StrSet.empty_spec in H; contradiction|
                      intros []].
  - intros l. split; [intros H; apply StrSet.empty_spec in H; contradiction|
                      intros []].
  - reflexivity.
  - intros base n H. apply StrMap.find_1 in H. discriminate H.
Qed.

Local Lemma id_taken_in : forall used s, id_taken used s = true <-> In s used.
Proof.
  intros used s. unfold id_taken. rewrite existsb_exists. split.
  - intros [x [Hx He]]. apply String.eqb_eq in He. subst x. exact Hx.
  - intros H. exists s. split; [exact H|apply String.eqb_refl].
Qed.

Local Lemma mem_taken : forall st s,
  (forall s, StrSet.In s (id_used_set st) <-> In s (id_used st)) ->
  StrSet.mem s (id_used_set st) = id_taken (id_used st) s.
Proof.
  intros st s H. destruct (StrSet.mem s (id_used_set st)) eqn:E;
    destruct (id_taken (id_used st) s) eqn:E'; try reflexivity.
  - apply StrSet.mem_spec, H, id_taken_in in E. congruence.
  - apply id_taken_in, H, StrSet.mem_spec in E'. congruence.
Qed.

(* Taking an identifier only makes more candidates taken. *)
Local Lemma id_free_cons : forall used x base j,
  id_free used base j = false -> id_free (x :: used) base j = false.
Proof.
  intros used x base j H. unfold id_free, id_taken in *. cbn [existsb].
  destruct (nonempty_str (id_candidate base j)); [|reflexivity].
  destruct (existsb (String.eqb (id_candidate base j)) used); [|discriminate H].
  rewrite orb_true_r. reflexivity.
Qed.

Local Lemma fresh_index_spec : forall st base f i,
  (forall s, StrSet.In s (id_used_set st) <-> In s (id_used st)) ->
  id_candidate base (fresh_index (id_used_set st) base f i)
  = unique_id_from f i (id_used st) base
  /\ i <= fresh_index (id_used_set st) base f i <= i + f
  /\ (forall j, i <= j < fresh_index (id_used_set st) base f i ->
        id_free (id_used st) base j = false).
Proof.
  intros st base f. induction f as [|f IH]; intros i Hset.
  - cbn. split; [reflexivity|split; [lia|intros j Hj; lia]].
  - cbn [fresh_index unique_id_from]. rewrite (mem_taken st _ Hset).
    destruct (nonempty_str (id_candidate base i)
              && negb (id_taken (id_used st) (id_candidate base i))) eqn:E.
    + split; [reflexivity|split; [lia|intros j Hj; lia]].
    + destruct (IH (S i) Hset) as [Hc [Hb Hf]].
      split; [exact Hc|split; [lia|]].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne]; [exact E|].
      apply Hf. lia.
Qed.

(* Skipping candidates known to be taken does not change the answer. *)
Local Lemma unique_id_from_skip : forall used base k f i,
  (forall j, i <= j < i + k -> id_free used base j = false) ->
  unique_id_from (k + f) i used base = unique_id_from f (i + k) used base.
Proof.
  intros used base k. induction k as [|k IH]; intros f i H.
  - rewrite Nat.add_0_r. reflexivity.
  - cbn [Nat.add unique_id_from].
    pose proof (H i ltac:(lia)) as Hi. unfold id_free in Hi. rewrite Hi.
    rewrite IH by (intros j Hj; apply H; lia).
    f_equal. lia.
Qed.

Local Lemma fresh_for_spec : forall st base,
  id_inv st ->
  id_candidate base (fresh_for st base) = unique_id (id_used st) base
  /\ fresh_for st base <= S (S (length (id_used st)))
  /\ forall j, j < fresh_for st base -> id_free (id_used st) base j = false.
Proof.
  intros st base [Hset [_ [Hcount Hnext]]]. unfold fresh_for, unique_id.
  rewrite Hcount.
  set (L := S (S (length (id_used st)))).
  destruct (StrMap.find base (id_next st)) as [n|] eqn:Ef.
  - apply StrMap.find_2 in Ef. destruct (Hnext base n Ef) as [Hn Hlow].
    destruct (fresh_index_spec st base (L - n) n Hset) as [Hc [Hb Hf]].
    assert (Hu : unique_id_from L 0 (id_used st) base
                 = unique_id_from (L - n) n (id_used st) base).
    { replace L with (n + (L - n)) at 1 by lia.
      rewrite (unique_id_from_skip _ _ n (L - n) 0)
        by (intros j Hj; apply Hlow; lia).
      reflexivity. }
    rewrite Hu. split; [exact Hc|split; [lia|]].
    intros j Hj. destruct (Nat.lt_ge_cases j n); [apply Hlow; lia|apply Hf; lia].
  - destruct (fresh_index_spec st base (L - 0) 0 Hset) as [Hc [Hb Hf]].
    rewrite Nat.sub_0_r in *.
    split; [exact Hc|split; [lia|intros j Hj; apply Hf; lia]].
Qed.

Local Lemma take_id_inv : forall ident st,
  id_inv st -> id_inv (take_id ident st).
Proof.
  intros ident st [Hset [Hlab [Hcount Hnext]]].
  unfold take_id. split; [|split; [|split]]; cbn [id_used id_refs id_count
    id_used_set id_ref_labels id_next length In].
  - intros s. rewrite StrSet.add_spec, Hset. split; intros [H|H]; auto.
  - exact Hlab.
  - rewrite Hcount. reflexivity.
  - intros base n H. destruct (Hnext base n H) as [Hn Hlow].
    split; [lia|intros j Hj; apply id_free_cons, Hlow, Hj].
Qed.

Local Lemma add_auto_ref_inv : forall label ident st,
  id_inv st -> id_inv (add_auto_ref label ident st).
Proof.
  intros label ident st Hinv. unfold add_auto_ref.
  destruct (StrSet.mem label (id_ref_labels st)); [exact Hinv|].
  destruct Hinv as [Hset [Hlab [Hcount Hnext]]].
  split; [|split; [|split]]; cbn [id_used id_refs id_count
    id_used_set id_ref_labels id_next map fst In]; try assumption.
  intros l. rewrite StrSet.add_spec, Hlab. split; intros [H|H]; auto.
Qed.

Lemma register_id_inv : forall a st, id_inv st -> id_inv (register_id a st).
Proof.
  intros a st H. unfold register_id.
  destruct (alist_lookup "id" a); [apply take_id_inv, H|exact H].
Qed.

(* The pass assigns what the specification assigns, and keeps `id_inv`. *)
Theorem assign_heading_id_spec : forall p a lvl ils st,
  id_inv st ->
  alist_lookup "id" a = None ->
  snd (assign_heading_id p a lvl ils st)
  = Node p (("id", unique_id (id_used st) (id_base (inlines_text ils))) :: a)
         (Heading lvl ils).
Proof.
  intros p a lvl ils st Hinv Ha. unfold assign_heading_id. rewrite Ha.
  cbn [snd]. destruct (fresh_for_spec st (id_base (inlines_text ils)) Hinv)
    as [Hc _]. rewrite Hc. reflexivity.
Qed.

Lemma assign_heading_id_inv : forall p a lvl ils st,
  id_inv st -> id_inv (fst (assign_heading_id p a lvl ils st)).
Proof.
  intros p a lvl ils st Hinv. unfold assign_heading_id.
  destruct (alist_lookup "id" a) as [ident|] eqn:Ha; cbn [fst].
  - apply add_auto_ref_inv, register_id_inv, Hinv.
  - apply add_auto_ref_inv.
    set (base := id_base (inlines_text ils)).
    destruct (fresh_for_spec st base Hinv) as [_ [Hb Hlow]].
    set (i := fresh_for st base) in *.
    pose proof (take_id_inv (id_candidate base i) st Hinv)
      as [Hset [Hlab [Hcount Hnext]]].
    unfold take_id in *.
    split; [|split; [|split]]; cbn [id_used id_refs id_count
      id_used_set id_ref_labels id_next] in *; try assumption.
    intros b n Hm.
    destruct (String.string_dec b base) as [->|Hne].
    + assert (n = S i) as ->.
      { apply StrMap.find_1 in Hm.
        assert (Hm' : StrMap.MapsTo base (S i)
                        (StrMap.add base (S i) (id_next st)))
          by (apply StrMap.add_1; reflexivity).
        apply StrMap.find_1 in Hm'. congruence. }
      split; [cbn [length]; lia|].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne].
      * unfold id_free, id_taken. cbn [existsb].
        rewrite String.eqb_refl, orb_true_l, andb_false_r. reflexivity.
      * apply id_free_cons, Hlow. lia.
    + apply StrMap.add_3 in Hm; [exact (Hnext b n Hm)|].
      intros He. apply Hne. symmetry. exact He.
Qed.

End WithTable.
Module Ids.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(* Pre-order, which is document order for headings: a heading closes
   before anything that starts after it, and headings do not nest.

   Recursion is on the payload, with the node's position and attributes
   passed alongside, because `block` recurses through `list (node
   block)`, two type constructors deep, which the guard checker will not
   follow from a `node block` principal argument.  `Html.render_block`
   has the same shape for the same reason. *)
Fixpoint of_block (b : block) (p : pos) (a : attr) (st : id_state)
  {struct b} : id_state * node block :=
  let go :=
    fix go (ns : blocks) (s : id_state) {struct ns} : id_state * blocks :=
      match ns with
      | [] => (s, [])
      | Node p' a' x :: rest =>
          let (s1, n1) := of_block x p' a' s in
          let (s2, rest1) := go rest s1 in
          (s2, n1 :: rest1)
      end in
  match b with
  | Heading lvl ils => assign_heading_id p a lvl ils st
  | BlockQuote bs =>
      let (st', bs') := go bs (register_id a st) in
      (st', Node p a (BlockQuote bs'))
  | Div bs =>
      let (st', bs') := go bs (register_id a st) in
      (st', Node p a (Div bs'))
  | FootnoteDef label bs =>
      let (st', bs') := go bs (register_id a st) in
      (st', Node p a (FootnoteDef label bs'))
  (* Its one block is a node, not a list, so the recursion is on the
     payload directly and no list wrapper is needed. *)
  | Keyed label (Node p' a' x) =>
      let (st', n') := of_block x p' a' (register_id a st) in
      (st', Node p a (Keyed label n'))
  | BulletList sp items =>
      let (st', items') :=
        (fix goit (its : list blocks) (s : id_state) {struct its}
           : id_state * list blocks :=
           match its with
           | [] => (s, [])
           | it :: rest =>
               let (s1, it1) := go it s in
               let (s2, rest1) := goit rest s1 in
               (s2, it1 :: rest1)
           end) items (register_id a st) in
      (st', Node p a (BulletList sp items'))
  | OrderedList oa sp items =>
      let (st', items') :=
        (fix goit (its : list blocks) (s : id_state) {struct its}
           : id_state * list blocks :=
           match its with
           | [] => (s, [])
           | it :: rest =>
               let (s1, it1) := go it s in
               let (s2, rest1) := goit rest s1 in
               (s2, it1 :: rest1)
           end) items (register_id a st) in
      (st', Node p a (OrderedList oa sp items'))
  (* A term holds inlines, so only the definition is descended into. *)
  | DefinitionList sp items =>
      let (st', items') :=
        (fix god (its : list (inlines * blocks)) (s : id_state) {struct its}
           : id_state * list (inlines * blocks) :=
           match its with
           | [] => (s, [])
           | (term, it) :: rest =>
               let (s1, it1) := go it s in
               let (s2, rest1) := god rest s1 in
               (s2, (term, it1) :: rest1)
           end) items (register_id a st) in
      (st', Node p a (DefinitionList sp items'))
  (* A status is a leaf, so a task item's descent is the definition's
     with the pair's other half carried through. *)
  | TaskList sp items =>
      let (st', items') :=
        (fix got (its : list (task_status * blocks)) (s : id_state) {struct its}
           : id_state * list (task_status * blocks) :=
           match its with
           | [] => (s, [])
           | (chk, it) :: rest =>
               let (s1, it1) := go it s in
               let (s2, rest1) := got rest s1 in
               (s2, (chk, it1) :: rest1)
           end) items (register_id a st) in
      (st', Node p a (TaskList sp items'))
  (* No other block needs an arm.  The line fold builds no `Section`, and
     a table's cells and caption hold inlines, so there is no heading
     inside one to find. *)
  | _ => (register_id a st, Node p a b)
  end.

Definition of_node (n : node block) (st : id_state)
  : id_state * node block :=
  match n with Node p a b => of_block b p a st end.

(* The list version, named so proofs can talk about it; `of_block`
   inlines its own copy because Rocq rejects the mutual spelling
   (see Render.v for the same pattern). *)
Fixpoint of_list (ns : blocks) (st : id_state) : id_state * blocks :=
  match ns with
  | [] => (st, [])
  | n :: rest =>
      let (st1, n1) := of_node n st in
      let (st2, rest1) := of_list rest st1 in
      (st2, n1 :: rest1)
  end.

Fixpoint of_items (its : list blocks) (st : id_state)
  : id_state * list blocks :=
  match its with
  | [] => (st, [])
  | it :: rest =>
      let (s1, it1) := of_list it st in
      let (s2, rest1) := of_items rest s1 in
      (s2, it1 :: rest1)
  end.

(* The same over definition items, whose term half is carried through
   untouched: it is inlines, and no identifier is assigned inside one. *)
Fixpoint of_def_items (its : list (inlines * blocks)) (st : id_state)
  : id_state * list (inlines * blocks) :=
  match its with
  | [] => (st, [])
  | (term, it) :: rest =>
      let (s1, it1) := of_list it st in
      let (s2, rest1) := of_def_items rest s1 in
      (s2, (term, it1) :: rest1)
  end.

Fixpoint of_task_items (its : list (task_status * blocks)) (st : id_state)
  : id_state * list (task_status * blocks) :=
  match its with
  | [] => (st, [])
  | (chk, it) :: rest =>
      let (s1, it1) := of_list it st in
      let (s2, rest1) := of_task_items rest s1 in
      (s2, (chk, it1) :: rest1)
  end.

(* The inner fixpoints of `of_block`, named.  Same shape as
   `Pristine.inner_go` and `Undo.pass_inner_go`: Rocq will not let the
   definition mention `of_list` directly, so the identity is
   proved once here. *)
Local Lemma inner_go :
  forall ns st,
    (fix go (l : blocks) (s : id_state) : id_state * blocks :=
       match l with
       | [] => (s, [])
       | Node p' a' x :: rest =>
           let (s1, n1) := of_block x p' a' s in
           let (s2, rest1) := go rest s1 in
           (s2, n1 :: rest1)
       end) ns st = of_list ns st.
Proof.
  induction ns as [|[p' a' x] rest IH]; intros st; [reflexivity|].
  cbn. destruct (of_block x p' a' st) as [s1 n1]. rewrite IH. reflexivity.
Qed.

Lemma quote :
  forall p a bs st,
    of_block (BlockQuote bs) p a st
    = let (st', bs') := of_list bs (register_id a st) in
      (st', Node p a (BlockQuote bs')).
Proof.
  intros p a bs st. cbn [of_block].
  rewrite inner_go. reflexivity.
Qed.

Lemma div :
  forall p a bs st,
    of_block (Div bs) p a st
    = let (st', bs') := of_list bs (register_id a st) in
      (st', Node p a (Div bs')).
Proof.
  intros p a bs st. cbn [of_block].
  rewrite inner_go. reflexivity.
Qed.

Lemma foot :
  forall p a label bs st,
    of_block (FootnoteDef label bs) p a st
    = let (st', bs') := of_list bs (register_id a st) in
      (st', Node p a (FootnoteDef label bs')).
Proof.
  intros p a label bs st. cbn [of_block].
  rewrite inner_go. reflexivity.
Qed.

(* The traversal rewrites items in place, so a list that was nonempty
   still is.  `wf_block (BulletList ...)` needs this. *)
Lemma items_nonempty :
  forall its st, nonempty (snd (of_items its st)) = nonempty its.
Proof.
  intros [|it rest] st; [reflexivity|].
  cbn [of_items].
  destruct (of_list it st) as [s1 it1].
  destruct (of_items rest s1) as [s2 rest1].
  reflexivity.
Qed.

Lemma blist :
  forall p a sp items st,
    of_block (BulletList sp items) p a st
    = let (st', items') := of_items items (register_id a st) in
      (st', Node p a (BulletList sp items')).
Proof.
  assert (H : forall its st,
             (fix goit (l : list blocks) (s : id_state)
                : id_state * list blocks :=
                match l with
                | [] => (s, [])
                | it :: rest =>
                    let (s1, it1) :=
                      (fix go (m : blocks) (s' : id_state) : id_state * blocks :=
                         match m with
                         | [] => (s', [])
                         | Node p' a' x :: r =>
                             let (s2, n2) := of_block x p' a' s' in
                             let (s3, r1) := go r s2 in
                             (s3, n2 :: r1)
                         end) it s in
                    let (s4, rest1) := goit rest s1 in
                    (s4, it1 :: rest1)
                end) its st = of_items its st).
  { induction its as [|it rest IH]; intros st; [reflexivity|].
    cbn [of_items]. rewrite inner_go.
    destruct (of_list it st) as [s1 it1]. rewrite IH. reflexivity. }
  intros p a sp items st. cbn [of_block]. rewrite H. reflexivity.
Qed.

(* The definition arm, whose inner fixpoint differs from the bullet's
   only in carrying the term past the traversal. *)
Lemma deflist :
  forall p a sp items st,
    of_block (DefinitionList sp items) p a st
    = let (st', items') := of_def_items items (register_id a st) in
      (st', Node p a (DefinitionList sp items')).
Proof.
  assert (H : forall its st,
             (fix god (l : list (inlines * blocks)) (s : id_state)
                : id_state * list (inlines * blocks) :=
                match l with
                | [] => (s, [])
                | (term, it) :: rest =>
                    let (s1, it1) :=
                      (fix go (m : blocks) (s' : id_state) : id_state * blocks :=
                         match m with
                         | [] => (s', [])
                         | Node p' a' x :: r =>
                             let (s2, n2) := of_block x p' a' s' in
                             let (s3, r1) := go r s2 in
                             (s3, n2 :: r1)
                         end) it s in
                    let (s4, rest1) := god rest s1 in
                    (s4, (term, it1) :: rest1)
                end) its st = of_def_items its st).
  { induction its as [|[term it] rest IH]; intros st; [reflexivity|].
    cbn [of_def_items]. rewrite inner_go.
    destruct (of_list it st) as [s1 it1]. rewrite IH. reflexivity. }
  intros p a sp items st. cbn [of_block]. rewrite H. reflexivity.
Qed.

Lemma def_items_nonempty :
  forall its st,
    nonempty (snd (of_def_items its st)) = nonempty its.
Proof.
  intros [|[term it] rest] st; [reflexivity|].
  cbn [of_def_items].
  destruct (of_list it st) as [s1 it1].
  destruct (of_def_items rest s1) as [s2 rest1].
  reflexivity.
Qed.

Lemma tasklist :
  forall p a sp items st,
    of_block (TaskList sp items) p a st
    = let (st', items') := of_task_items items (register_id a st) in
      (st', Node p a (TaskList sp items')).
Proof.
  assert (H : forall its st,
             (fix got (l : list (task_status * blocks)) (s : id_state)
                : id_state * list (task_status * blocks) :=
                match l with
                | [] => (s, [])
                | (chk, it) :: rest =>
                    let (s1, it1) :=
                      (fix go (m : blocks) (s' : id_state) : id_state * blocks :=
                         match m with
                         | [] => (s', [])
                         | Node p' a' x :: r =>
                             let (s2, n2) := of_block x p' a' s' in
                             let (s3, r1) := go r s2 in
                             (s3, n2 :: r1)
                         end) it s in
                    let (s4, rest1) := got rest s1 in
                    (s4, (chk, it1) :: rest1)
                end) its st = of_task_items its st).
  { induction its as [|[chk it] rest IH]; intros st; [reflexivity|].
    cbn [of_task_items]. rewrite inner_go.
    destruct (of_list it st) as [s1 it1]. rewrite IH. reflexivity. }
  intros p a sp items st. cbn [of_block]. rewrite H. reflexivity.
Qed.

Lemma task_items_nonempty :
  forall its st,
    nonempty (snd (of_task_items its st)) = nonempty its.
Proof.
  intros [|[chk it] rest] st; [reflexivity|].
  cbn [of_task_items].
  destruct (of_list it st) as [s1 it1].
  destruct (of_task_items rest s1) as [s2 rest1].
  reflexivity.
Qed.

(* The ordered arm is the bullet arm with a different wrapper. *)
Lemma olist :
  forall p a oa sp items st,
    of_block (OrderedList oa sp items) p a st
    = let (st', items') := of_items items (register_id a st) in
      (st', Node p a (OrderedList oa sp items')).
Proof.
  assert (H : forall its st,
             (fix goit (l : list blocks) (s : id_state)
                : id_state * list blocks :=
                match l with
                | [] => (s, [])
                | it :: rest =>
                    let (s1, it1) :=
                      (fix go (m : blocks) (s' : id_state) : id_state * blocks :=
                         match m with
                         | [] => (s', [])
                         | Node p' a' x :: r =>
                             let (s2, n2) := of_block x p' a' s' in
                             let (s3, r1) := go r s2 in
                             (s3, n2 :: r1)
                         end) it s in
                    let (s4, rest1) := goit rest s1 in
                    (s4, it1 :: rest1)
                end) its st = of_items its st).
  { induction its as [|it rest IH]; intros st; [reflexivity|].
    cbn [of_items]. rewrite inner_go.
    destruct (of_list it st) as [s1 it1]. rewrite IH. reflexivity. }
  intros p a oa sp items st. cbn [of_block]. rewrite H. reflexivity.
Qed.

(* The pass keeps `id_inv`, so by `assign_heading_id_spec` every heading
   without an explicit id gets `unique_id` of the identifiers before it. *)
Lemma of_block_inv :
  forall b p a st, id_inv st -> id_inv (fst (of_block b p a st)).
Proof.
  intros b. induction b using block_ind2 with
    (Q := fun bs => forall st, id_inv st -> id_inv (fst (of_list bs st)))
    (R := fun its => forall st, id_inv st -> id_inv (fst (of_items its st)))
    (D := fun its => forall st, id_inv st -> id_inv (fst (of_def_items its st)))
    (K := fun its => forall st, id_inv st -> id_inv (fst (of_task_items its st)));
    intros.
  all: try solve [cbn [of_block fst]; apply register_id_inv; assumption].
  all: try solve [cbn [of_block]; apply assign_heading_id_inv; assumption].
  all: try solve [
    first [rewrite quote|rewrite div|rewrite foot|rewrite olist|rewrite blist
          |rewrite tasklist|rewrite deflist];
    match goal with
    | |- id_inv (fst (let (_, _) := ?e in _)) => destruct e as [s' x'] eqn:E
    end;
    cbn [fst]; change s' with (fst (s', x')); rewrite <- E;
    apply IHb, register_id_inv; assumption].
  all: try solve [exact H].
  - destruct b as [p' a' x].
    specialize (IHb (register_id a st) (register_id_inv _ _ H)).
    cbn [of_list of_node] in IHb. cbn [of_block].
    destruct (of_block x p' a' (register_id a st)) as [s1 n1].
    exact IHb.
  - cbn [of_list of_node].
    pose proof (IHb p a st H) as H1.
    destruct (of_block b p a st) as [s1 n1]. cbn [fst] in H1.
    pose proof (IHb0 s1 H1) as H2.
    destruct (of_list rest s1) as [s2 r2]. exact H2.
  - cbn [of_items].
    pose proof (IHb st H) as H1.
    destruct (of_list it st) as [s1 n1]. cbn [fst] in H1.
    pose proof (IHb0 s1 H1) as H2.
    destruct (of_items rest s1) as [s2 r2]. exact H2.
  - cbn [of_def_items].
    pose proof (IHb st H) as H1.
    destruct (of_list it st) as [s1 n1]. cbn [fst] in H1.
    pose proof (IHb0 s1 H1) as H2.
    destruct (of_def_items rest s1) as [s2 r2]. exact H2.
  - cbn [of_task_items].
    pose proof (IHb st H) as H1.
    destruct (of_list it st) as [s1 n1]. cbn [fst] in H1.
    pose proof (IHb0 s1 H1) as H2.
    destruct (of_task_items rest s1) as [s2 r2]. exact H2.
Qed.

Lemma of_list_inv :
  forall bs st, id_inv st -> id_inv (fst (of_list bs st)).
Proof.
  induction bs as [|[p a b] rest IH]; intros st H; [exact H|].
  cbn [of_list of_node].
  pose proof (of_block_inv b p a st H) as H1.
  destruct (of_block b p a st) as [s1 n1]. cbn [fst] in H1.
  pose proof (IH s1 H1) as H2.
  destruct (of_list rest s1) as [s2 r2]. exact H2.
Qed.

End WithTable.
End Ids.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
Section nesting
===============
*)

(* A stack of open sections, innermost first.  Each entry carries the
   heading level that opened it, the attributes moved off that heading,
   and the blocks collected so far in reverse.  The bottom entry is the
   document, at level 0: no heading level is <= 0, so it is never closed
   and the stack is never empty. *)
(* The section builder and the pass are the only parts of this file that
   build a node of their own, so they are the only ones the position
   policy reaches.  Closing the section before the lemmas below leaves
   every one of them at the semantic instance. *)
Section WithPolicy.
Context {P : PosPolicy}.

Definition sect_state : Type := list (nat * attr * blocks).

Local Definition sect_init : sect_state := [(0, [], [])].

(* Close every section a level-`lvl` heading interrupts, carrying the
   already-closed nodes inward-out in `pending` so each lands inside the
   section that encloses it.  Recursion is on the stack, so this is
   structural: `pending` is what lets the current section nest into its
   parent before the parent is tested. *)
(* A section covers its heading and everything under it, which is
   exactly the children it is built from. *)
Definition section_node (a : attr) (bs : blocks) : node block :=
  Node (hull_pos_with bs) a (Section bs).

Fixpoint close_ge (lvl : nat) (pending : blocks) (stk : sect_state)
  : sect_state :=
  match stk with
  | [] => []
  | [(l, a, acc)] => [(l, a, (pending ++ acc)%list)]
  | (l, a, acc) :: outer =>
      if Nat.leb lvl l
      then close_ge lvl [section_node a (rev (pending ++ acc))] outer
      else ((l, a, (pending ++ acc)%list) :: outer)
  end.

(* Equation lemmas, as everywhere else in this development: `cbn` on
   close_ge reduces the *recursive* call as well, and an induction
   hypothesis about it then no longer matches. *)
Local Lemma close_ge_singleton :
  forall lvl pending l a acc,
    close_ge lvl pending [(l, a, acc)] = [(l, a, (pending ++ acc)%list)].
Proof. reflexivity. Qed.

Local Lemma close_ge_cons :
  forall lvl pending l a acc outer,
    outer <> [] ->
    close_ge lvl pending ((l, a, acc) :: outer)
    = if Nat.leb lvl l
      then close_ge lvl [section_node a (rev (pending ++ acc))] outer
      else ((l, a, (pending ++ acc)%list) :: outer).
Proof. intros lvl pending l a acc [|e outer] H; [contradiction|reflexivity]. Qed.

(* End of input closes every open section, whatever its level.  Testing
   levels here would be wrong as well as unnecessary: a level-0 heading
   would leave its entry open, and sect_bottom would then drop it and
   everything it had collected. *)
Fixpoint close_all (pending : blocks) (stk : sect_state) : sect_state :=
  match stk with
  | [] => []
  | [(l, a, acc)] => [(l, a, (pending ++ acc)%list)]
  | (l, a, acc) :: outer =>
      close_all [section_node a (rev (pending ++ acc))] outer
  end.

Lemma close_all_cons :
  forall pending l a acc outer,
    outer <> [] ->
    close_all pending ((l, a, acc) :: outer)
    = close_all [section_node a (rev (pending ++ acc))] outer.
Proof. intros pending l a acc [|e outer] H; [contradiction|reflexivity]. Qed.

Definition sect_push (b : node block) (stk : sect_state) : sect_state :=
  match stk with
  | [] => []
  | (l, a, acc) :: rest => (l, a, b :: acc) :: rest
  end.

(* A heading closes the sections it interrupts, then opens its own with
   the heading as its first child.  The id moves from the heading to the
   section. *)
Definition sect_step (stk : sect_state) (n : node block) : sect_state :=
  match n with
  | Node p a (Heading lvl ils) =>
      (lvl, a, [Node p [] (Heading lvl ils)]) :: close_ge lvl [] stk
  | _ => sect_push n stk
  end.

(* The document's own accumulator, once every section above it is closed. *)
Fixpoint sect_bottom (stk : sect_state) : blocks :=
  match stk with
  | [] => []
  | [(_, _, acc)] => rev acc
  | _ :: outer => sect_bottom outer
  end.

Definition sectionize (bs : blocks) : blocks :=
  sect_bottom (close_all [] (fold_left sect_step bs sect_init)).

(*
The pass
========
*)

(*
Reference definitions
=====================

A definition contributes no HTML and no structure, only an entry in the
document's map, which is why it is collected here rather than in the
line fold, and why `Undo.pass` below needs no arm for it: the pass reads
the block tree and does not touch it.

Nesting is not a barrier: a definition inside a quote or a list item
registers with the document all the same, so the traversal descends
into every container the fold can build.
*)

(* Keyed by normalized label, assigned the way a JS object is: a repeated
   label keeps the first definition's position and takes the last one's
   value.  An empty label is dropped before normalization, so `[ ]: u`,
   whose normalized label is empty, is still recorded. *)
Local Definition add_ref (p : pos) (a : attr) (b : block) (m : reference_map)
  : reference_map :=
  match b with
  | RefDef label dest =>
      if nonempty_str label
      then alist_set (normalize_label label) (dest, a) m
      else m
  | _ => m
  end.

End WithPolicy.
End WithTable.
Module Refs.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.
Section WithPolicy.
Context {P : PosPolicy}.

(* Pre-order, which is document order, with the same inlined list
   recursion `Ids.of_block` needs and for the same guard-checker reason. *)
Local Fixpoint of_block (b : block) (p : pos) (a : attr) (m : reference_map)
  {struct b} : reference_map :=
  let go :=
    fix go (ns : blocks) (acc : reference_map) {struct ns} : reference_map :=
      match ns with
      | [] => acc
      | Node p' a' x :: rest => go rest (of_block x p' a' acc)
      end in
  let goit :=
    fix goit (its : list blocks) (acc : reference_map) {struct its}
      : reference_map :=
      match its with
      | [] => acc
      | it :: rest =>
          goit rest ((fix go' (ns : blocks) (acc' : reference_map)
                        {struct ns} : reference_map :=
                        match ns with
                        | [] => acc'
                        | Node p' a' x :: more => go' more (of_block x p' a' acc')
                        end) it acc)
      end in
  match b with
  | BlockQuote bs | Div bs | Section bs | FootnoteDef _ bs => go bs m
  | Keyed _ (Node p' a' x) => of_block x p' a' m
  | BulletList _ items | OrderedList _ _ items => goit items m
  | DefinitionList _ items =>
      (fix god (its : list (inlines * blocks)) (acc : reference_map)
         {struct its} : reference_map :=
         match its with
         | [] => acc
         | (_, it) :: rest =>
             god rest ((fix go' (ns : blocks) (acc' : reference_map)
                          {struct ns} : reference_map :=
                          match ns with
                          | [] => acc'
                          | Node p' a' x :: more => go' more (of_block x p' a' acc')
                          end) it acc)
         end) items m
  | TaskList _ items =>
      (fix got (its : list (task_status * blocks)) (acc : reference_map)
         {struct its} : reference_map :=
         match its with
         | [] => acc
         | (_, it) :: rest =>
             got rest ((fix go' (ns : blocks) (acc' : reference_map)
                          {struct ns} : reference_map :=
                          match ns with
                          | [] => acc'
                          | Node p' a' x :: more => go' more (of_block x p' a' acc')
                          end) it acc)
         end) items m
  | _ => add_ref p a b m
  end.

Local Fixpoint of_list (ns : blocks) (m : reference_map) : reference_map :=
  match ns with
  | [] => m
  | Node p a b :: rest => of_list rest (of_block b p a m)
  end.

Local Lemma inner_go : forall ns m,
  (fix go (ns : blocks) (acc : reference_map) : reference_map :=
     match ns with
     | [] => acc
     | Node p' a' x :: rest => go rest (of_block x p' a' acc)
     end) ns m = of_list ns m.
Proof.
  induction ns as [|[p a b] rest IH]; intros m; [reflexivity|].
  cbn [of_list]. rewrite IH. reflexivity.
Qed.

Local Lemma inner_goit : forall its m,
  (fix goit (its : list blocks) (acc : reference_map) : reference_map :=
     match its with
     | [] => acc
     | it :: rest =>
         goit rest
           ((fix go (ns : blocks) (acc' : reference_map) : reference_map :=
               match ns with
               | [] => acc'
               | Node p' a' x :: more => go more (of_block x p' a' acc')
               end) it acc)
     end) its m
  = fold_left (fun acc it => of_list it acc) its m.
Proof.
  induction its as [|it rest IH]; intros m; [reflexivity|].
  cbn [fold_left]. rewrite inner_go, IH. reflexivity.
Qed.

Local Lemma inner_god : forall its m,
  (fix god (its : list (inlines * blocks)) (acc : reference_map)
      : reference_map :=
     match its with
     | [] => acc
     | (_, it) :: rest =>
         god rest
           ((fix go (ns : blocks) (acc' : reference_map) : reference_map :=
               match ns with
               | [] => acc'
               | Node p' a' x :: more => go more (of_block x p' a' acc')
               end) it acc)
     end) its m
  = fold_left (fun acc kv => of_list (snd kv) acc) its m.
Proof.
  induction its as [|[term it] rest IH]; intros m; [reflexivity|].
  cbn [fold_left]. rewrite inner_go, IH. reflexivity.
Qed.

Local Lemma inner_got : forall its m,
  (fix got (its : list (task_status * blocks)) (acc : reference_map)
      : reference_map :=
     match its with
     | [] => acc
     | (_, it) :: rest =>
         got rest
           ((fix go (ns : blocks) (acc' : reference_map) : reference_map :=
               match ns with
               | [] => acc'
               | Node p' a' x :: more => go more (of_block x p' a' acc')
               end) it acc)
     end) its m
  = fold_left (fun acc kv => of_list (snd kv) acc) its m.
Proof.
  induction its as [|[chk it] rest IH]; intros m; [reflexivity|].
  cbn [fold_left]. rewrite inner_go, IH. reflexivity.
Qed.

End WithPolicy.
End WithTable.
End Refs.

Module Notes.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.
Section WithPolicy.
Context {P : PosPolicy}.

(** Remove footnote-definition nodes while assigning their recursively
    cleaned bodies into the document table.  A definition is assigned
    after its body, matching the order in which nested containers close. *)
Fixpoint of_block (b : block) (p : pos) (a : attr) (m : note_map)
  {struct b} : note_map * option (node block) :=
  let go :=
    fix go (ns : blocks) (acc : note_map) {struct ns} : note_map * blocks :=
      match ns with
      | [] => (acc, [])
      | Node p' a' x :: rest =>
          let (acc1, n1) := of_block x p' a' acc in
          let (acc2, rest1) := go rest acc1 in
          match n1 with
          | Some n => (acc2, n :: rest1)
          | None => (acc2, rest1)
          end
      end in
  let goit :=
    fix goit (its : list blocks) (acc : note_map) {struct its}
      : note_map * list blocks :=
      match its with
      | [] => (acc, [])
      | it :: rest =>
          let (acc1, it1) := go it acc in
          let (acc2, rest1) := goit rest acc1 in
          (acc2, it1 :: rest1)
      end in
  match b with
  | FootnoteDef label bs =>
      let (m', bs') := go bs m in
      (alist_set (normalize_label label) bs' m', None)
  | BlockQuote bs =>
      let (m', bs') := go bs m in (m', Some (Node p a (BlockQuote bs')))
  | Div bs =>
      let (m', bs') := go bs m in (m', Some (Node p a (Div bs')))
  (* A key whose one block is a definition has nothing left to name, so
     it goes with it.  Every other container keeps its (shorter) list. *)
  | Keyed label (Node p' a' x) =>
      let (m', o) := of_block x p' a' m in
      (m', match o with
           | Some n' => Some (Node p a (Keyed label n'))
           | None => None
           end)
  | BulletList sp items =>
      let (m', items') := goit items m in
      (m', Some (Node p a (BulletList sp items')))
  | OrderedList oa sp items =>
      let (m', items') := goit items m in
      (m', Some (Node p a (OrderedList oa sp items')))
  | DefinitionList sp items =>
      let (m', items') :=
        (fix god (its : list (inlines * blocks)) (acc : note_map) {struct its}
           : note_map * list (inlines * blocks) :=
           match its with
           | [] => (acc, [])
           | (term, it) :: rest =>
               let (acc1, it1) := go it acc in
               let (acc2, rest1) := god rest acc1 in
               (acc2, (term, it1) :: rest1)
           end) items m in
      (m', Some (Node p a (DefinitionList sp items')))
  | TaskList sp items =>
      let (m', items') :=
        (fix got (its : list (task_status * blocks)) (acc : note_map) {struct its}
           : note_map * list (task_status * blocks) :=
           match its with
           | [] => (acc, [])
           | (chk, it) :: rest =>
               let (acc1, it1) := go it acc in
               let (acc2, rest1) := got rest acc1 in
               (acc2, (chk, it1) :: rest1)
           end) items m in
      (m', Some (Node p a (TaskList sp items')))
  | _ => (m, Some (Node p a b))
  end.

Fixpoint of_list (ns : blocks) (m : note_map) : note_map * blocks :=
  match ns with
  | [] => (m, [])
  | Node p a b :: rest =>
      let (m1, n1) := of_block b p a m in
      let (m2, rest1) := of_list rest m1 in
      match n1 with
      | Some n => (m2, n :: rest1)
      | None => (m2, rest1)
      end
  end.

Fixpoint of_items (its : list blocks) (m : note_map)
  : note_map * list blocks :=
  match its with
  | [] => (m, [])
  | it :: rest =>
      let (m1, it1) := of_list it m in
      let (m2, rest1) := of_items rest m1 in
      (m2, it1 :: rest1)
  end.

Fixpoint of_def_items (its : list (inlines * blocks)) (m : note_map)
  : note_map * list (inlines * blocks) :=
  match its with
  | [] => (m, [])
  | (term, it) :: rest =>
      let (m1, it1) := of_list it m in
      let (m2, rest1) := of_def_items rest m1 in
      (m2, (term, it1) :: rest1)
  end.

Fixpoint of_task_items (its : list (task_status * blocks)) (m : note_map)
  : note_map * list (task_status * blocks) :=
  match its with
  | [] => (m, [])
  | (chk, it) :: rest =>
      let (m1, it1) := of_list it m in
      let (m2, rest1) := of_task_items rest m1 in
      (m2, (chk, it1) :: rest1)
  end.

Lemma items_nonempty :
  forall its m,
    nonempty (snd (of_items its m)) = nonempty its.
Proof.
  intros [|it rest] m; [reflexivity|].
  cbn [of_items].
  destruct (of_list it m) as [m1 it1].
  destruct (of_items rest m1) as [m2 rest1].
  reflexivity.
Qed.

Local Lemma inner_go :
  forall ns m,
    (fix go (ns' : blocks) (acc : note_map) {struct ns'}
       : note_map * blocks :=
       match ns' with
       | [] => (acc, [])
       | Node p a b :: rest =>
           let (acc1, n1) := of_block b p a acc in
           let (acc2, rest1) := go rest acc1 in
           match n1 with
           | Some n => (acc2, n :: rest1)
           | None => (acc2, rest1)
           end
       end) ns m = of_list ns m.
Proof.
  induction ns as [|[p a b] rest IH]; intros m; [reflexivity|].
  cbn [of_list].
  destruct (of_block b p a m) as [m1 [n|]] eqn:E;
    rewrite IH; reflexivity.
Qed.

Local Lemma inner_goit :
  forall its m,
    (fix goit (its' : list blocks) (acc : note_map) {struct its'}
       : note_map * list blocks :=
       match its' with
       | [] => (acc, [])
       | it :: rest =>
           let (acc1, it1) :=
             (fix go (ns : blocks) (acc0 : note_map) {struct ns}
                : note_map * blocks :=
                match ns with
                | [] => (acc0, [])
                | Node p a b :: more =>
                    let (acc2, n1) := of_block b p a acc0 in
                    let (acc3, more1) := go more acc2 in
                    match n1 with
                    | Some n => (acc3, n :: more1)
                    | None => (acc3, more1)
                    end
                end) it acc in
           let (acc2, rest1) := goit rest acc1 in
           (acc2, it1 :: rest1)
       end) its m = of_items its m.
Proof.
  induction its as [|it rest IH]; intros m; [reflexivity|].
  cbn [of_items]. rewrite inner_go.
  destruct (of_list it m) as [m1 it1]. rewrite IH. reflexivity.
Qed.

Lemma quote :
  forall p a bs m,
    of_block (BlockQuote bs) p a m
    = let (m', bs') := of_list bs m in
      (m', Some (Node p a (BlockQuote bs'))).
Proof.
  intros p a bs m. cbn [of_block]. rewrite inner_go.
  reflexivity.
Qed.

Lemma div :
  forall p a bs m,
    of_block (Div bs) p a m
    = let (m', bs') := of_list bs m in
      (m', Some (Node p a (Div bs'))).
Proof.
  intros p a bs m. cbn [of_block]. rewrite inner_go.
  reflexivity.
Qed.

Lemma foot :
  forall p a label bs m,
    of_block (FootnoteDef label bs) p a m
    = let (m', bs') := of_list bs m in
      (alist_set (normalize_label label) bs' m', None).
Proof.
  intros p a label bs m. cbn [of_block]. rewrite inner_go.
  reflexivity.
Qed.

Lemma blist :
  forall p a sp items m,
    of_block (BulletList sp items) p a m
    = let (m', items') := of_items items m in
      (m', Some (Node p a (BulletList sp items'))).
Proof.
  intros p a sp items m. cbn [of_block]. rewrite inner_goit.
  reflexivity.
Qed.

Lemma deflist :
  forall p a sp items m,
    of_block (DefinitionList sp items) p a m
    = let (m', items') := of_def_items items m in
      (m', Some (Node p a (DefinitionList sp items'))).
Proof.
  assert (H : forall its m,
             (fix god (l : list (inlines * blocks)) (acc : note_map)
                {struct l} : note_map * list (inlines * blocks) :=
                match l with
                | [] => (acc, [])
                | (term, it) :: rest =>
                    let (acc1, it1) :=
                      (fix go (ns : blocks) (acc0 : note_map) {struct ns}
                         : note_map * blocks :=
                         match ns with
                         | [] => (acc0, [])
                         | Node p a b :: more =>
                             let (acc2, n1) := of_block b p a acc0 in
                             let (acc3, more1) := go more acc2 in
                             match n1 with
                             | Some n => (acc3, n :: more1)
                             | None => (acc3, more1)
                             end
                         end) it acc in
                    let (acc2, rest1) := god rest acc1 in
                    (acc2, (term, it1) :: rest1)
                end) its m = of_def_items its m).
  { induction its as [|[term it] rest IH]; intros m; [reflexivity|].
    cbn [of_def_items]. rewrite inner_go.
    destruct (of_list it m) as [m1 it1]. rewrite IH. reflexivity. }
  intros p a sp items m. cbn [of_block]. rewrite H. reflexivity.
Qed.

Lemma def_items_nonempty :
  forall its m,
    nonempty (snd (of_def_items its m)) = nonempty its.
Proof.
  intros [|[term it] rest] m; [reflexivity|].
  cbn [of_def_items].
  destruct (of_list it m) as [m1 it1].
  destruct (of_def_items rest m1) as [m2 rest1].
  reflexivity.
Qed.

Lemma tasklist :
  forall p a sp items m,
    of_block (TaskList sp items) p a m
    = let (m', items') := of_task_items items m in
      (m', Some (Node p a (TaskList sp items'))).
Proof.
  assert (H : forall its m,
             (fix got (l : list (task_status * blocks)) (acc : note_map)
                {struct l} : note_map * list (task_status * blocks) :=
                match l with
                | [] => (acc, [])
                | (chk, it) :: rest =>
                    let (acc1, it1) :=
                      (fix go (ns : blocks) (acc0 : note_map) {struct ns}
                         : note_map * blocks :=
                         match ns with
                         | [] => (acc0, [])
                         | Node p a b :: more =>
                             let (acc2, n1) := of_block b p a acc0 in
                             let (acc3, more1) := go more acc2 in
                             match n1 with
                             | Some n => (acc3, n :: more1)
                             | None => (acc3, more1)
                             end
                         end) it acc in
                    let (acc2, rest1) := got rest acc1 in
                    (acc2, (chk, it1) :: rest1)
                end) its m = of_task_items its m).
  { induction its as [|[chk it] rest IH]; intros m; [reflexivity|].
    cbn [of_task_items]. rewrite inner_go.
    destruct (of_list it m) as [m1 it1]. rewrite IH. reflexivity. }
  intros p a sp items m. cbn [of_block]. rewrite H. reflexivity.
Qed.

Lemma task_items_nonempty :
  forall its m,
    nonempty (snd (of_task_items its m)) = nonempty its.
Proof.
  intros [|[chk it] rest] m; [reflexivity|].
  cbn [of_task_items].
  destruct (of_list it m) as [m1 it1].
  destruct (of_task_items rest m1) as [m2 rest1].
  reflexivity.
Qed.

Lemma olist :
  forall p a oa sp items m,
    of_block (OrderedList oa sp items) p a m
    = let (m', items') := of_items items m in
      (m', Some (Node p a (OrderedList oa sp items'))).
Proof.
  intros p a oa sp items m. cbn [of_block].
  rewrite inner_goit. reflexivity.
Qed.

End WithPolicy.
End WithTable.
End Notes.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.
Section WithPolicy.
Context {P : PosPolicy}.

Definition doc_pass (bs : blocks) : doc :=
  let (st, bs') := Ids.of_list bs id_state_init in
  let (notes, visible) := Notes.of_list bs' [] in
  {| doc_blocks := sectionize visible
   ; doc_footnotes := notes
   ; doc_references := Refs.of_list bs' []
   ; doc_auto_references := rev (id_refs st)
   ; doc_auto_identifiers := rev (id_used st) |}.

(** Parse a Djot document: first run the line fold, then perform
    whole-document resolution. *)
Definition parse_doc (s : string) : doc := doc_pass (parse_blocks s).

End WithPolicy.

(* Outside the policy section every mention means the semantic instance,
   where a section is the node it always was. *)
Lemma section_node_nopos :
  forall a bs, @section_node semantic_pos a bs = Node NoPos a (Section bs).
Proof. reflexivity. Qed.

Local Ltac nosect := rewrite ?section_node_nopos.

(* The located document: the same pass over the located block parse. *)
Definition parse_doc_located (s : string) : doc :=
  @doc_pass located_pos (parse_blocks_located s).

(*
Erasure
=======

The pass only adds, and what it adds is recoverable: a section is
exactly its heading plus the blocks that followed it, and an
auto-identifier is exactly an "id" attribute on a heading that carried
none.  `Undo.pass` takes both back out in one traversal, and
`pass_erase` says it takes out precisely what the pass put in.  That is
what keeps Roundtrip.v's theorem meaningful above the block layer:
render, parse, erase is the identity.
*)

(* Oriented like alist_lookup, so the two compose without an eqb flip. *)
Local Definition strip_id (a : attr) : attr :=
  filter (fun kv => negb (String.eqb "id" (fst kv))) a.

Local Lemma strip_id_absent :
  forall a, alist_lookup "id" a = None -> strip_id a = a.
Proof.
  induction a as [|[k v] rest IH]; intros H; [reflexivity|].
  cbn [alist_lookup] in H. cbn [strip_id filter fst].
  destruct (String.eqb "id" k); [discriminate|].
  cbn [negb]. f_equal. apply IH. exact H.
Qed.

Local Lemma strip_id_cons :
  forall v a, alist_lookup "id" a = None -> strip_id (("id", v) :: a) = a.
Proof.
  intros v a H. cbn [strip_id filter fst].
  rewrite String.eqb_refl. cbn [negb].
  apply strip_id_absent. exact H.
Qed.

(* A section's attributes came off the heading that opened it, which
   sectionize left as its first child. *)
Local Definition set_first (a : attr) (bs : blocks) : blocks :=
  match bs with
  | [] => []
  | Node p _ x :: rest => Node p a x :: rest
  end.

End WithTable.
Module Undo.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(* Stripping the id *before* handing the attributes back is what makes
   one traversal enough: the identifier the pass added rides on the
   section, so it has to come off there. *)
Local Fixpoint pass_block (b : block) (p : pos) (a : attr) {struct b}
  : blocks :=
  let go :=
    fix go (ns : blocks) : blocks :=
      match ns with
      | [] => []
      | Node p' a' x :: rest => (pass_block x p' a' ++ go rest)%list
      end in
  let goit :=
    fix goit (its : list blocks) : list blocks :=
      match its with
      | [] => []
      | it :: rest => go it :: goit rest
      end in
  match b with
  | Section inner => set_first (strip_id a) (go inner)
  | Heading lvl ils => [Node p (strip_id a) (Heading lvl ils)]
  | BlockQuote inner => [Node p a (BlockQuote (go inner))]
  | Div inner => [Node p a (Div (go inner))]
  | FootnoteDef label inner => [Node p a (FootnoteDef label (go inner))]
  (* `Section` is the one block whose undo is not a single node, and
     `sectionize` builds none below the top level, so the default is
     unreachable and the payload comes back as itself. *)
  | Keyed label (Node p' a' x) =>
      [Node p a (Keyed label
         (hd (Node p' a' x) (pass_block x p' a')))]
  | BulletList sp items => [Node p a (BulletList sp (goit items))]
  | OrderedList oa sp items => [Node p a (OrderedList oa sp (goit items))]
  | DefinitionList sp items =>
      [Node p a (DefinitionList sp
         ((fix god (its : list (inlines * blocks))
             : list (inlines * blocks) :=
             match its with
             | [] => []
             | (term, it) :: rest => (term, go it) :: god rest
             end) items))]
  | TaskList sp items =>
      [Node p a (TaskList sp
         ((fix got (its : list (task_status * blocks))
             : list (task_status * blocks) :=
             match its with
             | [] => []
             | (chk, it) :: rest => (chk, go it) :: got rest
             end) items))]
  | _ => [Node p a b]
  end.

Fixpoint pass (bs : blocks) : blocks :=
  match bs with
  | [] => []
  | Node p a b :: rest => (pass_block b p a ++ pass rest)%list
  end.

Local Fixpoint pass_items (its : list blocks) : list blocks :=
  match its with
  | [] => []
  | it :: rest => pass it :: pass_items rest
  end.

Local Fixpoint pass_def_items (its : list (inlines * blocks))
  : list (inlines * blocks) :=
  match its with
  | [] => []
  | (term, it) :: rest => (term, pass it) :: pass_def_items rest
  end.

Local Fixpoint pass_task_items (its : list (task_status * blocks))
  : list (task_status * blocks) :=
  match its with
  | [] => []
  | (chk, it) :: rest => (chk, pass it) :: pass_task_items rest
  end.

Local Lemma pass_inner_go :
  forall ns,
    (fix go (l : blocks) : blocks :=
       match l with
       | [] => []
       | Node p' a' x :: rest => (pass_block x p' a' ++ go rest)%list
       end) ns = pass ns.
Proof.
  induction ns as [|[p' a' x] rest IH]; [reflexivity|].
  cbn [pass]. rewrite IH. reflexivity.
Qed.

Local Lemma pass_section :
  forall inner p a,
    pass_block (Section inner) p a
    = set_first (strip_id a) (pass inner).
Proof.
  assert (H : forall ns,
             (fix go (l : blocks) : blocks :=
                match l with
                | [] => []
                | Node p' a' x :: rest =>
                    (pass_block x p' a' ++ go rest)%list
                end) ns = pass ns).
  { induction ns as [|[p' a' x] rest IH]; [reflexivity|].
    cbn [pass]. rewrite IH. reflexivity. }
  intros inner p a.
  change (pass_block (Section inner) p a)
    with (set_first (strip_id a)
            ((fix go (l : blocks) : blocks :=
                match l with
                | [] => []
                | Node p' a' x :: rest =>
                    (pass_block x p' a' ++ go rest)%list
                end) inner)).
  rewrite H. reflexivity.
Qed.

Local Lemma pass_quote :
  forall inner p a,
    pass_block (BlockQuote inner) p a
    = [Node p a (BlockQuote (pass inner))].
Proof.
  assert (H : forall ns,
             (fix go (l : blocks) : blocks :=
                match l with
                | [] => []
                | Node p' a' x :: rest =>
                    (pass_block x p' a' ++ go rest)%list
                end) ns = pass ns).
  { induction ns as [|[p' a' x] rest IH]; [reflexivity|].
    cbn [pass]. rewrite IH. reflexivity. }
  intros inner p a.
  change (pass_block (BlockQuote inner) p a)
    with [Node p a (BlockQuote
            ((fix go (l : blocks) : blocks :=
                match l with
                | [] => []
                | Node p' a' x :: rest =>
                    (pass_block x p' a' ++ go rest)%list
                end) inner))].
  rewrite H. reflexivity.
Qed.

Local Lemma pass_inner_goit :
  forall its,
    (fix goit (l : list blocks) : list blocks :=
       match l with
       | [] => []
       | it :: rest =>
           (fix go (m : blocks) : blocks :=
              match m with
              | [] => []
              | Node p' a' x :: r => (pass_block x p' a' ++ go r)%list
              end) it :: goit rest
       end) its = pass_items its.
Proof.
  induction its as [|it rest IH]; [reflexivity|].
  cbn [pass_items]. rewrite pass_inner_go, IH. reflexivity.
Qed.

Local Lemma pass_div :
  forall inner p a,
    pass_block (Div inner) p a = [Node p a (Div (pass inner))].
Proof.
  intros inner p a.
  change (pass_block (Div inner) p a)
    with [Node p a (Div
            ((fix go (l : blocks) : blocks :=
                match l with
                | [] => []
                | Node p' a' x :: rest =>
                    (pass_block x p' a' ++ go rest)%list
                end) inner))].
  rewrite pass_inner_go. reflexivity.
Qed.

Local Lemma pass_foot :
  forall label inner p a,
    pass_block (FootnoteDef label inner) p a
    = [Node p a (FootnoteDef label (pass inner))].
Proof.
  intros label inner p a.
  change (pass_block (FootnoteDef label inner) p a)
    with [Node p a (FootnoteDef label
            ((fix go (l : blocks) : blocks :=
                match l with
                | [] => []
                | Node p' a' x :: rest =>
                    (pass_block x p' a' ++ go rest)%list
                end) inner))].
  rewrite pass_inner_go. reflexivity.
Qed.

Local Lemma pass_blist :
  forall sp items p a,
    pass_block (BulletList sp items) p a
    = [Node p a (BulletList sp (pass_items items))].
Proof.
  intros sp items p a.
  change (pass_block (BulletList sp items) p a)
    with [Node p a (BulletList sp
            ((fix goit (its : list blocks) : list blocks :=
                match its with
                | [] => []
                | it :: rest =>
                    (fix go (l : blocks) : blocks :=
                       match l with
                       | [] => []
                       | Node p' a' x :: r => (pass_block x p' a' ++ go r)%list
                       end) it :: goit rest
                end) items))].
  rewrite pass_inner_goit. reflexivity.
Qed.

Local Lemma pass_olist :
  forall oa sp items p a,
    pass_block (OrderedList oa sp items) p a
    = [Node p a (OrderedList oa sp (pass_items items))].
Proof.
  intros oa sp items p a.
  change (pass_block (OrderedList oa sp items) p a)
    with [Node p a (OrderedList oa sp
            ((fix goit (its : list blocks) : list blocks :=
                match its with
                | [] => []
                | it :: rest =>
                    (fix go (l : blocks) : blocks :=
                       match l with
                       | [] => []
                       | Node p' a' x :: r => (pass_block x p' a' ++ go r)%list
                       end) it :: goit rest
                end) items))].
  rewrite pass_inner_goit. reflexivity.
Qed.

(* Convertible, where the bullet arm needs `pass_inner_goit`: the
   definition traversal has one inner fixpoint and `pass_def_items`
   is spelled as that fixpoint, so nothing has to be identified. *)
Local Lemma pass_deflist :
  forall sp items p a,
    pass_block (DefinitionList sp items) p a
    = [Node p a (DefinitionList sp (pass_def_items items))].
Proof. reflexivity. Qed.

Local Lemma pass_tasklist :
  forall sp items p a,
    pass_block (TaskList sp items) p a
    = [Node p a (TaskList sp (pass_task_items items))].
Proof. reflexivity. Qed.

Local Definition pass_node (n : node block) : blocks :=
  match n with Node p a b => pass_block b p a end.

Local Lemma pass_cons :
  forall n rest, pass (n :: rest) = (pass_node n ++ pass rest)%list.
Proof. intros [p a b] rest. reflexivity. Qed.

Local Lemma pass_single : forall n, pass [n] = pass_node n.
Proof. intros [p a b]. cbn [pass pass_node]. apply app_nil_r. Qed.

Local Lemma pass_app :
  forall l1 l2, pass (l1 ++ l2)%list = (pass l1 ++ pass l2)%list.
Proof.
  induction l1 as [|[p a b] rest IH]; intros l2; [reflexivity|].
  cbn [app pass]. rewrite IH, app_assoc. reflexivity.
Qed.

End WithTable.
End Undo.

Module Pristine.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(* Input the pass has not already run on: no sections, and no heading
   carrying an explicit id.  Checked exactly where `Undo.pass` looks (the
   top level and block-quote contents), because those are the only
   places either half of the pass reaches. *)
Local Fixpoint of_block (b : block) (a : attr) {struct b} : bool :=
  let go :=
    fix go (ns : blocks) : bool :=
      match ns with
      | [] => true
      | Node _ a' x :: rest => (of_block x a' && go rest)%bool
      end in
  let goit :=
    fix goit (its : list blocks) : bool :=
      match its with
      | [] => true
      | it :: rest => (go it && goit rest)%bool
      end in
  match b with
  | Section _ => false
  | Heading _ _ =>
      match alist_lookup "id" a with Some _ => false | None => true end
  | FootnoteDef _ _ => false
  | BlockQuote inner | Div inner => go inner
  | Keyed _ (Node _ a' x) => of_block x a'
  | BulletList _ items => goit items
  | OrderedList _ _ items => goit items
  | DefinitionList _ items =>
      (fix god (its : list (inlines * blocks)) : bool :=
         match its with
         | [] => true
         | (_, it) :: rest => (go it && god rest)%bool
         end) items
  | TaskList _ items =>
      (fix got (its : list (task_status * blocks)) : bool :=
         match its with
         | [] => true
         | (_, it) :: rest => (go it && got rest)%bool
         end) items
  | _ => true
  end.

Fixpoint of_list (bs : blocks) : bool :=
  match bs with
  | [] => true
  | Node _ a b :: rest => (of_block b a && of_list rest)%bool
  end.

(* A list is pristine when every item is.  Named so the equation lemma
   below has something to be stated against. *)
Fixpoint of_items (its : list blocks) : bool :=
  match its with
  | [] => true
  | it :: rest => (of_list it && of_items rest)%bool
  end.

Local Fixpoint of_def_items (its : list (inlines * blocks)) : bool :=
  match its with
  | [] => true
  | (_, it) :: rest => (of_list it && of_def_items rest)%bool
  end.

Fixpoint of_task_items (its : list (task_status * blocks)) : bool :=
  match its with
  | [] => true
  | (_, it) :: rest => (of_list it && of_task_items rest)%bool
  end.

(* Splitting the term off keeps an item pristine: the block that leaves
   is a paragraph, and `of_block` asks nothing of one. *)
Local Lemma after_def_split :
  forall bs ils def,
    of_list bs = true -> def_split bs = Some (ils, def) -> of_list def = true.
Proof.
  induction bs as [|[q b x] rest IH]; intros ils def H E; [discriminate|].
  cbn [of_list] in H. apply andb_true_iff in H as [Hx Hrest].
  cbn [def_split] in E. destruct x; try discriminate E.
  - injection E as <- <-. exact Hrest.
  - destruct (def_split rest) as [[ils' more]|] eqn:Es; [|discriminate E].
    injection E as <- <-.
    cbn [of_list]. rewrite Hx. exact (IH ils' more Hrest eq_refl).
  - destruct (def_split rest) as [[ils' more]|] eqn:Es; [|discriminate E].
    injection E as <- <-.
    cbn [of_list]. rewrite Hx. exact (IH ils' more Hrest eq_refl).
Qed.

Local Lemma after_def_items :
  forall its,
    of_items its = true -> of_def_items (def_items its) = true.
Proof.
  unfold def_items. induction its as [|it rest IH]; [reflexivity|].
  cbn [of_items map of_def_items]. intros H.
  apply andb_true_iff in H as [Hit Hrest].
  destruct (def_split it) as [[ils def]|] eqn:E.
  - rewrite (def_item_some it _ E). cbn [snd].
    rewrite (after_def_split it ils def Hit E), (IH Hrest). reflexivity.
  - rewrite (def_item_none it E). cbn [snd].
    rewrite Hit, (IH Hrest). reflexivity.
Qed.

(* The inner fixpoints of `of_block` are `of_list` and
   `of_items`; Rocq will not let them be spelled that way, so each
   arm needs its identity proved once and rewritten with thereafter. *)
Local Lemma inner_go :
  forall ns,
    (fix go (l : blocks) : bool :=
       match l with
       | [] => true
       | Node _ a' x :: rest => (of_block x a' && go rest)%bool
       end) ns = of_list ns.
Proof.
  induction ns as [|[p' a' x] rest IH]; [reflexivity|].
  cbn [of_list]. rewrite IH. reflexivity.
Qed.

Local Lemma quote :
  forall inner a, of_block (BlockQuote inner) a = of_list inner.
Proof.
  intros inner a.
  change (of_block (BlockQuote inner) a)
    with ((fix go (l : blocks) : bool :=
             match l with
             | [] => true
             | Node _ a' x :: rest => (of_block x a' && go rest)%bool
             end) inner).
  rewrite inner_go. reflexivity.
Qed.

Local Lemma div :
  forall inner a, of_block (Div inner) a = of_list inner.
Proof.
  intros inner a.
  change (of_block (Div inner) a)
    with ((fix go (l : blocks) : bool :=
             match l with
             | [] => true
             | Node _ a' x :: rest => (of_block x a' && go rest)%bool
             end) inner).
  rewrite inner_go. reflexivity.
Qed.

Local Lemma deflist :
  forall sp items a,
    of_block (DefinitionList sp items) a = of_def_items items.
Proof.
  intros sp items a.
  change (of_block (DefinitionList sp items) a)
    with ((fix god (its : list (inlines * blocks)) : bool :=
             match its with
             | [] => true
             | (_, it) :: rest =>
                 ((fix go (l : blocks) : bool :=
                     match l with
                     | [] => true
                     | Node _ a' x :: r => (of_block x a' && go r)%bool
                     end) it && god rest)%bool
             end) items).
  induction items as [|[term it] rest IH]; [reflexivity|].
  cbn [of_def_items]. rewrite inner_go, IH. reflexivity.
Qed.

Local Lemma tasklist :
  forall sp items a,
    of_block (TaskList sp items) a = of_task_items items.
Proof.
  intros sp items a.
  change (of_block (TaskList sp items) a)
    with ((fix got (its : list (task_status * blocks)) : bool :=
             match its with
             | [] => true
             | (_, it) :: rest =>
                 ((fix go (l : blocks) : bool :=
                     match l with
                     | [] => true
                     | Node _ a' x :: r => (of_block x a' && go r)%bool
                     end) it && got rest)%bool
             end) items).
  induction items as [|[chk it] rest IH]; [reflexivity|].
  cbn [of_task_items]. rewrite inner_go, IH. reflexivity.
Qed.

Local Lemma blist :
  forall sp items a,
    of_block (BulletList sp items) a = of_items items.
Proof.
  intros sp items a.
  change (of_block (BulletList sp items) a)
    with ((fix goit (its : list blocks) : bool :=
             match its with
             | [] => true
             | it :: rest =>
                 ((fix go (l : blocks) : bool :=
                     match l with
                     | [] => true
                     | Node _ a' x :: r => (of_block x a' && go r)%bool
                     end) it && goit rest)%bool
             end) items).
  induction items as [|it rest IH]; [reflexivity|].
  cbn [of_items]. rewrite inner_go, IH. reflexivity.
Qed.

Local Lemma olist :
  forall oa sp items a,
    of_block (OrderedList oa sp items) a = of_items items.
Proof.
  intros oa sp items a.
  change (of_block (OrderedList oa sp items) a)
    with ((fix goit (its : list blocks) : bool :=
             match its with
             | [] => true
             | it :: rest =>
                 ((fix go (l : blocks) : bool :=
                     match l with
                     | [] => true
                     | Node _ a' x :: r => (of_block x a' && go r)%bool
                     end) it && goit rest)%bool
             end) items).
  induction items as [|it rest IH]; [reflexivity|].
  cbn [of_items]. rewrite inner_go, IH. reflexivity.
Qed.

Local Lemma cons :
  forall p a b rest,
    of_list (Node p a b :: rest) = (of_block b a && of_list rest)%bool.
Proof. reflexivity. Qed.

Local Definition of_node (n : node block) : bool :=
  match n with Node _ a b => of_block b a end.

Local Lemma cons_node :
  forall n rest, of_list (n :: rest) = (of_node n && of_list rest)%bool.
Proof. intros [p a b] rest. reflexivity. Qed.

End WithTable.
End Pristine.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.
Local Ltac nosect := rewrite ?section_node_nopos.

(* The collection pass needs only this projection of `Pristine.of_list`: there is
   no definition node to remove.  Unlike `Pristine.of_list`, assigned heading ids
   do not affect it, so it survives `Ids.of_block`. *)
Local Fixpoint notes_free_block (b : block) {struct b} : bool :=
  let go :=
    fix go (ns : blocks) : bool :=
      match ns with
      | [] => true
      | Node _ _ x :: rest => (notes_free_block x && go rest)%bool
      end in
  let goit :=
    fix goit (its : list blocks) : bool :=
      match its with
      | [] => true
      | it :: rest => (go it && goit rest)%bool
      end in
  match b with
  | FootnoteDef _ _ => false
  | BlockQuote bs | Div bs | Section bs => go bs
  | Keyed _ (Node _ _ x) => notes_free_block x
  | BulletList _ items | OrderedList _ _ items => goit items
  | DefinitionList _ items =>
      (fix god (its : list (inlines * blocks)) : bool :=
         match its with
         | [] => true
         | (_, it) :: rest => (go it && god rest)%bool
         end) items
  | TaskList _ items =>
      (fix got (its : list (task_status * blocks)) : bool :=
         match its with
         | [] => true
         | (_, it) :: rest => (go it && got rest)%bool
         end) items
  | _ => true
  end.

Local Fixpoint notes_free (bs : blocks) : bool :=
  match bs with
  | [] => true
  | Node _ _ b :: rest => (notes_free_block b && notes_free rest)%bool
  end.

Local Fixpoint notes_free_items (its : list blocks) : bool :=
  match its with
  | [] => true
  | it :: rest => (notes_free it && notes_free_items rest)%bool
  end.

Local Fixpoint notes_free_def_items (its : list (inlines * blocks)) : bool :=
  match its with
  | [] => true
  | (_, it) :: rest => (notes_free it && notes_free_def_items rest)%bool
  end.

Local Fixpoint notes_free_task_items (its : list (task_status * blocks)) : bool :=
  match its with
  | [] => true
  | (_, it) :: rest => (notes_free it && notes_free_task_items rest)%bool
  end.

Local Lemma notes_free_inner_go :
  forall ns,
    (fix go (l : blocks) : bool :=
       match l with
       | [] => true
       | Node _ _ x :: rest => (notes_free_block x && go rest)%bool
       end) ns = notes_free ns.
Proof.
  induction ns as [|[p a b] rest IH]; [reflexivity|].
  cbn [notes_free]. rewrite IH. reflexivity.
Qed.

Local Lemma notes_free_inner_goit :
  forall its,
    (fix goit (l : list blocks) : bool :=
       match l with
       | [] => true
       | it :: rest =>
           ((fix go (m : blocks) : bool :=
               match m with
               | [] => true
               | Node _ _ x :: more =>
                   (notes_free_block x && go more)%bool
               end) it && goit rest)%bool
       end) its = notes_free_items its.
Proof.
  induction its as [|it rest IH]; [reflexivity|].
  cbn [notes_free_items]. rewrite notes_free_inner_go, IH. reflexivity.
Qed.

Local Lemma notes_free_quote :
  forall bs, notes_free_block (BlockQuote bs) = notes_free bs.
Proof. intros bs. cbn [notes_free_block]. apply notes_free_inner_go. Qed.

Local Lemma notes_free_section :
  forall bs, notes_free_block (Section bs) = notes_free bs.
Proof. intros bs. cbn [notes_free_block]. apply notes_free_inner_go. Qed.

Local Lemma notes_free_div :
  forall bs, notes_free_block (Div bs) = notes_free bs.
Proof. intros bs. cbn [notes_free_block]. apply notes_free_inner_go. Qed.

Local Lemma notes_free_deflist :
  forall sp items,
    notes_free_block (DefinitionList sp items) = notes_free_def_items items.
Proof.
  intros sp items.
  change (notes_free_block (DefinitionList sp items))
    with ((fix god (its : list (inlines * blocks)) : bool :=
             match its with
             | [] => true
             | (_, it) :: rest =>
                 ((fix go (l : blocks) : bool :=
                     match l with
                     | [] => true
                     | Node _ _ x :: r => (notes_free_block x && go r)%bool
                     end) it && god rest)%bool
             end) items).
  induction items as [|[term it] rest IH]; [reflexivity|].
  cbn [notes_free_def_items]. rewrite notes_free_inner_go, IH. reflexivity.
Qed.

Local Lemma notes_free_tasklist :
  forall sp items,
    notes_free_block (TaskList sp items) = notes_free_task_items items.
Proof.
  intros sp items.
  change (notes_free_block (TaskList sp items))
    with ((fix got (its : list (task_status * blocks)) : bool :=
             match its with
             | [] => true
             | (_, it) :: rest =>
                 ((fix go (l : blocks) : bool :=
                     match l with
                     | [] => true
                     | Node _ _ x :: r => (notes_free_block x && go r)%bool
                     end) it && got rest)%bool
             end) items).
  induction items as [|[chk it] rest IH]; [reflexivity|].
  cbn [notes_free_task_items]. rewrite notes_free_inner_go, IH. reflexivity.
Qed.

Local Lemma notes_free_blist :
  forall sp items,
    notes_free_block (BulletList sp items) = notes_free_items items.
Proof. intros sp items. cbn [notes_free_block]. apply notes_free_inner_goit. Qed.

Local Lemma notes_free_olist :
  forall oa sp items,
    notes_free_block (OrderedList oa sp items) = notes_free_items items.
Proof. intros oa sp items. cbn [notes_free_block]. apply notes_free_inner_goit. Qed.

(*
Undoing the identifiers
-----------------------
*)

Local Lemma undo_assign_ids :
  forall b p a st,
    Pristine.of_block b a = true ->
    Undo.pass_node (snd (Ids.of_block b p a st)) = [Node p a b].
Proof.
  intros b.
  induction b using block_ind2 with
    (Q := fun bs => forall st,
            Pristine.of_list bs = true ->
            Undo.pass (snd (Ids.of_list bs st)) = bs)
    (R := fun its => forall st,
            Pristine.of_items its = true ->
            Undo.pass_items (snd (Ids.of_items its st)) = its)
    (D := fun its => forall st,
            Pristine.of_def_items its = true ->
            Undo.pass_def_items (snd (Ids.of_def_items its st)) = its)
    (K := fun its => forall st,
            Pristine.of_task_items its = true ->
            Undo.pass_task_items (snd (Ids.of_task_items its st)) = its);
    intros; try reflexivity.
  - (* Section: excluded by `Pristine.of_list` *)
    discriminate.
  - (* Heading *)
    cbn [Pristine.of_block] in H.
    unfold Ids.of_block, assign_heading_id.
    destruct (alist_lookup "id" a) as [v|] eqn:Eid; [discriminate|].
    cbn [snd Undo.pass_node Undo.pass_block].
    rewrite strip_id_cons by exact Eid. reflexivity.
  - (* BlockQuote *)
    rewrite Pristine.quote in H.
    rewrite Ids.quote.
    destruct (Ids.of_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd Undo.pass_node]. rewrite Undo.pass_quote.
    change bs' with (snd (st', bs')). rewrite <- E.
    rewrite IHb by exact H. reflexivity.
  - (* Div: the same, one constructor over *)
    rewrite Pristine.div in H.
    rewrite Ids.div.
    destruct (Ids.of_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd Undo.pass_node]. rewrite Undo.pass_div.
    change bs' with (snd (st', bs')). rewrite <- E.
    rewrite IHb by exact H. reflexivity.
  - (* OrderedList: the same shape as the bullet case below *)
    rewrite Pristine.olist in H.
    rewrite Ids.olist.
    destruct (Ids.of_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd Undo.pass_node]. rewrite Undo.pass_olist.
    change its' with (snd (st', its')). rewrite <- E.
    rewrite IHb by exact H. reflexivity.
  - (* BulletList: the item list, which is what R is for *)
    rewrite Pristine.blist in H.
    rewrite Ids.blist.
    destruct (Ids.of_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd Undo.pass_node]. rewrite Undo.pass_blist.
    change its' with (snd (st', its')). rewrite <- E.
    rewrite IHb by exact H. reflexivity.
  - (* TaskList: the same over K's *)
    rewrite Pristine.tasklist in H.
    rewrite Ids.tasklist.
    destruct (Ids.of_task_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd Undo.pass_node]. rewrite Undo.pass_tasklist.
    change its' with (snd (st', its')). rewrite <- E.
    rewrite IHb by exact H. reflexivity.
  - (* DefinitionList: the bullet case again, over D's item list *)
    rewrite Pristine.deflist in H.
    rewrite Ids.deflist.
    destruct (Ids.of_def_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd Undo.pass_node]. rewrite Undo.pass_deflist.
    change its' with (snd (st', its')). rewrite <- E.
    rewrite IHb by exact H. reflexivity.
  - (* FootnoteDef: collection removes it, so `Pristine.of_list` excludes it. *)
    discriminate.
  - (* Keyed: its one block, through Q at the singleton. *)
    destruct b as [p' a' x].
    cbn [Pristine.of_block] in H.
    specialize (IHb (register_id a st)).
    cbn [Ids.of_block Ids.of_list Ids.of_node Undo.pass Undo.pass_node
      snd] in *.
    destruct (Ids.of_block x p' a' (register_id a st)) as [st1 n1] eqn:E1.
    cbn [snd] in *.
    assert (Hu : Undo.pass [n1] = [Node p' a' x])
      by (apply IHb; cbn [Pristine.of_list Pristine.of_node]; rewrite H; reflexivity).
    destruct n1 as [q b1 y].
    cbn [Undo.pass Undo.pass_node] in Hu. rewrite app_nil_r in Hu.
    cbn [Undo.pass_node Undo.pass_block]. rewrite Hu. reflexivity.
  - (* Node p a b :: rest ([] is closed by reflexivity above) *)
    rewrite Pristine.cons in H. apply andb_true_iff in H as [Hb Hrest].
    cbn [Ids.of_list Ids.of_node].
    destruct (Ids.of_block b p a st) as [st1 n1] eqn:E1.
    destruct (Ids.of_list rest st1) as [st2 rest1] eqn:E2.
    cbn [snd]. rewrite Undo.pass_cons.
    replace n1 with (snd (Ids.of_block b p a st)) by (rewrite E1; reflexivity).
    rewrite IHb by exact Hb.
    replace rest1 with (snd (Ids.of_list rest st1))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
  - (* R's cons: one item, then the rest *)
    cbn [Pristine.of_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [Ids.of_items].
    destruct (Ids.of_list it st) as [s1 it1] eqn:E1.
    destruct (Ids.of_items rest s1) as [s2 rest1] eqn:E2.
    cbn [snd Undo.pass_items].
    replace it1 with (snd (Ids.of_list it st)) by (rewrite E1; reflexivity).
    rewrite IHb by exact Hit.
    replace rest1 with (snd (Ids.of_items rest s1))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
  - (* D's cons: the term rides through untouched *)
    cbn [Pristine.of_def_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [Ids.of_def_items].
    destruct (Ids.of_list it st) as [s1 it1] eqn:E1.
    destruct (Ids.of_def_items rest s1) as [s2 rest1] eqn:E2.
    cbn [snd Undo.pass_def_items].
    replace it1 with (snd (Ids.of_list it st)) by (rewrite E1; reflexivity).
    rewrite IHb by exact Hit.
    replace rest1 with (snd (Ids.of_def_items rest s1))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
  - (* K's cons: the status rides through untouched *)
    cbn [Pristine.of_task_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [Ids.of_task_items].
    destruct (Ids.of_list it st) as [s1 it1] eqn:E1.
    destruct (Ids.of_task_items rest s1) as [s2 rest1] eqn:E2.
    cbn [snd Undo.pass_task_items].
    replace it1 with (snd (Ids.of_list it st)) by (rewrite E1; reflexivity).
    rewrite IHb by exact Hit.
    replace rest1 with (snd (Ids.of_task_items rest s1))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
Qed.

(* The list version, as in Wf.v: block_ind2 proves it as its Q, but the
   principle does not hand it back as a lemma. *)
Local Lemma undo_assign_ids_list :
  forall bs st,
    Pristine.of_list bs = true -> Undo.pass (snd (Ids.of_list bs st)) = bs.
Proof.
  induction bs as [|[p a b] rest IH]; intros st H; [reflexivity|].
  rewrite Pristine.cons in H. apply andb_true_iff in H as [Hb Hrest].
  cbn [Ids.of_list Ids.of_node].
  destruct (Ids.of_block b p a st) as [st1 n1] eqn:E1.
  destruct (Ids.of_list rest st1) as [st2 rest1] eqn:E2.
  cbn [snd]. rewrite Undo.pass_cons.
  replace n1 with (snd (Ids.of_block b p a st)) by (rewrite E1; reflexivity).
  rewrite undo_assign_ids by exact Hb.
  replace rest1 with (snd (Ids.of_list rest st1))
    by (rewrite E2; reflexivity).
  rewrite IH by exact Hrest. reflexivity.
Qed.

Local Lemma collect_notes_pristine_block :
  forall b p a m,
    notes_free_block b = true ->
    Notes.of_block b p a m = (m, Some (Node p a b)).
Proof.
  intros b. induction b using block_ind2 with
    (Q := fun bs => forall m,
        notes_free bs = true -> Notes.of_list bs m = (m, bs))
    (R := fun its => forall m,
        notes_free_items its = true -> Notes.of_items its m = (m, its))
    (D := fun its => forall m,
        notes_free_def_items its = true ->
        Notes.of_def_items its m = (m, its))
    (K := fun its => forall m,
        notes_free_task_items its = true ->
        Notes.of_task_items its m = (m, its));
    intros; try reflexivity.
  - rewrite notes_free_quote in H. rewrite Notes.quote, IHb by exact H.
    reflexivity.
  - rewrite notes_free_div in H. rewrite Notes.div, IHb by exact H.
    reflexivity.
  - rewrite notes_free_olist in H. rewrite Notes.olist, IHb by exact H.
    reflexivity.
  - rewrite notes_free_blist in H. rewrite Notes.blist, IHb by exact H.
    reflexivity.
  - rewrite notes_free_tasklist in H.
    rewrite Notes.tasklist, IHb by exact H. reflexivity.
  - rewrite notes_free_deflist in H.
    rewrite Notes.deflist, IHb by exact H. reflexivity.
  - discriminate.
  - (* Keyed: `Q` at the singleton says the block survives collection,
       and a key with a surviving block survives with it. *)
    destruct b as [p' a' x]. cbn [notes_free_block] in H.
    specialize (IHb m). cbn [notes_free] in IHb.
    rewrite H in IHb. cbn [Notes.of_list] in IHb.
    destruct (Notes.of_block x p' a' m) as [m1 n1] eqn:E1.
    destruct n1 as [n0|].
    + injection (IHb eq_refl) as <- ->.
      cbn [Notes.of_block]. rewrite E1. reflexivity.
    + discriminate (f_equal snd (IHb eq_refl)).
  - cbn [notes_free] in H. apply andb_true_iff in H as [Hb Hrest].
    cbn [Notes.of_list]. rewrite IHb by exact Hb.
    rewrite IHb0 by exact Hrest. reflexivity.
  - cbn [notes_free_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [Notes.of_items]. rewrite IHb by exact Hit.
    rewrite IHb0 by exact Hrest. reflexivity.
  - cbn [notes_free_def_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [Notes.of_def_items]. rewrite IHb by exact Hit.
    rewrite IHb0 by exact Hrest. reflexivity.
  - cbn [notes_free_task_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [Notes.of_task_items]. rewrite IHb by exact Hit.
    rewrite IHb0 by exact Hrest. reflexivity.
Qed.

Local Lemma collect_notes_list_pristine :
  forall bs m,
    notes_free bs = true -> Notes.of_list bs m = (m, bs).
Proof.
  induction bs as [|[p a b] rest IH]; intros m H; [reflexivity|].
  cbn [notes_free] in H. apply andb_true_iff in H as [Hb Hrest].
  cbn [Notes.of_list]. rewrite collect_notes_pristine_block by exact Hb.
  rewrite IH by exact Hrest. reflexivity.
Qed.

Local Lemma pristine_notes_free_block :
  forall b a, Pristine.of_block b a = true -> notes_free_block b = true.
Proof.
  intros b. induction b using block_ind2 with
    (Q := fun bs => Pristine.of_list bs = true -> notes_free bs = true)
    (R := fun its => Pristine.of_items its = true -> notes_free_items its = true)
    (D := fun its =>
            Pristine.of_def_items its = true -> notes_free_def_items its = true)
    (K := fun its =>
            Pristine.of_task_items its = true -> notes_free_task_items its = true);
    intros; try reflexivity.
  - discriminate.
  - rewrite Pristine.quote in H. rewrite notes_free_quote. apply IHb. exact H.
  - rewrite Pristine.div in H. rewrite notes_free_div. apply IHb. exact H.
  - rewrite Pristine.olist in H. rewrite notes_free_olist. apply IHb. exact H.
  - rewrite Pristine.blist in H. rewrite notes_free_blist. apply IHb. exact H.
  - rewrite Pristine.tasklist in H. rewrite notes_free_tasklist.
    apply IHb. exact H.
  - rewrite Pristine.deflist in H. rewrite notes_free_deflist.
    apply IHb. exact H.
  - discriminate.
  - (* Keyed: both predicates read straight through to the one block. *)
    destruct b as [p' a' x]. cbn [Pristine.of_block notes_free_block] in *.
    cbn [Pristine.of_list notes_free] in IHb. rewrite H in IHb.
    specialize (IHb eq_refl). rewrite andb_true_r in IHb. exact IHb.
  - rewrite Pristine.cons in H. apply andb_true_iff in H as [Hb Hrest].
    cbn [notes_free]. rewrite (IHb _ Hb), (IHb0 Hrest). reflexivity.
  - cbn [Pristine.of_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [notes_free_items]. rewrite (IHb Hit), (IHb0 Hrest). reflexivity.
  - cbn [Pristine.of_def_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [notes_free_def_items]. rewrite (IHb Hit), (IHb0 Hrest). reflexivity.
  - cbn [Pristine.of_task_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [notes_free_task_items]. rewrite (IHb Hit), (IHb0 Hrest). reflexivity.
Qed.

Local Lemma pristine_notes_free :
  forall bs, Pristine.of_list bs = true -> notes_free bs = true.
Proof.
  induction bs as [|[p a b] rest IH]; intros H; [reflexivity|].
  rewrite Pristine.cons in H. apply andb_true_iff in H as [Hb Hrest].
  cbn [notes_free]. rewrite (pristine_notes_free_block b a Hb), (IH Hrest).
  reflexivity.
Qed.

Local Lemma assign_ids_notes_free :
  forall b p a st,
    notes_free_block b = true ->
    notes_free_block (node_contents (snd (Ids.of_block b p a st))) = true.
Proof.
  intros b. induction b using block_ind2 with
    (Q := fun bs => forall st,
        notes_free bs = true ->
        notes_free (snd (Ids.of_list bs st)) = true)
    (R := fun its => forall st,
        notes_free_items its = true ->
        notes_free_items (snd (Ids.of_items its st)) = true)
    (D := fun its => forall st,
        notes_free_def_items its = true ->
        notes_free_def_items (snd (Ids.of_def_items its st)) = true)
    (K := fun its => forall st,
        notes_free_task_items its = true ->
        notes_free_task_items (snd (Ids.of_task_items its st)) = true);
    intros; try exact H; try reflexivity.
  - unfold Ids.of_block, assign_heading_id.
    destruct (alist_lookup "id" a); cbn [snd node_contents notes_free_block];
      reflexivity.
  - rewrite notes_free_quote in H. rewrite Ids.quote.
    destruct (Ids.of_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd node_contents]. rewrite notes_free_quote.
    change bs' with (snd (st', bs')). rewrite <- E. apply IHb. exact H.
  - rewrite notes_free_div in H. rewrite Ids.div.
    destruct (Ids.of_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd node_contents]. rewrite notes_free_div.
    change bs' with (snd (st', bs')). rewrite <- E. apply IHb. exact H.
  - rewrite notes_free_olist in H. rewrite Ids.olist.
    destruct (Ids.of_items items (register_id a st)) as [st' items'] eqn:E.
    cbn [snd node_contents]. rewrite notes_free_olist.
    change items' with (snd (st', items')). rewrite <- E. apply IHb. exact H.
  - rewrite notes_free_blist in H. rewrite Ids.blist.
    destruct (Ids.of_items items (register_id a st)) as [st' items'] eqn:E.
    cbn [snd node_contents]. rewrite notes_free_blist.
    change items' with (snd (st', items')). rewrite <- E. apply IHb. exact H.
  - rewrite notes_free_tasklist in H. rewrite Ids.tasklist.
    destruct (Ids.of_task_items items (register_id a st)) as [st' items']
      eqn:E.
    cbn [snd node_contents]. rewrite notes_free_tasklist.
    change items' with (snd (st', items')). rewrite <- E. apply IHb. exact H.
  - rewrite notes_free_deflist in H. rewrite Ids.deflist.
    destruct (Ids.of_def_items items (register_id a st)) as [st' items']
      eqn:E.
    cbn [snd node_contents]. rewrite notes_free_deflist.
    change items' with (snd (st', items')). rewrite <- E. apply IHb. exact H.
  - discriminate.
  - (* Keyed: the payload is one node, so `Q` at the singleton is the
       statement about it with a `&& true` on the end. *)
    destruct b as [p' a' x]. cbn [notes_free_block] in H.
    specialize (IHb (register_id a st)). cbn [notes_free] in IHb.
    rewrite H in IHb. specialize (IHb eq_refl).
    cbn [Ids.of_block Ids.of_list Ids.of_node] in *.
    destruct (Ids.of_block x p' a' (register_id a st)) as [st1 n1] eqn:E1.
    cbn [snd notes_free node_contents] in *.
    destruct n1 as [q b1 y]. cbn [notes_free_block] in *.
    rewrite andb_true_r in IHb. exact IHb.
  - cbn [notes_free] in H. apply andb_true_iff in H as [Hb Hrest].
    cbn [Ids.of_list Ids.of_node].
    destruct (Ids.of_block b p a st) as [st1 n1] eqn:E1.
    destruct n1 as [np na nb].
    destruct (Ids.of_list rest st1) as [st2 rest1] eqn:E2.
    cbn [snd notes_free].
    pose proof (IHb p a st Hb) as Hnode.
    rewrite E1 in Hnode. cbn [snd node_contents] in Hnode. rewrite Hnode.
    replace (notes_free rest1) with
      (notes_free (snd (Ids.of_list rest st1)))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
  - cbn [notes_free_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [Ids.of_items].
    destruct (Ids.of_list it st) as [st1 it1] eqn:E1.
    destruct (Ids.of_items rest st1) as [st2 rest1] eqn:E2.
    cbn [snd notes_free_items].
    replace (notes_free it1) with (notes_free (snd (Ids.of_list it st)))
      by (rewrite E1; reflexivity).
    rewrite IHb by exact Hit.
    replace (notes_free_items rest1) with
      (notes_free_items (snd (Ids.of_items rest st1)))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
  - cbn [notes_free_def_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [Ids.of_def_items].
    destruct (Ids.of_list it st) as [st1 it1] eqn:E1.
    destruct (Ids.of_def_items rest st1) as [st2 rest1] eqn:E2.
    cbn [snd notes_free_def_items].
    replace (notes_free it1) with (notes_free (snd (Ids.of_list it st)))
      by (rewrite E1; reflexivity).
    rewrite IHb by exact Hit.
    replace (notes_free_def_items rest1) with
      (notes_free_def_items (snd (Ids.of_def_items rest st1)))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
  - cbn [notes_free_task_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [Ids.of_task_items].
    destruct (Ids.of_list it st) as [st1 it1] eqn:E1.
    destruct (Ids.of_task_items rest st1) as [st2 rest1] eqn:E2.
    cbn [snd notes_free_task_items].
    replace (notes_free it1) with (notes_free (snd (Ids.of_list it st)))
      by (rewrite E1; reflexivity).
    rewrite IHb by exact Hit.
    replace (notes_free_task_items rest1) with
      (notes_free_task_items (snd (Ids.of_task_items rest st1)))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
Qed.

Local Lemma assign_ids_list_notes_free :
  forall bs st,
    notes_free bs = true -> notes_free (snd (Ids.of_list bs st)) = true.
Proof.
  induction bs as [|[p a b] rest IH]; intros st H; [reflexivity|].
  cbn [notes_free] in H. apply andb_true_iff in H as [Hb Hrest].
  cbn [Ids.of_list Ids.of_node].
  destruct (Ids.of_block b p a st) as [st1 n1] eqn:E1.
  destruct n1 as [np na nb].
  destruct (Ids.of_list rest st1) as [st2 rest1] eqn:E2.
  cbn [snd notes_free].
  pose proof (assign_ids_notes_free b p a st Hb) as Hnode.
  rewrite E1 in Hnode. cbn [snd node_contents] in Hnode. rewrite Hnode.
  replace (notes_free rest1) with (notes_free (snd (Ids.of_list rest st1)))
    by (rewrite E2; reflexivity).
  rewrite IH by exact Hrest. reflexivity.
Qed.

(*
Undoing the sections
--------------------

Unconditional: sectionize only ever wraps, and Undo.pass unwraps.  A
`Section` already present in the input is flattened the same way on both
sides, so it needs no hypothesis; only the identifier half cares what
the input looked like.
*)

Local Lemma set_first_app :
  forall z X Y,
    nonempty X = true -> set_first z (X ++ Y)%list = (set_first z X ++ Y)%list.
Proof. intros z [|[p a b] X'] Y H; [discriminate|reflexivity]. Qed.

(* The blocks the stack has consumed so far, recovered.  Entries hold
   their accumulators reversed, and every entry above the document's
   carries the attributes that came off its heading, hence the
   set_first, which is why those entries have to erase to something
   nonempty.  That, plus "only the document sits at level 0", is the
   whole invariant. *)
Local Fixpoint stack_erase (stk : sect_state) : blocks :=
  match stk with
  | [] => []
  | [(_, _, acc)] => Undo.pass (rev acc)
  | (_, a, acc) :: outer =>
      (stack_erase outer ++ set_first (strip_id a) (Undo.pass (rev acc)))%list
  end.

(* The only thing erasure needs of the stack: every entry above the
   document's erases to something nonempty, so that set_first has a node
   to put the section's attributes back on.  True by construction: such
   an entry always starts with the heading that opened it. *)
Local Fixpoint sect_ok (stk : sect_state) : bool :=
  match stk with
  | [] => false
  | [_] => true
  | (_, _, acc) :: outer => (nonempty (Undo.pass (rev acc)) && sect_ok outer)%bool
  end.

Local Lemma stack_erase_cons :
  forall l a acc outer,
    outer <> [] ->
    stack_erase ((l, a, acc) :: outer)
    = (stack_erase outer ++ set_first (strip_id a) (Undo.pass (rev acc)))%list.
Proof. intros l a acc [|e outer] H; [contradiction|reflexivity]. Qed.

Local Lemma sect_ok_cons :
  forall l a acc outer,
    outer <> [] ->
    sect_ok ((l, a, acc) :: outer)
    = (nonempty (Undo.pass (rev acc)) && sect_ok outer)%bool.
Proof. intros l a acc [|e outer] H; [contradiction|reflexivity]. Qed.

Local Lemma sect_ok_nonnil : forall stk, sect_ok stk = true -> stk <> [].
Proof. intros [|e stk] H; [discriminate|congruence]. Qed.

Local Lemma close_ge_ok :
  forall stk lvl pending,
    sect_ok stk = true -> sect_ok (close_ge lvl pending stk) = true.
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros lvl pending Hs;
    [discriminate|].
  destruct outer as [|e outer']; [exact Hs|].
  rewrite sect_ok_cons in Hs by discriminate.
  apply andb_true_iff in Hs as [Hne Houter].
  rewrite close_ge_cons by discriminate. destruct (Nat.leb lvl l).
  - apply IH. exact Houter.
  - rewrite sect_ok_cons by discriminate.
    rewrite Houter, andb_true_r.
    rewrite rev_app_distr, Undo.pass_app.
    destruct (Undo.pass (rev acc)) as [|x r]; [discriminate|reflexivity].
Qed.

Local Lemma close_ge_erase :
  forall stk lvl pending,
    sect_ok stk = true ->
    stack_erase (close_ge lvl pending stk)
    = (stack_erase stk ++ Undo.pass (rev pending))%list.
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros lvl pending Hs;
    [discriminate|].
  destruct outer as [|e outer'].
  - rewrite close_ge_singleton. cbn [stack_erase].
    rewrite rev_app_distr, Undo.pass_app. reflexivity.
  - rewrite sect_ok_cons in Hs by discriminate.
    apply andb_true_iff in Hs as [Hne Houter].
    rewrite stack_erase_cons by discriminate.
    rewrite close_ge_cons by discriminate. destruct (Nat.leb lvl l).
    + rewrite (IH _ _ Houter).
      nosect. cbn [Undo.pass rev app]. rewrite app_nil_r.
      rewrite Undo.pass_section, rev_app_distr, Undo.pass_app.
      rewrite set_first_app by exact Hne.
      rewrite app_assoc. reflexivity.
    + rewrite stack_erase_cons by discriminate.
      rewrite rev_app_distr, Undo.pass_app.
      rewrite set_first_app by exact Hne.
      rewrite app_assoc. reflexivity.
Qed.

(* close_all always lands on the document entry alone, which is what
   lets sect_bottom read the answer off. *)
Local Lemma close_all_singleton :
  forall stk pending,
    stk <> [] -> exists l a acc, close_all pending stk = [(l, a, acc)].
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros pending H; [contradiction|].
  destruct outer as [|e outer'].
  - exists l, a, (pending ++ acc)%list. reflexivity.
  - rewrite close_all_cons by discriminate. apply IH. discriminate.
Qed.

Local Lemma close_all_erase :
  forall stk pending,
    sect_ok stk = true ->
    stack_erase (close_all pending stk)
    = (stack_erase stk ++ Undo.pass (rev pending))%list.
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros pending Hs; [discriminate|].
  destruct outer as [|e outer'].
  - cbn [close_all stack_erase].
    rewrite rev_app_distr, Undo.pass_app. reflexivity.
  - rewrite sect_ok_cons in Hs by discriminate.
    apply andb_true_iff in Hs as [Hne Houter].
    rewrite stack_erase_cons by discriminate.
    rewrite close_all_cons by discriminate.
    rewrite (IH _ Houter).
    nosect. cbn [Undo.pass rev app]. rewrite app_nil_r.
    rewrite Undo.pass_section, rev_app_distr, Undo.pass_app.
    rewrite set_first_app by exact Hne.
    rewrite app_assoc. reflexivity.
Qed.

Local Lemma sect_push_ok :
  forall stk n, sect_ok stk = true -> sect_ok (sect_push n stk) = true.
Proof.
  intros [|[[l a] acc] outer] n Hs; [discriminate|].
  cbn [sect_push]. destruct outer as [|e outer']; [exact Hs|].
  rewrite sect_ok_cons in Hs |- * by discriminate.
  apply andb_true_iff in Hs as [Hne Houter].
  rewrite Houter, andb_true_r.
  cbn [rev]. rewrite Undo.pass_app.
  destruct (Undo.pass (rev acc)) as [|x r]; [discriminate|reflexivity].
Qed.

Local Lemma sect_push_erase :
  forall stk n,
    sect_ok stk = true ->
    stack_erase (sect_push n stk) = (stack_erase stk ++ Undo.pass_node n)%list.
Proof.
  intros [|[[l a] acc] outer] n Hs; [discriminate|].
  cbn [sect_push]. destruct outer as [|e outer'].
  - cbn [stack_erase rev]. rewrite Undo.pass_app, Undo.pass_single.
    reflexivity.
  - rewrite sect_ok_cons in Hs by discriminate.
    apply andb_true_iff in Hs as [Hne _].
    rewrite !stack_erase_cons by discriminate.
    cbn [rev]. rewrite Undo.pass_app, Undo.pass_single.
    rewrite set_first_app by exact Hne.
    rewrite app_assoc. reflexivity.
Qed.

Local Lemma sect_step_ok :
  forall stk n, sect_ok stk = true -> sect_ok (sect_step stk n) = true.
Proof.
  intros stk [p a b] Hs. destruct b; try (apply sect_push_ok; exact Hs).
  cbn [sect_step].
  pose proof (close_ge_ok stk level [] Hs) as Hc.
  destruct (close_ge level [] stk) as [|e rest] eqn:E; [discriminate|].
  rewrite sect_ok_cons by discriminate.
  rewrite Hc, andb_true_r.
  (* a heading erases to exactly one block, so the entry is nonempty *)
  cbn [rev Undo.pass Undo.pass_block app nonempty]. reflexivity.
Qed.

Local Lemma sect_step_erase :
  forall stk n,
    sect_ok stk = true ->
    stack_erase (sect_step stk n) = (stack_erase stk ++ Undo.pass_node n)%list.
Proof.
  intros stk [p a b] Hs. destruct b; try (apply sect_push_erase; exact Hs).
  cbn [sect_step].
  pose proof (close_ge_ok stk level [] Hs) as Hc.
  pose proof (close_ge_erase stk level [] Hs) as He.
  destruct (close_ge level [] stk) as [|e rest] eqn:E; [discriminate|].
  rewrite stack_erase_cons by discriminate.
  rewrite He. cbn [rev Undo.pass]. rewrite app_nil_r.
  cbn [rev Undo.pass Undo.pass_node Undo.pass_block strip_id filter
       set_first app].
  reflexivity.
Qed.

Local Lemma fold_sect_step_ok :
  forall bs stk,
    sect_ok stk = true -> sect_ok (fold_left sect_step bs stk) = true.
Proof.
  induction bs as [|n rest IH]; intros stk Hs; [exact Hs|].
  cbn [fold_left]. apply IH. apply sect_step_ok. exact Hs.
Qed.

Local Lemma fold_sect_step_erase :
  forall bs stk,
    sect_ok stk = true ->
    stack_erase (fold_left sect_step bs stk)
    = (stack_erase stk ++ Undo.pass bs)%list.
Proof.
  induction bs as [|n rest IH]; intros stk Hs.
  - cbn [fold_left Undo.pass]. rewrite app_nil_r. reflexivity.
  - cbn [fold_left]. rewrite IH by (apply sect_step_ok; exact Hs).
    rewrite sect_step_erase by exact Hs.
    rewrite Undo.pass_cons, app_assoc. reflexivity.
Qed.

(** Sectioning is invisible to erasure: it only wraps, and Undo.pass
    unwraps exactly what it wrapped. *)
Lemma undo_sectionize :
  forall bs, Undo.pass (sectionize bs) = Undo.pass bs.
Proof.
  intros bs. unfold sectionize.
  pose proof (fold_sect_step_ok bs sect_init eq_refl) as Hok.
  pose proof (fold_sect_step_erase bs sect_init eq_refl) as Her.
  cbn [stack_erase rev Undo.pass] in Her.
  destruct (close_all_singleton _ [] (sect_ok_nonnil _ Hok)) as [l [a [acc E]]].
  pose proof (close_all_erase _ [] Hok) as Hc.
  rewrite E in Hc. cbn [stack_erase rev Undo.pass] in Hc.
  rewrite app_nil_r in Hc.
  rewrite E. cbn [sect_bottom].
  rewrite Hc, Her. reflexivity.
Qed.

(*
The theorem
-----------
*)

(** The whole-document pass adds only structure that erasure recovers:
    on input the pass has not already run on, undoing it is exact. *)
Theorem pass_erase :
  forall bs, Pristine.of_list bs = true -> Undo.pass (doc_blocks (doc_pass bs)) = bs.
Proof.
  intros bs H. unfold doc_pass.
  pose proof (pristine_notes_free bs H) as Hfree.
  pose proof (assign_ids_list_notes_free bs id_state_init Hfree) as Hfree'.
  destruct (Ids.of_list bs id_state_init) as [st bs'] eqn:E.
  cbn [snd] in Hfree'.
  rewrite (collect_notes_list_pristine bs' [] Hfree').
  cbn [doc_blocks]. rewrite undo_sectionize.
  replace bs' with (snd (Ids.of_list bs id_state_init))
    by (rewrite E; reflexivity).
  apply undo_assign_ids_list. exact H.
Qed.

(*
Erasure of the side tables
==========================

The document pass reads the tree and writes two side tables; erasing a
located tree's positions has to give the document the pass produces on
the erased tree.  The traversals below are the pos-blind half of that:
none of `Ids.of_block`, `Notes.of_block` or `Refs.of_block` reads a
position, so each commutes with `Erase.of_blocks` structurally.  The
sectionizer is the other half and is not here.

`erase_note_map` and `erase_doc` are the erasure of the two maps and of
the record; `doc_references`, `doc_auto_references` and
`doc_auto_identifiers` hold no nodes, so they are carried through.
*)

Local Lemma inlines_text_cons : forall (n : node inline) (rest : inlines),
  inlines_text (n :: rest)%list
  = (inline_text (node_contents n) ++ inlines_text rest)%string.
Proof.
  intros n rest. unfold inlines_text. cbn [map].
  destruct rest as [|y rest].
  - cbn [String.concat]. symmetry. apply append_empty_r.
  - reflexivity.
Qed.

Local Lemma inline_text_go : forall ns,
  (fix go (ns : list (node inline)) : string :=
     match ns with
     | [] => ""
     | Node _ _ x :: rest => (inline_text x ++ go rest)%string
     end) ns = inlines_text ns.
Proof.
  induction ns as [|[p a x] rest IH]; [reflexivity|].
  rewrite inlines_text_cons. cbn [inline_text]. rewrite IH. reflexivity.
Qed.

Local Lemma inline_text_erase : forall il,
  inline_text (Erase.of_inline il) = inline_text il.
Proof.
  induction il using inline_ind2 with
    (Q := fun ils =>
       (fix go (ns : list (node inline)) : string :=
          match ns with
          | [] => ""
          | Node _ _ x :: rest => (inline_text x ++ go rest)%string
          end) (Erase.of_inlines ils)
       = (fix go (ns : list (node inline)) : string :=
          match ns with
          | [] => ""
          | Node _ _ x :: rest => (inline_text x ++ go rest)%string
          end) ils);
    cbn [Erase.of_inline inline_text].
  all: try reflexivity.
  all: try (rewrite Erase.inline_children; assumption).
  - (* hcons *)
    rewrite Erase.inlines_cons. cbn [Erase.inode inline_text].
    congruence.
Qed.

Local Lemma inlines_text_erase : forall ils,
  inlines_text (Erase.of_inlines ils) = inlines_text ils.
Proof.
  induction ils as [|[p a x] rest IH]; [reflexivity|].
  rewrite Erase.inlines_cons. cbn [Erase.inode node_contents].
  rewrite inlines_text_cons. cbn [node_contents].
  rewrite inlines_text_cons. cbn [node_contents].
  rewrite IH, inline_text_erase. reflexivity.
Qed.

Local Definition erase_note_map (m : note_map) : note_map :=
  map (fun kv => (fst kv, Erase.of_blocks (snd kv))) m.

Definition erase_doc (d : doc) : doc :=
  {| doc_blocks := Erase.of_blocks (doc_blocks d)
   ; doc_footnotes := erase_note_map (doc_footnotes d)
   ; doc_references := doc_references d
   ; doc_auto_references := doc_auto_references d
   ; doc_auto_identifiers := doc_auto_identifiers d |}.

Local Lemma erase_note_map_alist_set : forall k v m,
  erase_note_map (alist_set k v m)
  = alist_set k (Erase.of_blocks v) (erase_note_map m).
Proof.
  intros k v m. induction m as [|[k' v'] rest IH];
    cbn [alist_set fst snd]; [reflexivity|].
  destruct (String.eqb k k') eqn:E.
  - cbn [erase_note_map map alist_set fst snd]. rewrite E. reflexivity.
  - cbn [erase_note_map map alist_set fst snd]. rewrite E.
    change ((k', Erase.of_blocks v') :: erase_note_map (alist_set k v rest)
            = (k', Erase.of_blocks v') :: alist_set k (Erase.of_blocks v)
                (erase_note_map rest)).
    rewrite IH. reflexivity.
Qed.

(* The item erasures as `Erase.of_block` spells them internally, bridged to
   the map form the statements below use. *)
Local Lemma erase_items_fix : forall its,
  (fix goitems (its : list blocks) : list blocks :=
     match its with
     | [] => []
     | item :: rest => Erase.of_blocks item :: goitems rest
     end) its = map Erase.of_blocks its.
Proof.
  induction its as [|it rest IH]; [reflexivity|].
  cbn [map]. rewrite IH. reflexivity.
Qed.

Local Lemma erase_def_items_fix : forall its,
  (fix godefs (its : list (inlines * blocks)) : list (inlines * blocks) :=
     match its with
     | [] => []
     | (term, item) :: rest =>
         (Erase.of_inlines term, Erase.of_blocks item) :: godefs rest
     end) its
  = map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv))) its.
Proof.
  induction its as [|[term it] rest IH]; [reflexivity|].
  cbn [map fst snd]. rewrite IH. reflexivity.
Qed.

Local Lemma erase_task_items_fix : forall its,
  (fix gotasks (its : list (task_status * blocks))
      : list (task_status * blocks) :=
     match its with
     | [] => []
     | (status, item) :: rest =>
         (status, Erase.of_blocks item) :: gotasks rest
     end) its
  = map (fun kv => (fst kv, Erase.of_blocks (snd kv))) its.
Proof.
  induction its as [|[status it] rest IH]; [reflexivity|].
  cbn [map fst snd]. rewrite IH. reflexivity.
Qed.

(*
Ids.of_block
*)

Local Lemma assign_ids_erase :
  forall b p a st,
    fst (Ids.of_block (Erase.of_block b) NoPos a st) = fst (Ids.of_block b p a st)
    /\ Erase.of_blocks [snd (Ids.of_block b p a st)]
       = [snd (Ids.of_block (Erase.of_block b) NoPos a st)].
Proof.
  intros b.
  induction b using block_ind2 with
    (Q := fun bs => forall st,
        fst (Ids.of_list (Erase.of_blocks bs) st) = fst (Ids.of_list bs st)
        /\ Erase.of_blocks (snd (Ids.of_list bs st))
           = snd (Ids.of_list (Erase.of_blocks bs) st))
    (R := fun its => forall st,
        fst (Ids.of_items (map Erase.of_blocks its) st)
          = fst (Ids.of_items its st)
        /\ map Erase.of_blocks (snd (Ids.of_items its st))
           = snd (Ids.of_items (map Erase.of_blocks its) st))
    (D := fun its => forall st,
        fst (Ids.of_def_items
               (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv)))
                  its) st)
          = fst (Ids.of_def_items its st)
        /\ map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv)))
               (snd (Ids.of_def_items its st))
           = snd (Ids.of_def_items
                    (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv)))
                       its) st))
    (K := fun its => forall st,
        fst (Ids.of_task_items
               (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) its) st)
          = fst (Ids.of_task_items its st)
        /\ map (fun kv => (fst kv, Erase.of_blocks (snd kv)))
               (snd (Ids.of_task_items its st))
           = snd (Ids.of_task_items
                    (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) its) st));
    intros; try solve [split; reflexivity].
  - (* Heading *)
    cbn [Erase.of_block Ids.of_block]. unfold assign_heading_id. rewrite inlines_text_erase.
    destruct (alist_lookup "id" a) as [v|] eqn:E;
      cbn [fst snd Erase.of_blocks Erase.of_block]; split; reflexivity.
  - (* BlockQuote *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite !Ids.quote.
    destruct (Ids.of_list (Erase.of_blocks bs) (register_id a st)) as [st2 bs2] eqn:E2.
    destruct (Ids.of_list bs (register_id a st)) as [st1 bs1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [Erase.of_blocks Erase.of_block]. fold Erase.of_blocks.
    rewrite He. reflexivity.
  - (* Div *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite !Ids.div.
    destruct (Ids.of_list (Erase.of_blocks bs) (register_id a st)) as [st2 bs2] eqn:E2.
    destruct (Ids.of_list bs (register_id a st)) as [st1 bs1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [Erase.of_blocks Erase.of_block]. fold Erase.of_blocks.
    rewrite He. reflexivity.
  - (* OrderedList *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite erase_items_fix.
    rewrite !Ids.olist.
    destruct (Ids.of_items (map Erase.of_blocks items) (register_id a st)) as [st2 its2] eqn:E2.
    destruct (Ids.of_items items (register_id a st)) as [st1 its1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [Erase.of_blocks Erase.of_block]. fold Erase.of_blocks.
    rewrite erase_items_fix. rewrite He. reflexivity.
  - (* BulletList *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite erase_items_fix.
    rewrite !Ids.blist.
    destruct (Ids.of_items (map Erase.of_blocks items) (register_id a st)) as [st2 its2] eqn:E2.
    destruct (Ids.of_items items (register_id a st)) as [st1 its1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [Erase.of_blocks Erase.of_block]. fold Erase.of_blocks.
    rewrite erase_items_fix. rewrite He. reflexivity.
  - (* TaskList *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite erase_task_items_fix.
    rewrite !Ids.tasklist.
    destruct (Ids.of_task_items
      (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) items)
      (register_id a st)) as [st2 its2] eqn:E2.
    destruct (Ids.of_task_items items (register_id a st)) as [st1 its1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [Erase.of_blocks Erase.of_block]. fold Erase.of_blocks.
    rewrite erase_task_items_fix. rewrite He. reflexivity.
  - (* DefinitionList *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite erase_def_items_fix.
    rewrite !Ids.deflist.
    destruct (Ids.of_def_items
      (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv))) items)
      (register_id a st)) as [st2 its2] eqn:E2.
    destruct (Ids.of_def_items items (register_id a st)) as [st1 its1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [Erase.of_blocks Erase.of_block]. fold Erase.of_blocks.
    rewrite erase_def_items_fix. rewrite He. reflexivity.
  - (* FootnoteDef *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite !Ids.foot.
    destruct (Ids.of_list (Erase.of_blocks bs) (register_id a st)) as [st2 bs2] eqn:E2.
    destruct (Ids.of_list bs (register_id a st)) as [st1 bs1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [Erase.of_blocks Erase.of_block]. fold Erase.of_blocks.
    rewrite He. reflexivity.
  - (* Keyed *)
    destruct b as [p' a' x]. cbn [Erase.of_block Ids.of_block].
    destruct (Ids.of_block x p' a' (register_id a st)) as [st1 n1] eqn:E1.
    destruct (Ids.of_block (Erase.of_block x) NoPos a' (register_id a st)) as [st2 n2] eqn:E2.
    pose proof (IHb (register_id a st)) as Hk.
    cbn [Erase.of_blocks Ids.of_list Ids.of_node] in Hk.
    rewrite E1, E2 in Hk. cbn [fst snd] in Hk.
    destruct Hk as [Hf He].
    destruct n1 as [np na nb].
    cbn [Erase.of_blocks Erase.of_block] in He. injection He as Hn2.
    split; [exact Hf|]. subst n2. reflexivity.
  - (* Q cons *)
    cbn [Erase.of_blocks Ids.of_list Ids.of_node].
    destruct (Ids.of_block b p a st) as [st1 n1] eqn:E1.
    destruct (Ids.of_block (Erase.of_block b) NoPos a st) as [st2 n2] eqn:E2.
    destruct (Ids.of_list rest st1) as [st3 rest1] eqn:E3.
    destruct (Ids.of_list (Erase.of_blocks rest) st2) as [st4 rest2] eqn:E4.
    destruct n1 as [np na nb].
    destruct (IHb p a st) as [Hf He]. rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
    destruct (IHb0 st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
    cbn [Erase.of_blocks Erase.of_block] in He. fold Erase.of_blocks in He. injection He as Hn2.
    split; [exact Hf2|].
    cbn [snd fst]. cbn [Erase.of_blocks Erase.of_block]. fold Erase.of_blocks.
    rewrite He2. subst n2. reflexivity.
  - (* R cons *)
    cbn [Ids.of_items map].
    destruct (Ids.of_list it st) as [st1 it1] eqn:E1.
    destruct (Ids.of_list (Erase.of_blocks it) st) as [st2 it2] eqn:E2.
    destruct (Ids.of_items rest st1) as [st3 rest1] eqn:E3.
    destruct (Ids.of_items (map Erase.of_blocks rest) st2) as [st4 rest2] eqn:E4.
    destruct (IHb st) as [Hf He]. rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
    destruct (IHb0 st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
    split; [exact Hf2|].
    cbn [snd fst map]. rewrite He, He2. reflexivity.
  - (* D cons *)
    cbn [Ids.of_def_items map fst snd].
    destruct (Ids.of_list it st) as [st1 it1] eqn:E1.
    destruct (Ids.of_list (Erase.of_blocks it) st) as [st2 it2] eqn:E2.
    destruct (Ids.of_def_items rest st1) as [st3 rest1] eqn:E3.
    destruct (Ids.of_def_items
      (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv))) rest)
      st2) as [st4 rest2] eqn:E4.
    destruct (IHb st) as [Hf He]. rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
    destruct (IHb0 st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
    split; [exact Hf2|].
    cbn [snd fst map fst snd]. rewrite He, He2. reflexivity.
  - (* K cons *)
    cbn [Ids.of_task_items map fst snd].
    destruct (Ids.of_list it st) as [st1 it1] eqn:E1.
    destruct (Ids.of_list (Erase.of_blocks it) st) as [st2 it2] eqn:E2.
    destruct (Ids.of_task_items rest st1) as [st3 rest1] eqn:E3.
    destruct (Ids.of_task_items
      (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) rest) st2) as [st4 rest2] eqn:E4.
    destruct (IHb st) as [Hf He]. rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
    destruct (IHb0 st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
    split; [exact Hf2|].
    cbn [snd fst map fst snd]. rewrite He, He2. reflexivity.
Qed.

Local Lemma assign_ids_list_erase : forall bs st,
  fst (Ids.of_list (Erase.of_blocks bs) st) = fst (Ids.of_list bs st)
  /\ Erase.of_blocks (snd (Ids.of_list bs st))
     = snd (Ids.of_list (Erase.of_blocks bs) st).
Proof.
  induction bs as [|[p a b] rest IH]; intros st; [split; reflexivity|].
  cbn [Erase.of_blocks Ids.of_list Ids.of_node].
  destruct (Ids.of_block b p a st) as [st1 n1] eqn:E1.
  destruct (Ids.of_block (Erase.of_block b) NoPos a st) as [st2 n2] eqn:E2.
  destruct (Ids.of_list rest st1) as [st3 rest1] eqn:E3.
  destruct (Ids.of_list (Erase.of_blocks rest) st2) as [st4 rest2] eqn:E4.
  destruct n1 as [np na nb].
  destruct (assign_ids_erase b p a st) as [Hf He].
  rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
  destruct (IH st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
  cbn [Erase.of_blocks Erase.of_block] in He. fold Erase.of_blocks in He. injection He as Hn2.
  split; [exact Hf2|].
  cbn [snd fst]. cbn [Erase.of_blocks Erase.of_block]. fold Erase.of_blocks.
  rewrite He2. subst n2. reflexivity.
Qed.

Local Lemma assign_ids_items_erase : forall its st,
  fst (Ids.of_items (map Erase.of_blocks its) st)
    = fst (Ids.of_items its st)
  /\ map Erase.of_blocks (snd (Ids.of_items its st))
     = snd (Ids.of_items (map Erase.of_blocks its) st).
Proof.
  induction its as [|it rest IH]; intros st; [split; reflexivity|].
  cbn [Ids.of_items map].
  destruct (Ids.of_list it st) as [st1 it1] eqn:E1.
  destruct (Ids.of_list (Erase.of_blocks it) st) as [st2 it2] eqn:E2.
  destruct (Ids.of_items rest st1) as [st3 rest1] eqn:E3.
  destruct (Ids.of_items (map Erase.of_blocks rest) st2) as [st4 rest2] eqn:E4.
  destruct (assign_ids_list_erase it st) as [Hf He].
  rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
  destruct (IH st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
  split; [exact Hf2|].
  cbn [snd fst map]. rewrite He, He2. reflexivity.
Qed.

Local Lemma assign_ids_def_items_erase : forall its st,
  fst (Ids.of_def_items
         (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv))) its)
         st)
    = fst (Ids.of_def_items its st)
  /\ map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv)))
       (snd (Ids.of_def_items its st))
     = snd (Ids.of_def_items
              (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv))) its)
              st).
Proof.
  induction its as [|[term it] rest IH]; intros st; [split; reflexivity|].
  cbn [Ids.of_def_items map fst snd].
  destruct (Ids.of_list it st) as [st1 it1] eqn:E1.
  destruct (Ids.of_list (Erase.of_blocks it) st) as [st2 it2] eqn:E2.
  destruct (Ids.of_def_items rest st1) as [st3 rest1] eqn:E3.
  destruct (Ids.of_def_items
    (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv))) rest)
    st2) as [st4 rest2] eqn:E4.
  destruct (assign_ids_list_erase it st) as [Hf He].
  rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
  destruct (IH st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
  split; [exact Hf2|].
  cbn [snd fst map fst snd]. rewrite He, He2. reflexivity.
Qed.

Local Lemma assign_ids_task_items_erase : forall its st,
  fst (Ids.of_task_items
         (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) its) st)
    = fst (Ids.of_task_items its st)
  /\ map (fun kv => (fst kv, Erase.of_blocks (snd kv)))
       (snd (Ids.of_task_items its st))
     = snd (Ids.of_task_items
              (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) its) st).
Proof.
  induction its as [|[chk it] rest IH]; intros st; [split; reflexivity|].
  cbn [Ids.of_task_items map fst snd].
  destruct (Ids.of_list it st) as [st1 it1] eqn:E1.
  destruct (Ids.of_list (Erase.of_blocks it) st) as [st2 it2] eqn:E2.
  destruct (Ids.of_task_items rest st1) as [st3 rest1] eqn:E3.
  destruct (Ids.of_task_items
    (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) rest) st2) as [st4 rest2] eqn:E4.
  destruct (assign_ids_list_erase it st) as [Hf He].
  rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
  destruct (IH st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
  split; [exact Hf2|].
  cbn [snd fst map fst snd]. rewrite He, He2. reflexivity.
Qed.

(*
Notes.of_block
*)

Local Lemma collect_notes_erase : forall b p a m,
  Notes.of_block (Erase.of_block b) NoPos a (erase_note_map m)
  = (erase_note_map (fst (Notes.of_block b p a m)),
     option_map (fun n => match n with
                          | Node _ a' x => Node NoPos a' (Erase.of_block x)
                          end)
       (snd (Notes.of_block b p a m))).
Proof.
  intros b.
  induction b using block_ind2 with
    (Q := fun ns => forall m,
        Notes.of_list (Erase.of_blocks ns) (erase_note_map m)
        = (erase_note_map (fst (Notes.of_list ns m)),
           Erase.of_blocks (snd (Notes.of_list ns m))))
    (R := fun its => forall m,
        Notes.of_items (map Erase.of_blocks its) (erase_note_map m)
        = (erase_note_map (fst (Notes.of_items its m)),
           map Erase.of_blocks (snd (Notes.of_items its m))))
    (D := fun its => forall m,
        Notes.of_def_items
          (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv))) its)
          (erase_note_map m)
        = (erase_note_map (fst (Notes.of_def_items its m)),
           map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv)))
             (snd (Notes.of_def_items its m))))
    (K := fun its => forall m,
        Notes.of_task_items
          (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) its)
          (erase_note_map m)
        = (erase_note_map (fst (Notes.of_task_items its m)),
           map (fun kv => (fst kv, Erase.of_blocks (snd kv)))
             (snd (Notes.of_task_items its m))));
    intros; try reflexivity.
  - (* BlockQuote *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite !Notes.quote.
    destruct (Notes.of_list (Erase.of_blocks bs) (erase_note_map m)) as [m2 bs2] eqn:E2.
    destruct (Notes.of_list bs m) as [m1 bs1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 bs2.
    cbn [Erase.of_block]. reflexivity.
  - (* Div *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite !Notes.div.
    destruct (Notes.of_list (Erase.of_blocks bs) (erase_note_map m)) as [m2 bs2] eqn:E2.
    destruct (Notes.of_list bs m) as [m1 bs1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 bs2.
    cbn [Erase.of_block]. reflexivity.
  - (* OrderedList *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite erase_items_fix.
    rewrite !Notes.olist.
    destruct (Notes.of_items (map Erase.of_blocks items) (erase_note_map m)) as [m2 its2] eqn:E2.
    destruct (Notes.of_items items m) as [m1 its1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 its2.
    cbn [Erase.of_block]. reflexivity.
  - (* BulletList *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite erase_items_fix.
    rewrite !Notes.blist.
    destruct (Notes.of_items (map Erase.of_blocks items) (erase_note_map m)) as [m2 its2] eqn:E2.
    destruct (Notes.of_items items m) as [m1 its1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 its2.
    cbn [Erase.of_block]. reflexivity.
  - (* TaskList *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite erase_task_items_fix.
    rewrite !Notes.tasklist.
    destruct (Notes.of_task_items
      (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) items)
      (erase_note_map m)) as [m2 its2] eqn:E2.
    destruct (Notes.of_task_items items m) as [m1 its1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 its2.
    cbn [snd fst option_map Erase.of_block]. rewrite erase_task_items_fix. reflexivity.
  - (* DefinitionList *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite erase_def_items_fix.
    rewrite !Notes.deflist.
    destruct (Notes.of_def_items
      (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv))) items)
      (erase_note_map m)) as [m2 its2] eqn:E2.
    destruct (Notes.of_def_items items m) as [m1 its1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 its2.
    cbn [snd fst option_map Erase.of_block]. rewrite erase_def_items_fix. reflexivity.
  - (* FootnoteDef *)
    cbn [Erase.of_block]. fold Erase.of_blocks. rewrite !Notes.foot.
    destruct (Notes.of_list (Erase.of_blocks bs) (erase_note_map m)) as [m2 bs2] eqn:E2.
    destruct (Notes.of_list bs m) as [m1 bs1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 bs2.
    rewrite <- erase_note_map_alist_set. reflexivity.
  - (* Keyed *)
    destruct b as [p' a' x]. cbn [Erase.of_block Notes.of_block].
    destruct (Notes.of_block x p' a' m) as [m1 o1] eqn:E1.
    destruct (Notes.of_block (Erase.of_block x) NoPos a' (erase_note_map m)) as [m2 o2] eqn:E2.
    pose proof (IHb m) as Hq.
    cbn [Erase.of_blocks Notes.of_list] in Hq.
    rewrite E1, E2 in Hq. cbn [fst snd] in Hq.
    destruct o1 as [n1|]; destruct o2 as [n2|]; cbn [fst snd] in Hq.
    + destruct n1 as [np na nb]. cbn [Erase.of_blocks Erase.of_block] in Hq.
      injection Hq as Hm Hn. subst m2 n2. reflexivity.
    + destruct n1 as [np na nb]. cbn [Erase.of_blocks Erase.of_block] in Hq.
      discriminate Hq.
    + discriminate Hq.
    + injection Hq as Hm. subst m2. reflexivity.
  - (* Q cons *)
    cbn [Erase.of_blocks Notes.of_list].
    destruct (Notes.of_block b p a m) as [m1 n1] eqn:E1.
    destruct (Notes.of_block (Erase.of_block b) NoPos a (erase_note_map m)) as [m0 n0] eqn:E0.
    pose proof (IHb p a m) as Hq. rewrite E1, E0 in Hq.
    destruct n1 as [n1|]; destruct n0 as [n0|];
      cbn [fst snd option_map] in Hq.
    + destruct n1 as [np na nb]. cbn [Erase.of_blocks Erase.of_block] in Hq.
      injection Hq as Hm Hn. subst m0 n0.
      destruct (Notes.of_list rest m1) as [m3 rest1] eqn:E3.
      destruct (Notes.of_list (Erase.of_blocks rest) (erase_note_map m1)) as [m4 rest2] eqn:E4.
      pose proof (IHb0 m1) as Hq2. rewrite E3, E4 in Hq2.
      injection Hq2 as Hm2 Hb2. subst m4 rest2. reflexivity.
    + discriminate Hq.
    + discriminate Hq.
    + injection Hq as Hm. subst m0.
      destruct (Notes.of_list rest m1) as [m3 rest1] eqn:E3.
      destruct (Notes.of_list (Erase.of_blocks rest) (erase_note_map m1)) as [m4 rest2] eqn:E4.
      pose proof (IHb0 m1) as Hq2. rewrite E3, E4 in Hq2.
      injection Hq2 as Hm2 Hb2. subst m4 rest2. reflexivity.
  - (* R cons *)
    cbn [Notes.of_items map].
    destruct (Notes.of_list it m) as [m1 it1] eqn:E1.
    destruct (Notes.of_list (Erase.of_blocks it) (erase_note_map m)) as [m2 it2] eqn:E2.
    destruct (Notes.of_items rest m1) as [m3 rest1] eqn:E3.
    destruct (Notes.of_items (map Erase.of_blocks rest) m2) as [m4 rest2] eqn:E4.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 it2.
    pose proof (IHb0 m1) as Hq2. rewrite E3, E4 in Hq2.
    injection Hq2 as Hm2 Hb2. subst m4 rest2.
    cbn [fst snd map]. reflexivity.
  - (* D cons *)
    cbn [Notes.of_def_items map fst snd].
    destruct (Notes.of_list it m) as [m1 it1] eqn:E1.
    destruct (Notes.of_list (Erase.of_blocks it) (erase_note_map m)) as [m2 it2] eqn:E2.
    destruct (Notes.of_def_items rest m1) as [m3 rest1] eqn:E3.
    destruct (Notes.of_def_items
      (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv))) rest)
      m2) as [m4 rest2] eqn:E4.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 it2.
    pose proof (IHb0 m1) as Hq2. rewrite E3, E4 in Hq2.
    injection Hq2 as Hm2 Hb2. subst m4 rest2.
    cbn [fst snd map]. reflexivity.
  - (* K cons *)
    cbn [Notes.of_task_items map fst snd].
    destruct (Notes.of_list it m) as [m1 it1] eqn:E1.
    destruct (Notes.of_list (Erase.of_blocks it) (erase_note_map m)) as [m2 it2] eqn:E2.
    destruct (Notes.of_task_items rest m1) as [m3 rest1] eqn:E3.
    destruct (Notes.of_task_items
      (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) rest) m2) as [m4 rest2] eqn:E4.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 it2.
    pose proof (IHb0 m1) as Hq2. rewrite E3, E4 in Hq2.
    injection Hq2 as Hm2 Hb2. subst m4 rest2.
    cbn [fst snd map]. reflexivity.
Qed.

Local Lemma collect_notes_list_erase : forall ns m,
  Notes.of_list (Erase.of_blocks ns) (erase_note_map m)
  = (erase_note_map (fst (Notes.of_list ns m)),
     Erase.of_blocks (snd (Notes.of_list ns m))).
Proof.
  induction ns as [|[p a b] rest IH]; intros m; [reflexivity|].
  cbn [Erase.of_blocks Notes.of_list].
  destruct (Notes.of_block b p a m) as [m1 n1] eqn:E1.
  destruct (Notes.of_block (Erase.of_block b) NoPos a (erase_note_map m)) as [m0 n0] eqn:E0.
  pose proof (collect_notes_erase b p a m) as Hq. rewrite E1, E0 in Hq.
  destruct n1 as [n1|]; destruct n0 as [n0|]; cbn [fst snd option_map] in Hq.
  + destruct n1 as [np na nb]. cbn [Erase.of_blocks Erase.of_block] in Hq.
    injection Hq as Hm Hn. subst m0 n0.
    destruct (Notes.of_list rest m1) as [m3 rest1] eqn:E3.
    destruct (Notes.of_list (Erase.of_blocks rest) (erase_note_map m1)) as [m4 rest2] eqn:E4.
    pose proof (IH m1) as Hq2. rewrite E3, E4 in Hq2.
    injection Hq2 as Hm2 Hb2. subst m4 rest2. reflexivity.
  + discriminate Hq.
  + discriminate Hq.
  + injection Hq as Hm. subst m0.
    destruct (Notes.of_list rest m1) as [m3 rest1] eqn:E3.
    destruct (Notes.of_list (Erase.of_blocks rest) (erase_note_map m1)) as [m4 rest2] eqn:E4.
    pose proof (IH m1) as Hq2. rewrite E3, E4 in Hq2.
    injection Hq2 as Hm2 Hb2. subst m4 rest2. reflexivity.
Qed.

Local Lemma collect_notes_items_erase : forall its m,
  Notes.of_items (map Erase.of_blocks its) (erase_note_map m)
  = (erase_note_map (fst (Notes.of_items its m)),
     map Erase.of_blocks (snd (Notes.of_items its m))).
Proof.
  induction its as [|it rest IH]; intros m; [reflexivity|].
  cbn [Notes.of_items map].
  destruct (Notes.of_list it m) as [m1 it1] eqn:E1.
  destruct (Notes.of_list (Erase.of_blocks it) (erase_note_map m)) as [m2 it2] eqn:E2.
  pose proof (collect_notes_list_erase it m) as Hq. rewrite E1, E2 in Hq.
  injection Hq as Hm Hb. subst m2 it2.
  destruct (Notes.of_items rest m1) as [m3 rest1] eqn:E3.
  destruct (Notes.of_items (map Erase.of_blocks rest) (erase_note_map m1)) as [m4 rest2] eqn:E4.
  pose proof (IH m1) as Hq2. rewrite E3, E4 in Hq2.
  injection Hq2 as Hm2 Hb2. subst m4 rest2.
  cbn [fst snd map]. reflexivity.
Qed.

Local Lemma collect_notes_def_items_erase : forall its m,
  Notes.of_def_items
    (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv))) its)
    (erase_note_map m)
  = (erase_note_map (fst (Notes.of_def_items its m)),
     map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv)))
       (snd (Notes.of_def_items its m))).
Proof.
  induction its as [|[term it] rest IH]; intros m; [reflexivity|].
  cbn [Notes.of_def_items map fst snd].
  destruct (Notes.of_list it m) as [m1 it1] eqn:E1.
  destruct (Notes.of_list (Erase.of_blocks it) (erase_note_map m)) as [m2 it2] eqn:E2.
  pose proof (collect_notes_list_erase it m) as Hq. rewrite E1, E2 in Hq.
  injection Hq as Hm Hb. subst m2 it2.
  destruct (Notes.of_def_items rest m1) as [m3 rest1] eqn:E3.
  destruct (Notes.of_def_items
    (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv))) rest)
    (erase_note_map m1)) as [m4 rest2] eqn:E4.
  pose proof (IH m1) as Hq2. rewrite E3, E4 in Hq2.
  injection Hq2 as Hm2 Hb2. subst m4 rest2.
  cbn [fst snd map fst snd]. reflexivity.
Qed.

Local Lemma collect_notes_task_items_erase : forall its m,
  Notes.of_task_items
    (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) its)
    (erase_note_map m)
  = (erase_note_map (fst (Notes.of_task_items its m)),
     map (fun kv => (fst kv, Erase.of_blocks (snd kv)))
       (snd (Notes.of_task_items its m))).
Proof.
  induction its as [|[chk it] rest IH]; intros m; [reflexivity|].
  cbn [Notes.of_task_items map fst snd].
  destruct (Notes.of_list it m) as [m1 it1] eqn:E1.
  destruct (Notes.of_list (Erase.of_blocks it) (erase_note_map m)) as [m2 it2] eqn:E2.
  pose proof (collect_notes_list_erase it m) as Hq. rewrite E1, E2 in Hq.
  injection Hq as Hm Hb. subst m2 it2.
  destruct (Notes.of_task_items rest m1) as [m3 rest1] eqn:E3.
  destruct (Notes.of_task_items
    (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) rest)
    (erase_note_map m1)) as [m4 rest2] eqn:E4.
  pose proof (IH m1) as Hq2. rewrite E3, E4 in Hq2.
  injection Hq2 as Hm2 Hb2. subst m4 rest2.
  cbn [fst snd map fst snd]. reflexivity.
Qed.

(*
Refs.of_block
*)

Local Lemma collect_refs_erase : forall b p a m,
  Refs.of_block (Erase.of_block b) NoPos a m = Refs.of_block b p a m.
Proof.
  intros b.
  induction b using block_ind2 with
    (Q := fun ns => forall m,
        Refs.of_list (Erase.of_blocks ns) m = Refs.of_list ns m)
    (R := fun its => forall m,
        fold_left (fun acc it => Refs.of_list it acc)
          (map Erase.of_blocks its) m
        = fold_left (fun acc it => Refs.of_list it acc) its m)
    (D := fun its => forall m,
        fold_left (fun acc kv => Refs.of_list (snd kv) acc)
          (map (fun kv => (Erase.of_inlines (fst kv), Erase.of_blocks (snd kv))) its) m
        = fold_left (fun acc kv => Refs.of_list (snd kv) acc) its m)
    (K := fun its => forall m,
        fold_left (fun acc kv => Refs.of_list (snd kv) acc)
          (map (fun kv => (fst kv, Erase.of_blocks (snd kv))) its) m
        = fold_left (fun acc kv => Refs.of_list (snd kv) acc) its m);
    intros; try (cbn [Erase.of_block Refs.of_block]; reflexivity).
  all: try solve [cbn [Erase.of_block Refs.of_block]; fold Erase.of_blocks;
                  rewrite !Refs.inner_go; exact (IHb m)].
  all: try solve [cbn [Erase.of_block Refs.of_block]; fold Erase.of_blocks;
                  rewrite erase_items_fix; rewrite !Refs.inner_goit;
                  exact (IHb m)].
  all: try solve [cbn [Erase.of_block Refs.of_block]; fold Erase.of_blocks;
                  rewrite erase_task_items_fix; rewrite !Refs.inner_got;
                  exact (IHb m)].
  all: try solve [cbn [Erase.of_block Refs.of_block]; fold Erase.of_blocks;
                  rewrite erase_def_items_fix; rewrite !Refs.inner_god;
                  exact (IHb m)].
  all: try solve [destruct b as [p' a' x]; cbn [Erase.of_block Refs.of_block];
                  pose proof (IHb m) as Hk;
                  cbn [Erase.of_blocks Refs.of_list] in Hk; exact Hk].
  - (* Q cons *)
    cbn [Erase.of_blocks Refs.of_list].
    rewrite (IHb p a m), IHb0. reflexivity.
  - (* R cons *)
    cbn [map fold_left].
    rewrite (IHb m), IHb0. reflexivity.
  - (* D cons *)
    cbn [map fst snd fold_left].
    rewrite (IHb m), IHb0. reflexivity.
  - (* K cons *)
    cbn [map fst snd fold_left].
    rewrite (IHb m), IHb0. reflexivity.
Qed.

Local Lemma collect_refs_list_erase : forall ns m,
  Refs.of_list (Erase.of_blocks ns) m = Refs.of_list ns m.
Proof.
  induction ns as [|[p a b] rest IH]; intros m; [reflexivity|].
  cbn [Erase.of_blocks Refs.of_list].
  rewrite (collect_refs_erase b p a m), IH. reflexivity.
Qed.
(* The sectionizer is the one part of the pass that reads a position:
   `section_node` takes the hull of the children it wraps.  Erasure of
   the stack is erasure of each entry's accumulator. *)
Local Fixpoint erase_sect (stk : sect_state) : sect_state :=
  match stk with
  | [] => []
  | (l, a, acc) :: rest => (l, a, Erase.of_blocks acc) :: erase_sect rest
  end.

Local Lemma section_node_pos : forall a bs,
  Erase.of_blocks [@section_node located_pos a bs]
  = [@section_node semantic_pos a (Erase.of_blocks bs)].
Proof.
  intros a bs. cbn [Erase.of_blocks Erase.of_block section_node]. fold Erase.of_blocks.
  rewrite section_node_nopos. reflexivity.
Qed.

Local Lemma close_ge_pos : forall lvl pending stk,
  erase_sect (@close_ge located_pos lvl pending stk) =
  @close_ge semantic_pos lvl (Erase.of_blocks pending) (erase_sect stk).
Proof.
  intros lvl pending stk. revert lvl pending.
  induction stk as [|[[l a] acc] outer IH]; intros lvl pending.
  - reflexivity.
  - destruct outer as [|e outer'].
    + rewrite (@close_ge_singleton located_pos). cbn [erase_sect].
      rewrite (@close_ge_singleton semantic_pos), Erase.blocks_app.
      reflexivity.
    + destruct e as [[l1 a1] acc1].
      rewrite (@close_ge_cons located_pos) by discriminate.
      cbn [erase_sect].
      rewrite (@close_ge_cons semantic_pos) by discriminate.
      destruct (Nat.leb lvl l).
      * rewrite IH, section_node_pos, Erase.blocks_rev, Erase.blocks_app.
        cbn [erase_sect]. reflexivity.
      * cbn [erase_sect]. rewrite Erase.blocks_app. reflexivity.
Qed.

Local Lemma close_all_pos : forall pending stk,
  erase_sect (@close_all located_pos pending stk) =
  @close_all semantic_pos (Erase.of_blocks pending) (erase_sect stk).
Proof.
  intros pending stk. revert pending.
  induction stk as [|[[l a] acc] outer IH]; intros pending.
  - reflexivity.
  - destruct outer as [|[[l1 a1] acc1] outer'].
    + cbn [close_all erase_sect]. rewrite Erase.blocks_app. reflexivity.
    + rewrite (@close_all_cons located_pos) by discriminate.
      cbn [erase_sect].
      rewrite (@close_all_cons semantic_pos) by discriminate.
      rewrite IH, section_node_pos.
      rewrite Erase.blocks_rev, Erase.blocks_app. reflexivity.
Qed.

Local Lemma sect_push_pos : forall p a b stk,
  erase_sect (sect_push (Node p a b) stk) =
  sect_push (Node NoPos a (Erase.of_block b)) (erase_sect stk).
Proof. intros p a b [|[[l a'] acc] outer]; reflexivity. Qed.

Local Lemma sect_step_pos : forall stk p a b,
  erase_sect (@sect_step located_pos stk (Node p a b)) =
  @sect_step semantic_pos (erase_sect stk) (Node NoPos a (Erase.of_block b)).
Proof.
  intros stk p a b. destruct b;
    try (cbn [sect_step]; apply sect_push_pos).
  (* a key's node has to be destructured before `Erase.of_block` reduces *)
  2: (destruct b; cbn [sect_step Erase.of_block]; apply sect_push_pos).
  cbn [sect_step erase_sect Erase.of_blocks Erase.of_block].
  rewrite close_ge_pos. reflexivity.
Qed.

Local Lemma fold_sect_step_pos : forall bs stk,
  erase_sect (fold_left (@sect_step located_pos) bs stk) =
  fold_left (@sect_step semantic_pos) (Erase.of_blocks bs) (erase_sect stk).
Proof.
  induction bs as [|[p a b] rest IH]; intros stk; [reflexivity|].
  cbn [fold_left Erase.of_blocks]. rewrite IH, sect_step_pos. reflexivity.
Qed.

Local Lemma sect_bottom_pos : forall stk,
  Erase.of_blocks (sect_bottom stk) = sect_bottom (erase_sect stk).
Proof.
  induction stk as [|[[l a] acc] outer IH]; [reflexivity|].
  destruct outer as [|[[l1 a1] acc1] outer'].
  - cbn [sect_bottom erase_sect]. apply Erase.blocks_rev.
  - cbn [erase_sect]. cbn [sect_bottom]. cbn [erase_sect] in IH. exact IH.
Qed.

Local Lemma sectionize_erase : forall bs,
  Erase.of_blocks (@sectionize located_pos bs) =
  @sectionize semantic_pos (Erase.of_blocks bs).
Proof.
  intros bs. unfold sectionize.
  rewrite sect_bottom_pos, close_all_pos, fold_sect_step_pos.
  reflexivity.
Qed.

(* The pass as a whole.  Three of its four components never read a
   position, so erasing the blocks they are given commutes with each;
   the fourth is the sectionizer above. *)
Local Lemma doc_pass_erase : forall bs,
  erase_doc (@doc_pass located_pos bs) =
  @doc_pass semantic_pos (Erase.of_blocks bs).
Proof.
  intros bs. unfold doc_pass.
  destruct (Ids.of_list bs id_state_init) as [st tagged] eqn:E.
  destruct (Ids.of_list (Erase.of_blocks bs) id_state_init)
    as [st' tagged'] eqn:E'.
  destruct (assign_ids_list_erase bs id_state_init) as [Hst Htagged].
  rewrite E, E' in Hst, Htagged. cbn [fst snd] in Hst, Htagged.
  subst st' tagged'.
  destruct (Notes.of_list tagged []) as [notes visible] eqn:En.
  pose proof (collect_notes_list_erase tagged []) as Hn.
  cbn [erase_note_map map] in Hn. rewrite En in Hn. cbn [fst snd] in Hn.
  rewrite Hn. unfold erase_doc.
  cbn [doc_blocks doc_footnotes doc_references doc_auto_references
    doc_auto_identifiers].
  rewrite sectionize_erase, collect_refs_list_erase. reflexivity.
Qed.

(* The located document is the semantic one with positions on it. *)
Theorem parse_doc_located_erase : forall s,
  erase_doc (parse_doc_located s) = @parse_doc T K semantic_pos s.
Proof.
  intros s. unfold parse_doc_located, parse_doc.
  rewrite doc_pass_erase, parse_blocks_located_erase. reflexivity.
Qed.

(*
Examples
========

Each is a case from djot.js/test/headings.test, checked at the AST level.
*)

End WithTable.

Example section_simple :
  doc_blocks (parse_doc "## Heading")
  = [Node NoPos [("id", "Heading")]
       (Section [mk (Heading 2 [mk (Str "Heading")])])].
Proof. reflexivity. Qed.

Example section_nested :
  doc_blocks (parse_doc "## Heading
### Next level")
  = [Node NoPos [("id", "Heading")]
       (Section [ mk (Heading 2 [mk (Str "Heading")])
                ; Node NoPos [("id", "Next-level")]
                    (Section [mk (Heading 3 [mk (Str "Next level")])]) ])].
Proof. reflexivity. Qed.

Example section_siblings :
  doc_blocks (parse_doc "# Heading

# another")
  = [ Node NoPos [("id", "Heading")]
        (Section [mk (Heading 1 [mk (Str "Heading")])])
    ; Node NoPos [("id", "another")]
        (Section [mk (Heading 1 [mk (Str "another")])]) ].
Proof. reflexivity. Qed.

(* A multi-line heading's id joins its lines: the SoftBreak contributes a
   newline, which is an id separator. *)
Example section_multiline_id :
  doc_auto_identifiers (parse_doc "# Heading
continued") = ["Heading-continued"].
Proof. reflexivity. Qed.

(* An empty heading has an empty base, so the disambiguator starts at 1. *)
Example section_empty_id :
  doc_auto_identifiers (parse_doc "##") = ["s-1"].
Proof. reflexivity. Qed.

Example section_duplicate_ids :
  doc_auto_identifiers (parse_doc "# Foo bar

## Foo  bar") = ["Foo-bar"; "Foo-bar-1"].
Proof. reflexivity. Qed.

(* Explicit ids occupy the same rendered fragment namespace as automatic
   heading ids.  They remain distinct for editing: only the former came
   from stable source identity. *)
Example explicit_id_displaces_auto_id :
  doc_auto_identifiers (parse_doc "{#x}
a

# x") = ["x"; "x-1"].
Proof. reflexivity. Qed.

(* Sections are top-level only: inside a quote the heading keeps its id. *)
Example quote_heading_unsectioned :
  doc_blocks (parse_doc "> # Heading")
  = [mk (BlockQuote
           [Node NoPos [("id", "Heading")]
              (Heading 1 [mk (Str "Heading")])])].
Proof. reflexivity. Qed.

(* The map keys by normalized label, and a repeated label keeps the first
   definition's position with the last one's value. *)
Example reference_map_last_wins :
  doc_references (parse_doc "[a]: u

[b]: w

[a]: v")
  = [("a", ("v", [])); ("b", ("w", []))].
Proof. reflexivity. Qed.

(* A definition inside a container still registers with the document. *)
Example reference_map_nested :
  doc_references (parse_doc "> [q]: u

- [l]: v")
  = [("q", ("u", [])); ("l", ("v", []))].
Proof. reflexivity. Qed.

(* Block attributes on the definition ride into the map, where the HTML
   renderer puts them on the link. *)
Example reference_map_attributes :
  doc_references (parse_doc "{#x}
[a]: u")
  = [("a", ("u", [("id", "x")]))].
Proof. reflexivity. Qed.

(* An empty raw label is dropped before normalization, so `[]: u` defines
   nothing while `[ ]: u`, whose normalized label is also empty, does. *)
Example reference_map_empty_label_dropped :
  doc_references (parse_doc "[]: u") = [].
Proof. reflexivity. Qed.

Example reference_map_blank_label_kept :
  doc_references (parse_doc "[ ]: u") = [("", ("u", []))].
Proof. reflexivity. Qed.

Example footnote_map_last_wins :
  doc_footnotes (parse_doc "[^a]: one

[^a]: two")
  = [("a", [mk (Para [mk (Str "two")])])].
Proof. reflexivity. Qed.

Example footnote_map_normalized_label :
  doc_footnotes (parse_doc "[^A  B]: one

[^A B]: two")
  = [("A B", [mk (Para [mk (Str "two")])])].
Proof. reflexivity. Qed.

Example footnote_map_nested_close_order :
  doc_footnotes (parse_doc "[^a]: outer

  [^b]: inner")
  = [ ("b", [mk (Para [mk (Str "inner")])])
    ; ("a", [mk (Para [mk (Str "outer")])]) ].
Proof. reflexivity. Qed.

Example footnote_removed_inside_quote :
  doc_blocks (parse_doc "> [^a]: note") = [mk (BlockQuote [])].
Proof. reflexivity. Qed.

Example footnote_heading_shares_identifier_pass :
  doc_auto_identifiers (parse_doc "[^a]: # Heading

# After") = ["Heading"; "After"].
Proof. reflexivity. Qed.

Example implicit_heading_reference :
  doc_auto_references (parse_doc "# Introduction")
  = [("Introduction", ("#Introduction", []))].
Proof. reflexivity. Qed.

(* An explicit id suppresses the auto-*identifier*, not the reference:
   the label is still the heading's text, and it points at the spec's
   id. *)
Example implicit_heading_reference_explicit_id :
  doc_auto_references (parse_doc "{#foo}
# Introduction")
  = [("Introduction", ("#foo", []))].
Proof. reflexivity. Qed.

(* Blocks before the first heading stay at the document level. *)
Example section_preamble :
  doc_blocks (parse_doc "intro

# h")
  = [ mk (Para [mk (Str "intro")])
    ; Node NoPos [("id", "h")] (Section [mk (Heading 1 [mk (Str "h")])]) ].
Proof. reflexivity. Qed.

(* Closing two levels at once: the h3's section nests inside the h2's,
   and both close when the h1 arrives. *)
Example section_close_multiple :
  doc_blocks (parse_doc "## a

### b

# c")
  = [ Node NoPos [("id", "a")]
        (Section [ mk (Heading 2 [mk (Str "a")])
                 ; Node NoPos [("id", "b")]
                     (Section [mk (Heading 3 [mk (Str "b")])]) ])
    ; Node NoPos [("id", "c")]
        (Section [mk (Heading 1 [mk (Str "c")])]) ].
Proof. reflexivity. Qed.
