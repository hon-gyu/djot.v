(* ai-disclosure: autonomous *)

(** * Addressing a block by its explicit id

   An editor holding a `list cblock` needs to name one block and come
   back to it after an unrelated edit.  Three answers are possible and
   only one survives: a position in the list moves, a source span moves,
   and an explicit `{#id}` does not.  Automatic identifiers are not
   addresses either -- `Document.doc_pass` renumbers a duplicate heading
   id, so inserting a block can rename one that did not change.

   So an address is a `CId` wrapper, and everything here is about the
   two scopes it comes in.  `top_level_ids` drives replacement, and
   matches `Roundtrip.block_replace`'s `pre ++ block :: post` boundary.
   `all_explicit_ids` descends containers and is what page-wide
   uniqueness and link checking read.

   Parsing accepts duplicate ids -- both oracles do, and `cb_ok` follows
   them -- so uniqueness is a condition on the operations rather than on
   the document: `resolve_top_id` reports absence and ambiguity rather
   than choosing the first occurrence, since choosing would make
   inserting a duplicate silently retarget the next edit. *)

From Stdlib Require Import String Ascii List Bool Lia.
From DjotV Require Import Strings Line Ast Parser Document Render Roundtrip.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
The two scopes
==============
*)

Definition top_id (cb : cblock) : option string :=
  match cb with CId i _ => Some i | _ => None end.

Definition top_level_ids (cbs : list cblock) : list string :=
  flat_map (fun cb => match top_id cb with Some i => [i] | None => [] end) cbs.

(* Every explicit id on the page, containers included.  A quote's
   contents and a list item's blocks are `list cblock`, so the recursion
   is the same three-way one `cb_ok` uses. *)
Fixpoint all_explicit_ids (cb : cblock) : list string :=
  match cb with
  | CId i inner => i :: all_explicit_ids inner
  | CKey _ inner => all_explicit_ids inner
  | CQuote inner | CDiv inner => flat_map all_explicit_ids inner
  | CList _ _ items => flat_map (flat_map all_explicit_ids) items
  | _ => []
  end.

Definition page_ids (cbs : list cblock) : list string :=
  flat_map all_explicit_ids cbs.

Fixpoint no_dups (xs : list string) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (existsb (String.eqb x) rest) && no_dups rest
  end.

(* The condition an addressed operation asks of its scope.  Not a
   condition on parsing: a document with two `{#x}` specs is Djot, and
   it is exactly the document no id-addressed edit may touch. *)
Definition explicit_ids_unique (cbs : list cblock) : bool :=
  no_dups (top_level_ids cbs).

Definition page_ids_unique (cbs : list cblock) : bool :=
  no_dups (page_ids cbs).

(*
Resolution
==========
*)

(* Every way the name could be read, as splits of the input.  A list
   rather than an option: the two failures an editor must not confuse
   are "no such block" and "more than one", and both are visible here. *)
Fixpoint find_top_ids (i : string) (cbs : list cblock)
  : list (list cblock * cblock * list cblock) :=
  match cbs with
  | [] => []
  | cb :: rest =>
      let below :=
        map (fun s => let '(pre, c, post) := s in (cb :: pre, c, post))
            (find_top_ids i rest) in
      match top_id cb with
      | Some j => if String.eqb i j then ([], cb, rest) :: below else below
      | None => below
      end
  end.

Inductive address_error : Type :=
  | AddrMissing
  | AddrAmbiguous (n : nat).

Definition resolve_top_id (i : string) (cbs : list cblock)
  : sum (list cblock * cblock * list cblock) address_error :=
  match find_top_ids i cbs with
  | [s] => inl s
  | [] => inr AddrMissing
  | ss => inr (AddrAmbiguous (length ss))
  end.

(* Replacing the *body*: the wrapper is rebuilt, so the address an
   editor used survives the edit that used it. *)
Definition replace_at_id (i : string) (body : cblock) (cbs : list cblock)
  : sum (list cblock) address_error :=
  match resolve_top_id i cbs with
  | inl (pre, _, post) => inl (pre ++ CId i body :: post)%list
  | inr e => inr e
  end.

(*
What a resolved address means
=============================
*)

(* Every candidate a search returns reconstructs the document, so the
   caller can rebuild it without an index and without trusting the
   search: the split *is* the answer. *)
Lemma find_top_ids_sound :
  forall i cbs pre c post,
    In (pre, c, post) (find_top_ids i cbs) ->
    cbs = (pre ++ c :: post)%list /\ top_id c = Some i.
Proof.
  induction cbs as [|cb rest IH]; intros pre c post H; [destruct H|].
  cbn [find_top_ids] in H.
  assert (Hbelow : forall s,
             In s (map (fun s => let '(p, x, q) := s in (cb :: p, x, q))
                     (find_top_ids i rest)) ->
             let '(p, x, q) := s in
             (cb :: rest)%list = (p ++ x :: q)%list /\ top_id x = Some i).
  { intros [[p x] q] Hin. apply in_map_iff in Hin as [[[p0 x0] q0] [Heq Hin0]].
    injection Heq as <- <- <-.
    destruct (IH p0 x0 q0 Hin0) as [Hsplit Hid].
    split; [cbn; rewrite <- Hsplit; reflexivity | exact Hid]. }
  destruct (top_id cb) as [j|] eqn:Ej.
  - destruct (String.eqb i j) eqn:Eij.
    + destruct H as [H|H].
      * injection H as <- <- <-. apply String.eqb_eq in Eij.
        split; [reflexivity | rewrite Ej, Eij; reflexivity].
      * exact (Hbelow _ H).
    + exact (Hbelow _ H).
  - exact (Hbelow _ H).
Qed.

Lemma find_top_ids_absent :
  forall i cbs, existsb (String.eqb i) (top_level_ids cbs) = false ->
    find_top_ids i cbs = [].
Proof.
  induction cbs as [|cb rest IH]; intros H; [reflexivity|].
  cbn [top_level_ids flat_map] in H.
  destruct (top_id cb) as [j|] eqn:Ej.
  - cbn [app existsb] in H. apply orb_false_iff in H as [Hij Hrest].
    cbn [find_top_ids]. rewrite Ej, Hij, (IH Hrest). reflexivity.
  - cbn [app] in H. cbn [find_top_ids]. rewrite Ej, (IH H). reflexivity.
Qed.

(* Uniqueness is what turns the search into a lookup: a name that occurs
   at all occurs once, so the ambiguous answer is unreachable and no
   caller has to decide which occurrence was meant. *)
Lemma find_top_ids_unique :
  forall i cbs,
    explicit_ids_unique cbs = true ->
    existsb (String.eqb i) (top_level_ids cbs) = true ->
    exists pre c post, find_top_ids i cbs = [(pre, c, post)].
Proof.
  induction cbs as [|cb rest IH]; intros Hu Hin; [discriminate Hin|].
  unfold explicit_ids_unique in Hu. cbn [top_level_ids flat_map] in Hu, Hin.
  destruct (top_id cb) as [j|] eqn:Ej.
  - cbn [app no_dups existsb] in Hu, Hin.
    apply andb_true_iff in Hu as [Hj Hrest].
    apply negb_true_iff in Hj.
    destruct (String.eqb i j) eqn:Eij.
    + apply String.eqb_eq in Eij. subst j.
      cbn [find_top_ids]. rewrite Ej, String.eqb_refl.
      rewrite (find_top_ids_absent i rest Hj). cbn [map].
      exists [], cb, rest. reflexivity.
    + cbn [orb] in Hin.
      destruct (IH Hrest Hin) as [pre [c [post Hfind]]].
      cbn [find_top_ids]. rewrite Ej, Eij, Hfind. cbn [map].
      exists (cb :: pre), c, post. reflexivity.
  - cbn [app] in Hu, Hin.
    destruct (IH Hu Hin) as [pre [c [post Hfind]]].
    cbn [find_top_ids]. rewrite Ej, Hfind. cbn [map].
    exists (cb :: pre), c, post. reflexivity.
Qed.

(** A resolved address is a split of the document at a block carrying
    that id.  Nothing weaker is needed downstream: `Roundtrip.block_replace`
    takes exactly this shape. *)
Theorem resolve_top_id_split :
  forall i cbs pre c post,
    resolve_top_id i cbs = inl (pre, c, post) ->
    cbs = (pre ++ c :: post)%list /\ top_id c = Some i.
Proof.
  intros i cbs pre c post H. unfold resolve_top_id in H.
  destruct (find_top_ids i cbs) as [|s [|s' more]] eqn:Efind; try discriminate H.
  injection H as H. subst s.
  apply (find_top_ids_sound i cbs). rewrite Efind. left. reflexivity.
Qed.

Theorem resolve_top_id_missing :
  forall i cbs, existsb (String.eqb i) (top_level_ids cbs) = false ->
    resolve_top_id i cbs = inr AddrMissing.
Proof.
  intros i cbs H. unfold resolve_top_id.
  rewrite (find_top_ids_absent i cbs H). reflexivity.
Qed.

(** And under uniqueness a present id resolves, so the two error
    constructors report the two things that are actually wrong with a
    document rather than a limitation of the search. *)
Theorem resolve_top_id_present :
  forall i cbs,
    explicit_ids_unique cbs = true ->
    existsb (String.eqb i) (top_level_ids cbs) = true ->
    exists pre c post,
      resolve_top_id i cbs = inl (pre, c, post)
      /\ cbs = (pre ++ c :: post)%list /\ top_id c = Some i.
Proof.
  intros i cbs Hu Hin.
  destruct (find_top_ids_unique i cbs Hu Hin) as [pre [c [post Hfind]]].
  exists pre, c, post.
  assert (Hres : resolve_top_id i cbs = inl (pre, c, post))
    by (unfold resolve_top_id; rewrite Hfind; reflexivity).
  split; [exact Hres|].
  apply (resolve_top_id_split i cbs), Hres.
Qed.

(*
Replacement
===========
*)

Theorem replace_at_id_split :
  forall i body cbs cbs',
    replace_at_id i body cbs = inl cbs' ->
    exists pre c post,
      cbs = (pre ++ c :: post)%list /\ top_id c = Some i
      /\ cbs' = (pre ++ CId i body :: post)%list.
Proof.
  intros i body cbs cbs' H. unfold replace_at_id in H.
  destruct (resolve_top_id i cbs) as [[[pre c] post]|e] eqn:Eres;
    [|discriminate H].
  injection H as <-.
  destruct (resolve_top_id_split i cbs pre c post Eres) as [Hsplit Hid].
  exists pre, c, post. repeat split; assumption.
Qed.

(** The edit does not spend the address it used: the wrapper is rebuilt,
    so the next edit finds the block where this one left it. *)
Theorem replace_at_id_ids :
  forall i body cbs cbs',
    replace_at_id i body cbs = inl cbs' ->
    top_level_ids cbs' = top_level_ids cbs.
Proof.
  intros i body cbs cbs' H.
  destruct (replace_at_id_split i body cbs cbs' H)
    as [pre [c [post (-> & Hid & ->)]]].
  unfold top_level_ids. rewrite !flat_map_app. cbn [flat_map].
  rewrite Hid. reflexivity.
Qed.

(** And the parse of the edited document is the old blocks either side of
    the new one, named through the same `map cb_ast` they had before --
    `Roundtrip.block_replace` at an address.  Canonicality is asked of the
    document coming out, since that is the one being rendered. *)
Theorem replace_at_id_parse :
  forall i body cbs cbs',
    replace_at_id i body cbs = inl cbs' ->
    cblocks_ok cbs' = true ->
    exists pre post,
      cbs' = (pre ++ CId i body :: post)%list
      /\ parse_blocks (render_djot (blocks_of_cblocks cbs'))
         = (map cb_ast pre ++ cb_ast (CId i body) :: map cb_ast post)%list.
Proof.
  intros i body cbs cbs' H Hok.
  destruct (replace_at_id_split i body cbs cbs' H)
    as [pre [c [post (_ & _ & ->)]]].
  exists pre, post. split; [reflexivity|].
  apply block_replace, Hok.
Qed.

(*
Generated blocks
================

A block a build step writes rather than an author: a table of contents,
an index, a list of backlinks.  It is a *section of a projection* -- the
view says what it is made of, the id says where it goes -- and what
makes a build a function rather than an iteration is that installing it
once is enough.
*)

Lemma find_top_ids_app :
  forall i xs ys,
    find_top_ids i (xs ++ ys)%list
    = (map (fun s => let '(p, c, q) := s in (p, c, (q ++ ys)%list))
           (find_top_ids i xs)
       ++ map (fun s => let '(p, c, q) := s in ((xs ++ p)%list, c, q))
              (find_top_ids i ys))%list.
Proof.
  induction xs as [|x xs IH]; intros ys.
  - cbn [app find_top_ids map].
    induction (find_top_ids i ys) as [|[[p c] q] more IHm]; [reflexivity|].
    cbn [map]. rewrite <- IHm. reflexivity.
  - cbn [app find_top_ids]. rewrite IH, !map_app, !map_map.
    destruct (top_id x) as [j|] eqn:Ej; [destruct (String.eqb i j) eqn:Eij|];
      cbn [map]; rewrite ?map_app, ?map_map; cbn [app];
      f_equal; try (apply map_ext; intros [[p c] q]; reflexivity).
    all: f_equal; apply map_ext; intros [[p c] q]; reflexivity.
Qed.

(* A name that resolves occurs nowhere else, so neither side of the
   split can hide a second occurrence.  This is what survives the edit:
   the id the caller used still resolves in the document the edit
   produced. *)
Lemma find_top_ids_singleton_parts :
  forall i pre c post,
    top_id c = Some i ->
    find_top_ids i (pre ++ c :: post)%list = [(pre, c, post)] ->
    find_top_ids i pre = [] /\ find_top_ids i post = [].
Proof.
  intros i pre c post Hid H.
  rewrite find_top_ids_app in H.
  cbn [find_top_ids] in H. rewrite Hid, String.eqb_refl in H.
  pose proof (f_equal (@length _) H) as Hlen.
  rewrite length_app, !length_map in Hlen. cbn [length] in Hlen.
  rewrite length_map in Hlen.
  split; apply length_zero_iff_nil; lia.
Qed.

Lemma find_top_ids_replace :
  forall i body pre post,
    find_top_ids i pre = [] -> find_top_ids i post = [] ->
    find_top_ids i (pre ++ CId i body :: post)%list = [(pre, CId i body, post)].
Proof.
  intros i body pre post Hpre Hpost.
  rewrite find_top_ids_app, Hpre. cbn [map app find_top_ids top_id].
  rewrite String.eqb_refl, Hpost. cbn [map app]. rewrite app_nil_r. reflexivity.
Qed.

(** Writing the same body twice is writing it once.  The wrapper is what
    makes this true: the edit leaves the address it used exactly where it
    found it, so the second edit resolves to the same split. *)
Theorem replace_at_id_idem :
  forall i body cbs cbs',
    replace_at_id i body cbs = inl cbs' ->
    replace_at_id i body cbs' = inl cbs'.
Proof.
  intros i body cbs cbs' H.
  unfold replace_at_id in H.
  destruct (resolve_top_id i cbs) as [[[pre c] post]|e] eqn:Eres;
    [|discriminate H].
  injection H as <-.
  destruct (resolve_top_id_split i cbs pre c post Eres) as [Hsplit Hid].
  unfold resolve_top_id in Eres. rewrite Hsplit in Eres.
  destruct (find_top_ids i (pre ++ c :: post)) as [|s [|s' more]] eqn:Efind;
    try discriminate Eres.
  injection Eres as Eres. subst s.
  destruct (find_top_ids_singleton_parts i pre c post Hid Efind) as [Hp Hq].
  unfold replace_at_id, resolve_top_id.
  rewrite (find_top_ids_replace i body pre post Hp Hq). reflexivity.
Qed.

(* A generated block, as the three things a build step has to name: where
   it goes, what it is made of, and how the one becomes the other.  The
   view is a projection of the whole document, since that is what a table
   of contents reads. *)
Record derived (V : Type) : Type := Derived {
  d_id : string;
  d_view : list cblock -> V;
  d_make : V -> cblock }.

(* Global, since the record is what a caller writes and none of it
   depends on the section's table. *)
#[global] Arguments Derived {V} d_id d_view d_make.
#[global] Arguments d_id {V} d.
#[global] Arguments d_view {V} d.
#[global] Arguments d_make {V} d.

Definition refresh {V : Type} (D : derived V) (cbs : list cblock)
  : sum (list cblock) address_error :=
  replace_at_id (d_id D) (d_make D (d_view D cbs)) cbs.

(** One-step convergence, which is what lets a build run the step once
    rather than to a fixed point.  The hypothesis is the whole content of
    it, and it is decidable by running the view again -- so a build
    checks it rather than assuming it.  `refresh_view_can_move` below is
    a document where it fails. *)
Theorem refresh_stable :
  forall (V : Type) (D : derived V) cbs cbs',
    refresh D cbs = inl cbs' ->
    d_view D cbs' = d_view D cbs ->
    refresh D cbs' = inl cbs'.
Proof.
  intros V D cbs cbs' H Hview. unfold refresh in H |- *.
  rewrite Hview. apply (replace_at_id_idem _ _ cbs), H.
Qed.

(* And a refresh spends no addresses, its own included, so a document
   with several generated blocks can be refreshed in any order. *)
Theorem refresh_ids :
  forall (V : Type) (D : derived V) cbs cbs',
    refresh D cbs = inl cbs' -> top_level_ids cbs' = top_level_ids cbs.
Proof.
  intros V D cbs cbs' H. unfold refresh in H.
  apply (replace_at_id_ids _ _ _ _ H).
Qed.

End WithTable.

(*
Worked examples
===============
*)

Definition named_doc : list cblock :=
  [ cpara ["intro"] ; CId "x" (cpara ["a"]) ; cpara ["outro"] ].

Example named_doc_ok : cblocks_ok named_doc = true.
Proof. reflexivity. Qed.

Example named_doc_render :
  render_djot (blocks_of_cblocks named_doc)
  = ("intro" ++ nl ++ nl ++ "{#x}" ++ nl ++ "a" ++ nl ++ nl ++ "outro")%string.
Proof. reflexivity. Qed.

(* The edit an editor runs, and the address it leaves behind. *)
Example named_doc_replace :
  replace_at_id "x" (CHeading 1 [[CIStr "h"]]) named_doc
  = inl [ cpara ["intro"] ; CId "x" (CHeading 1 [[CIStr "h"]])
        ; cpara ["outro"] ].
Proof. reflexivity. Qed.

Example named_doc_replace_roundtrip :
  let edited := [ cpara ["intro"] ; CId "x" (CHeading 1 [[CIStr "h"]])
                ; cpara ["outro"] ] in
  parse_blocks (render_djot (blocks_of_cblocks edited))
  = blocks_of_cblocks edited.
Proof. apply roundtrip_blocks; reflexivity. Qed.

(* The two failures, kept apart.  A duplicate id is a parseable document
   that no addressed edit may touch, and the count says how bad it is;
   an absent one is not the same answer. *)
Example duplicate_ids_not_addressable :
  let doc := [CId "x" (cpara ["a"]); CId "x" (cpara ["b"])] in
  (explicit_ids_unique doc,
   resolve_top_id "x" doc,
   resolve_top_id "y" doc)
  = (false, inr (AddrAmbiguous 2), inr AddrMissing).
Proof. reflexivity. Qed.

(* The two scopes really are different: an id inside a quote decorates
   the nested block, so it is invisible to replacement and visible to a
   page-wide link check. *)
Example scopes_differ :
  let doc := [CQuote [CId "x" (cpara ["a"])]] in
  (top_level_ids doc, page_ids doc) = ([], ["x"]).
Proof. reflexivity. Qed.

(*
A generated block, and the one thing that can go wrong with it
-------------------------------------------------------------
*)

(* The view a table of contents wants is a projection of the whole
   document, so it is computed the way a reader sees it: render, parse,
   read the pass's own answer. *)
Definition auto_ids (cbs : list cblock) : list string :=
  doc_auto_identifiers (parse_doc (render_djot (blocks_of_cblocks cbs))).

Definition toc_doc : list cblock :=
  [ CId "toc" (cpara ["stale"]) ; CHeading 1 [[CIStr "H"]] ].

Definition refresh_twice {V : Type} (D : derived V) (cbs : list cblock)
  : sum (list cblock) address_error :=
  match refresh D cbs with inl cbs' => refresh D cbs' | inr e => inr e end.

(* A generated block that holds a heading.  Installing it gives that
   heading the automatic id the document's own heading had, and the
   document's heading becomes `H-1` -- so the view this block is built
   from moved because the block was installed.  `refresh_stable`'s
   hypothesis is exactly what this document fails. *)
Definition toc_make (v : list string) : cblock :=
  CDiv (CHeading 1 [[CIStr "H"]] :: map (fun s => cpara [s]) v).

Definition toc : derived (list string) := Derived "toc" auto_ids toc_make.

Example refresh_view_can_move :
  auto_ids toc_doc = ["toc"; "H"]
  /\ match refresh toc toc_doc with
     | inl cbs => auto_ids cbs
     | inr _ => []
     end = ["toc"; "H"; "H-1"].
Proof. split; reflexivity. Qed.

(* And so the build does not converge: a second refresh writes a
   different block.  This is the document-level echo of
   `Uniformity.reparse_only_new`'s state hypothesis -- return the check,
   never assume it. *)
Example refresh_not_stable : refresh_twice toc toc_doc <> refresh toc toc_doc.
Proof. vm_compute. discriminate. Qed.

(* The same view with a block that generates no heading converges in one
   step, and `refresh_stable` is what says so: the only obligation is the
   view equality, which the build can run. *)
Definition ids_make (v : list string) : cblock :=
  CDiv (map (fun s => cpara [s]) v).

Definition ids_block : derived (list string) := Derived "toc" auto_ids ids_make.

Example refresh_converges :
  forall cbs, refresh ids_block toc_doc = inl cbs -> refresh ids_block cbs = inl cbs.
Proof.
  intros cbs H. apply (refresh_stable _ ids_block toc_doc cbs H).
  vm_compute in H. injection H as <-. vm_compute. reflexivity.
Qed.
