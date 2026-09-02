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

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Line Ast Parser Render Roundtrip.
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
