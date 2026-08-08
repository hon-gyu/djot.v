(* ai-disclosure: ai-generated *)

(* Exhaustive generation of canonical blocks, and the roundtrip checked
   on every generated inhabitant by computation.

   `parse_blocks (render_djot ...)` and `cb_ast` are both closed terms on
   a closed `cblock`, so agreement between them is decided by
   `vm_compute; reflexivity` — no decidable equality on `block` is
   needed, and no extraction or oracle process.

   What it is for.  `roundtrip_blocks` already implies the accepted-side
   examples below, so they prove nothing new *today*.  Their value is
   under change: relaxing `cb_ok` re-scopes `accepted` automatically, so
   a proposed relaxation can be tested for soundness in seconds, before
   any proof work.  That is how `nested_loose_promotes_outer` (below) was
   found.

   Coverage of *shapes*, not volume: the alphabet is deliberately tiny
   and sequences take their tail from a fixed set, so the pool grows
   linearly (5, 110, 2315, 48620) instead of quadratically. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Line Ast Parser Render.
Import ListNotations.

Local Open Scope string_scope.

(*
The alphabet
============
*)

(* One inhabitant per leaf construct, plus a two-line paragraph so that
   interior-line handling is exercised. *)
Definition leaves : list cblock :=
  [ CPara ["a"]
  ; CPara ["a"; "b"]
  ; CThematic
  ; CHeading 1 ["h"]
  ; CCode "" ["x"] ].

(* Second-position fillers.  A list is among them so that "container
   after a paragraph" shapes are generated; keeping the set fixed is
   what holds the enumeration linear. *)
Definition tails : list cblock :=
  [ CPara ["t"] ; CList Tight [[CPara ["n"]]] ].

Definition item_tails : list (list cblock) :=
  [ [CPara ["t"]] ; [CList Tight [[CPara ["n"]]]] ].

(*
The enumeration
===============
*)

Definition seqs (pool : list cblock) : list (list cblock) :=
  (map (fun c => [c]) pool
   ++ flat_map (fun c => map (fun t => [c; t]) tails) pool)%list.

Definition itemlists (items : list (list cblock)) : list (list (list cblock)) :=
  (map (fun it => [it]) items
   ++ flat_map (fun it => map (fun t => [it; t]) item_tails) items)%list.

Definition containers (pool : list cblock) : list cblock :=
  (map CQuote (seqs pool)
   ++ flat_map (fun its => [CList Tight its; CList Loose its])
        (itemlists (seqs pool)))%list.

(* Depth counts container nesting: `enum_cblock 3` contains a list inside
   a list inside a list. *)
Fixpoint enum_cblock (d : nat) : list cblock :=
  match d with
  | O => leaves
  | S d' => (leaves ++ containers (enum_cblock d'))%list
  end.

Definition accepted (d : nat) : list cblock := filter cb_ok (enum_cblock d).

(*
The roundtrip, decided
======================
*)

Definition rt_lhs (c : cblock) : blocks :=
  parse_blocks (render_djot (blocks_of_cblocks [c])).

Definition rt_rhs (c : cblock) : blocks := blocks_of_cblocks [c].

Example gen_roundtrip_1 : map rt_lhs (accepted 1) = map rt_rhs (accepted 1).
Proof. vm_compute. reflexivity. Qed.

Example gen_roundtrip_2 : map rt_lhs (accepted 2) = map rt_rhs (accepted 2).
Proof. vm_compute. reflexivity. Qed.

Example gen_roundtrip_3 : map rt_lhs (accepted 3) = map rt_rhs (accepted 3).
Proof. vm_compute. reflexivity. Qed.

(*
Boundary records
================
*)

(* Relaxing `list_content_safe`'s `CList => false` (the nested-list ban)
   admits this, and it does not roundtrip:

       - - a
             <- blank
         t

   `item_forces_loose` reads the outer item as tight, because the item
   holds exactly one block and there is no block *pair* to inspect.  But
   the blank belonging to the inner list is a blank line inside the outer
   item too, and the parser spends it: the outer list comes back Loose.

   So `item_forces_loose` is too *permissive* here, not too coarse.  The
   `KList` exemption it mirrors covers a gap whose successor is a nested
   list; it does not cover a gap nested inside an item's only block.  Any
   relaxation of `list_content_safe` has to strengthen this predicate at
   the same time. *)
Example nested_loose_promotes_outer :
  rt_lhs (CList Tight [[CList Loose [[CPara ["a"]; CPara ["t"]]]]])
  = [ mk (BulletList Loose
            [[ mk (BulletList Loose
                     [[ mk (Para [mk (Str "a")])
                      ; mk (Para [mk (Str "t")]) ]]) ]]) ].
Proof. reflexivity. Qed.

(* The same shape with the outer spacing declared Loose is what actually
   parses back, and is what a corrected predicate must accept. *)
Example nested_loose_outer_loose_roundtrips :
  rt_lhs (CList Loose [[CList Loose [[CPara ["a"]; CPara ["t"]]]]])
  = rt_rhs (CList Loose [[CList Loose [[CPara ["a"]; CPara ["t"]]]]]).
Proof. reflexivity. Qed.

(*
List-item uniformity applies
============================

`Parser.list_item_uniformity` is proved, so the roundtrip no longer has
to reason about an item's contents: they are a top-level parse.  What is
left to check by computation is that its hypotheses are *satisfiable* --
that real canonical renderings clear them -- since a theorem whose side
conditions never hold would prove nothing about this fragment.

The hypotheses are the marker line not forming a thematic break, and
`run_pad_safe`, which says no fence is open directly inside the item.
Neither mentions nesting, which is the point: nested lists clear them
exactly as flat content does.
*)

(* `list_content_safe` without its `CList` case -- the ban the uniformity
   theorem makes unnecessary.  `CCode` stays out: fence content is
   verbatim, which is what `run_pad_safe` rules out. *)
Fixpoint no_fence (cb : cblock) : bool :=
  let go := fix go (cs : list cblock) : bool :=
    match cs with [] => true | c :: rest => (no_fence c && go rest)%bool end in
  match cb with
  | CPara _ | CThematic | CHeading _ _ => true
  | CCode _ _ => false
  | CList _ items => forallb (forallb no_fence) items
  | CQuote inner => go inner
  end.

Definition ok_content (c : cblock) : bool := (no_fence c && item_marker_ok [c])%bool.

(* Every generated block's rendering, plus every two-block sequence's:
   1716 line sets, including the nested-list shapes `cb_ok` rejects. *)
Definition item_pool : list (list string) :=
  (map cb_lines (filter ok_content (enum_cblock 2))
   ++ map (fun cs => sep_lines (map cb_lines cs))
        (filter (forallb ok_content) (seqs (filter ok_content (enum_cblock 1)))))%list.

Definition uniformity_hyps (L : list string) : bool :=
  match L with
  | [] => false
  | l0 :: rest =>
      (negb (is_thematic (bullet_open ++ l0))
       && run_pad_safe rest (snd (step l0 (PPara []))))%bool
  end.

Example uniformity_applies : forallb uniformity_hyps item_pool = true.
Proof. vm_compute. reflexivity. Qed.

(* The spacing rule the theorem carries, on the cases that pin its shape:
   a gap before a list marker does not loosen, a gap before anything else
   does, and blank runs collapse. *)
Example spacing_gap_then_text : lines_loose false false [""; "t"] = true.
Proof. reflexivity. Qed.
Example spacing_gap_then_list : lines_loose false false [""; "- b"] = false.
Proof. reflexivity. Qed.
Example spacing_gaps_then_list : lines_loose false false [""; ""; "- b"] = false.
Proof. reflexivity. Qed.
Example spacing_nested_gap : lines_loose false false [""; "  t"] = true.
Proof. reflexivity. Qed.
