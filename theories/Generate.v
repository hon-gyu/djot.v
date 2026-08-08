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
List-item uniformity, probed
============================

`quote_uniformity` (Parser.v) says a quote's contents parse exactly as
they would at top level: one theorem, every construct, no
well-formedness hypothesis.  The list analogue has never been stated.
What follows is the statement and its evidence; the theorem itself is
not proved yet.

    parse_lines (indent_lines "- " "  " L) (PPara [])
      = [mk (BulletList (item_spacing L) [parse_lines L (PPara [])])]

The *contents* are uniform unconditionally.  Only the tight/loose bit
depends on L, and it is a line-level scan, not a property of the block
tree -- which is why `item_forces_loose`, which reads the tree, cannot
express it: the tree has lost where the blanks sit relative to the
markers.

Two side conditions, both already known and both independent of nesting:
no fence in L (fence content is verbatim and keeps the ambient indent),
and `bullet_open ++ first line of L` must not itself be a thematic
break.
*)

(* Loose exactly when some blank run is followed by a line that does not
   open a list.  This is Parser.list_content's `KList` exemption, read
   off the lines instead of off the event stream. *)
Fixpoint lines_loose (gap : bool) (ls : list string) : bool :=
  match ls with
  | [] => false
  | l :: rest =>
      match classify l with
      | KBlank => lines_loose true rest
      | KList _ _ => lines_loose false rest
      | _ => if gap then true else lines_loose false rest
      end
  end.

Definition item_spacing (L : list string) : list_spacing :=
  if lines_loose false L then Loose else Tight.

(* `list_content_safe` without its `CList` case, which is the ban the
   uniformity statement is meant to make unnecessary. *)
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
   1716 line sets, including the nested-list shapes `cb_ok` still
   rejects. *)
Definition item_pool : list (list string) :=
  (map cb_lines (filter ok_content (enum_cblock 2))
   ++ map (fun cs => sep_lines (map cb_lines cs))
        (filter (forallb ok_content) (seqs (filter ok_content (enum_cblock 1)))))%list.

Example uniformity_sweep :
  map (fun L => parse_lines (indent_lines bullet_open bullet_cont L) (PPara [])) item_pool
  = map (fun L => [mk (BulletList (item_spacing L) [parse_lines L (PPara [])])]) item_pool.
Proof. vm_compute. reflexivity. Qed.

(* The four line sets that pin the spacing rule's shape.  A gap before a
   list marker does not loosen; a gap before anything else does; blank
   runs collapse. *)
Example spacing_gap_then_text : item_spacing ["a"; ""; "t"] = Loose.
Proof. reflexivity. Qed.
Example spacing_gap_then_list : item_spacing ["a"; ""; "- b"] = Tight.
Proof. reflexivity. Qed.
Example spacing_gaps_then_list : item_spacing ["a"; ""; ""; "- b"] = Tight.
Proof. reflexivity. Qed.
Example spacing_nested_gap : item_spacing ["- a"; ""; "  t"] = Loose.
Proof. reflexivity. Qed.
