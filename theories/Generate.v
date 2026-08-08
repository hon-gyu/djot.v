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

(* The nested-list shape that pins the spacing condition.  Rendered, the
   outer item's lines carry the inner list's blank:

       - - a
                <- the pad, "    "
         t

   so `item_forces_loose`, which reads `lines_loose` off exactly those
   lines, calls the outer item loose.  Declaring the outer list Tight is
   therefore rejected, and it has to be: the parser comes back Loose. *)
Example nested_loose_promotes_outer :
  rt_lhs (CList Tight [[CList Loose [[CPara ["a"]; CPara ["t"]]]]])
  = [ mk (BulletList Loose
            [[ mk (BulletList Loose
                     [[ mk (Para [mk (Str "a")])
                      ; mk (Para [mk (Str "t")]) ]]) ]]) ].
Proof. reflexivity. Qed.

Example nested_loose_outer_tight_rejected :
  cb_ok (CList Tight [[CList Loose [[CPara ["a"]; CPara ["t"]]]]]) = false.
Proof. reflexivity. Qed.

(* The same shape with the outer spacing declared Loose is accepted, and
   roundtrips. *)
Example nested_loose_outer_loose_roundtrips :
  rt_lhs (CList Loose [[CList Loose [[CPara ["a"]; CPara ["t"]]]]])
  = rt_rhs (CList Loose [[CList Loose [[CPara ["a"]; CPara ["t"]]]]]).
Proof. reflexivity. Qed.

(*
List uniformity applies
=======================

`Parser.list_uniformity` is what `cb_ok`'s list case now asks for
directly: `item_ok` on the item's rendering, and nothing about what is
inside it.  So the fragment covers nested lists, and the checks below
record how much that is worth and that the hypothesis is satisfiable on
renderings `cb_ok` does not itself constrain.
*)

(* No code/raw block anywhere inside -- fence content is verbatim, which
   is what `run_pad_safe`, `item_ok`'s third conjunct, rules out.  A
   nested list is fine, which is the point. *)
Fixpoint no_fence (cb : cblock) : bool :=
  let go := fix go (cs : list cblock) : bool :=
    match cs with [] => true | c :: rest => (no_fence c && go rest)%bool end in
  match cb with
  | CPara _ | CThematic | CHeading _ _ => true
  | CCode _ _ => false
  | CList _ items => forallb (forallb no_fence) items
  | CQuote inner => go inner
  end.

Definition ok_content (c : cblock) : bool :=
  (no_fence c && item_ok (cb_lines c))%bool.

(* Every fence-free generated block's rendering, plus every two-block
   sequence built from them.  The sequences are the informative half:
   `item_ok` on a sequence is not implied by `item_ok` on each block,
   since the run_pad_safe scan threads state across the blank between
   them. *)
Definition item_pool : list (list string) :=
  (map cb_lines (filter ok_content (enum_cblock 2))
   ++ map (fun cs => sep_lines (map cb_lines cs))
        (filter (forallb ok_content) (seqs (filter ok_content (enum_cblock 1)))))%list.

Example uniformity_applies : forallb item_ok item_pool = true.
Proof. vm_compute. reflexivity. Qed.

(* What the restated `cb_ok` bought: the fragment now contains lists
   whose items are themselves lists. *)
Example nested_list_accepted :
  cb_ok (CList Tight [[CList Tight [[CPara ["a"]]]]]) = true.
Proof. reflexivity. Qed.

Example accepted_counts : (List.length (accepted 1),
                           List.length (accepted 2),
                           List.length (accepted 3)) = (59, 671, 7151).
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
