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
   linearly (5, 110, 2315, 48620) instead of quadratically.

   Depth 3 is not here.  It is in `check/Deep.v`, which dune does not
   build, because those two checks were ~260s of a ~270s clean build and
   this file sits downstream of `Parser.v`.  `make deep` runs them; that
   file says what they cost and why. *)

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
  [ CPara ["t"] ; CList LKBullet Tight [[CPara ["n"]]] ].

Definition item_tails : list (list cblock) :=
  [ [CPara ["t"]] ; [CList LKBullet Tight [[CPara ["n"]]]] ].

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
   ++ map CDiv (seqs pool)
   ++ flat_map (fun its => [CList LKBullet Tight its; CList LKBullet Loose its])
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

(* Depth 3 lives in `check/Deep.v`, outside the dune build: it costs
   ~176s, and this file is downstream of Parser.v, so every parser edit
   was paying it.  `make deep` runs it. *)

(*
Ordered lists
-------------

Enumerated separately rather than folded into `containers`, which would
multiply the whole depth-2 pool by the number of kinds for no new
*shape* coverage: a list's kind changes its markers, not what its items
may contain.  What is new is the markers themselves, so the starts below
are chosen to cross a width boundary: at start 9 the second item's
marker is `10.` and its continuation pad is one wider than the first's,
which is the case a single marker per list could not express.
*)
Definition ordered_kinds : list list_kind :=
  [ LKDecimal RightPeriod 1
  ; LKDecimal RightPeriod 9
  ; LKDecimal RightParen 3
  ; LKDecimal LeftRightParen 99 ].

Definition ordered_pool : list cblock :=
  flat_map (fun k => flat_map (fun its => [CList k Tight its; CList k Loose its])
                       (itemlists (seqs leaves))) ordered_kinds.

Definition ordered_accepted : list cblock := filter cb_ok ordered_pool.

Example gen_roundtrip_ordered :
  map rt_lhs ordered_accepted = map rt_rhs ordered_accepted.
Proof. vm_compute. reflexivity. Qed.

(* Not vacuous, and the width boundary really is crossed: the second
   item's pad is four spaces where the first's is three. *)
Example ordered_renumbering_lines :
  cb_lines (CList (LKDecimal RightPeriod 9) Tight
              [[CPara ["a"; "a2"]]; [CPara ["b"; "b2"]]])
  = ["9. a"; "   a2"; "10. b"; "    b2"].
Proof. reflexivity. Qed.

Example ordered_renumbering_roundtrips :
  let c := CList (LKDecimal RightPeriod 9) Tight
             [[CPara ["a"; "a2"]]; [CPara ["b"; "b2"]]] in
  cb_ok c = true /\ rt_lhs c = rt_rhs c.
Proof. split; reflexivity. Qed.

(*
Boundary records
================
*)

(* The nested-list shape that pins the spacing condition.  Rendered, the
   outer item's lines carry the inner list's blank:

       - - a
                <- the pad, "    "
         t

   The blank is inside the inner list, so `step` gives it there and the
   outer list stays tight -- the spec's "blank lines at the start or end
   of a list do not count" reaching one level out.  `Tight` is the
   spelling that roundtrips. *)
Example nested_loose_promotes_outer :
  rt_lhs (CList LKBullet Tight [[CList LKBullet Loose [[CPara ["a"]; CPara ["t"]]]]])
  = [ mk (BulletList Tight
            [[ mk (BulletList Loose
                     [[ mk (Para [mk (Str "a")])
                      ; mk (Para [mk (Str "t")]) ]]) ]]) ].
Proof. reflexivity. Qed.

Example nested_loose_outer_tight_roundtrips :
  rt_lhs (CList LKBullet Tight [[CList LKBullet Loose [[CPara ["a"]; CPara ["t"]]]]])
  = rt_rhs (CList LKBullet Tight [[CList LKBullet Loose [[CPara ["a"]; CPara ["t"]]]]]).
Proof. reflexivity. Qed.

(* And the `Loose` spelling of the same tree is rejected, because no
   source text denotes it: the rendering above is the only one, and it
   parses back tight. *)
Example nested_loose_outer_loose_rejected :
  cb_ok (CList LKBullet Loose [[CList LKBullet Loose [[CPara ["a"]; CPara ["t"]]]]]) = false.
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
  | CList _ _ items => forallb (forallb no_fence) items
  | CQuote inner | CDiv inner => go inner
  end.

Definition ok_content (c : cblock) : bool :=
  (no_fence c && item_ok bullet (cb_lines c))%bool.

(* Every fence-free generated block's rendering, plus every two-block
   sequence built from them.  The sequences are the informative half:
   `item_ok` on a sequence is not implied by `item_ok` on each block,
   since the run_pad_safe scan threads state across the blank between
   them. *)
Definition item_pool : list (list string) :=
  (map cb_lines (filter ok_content (enum_cblock 2))
   ++ map (fun cs => sep_lines (map cb_lines cs))
        (filter (forallb ok_content) (seqs (filter ok_content (enum_cblock 1)))))%list.

Example uniformity_applies : forallb (item_ok bullet) item_pool = true.
Proof. vm_compute. reflexivity. Qed.

(* What the restated `cb_ok` bought: the fragment now contains lists
   whose items are themselves lists. *)
Example nested_list_accepted :
  cb_ok (CList LKBullet Tight [[CList LKBullet Tight [[CPara ["a"]]]]]) = true.
Proof. reflexivity. Qed.

(* The counts are (68, 888, 11368); divs took them from (53, 593, 6437),
   a div accepting any block sequence its contents do not close.  Pinned
   in `check/Deep.v` rather than here — the depth-3 length alone costs
   ~84s, which is a lot for a documentation number. *)

(* The spacing rule the theorem carries, on the cases that pin its shape:
   a gap before a list marker does not loosen, a gap before anything else
   does, and blank runs collapse. *)
Example spacing_gap_then_text : item_loose [""; "t"] = true.
Proof. reflexivity. Qed.
Example spacing_gap_then_list : item_loose [""; "- b"] = false.
Proof. reflexivity. Qed.
Example spacing_gaps_then_list : item_loose [""; ""; "- b"] = false.
Proof. reflexivity. Qed.
Example spacing_nested_gap : item_loose [""; "  t"] = true.
Proof. reflexivity. Qed.

(* ...and the clause the fix added: a gap that a list already open in
   these very lines will claim does not loosen, while the same gap after
   that list has closed does. *)
Example spacing_gap_inside_open_list : item_loose ["- b"; ""; "- c"] = false.
Proof. reflexivity. Qed.
Example spacing_gap_after_list_closed : item_loose ["- b"; ""; "t"] = false.
Proof. reflexivity. Qed.
Example spacing_gap_then_text_after_list : item_loose ["- b"; ""; "t"; ""; "u"] = true.
Proof. reflexivity. Qed.

(*
A blank at the end of a nested list
===================================

`["- - b"; ""; "- d"]`: the blank ends the inner list and separates two
items of the outer one.  The spec exempts a list's trailing blank from
tightness, and both oracles read it that way, so the outer list is
Tight; we used to spend the blank at the outer sibling and return Loose.
See `.project/oracle-disagreements.md` (2026-08-09, "a blank at the end
of a nested list").

The three below pin the boundary: the `Tight` tree is what the source
denotes, the `Loose` tree is unreachable and `cb_ok` rejects it, and the
`Tight` rendering carries no separator blank at all.
*)
Definition end_blank_shape (sp : list_spacing) : cblock :=
  CList LKBullet sp [ [CList LKBullet Tight [ [CPara ["b"]] ]] ; [CPara ["d"]] ].

Example nested_list_end_blank_tight :
  rt_lhs (end_blank_shape Tight)
  = [ mk (BulletList Tight
            [ [ mk (BulletList Tight [[ mk (Para [mk (Str "b")]) ]]) ]
            ; [ mk (Para [mk (Str "d")]) ] ]) ].
Proof. reflexivity. Qed.

Example nested_list_end_blank_loose_rejected :
  cb_ok (end_blank_shape Loose) = false.
Proof. reflexivity. Qed.

Example nested_list_end_blank_lines :
  (cb_lines (end_blank_shape Tight), cb_lines (end_blank_shape Loose))
  = (["- - b"; "- d"], ["- - b"; ""; "- d"]).
Proof. reflexivity. Qed.
