(* ai-disclosure: autonomous *)

(* Exhaustive generation of canonical blocks, and the roundtrip checked
   on every generated inhabitant by computation.

   Part of the build, not a side tool.  `parse_blocks (render_djot ...)`
   and `cb_ast` are both closed terms on a closed `cblock`, so agreement
   between them is decided by `vm_compute; reflexivity`: no decidable
   equality on `block`, no extraction, no oracle process.  The `Example`s
   below are therefore kernel-checked on every `dune build`, and
   `harness/Extract.v` extracts the pools here to drive the differential
   run against djot.js.

   `roundtrip_blocks` implies the accepted-side examples, so they prove
   nothing new at a fixed `cb_ok`.  Their value is under change: relaxing
   `cb_ok` re-scopes `accepted` automatically, so a proposed relaxation
   is tested for soundness before any proof work.

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

(* One inhabitant per leaf construct, plus two two-line paragraphs so
   that interior-line handling is exercised.  The second interior line
   is a bullet marker, which `cline` escapes: it is the only leaf that
   reaches the escaper's line-initial rule.  That rule is why the
   accepted fragment does not move with the block knob -- filtering this
   pool by `cb_ok` at a knob that lets markers interrupt gives the same
   245 and 2910 -- and without this leaf no generated document could
   say so. *)
Definition leaves : list cblock :=
  [ cpara ["a"]
  ; cpara ["a"; "b"]
  ; cpara ["a"; "- b"]
  ; CPara [[CIDelim DEmph [CIStr "e"]]]
  ; CPara [[CILink false [CIStr "l"] "u"]]
  ; CPara [[CILink true [CIStr "i"] "u"]]
  ; CPara [[CIRef false [CIStr "r"] "lab"]]
  ; CPara [[CIAuto "u:v"]]
  ; CPara [[CIRaw "html" "<br>"]]
  ; CThematic
  ; cheading 1 ["h"]
  ; CCode "" ["x"]
  ; CRaw "html" ["x"]
  ; CRef "r" "u"
  (* Both table shapes: a body row alone, and a header governing one.
     The header is right-aligned so that the separator carries something
     the AST has to give back. *)
  ; CTable [CTBody [[CIStr "a"]]]
  (* The destination renderer escapes the backtick.  This leaf is the
     only one where the row scanner and the inline scanner have to agree
     on that escape. *)
  ; CTable [CTBody [[CILink false [CIStr "a"] "a`b"]]]
  ; CTable [CTHead [AlignRight; AlignDefault] [[CIStr "h"]; [CIStr "i"]];
            CTBody [[CIStr "b"]; [CIStr "c"]]] ].

(* Second-position fillers.  A list is among them so that "container
   after a paragraph" shapes are generated; keeping the set fixed is
   what holds the enumeration linear. *)
Definition tails : list cblock :=
  [ cpara ["t"] ; CList LKBullet Tight [[cpara ["n"]]] ].

Definition item_tails : list (list cblock) :=
  [ [cpara ["t"]] ; [CList LKBullet Tight [[cpara ["n"]]]] ].

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

(* `CId` is a wrapper rather than a leaf, so it belongs here: one named
   copy of every block in the pool.  At depth two the pool already holds
   named blocks, so the nested spellings `cb_ok` rejects are generated
   too. *)
Definition containers (pool : list cblock) : list cblock :=
  (map CQuote (seqs pool)
   ++ map CDiv (seqs pool)
   ++ map (CId "i") pool
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

(* Keys have no differential oracle.  Keep their pool separate so the
   djot.js corpus stays meaningful, and exercise both sides of nesting:
   a key over each ordinary child, and containers over each key. *)
Definition keyed_pool (d : nat) : list cblock :=
  flat_map (fun label =>
    flat_map (fun child =>
      let key := CKey label child in
      [key; CKey (CIStr "outer") key; CQuote [key]; CDiv [key];
       CList LKBullet Tight [[key]]; CId "key" key])
      (enum_cblock d))
    [CIStr "Note: this"; CIVerb "code";
     CIDelim DStrong [CIStr "strong"]; CILink false [CIStr "see"] "note"].

Definition keyed_accepted (d : nat) : list cblock :=
  filter (@cb_ok _ keyed_bconfig) (keyed_pool d).

Definition keyed_rt_lhs (c : cblock) : blocks :=
  @parse_blocks _ keyed_bconfig (render_djot (blocks_of_cblocks [c])).

Example gen_roundtrip_1 : map rt_lhs (accepted 1) = map rt_rhs (accepted 1).
Proof. vm_compute. reflexivity. Qed.

Example gen_roundtrip_2 : map rt_lhs (accepted 2) = map rt_rhs (accepted 2).
Proof. vm_compute. reflexivity. Qed.

(* Depth 3 lives in `dev/check/Deep.v`, outside the dune build: it costs
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
  ; LKDecimal LeftRightParen 99
  (* Roman.  Start 1 is the ambiguous opener -- `i.` names roman and
     alpha both, and only the run decides -- which is the case the
     narrowing theorems exist for.  Start 4 puts a bare `v.` in the
     middle of a run, a sibling whose marker is ambiguous where the
     opener's was not.  Start 39 crosses `xxxix` to `xl`, where the
     marker gets *narrower* and the continuation pad with it, the
     opposite of the `9.`/`10.` widening above. *)
  ; LKRoman false RightPeriod 1
  ; LKRoman false RightPeriod 4
  ; LKRoman false RightParen 39
  ; LKRoman true LeftRightParen 1
  (* Alpha.  Start 1 runs `a.` through `d.`, and `c` and `d` are roman
     digits, so the siblings are ambiguous while the opener is not.
     Start 25 sits at the wrap: `y`, `z`, and then nothing, so `cb_ok`
     is what stops the run rather than the enumeration. *)
  ; LKAlpha false RightPeriod 1
  ; LKAlpha true RightParen 25
  ; LKAlpha false LeftRightParen 2
  (* The ambiguous alpha openers, which only a second item resolves: `i.`
     also names roman, and `j.` is what settles it.  `cb_ok` rejects the
     one-item spellings, so the enumeration and the filter together are
     what pin the boundary. *)
  ; LKAlpha false RightPeriod 9
  ; LKAlpha true RightPeriod 4
  ].

Definition ordered_pool : list cblock :=
  flat_map (fun k => flat_map (fun its => [CList k Tight its; CList k Loose its])
                       (itemlists (seqs leaves))) ordered_kinds.

(* The doubly ambiguous openers need *three* items: `c.` then `d.` are
   both roman digits, so only `e.` settles the list, and `cb_ok` rejects
   the one- and two-item spellings.  `itemlists` tops out at two, so they
   get their own pool rather than widening the shared one -- three items
   everywhere would multiply every kind for no new shape. *)
Definition ordered_kinds3 : list list_kind :=
  [ LKAlpha false RightPeriod 3
  ; LKAlpha false RightParen 12
  ; LKAlpha true RightPeriod 3 ].

Definition ordered_pool3 : list cblock :=
  flat_map (fun k => flat_map (fun its => [CList k Tight its; CList k Loose its])
                       (map (fun it => [it; it; it]) (seqs leaves)))
           ordered_kinds3.

Definition ordered_accepted : list cblock :=
  filter cb_ok (ordered_pool ++ ordered_pool3)%list.

Example gen_roundtrip_ordered :
  map rt_lhs ordered_accepted = map rt_rhs ordered_accepted.
Proof. vm_compute. reflexivity. Qed.

(*
Definition lists
----------------

Enumerated separately for the reason the ordered kinds are, and with the
opposite justification: a definition list's markers are a bullet's, so
nothing about them is new.  What is new is the *item shape*, because
`ck_block LKDef` splits a leading paragraph off as the term.  `seqs
leaves` supplies both readings -- an item that starts with a paragraph
has a term, one that starts with a heading or a fence has none -- and
`item_tails` puts a second block after each, which is the case where the
term and the definition are different blocks rather than the same one.
*)

Definition def_pool : list cblock :=
  flat_map (fun its => [CList LKDef Tight its; CList LKDef Loose its])
    (itemlists (seqs leaves)).

Definition def_accepted : list cblock := filter cb_ok def_pool.

Example gen_roundtrip_def :
  map rt_lhs def_accepted = map rt_rhs def_accepted.
Proof. vm_compute. reflexivity. Qed.

(* Task lists vary data per item rather than per list.  Alternate statuses so
   every two-item generated list exercises the status-preserving uniformity
   path; derive the list length structurally so [ck_ok]'s equality is never a
   hand-maintained side condition. *)
Definition alternating_checks (items : list (list cblock)) : list task_status :=
  match items with
  | [] => []
  | _ :: rest =>
      Incomplete ::
        (fix go (complete : bool) (xs : list (list cblock)) :=
           match xs with
           | [] => []
           | _ :: ys => (if complete then Complete else Incomplete) :: go (negb complete) ys
           end) true rest
  end.

Definition task_pool : list cblock :=
  flat_map
    (fun its =>
       let k := LKTask (alternating_checks its) in
       [CList k Tight its; CList k Loose its])
    (itemlists (seqs leaves)).

Definition task_accepted : list cblock := filter cb_ok task_pool.

Example gen_roundtrip_task :
  map rt_lhs task_accepted = map rt_rhs task_accepted.
Proof. vm_compute. reflexivity. Qed.

Example mixed_task_lines :
  cb_lines (CList (LKTask [Incomplete; Complete]) Tight
              [[cpara ["a"; "a2"]]; [cpara ["b"]]])
  = ["- [ ] a"; "      a2"; "- [x] b"].
Proof. reflexivity. Qed.

Example mixed_task_roundtrips :
  let c := CList (LKTask [Incomplete; Complete]) Tight
             [[cpara ["a"; "a2"]]; [cpara ["b"]]] in
  cb_ok c = true /\ rt_lhs c = rt_rhs c.
Proof. split; reflexivity. Qed.

(* Not vacuous, and the width boundary really is crossed: the second
   item's pad is four spaces where the first's is three. *)
Example ordered_renumbering_lines :
  cb_lines (CList (LKDecimal RightPeriod 9) Tight
              [[cpara ["a"; "a2"]]; [cpara ["b"; "b2"]]])
  = ["9. a"; "   a2"; "10. b"; "    b2"].
Proof. reflexivity. Qed.

Example ordered_renumbering_roundtrips :
  let c := CList (LKDecimal RightPeriod 9) Tight
             [[cpara ["a"; "a2"]]; [cpara ["b"; "b2"]]] in
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
  rt_lhs (CList LKBullet Tight [[CList LKBullet Loose [[cpara ["a"]; cpara ["t"]]]]])
  = [ mk (BulletList Tight
            [[ mk (BulletList Loose
                     [[ mk (Para [mk (Str "a")])
                      ; mk (Para [mk (Str "t")]) ]]) ]]) ].
Proof. reflexivity. Qed.

Example nested_loose_outer_tight_roundtrips :
  rt_lhs (CList LKBullet Tight [[CList LKBullet Loose [[cpara ["a"]; cpara ["t"]]]]])
  = rt_rhs (CList LKBullet Tight [[CList LKBullet Loose [[cpara ["a"]; cpara ["t"]]]]]).
Proof. reflexivity. Qed.

(* And the `Loose` spelling of the same tree is rejected, because no
   source text denotes it: the rendering above is the only one, and it
   parses back tight. *)
Example nested_loose_outer_loose_rejected :
  cb_ok (CList LKBullet Loose [[CList LKBullet Loose [[cpara ["a"]; cpara ["t"]]]]]) = false.
Proof. reflexivity. Qed.

(*
List uniformity applies
=======================

`Parser.list_uniformity` is what `cb_ok`'s list case now asks for
directly: `item_ok` on the item's rendering, and nothing about what is
inside it.  So the fragment covers nested lists and code blocks, and the
checks below record how much that is worth and that the hypothesis is
satisfiable on renderings `cb_ok` does not itself constrain.
*)

(* A fence records its own column, so `run_safe` accepts one inside an
   item: an item may contain a code block, and need only not *end*
   inside an open one, which no canonical rendering does. *)
Definition ok_content (c : cblock) : bool := item_ok bullet (cb_lines c).

(* Every generated block's rendering, plus every two-block sequence built
   from them.  The sequences are the informative half: `item_ok` on a
   sequence is not implied by `item_ok` on each block, since the
   run_safe scan threads state across the blank between them. *)
Definition item_pool : list (list string) :=
  (map cb_lines (filter ok_content (enum_cblock 2))
   ++ map (fun cs => sep_lines (map cb_lines cs))
        (filter (forallb ok_content) (seqs (filter ok_content (enum_cblock 1)))))%list.

Example uniformity_applies : forallb (item_ok bullet) item_pool = true.
Proof. vm_compute. reflexivity. Qed.

(* The fragment contains lists whose items are themselves lists. *)
Example nested_list_accepted :
  cb_ok (CList LKBullet Tight [[CList LKBullet Tight [[cpara ["a"]]]]]) = true.
Proof. reflexivity. Qed.

(* An item may contain a code block, at any depth: the pad the marker
   puts in front of the item's lines reaches the fence as a shift of its
   recorded column rather than as content. *)
Example item_code_accepted :
  cb_ok (CList LKBullet Tight [[CCode "" ["x"]]]) = true.
Proof. reflexivity. Qed.

Example item_para_then_code_accepted :
  cb_ok (CList LKBullet Loose [[cpara ["a"]; CCode "" ["x"]]]) = true.
Proof. reflexivity. Qed.

Example nested_item_code_accepted :
  cb_ok (CList LKBullet Tight
           [[CList LKBullet Tight [[CCode "" ["x"]]]]]) = true.
Proof. reflexivity. Qed.

(* The pool counts are pinned in `dev/check/Deep.v` rather than here:
   computing the depth-3 length is expensive, and they move whenever
   `leaves` gains a canonical construct. *)

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

(* And a gap that a list already open in these very lines will claim
   does not loosen, while the same gap after that list has closed
   does. *)
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
Tight.

The three below pin the boundary: the `Tight` tree is what the source
denotes, the `Loose` tree is unreachable and `cb_ok` rejects it, and the
`Tight` rendering carries no separator blank at all.
*)

Definition end_blank_shape (sp : list_spacing) : cblock :=
  CList LKBullet sp [ [CList LKBullet Tight [ [cpara ["b"]] ]] ; [cpara ["d"]] ].

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
