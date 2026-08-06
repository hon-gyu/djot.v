(* The whole-document pass: the part of parsing that is a function of the
   finished block list rather than of a single line.

   It runs strictly *after* `Parser.parse_blocks`, never inside the fold.
   That separation is deliberate and load-bearing: Phase 3's locality
   theorem says inline classification does not depend on the reference and
   note maps, which is only true if those maps are built by a pass the
   line fold cannot see.

   Two computations live here today, both driven by headings:

   - Auto-identifiers and implicit heading references, assigned in
     document order because uniqueness suffixes depend on what came
     before (djot.js `getUniqueIdentifier`, parse.ts ~line 193).
   - Section nesting: a level-driven container stack over the top-level
     block list, moving each heading's id onto the section that wraps it
     (djot.js parse.ts ~line 769).

   Reference definitions and footnotes are the same shape of computation —
   block syntax that produces no block, only side-table entries — and
   belong in this file when they land.

   Sectioning is top-level only.  djot.js pushes a section container only
   when the enclosing container tracks a heading level, which the document
   does and a block quote does not, so `> # h` yields a bare
   `<h1 id="h">` (djot.js test/block_quote.test).  Identifiers, by
   contrast, are assigned everywhere and share one counter. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Ast Parser.
Import ListNotations.

Local Open Scope string_scope.

(*
Heading text
============
*)

(* The string an element contributes to its heading's identifier
   (djot.js `addStringContent`): text-carrying leaves give their text,
   breaks give a newline, containers concatenate their children, and
   footnote references contribute nothing — a heading's marker must not
   leak into its id.

   Only Str and SoftBreak occur until the inline pass lands; the rest
   follow djot.js's AST field names, so a constructor whose djot.js node
   has neither `text` nor `children` (Symbol carries `alias`) is silent. *)
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
  | Symbol _ | UrlLink _ | EmailLink _ | NonBreakingSpace => ""
  end.

Definition inlines_text (ils : inlines) : string :=
  String.concat "" (map (fun n => inline_text (node_contents n)) ils).

(*
Auto-identifiers
================
*)

(* djot.js replaces runs of this class with a space, trims, then joins
   with "-" (parse.ts `getUniqueIdentifier`).  That is `words` over the
   class, joined with "-": collapsing and trimming are what dropping
   empty tokens already does, so the source-level `.trim()` on the
   heading text is subsumed here and in `normalize_label`. *)
Definition is_id_sep (c : ascii) : bool :=
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

Definition id_base (s : string) : string :=
  String.concat "-" (words is_id_sep s).

Definition id_taken (used : list string) (s : string) : bool :=
  existsb (String.eqb s) used.

(* Candidate i: the base itself at 0, then base-1, base-2, ...  An empty
   base is rejected at 0 and becomes "s-1", "s-2", ... *)
Definition id_candidate (base : string) (i : nat) : string :=
  if Nat.eqb i 0 then base
  else (match base with EmptyString => "s" | _ => base end)
       ++ "-" ++ nat_str i.

(* Fuel, fixed by `unique_id` below so that nothing outside this section
   mentions it.  With n identifiers taken, candidates 0..n+1 are n+2
   distinct strings, so one of them is free and the O branch is
   unreachable — argued here, not yet proved: the discharge lemma
   (compare Parser.step_fuel_enough) needs pigeonhole plus injectivity of
   nat_str.  Nothing depends on it today; freshness of the assigned
   identifier is exactly what it would buy. *)
Fixpoint unique_id_from (fuel i : nat) (used : list string) (base : string)
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

(* Threaded through the block tree in document order.  Both accumulators
   hold their entries newest-first; `doc_pass` reverses them. *)
Record id_state : Type := IdSt
  { id_used : list string
  ; id_refs : reference_map }.

Definition id_state_init : id_state := IdSt [] [].

(* An implicit reference from the heading's text to its own id, unless
   that label is already spoken for (djot.js checks `references` too;
   there are none until reference definitions land). *)
Definition add_auto_ref (label ident : string) (st : id_state) : id_state :=
  if existsb (fun p => String.eqb (fst p) label) (id_refs st)
  then st
  else IdSt (id_used st) ((label, ("#" ++ ident, [])) :: id_refs st).

Definition assign_heading_id (p : pos) (a : attr) (lvl : nat) (ils : inlines)
  (st : id_state) : id_state * node block :=
  match lookup_attr "id" a with
  (* An explicit id wins and is registered by the attribute pass, which
     does not exist yet — hence no counter slot consumed here. *)
  | Some _ => (st, Node p a (Heading lvl ils))
  | None =>
      let text := inlines_text ils in
      let ident := unique_id (id_used st) (id_base text) in
      let st' := IdSt (ident :: id_used st) (id_refs st) in
      (add_auto_ref (normalize_label text) ident st',
       Node p (("id", ident) :: a) (Heading lvl ils))
  end.

(* Pre-order, which is document order for headings: a heading closes
   before anything that starts after it, and headings do not nest.

   Recursion is on the *payload*, with the node's position and attributes
   passed alongside, because `block` recurses through `list (node block)`
   — two type constructors deep, which the guard checker will not follow
   from a `node block` principal argument.  Html.render_block has the
   same shape for the same reason. *)
Fixpoint assign_ids (b : block) (p : pos) (a : attr) (st : id_state)
  {struct b} : id_state * node block :=
  match b with
  | Heading lvl ils => assign_heading_id p a lvl ils st
  | BlockQuote bs =>
      let (st', bs') :=
        (fix go (ns : blocks) (s : id_state) {struct ns} : id_state * blocks :=
           match ns with
           | [] => (s, [])
           | Node p' a' x :: rest =>
               let (s1, n1) := assign_ids x p' a' s in
               let (s2, rest1) := go rest s1 in
               (s2, n1 :: rest1)
           end) bs st in
      (st', Node p a (BlockQuote bs'))
  | _ => (st, Node p a b)
  end.

Definition assign_ids_node (n : node block) (st : id_state)
  : id_state * node block :=
  match n with Node p a b => assign_ids b p a st end.

(* The list version, named so proofs can talk about it; `assign_ids`
   inlines its own copy because Rocq rejects the mutual spelling
   (see Render.v for the same pattern). *)
Fixpoint assign_ids_list (ns : blocks) (st : id_state) : id_state * blocks :=
  match ns with
  | [] => (st, [])
  | n :: rest =>
      let (st1, n1) := assign_ids_node n st in
      let (st2, rest1) := assign_ids_list rest st1 in
      (st2, n1 :: rest1)
  end.

Lemma assign_ids_quote :
  forall p a bs st,
    assign_ids (BlockQuote bs) p a st
    = let (st', bs') := assign_ids_list bs st in
      (st', Node p a (BlockQuote bs')).
Proof.
  intros p a bs st.
  assert (H : forall ns st0,
             (fix go (l : blocks) (s : id_state) : id_state * blocks :=
                match l with
                | [] => (s, [])
                | Node p' a' x :: rest =>
                    let (s1, n1) := assign_ids x p' a' s in
                    let (s2, rest1) := go rest s1 in
                    (s2, n1 :: rest1)
                end) ns st0 = assign_ids_list ns st0).
  { induction ns as [|[p' a' x] rest IH]; intros st0; [reflexivity|].
    cbn. destruct (assign_ids x p' a' st0) as [s1 n1]. rewrite IH. reflexivity. }
  change (assign_ids (BlockQuote bs) p a st)
    with (let (s', bs') :=
            (fix go (l : blocks) (s : id_state) : id_state * blocks :=
               match l with
               | [] => (s, [])
               | Node p' a' x :: rest =>
                   let (s1, n1) := assign_ids x p' a' s in
                   let (s2, rest1) := go rest s1 in
                   (s2, n1 :: rest1)
               end) bs st in
          (s', Node p a (BlockQuote bs'))).
  rewrite H. reflexivity.
Qed.

(*
Section nesting
===============
*)

(* A stack of open sections, innermost first, mirroring djot.js's
   container stack.  Each entry carries the heading level that opened it,
   the attributes moved off that heading, and the blocks collected so far
   in reverse.  The bottom entry is the document, at level 0: no heading
   level is <= 0, so it is never closed and the stack is never empty. *)
Definition sect_state : Type := list (nat * attr * blocks).

Definition sect_init : sect_state := [(0, [], [])].

(* Close every section a level-`lvl` heading interrupts, carrying the
   already-closed nodes inward-out in `pending` so each lands inside the
   section that encloses it.  Recursion is on the stack, so this is
   structural — nesting the current section into its parent *before*
   testing the parent is what the `pending` argument buys. *)
Fixpoint close_ge (lvl : nat) (pending : blocks) (stk : sect_state)
  : sect_state :=
  match stk with
  | [] => []
  | [(l, a, acc)] => [(l, a, (pending ++ acc)%list)]
  | (l, a, acc) :: outer =>
      if Nat.leb lvl l
      then close_ge lvl [Node NoPos a (Section (rev (pending ++ acc)))] outer
      else ((l, a, (pending ++ acc)%list) :: outer)
  end.

Definition sect_push (b : node block) (stk : sect_state) : sect_state :=
  match stk with
  | [] => []
  | (l, a, acc) :: rest => (l, a, b :: acc) :: rest
  end.

(* A heading closes the sections it interrupts, then opens its own with
   the heading as its first child.  The id moves from the heading to the
   section (djot.js: "move id attribute from heading to section"). *)
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
  sect_bottom (close_ge 1 [] (fold_left sect_step bs sect_init)).

(*
The pass
========
*)

Definition doc_pass (bs : blocks) : doc :=
  let (st, bs') := assign_ids_list bs id_state_init in
  {| doc_blocks := sectionize bs'
   ; doc_footnotes := []
   ; doc_references := []
   ; doc_auto_references := rev (id_refs st)
   ; doc_auto_identifiers := rev (id_used st) |}.

(** Parse a djot document: the line fold, then the whole-document pass. *)
Definition parse_doc (s : string) : doc := doc_pass (parse_blocks s).

(*
Examples
========

Each is a case from djot.js/test/headings.test, checked at the AST level.
*)

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

(* Sections are top-level only: inside a quote the heading keeps its id. *)
Example quote_heading_unsectioned :
  doc_blocks (parse_doc "> # Heading")
  = [mk (BlockQuote
           [Node NoPos [("id", "Heading")]
              (Heading 1 [mk (Str "Heading")])])].
Proof. reflexivity. Qed.

Example implicit_heading_reference :
  doc_auto_references (parse_doc "# Introduction")
  = [("Introduction", ("#Introduction", []))].
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
