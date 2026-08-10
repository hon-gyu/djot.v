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

(* An identifier that a block attribute spec supplied is taken, and a
   later heading's auto-identifier has to step around it: djot.js records
   it into `identifiers` when the spec closes (parse.ts:519), before the
   block it decorates is opened.  Every id present in the tree at this
   point came from a spec, since this pass is what adds the others. *)
Definition register_id (a : attr) (st : id_state) : id_state :=
  match lookup_attr "id" a with
  | None => st
  | Some ident => IdSt (ident :: id_used st) (id_refs st)
  end.

Definition assign_heading_id (p : pos) (a : attr) (lvl : nat) (ils : inlines)
  (st : id_state) : id_state * node block :=
  match lookup_attr "id" a with
  (* An explicit id wins, and takes its slot. *)
  | Some _ => (register_id a st, Node p a (Heading lvl ils))
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
  let go :=
    fix go (ns : blocks) (s : id_state) {struct ns} : id_state * blocks :=
      match ns with
      | [] => (s, [])
      | Node p' a' x :: rest =>
          let (s1, n1) := assign_ids x p' a' s in
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
  (* The remaining containers -- Section, the other list flavours, Table
     -- are not reachable from the line fold yet (`Wf.supported` is the
     record of that).  Each needs its arm here when it lands, or a
     heading inside it silently goes without an identifier. *)
  | _ => (register_id a st, Node p a b)
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

Fixpoint assign_ids_items (its : list blocks) (st : id_state)
  : id_state * list blocks :=
  match its with
  | [] => (st, [])
  | it :: rest =>
      let (s1, it1) := assign_ids_list it st in
      let (s2, rest1) := assign_ids_items rest s1 in
      (s2, it1 :: rest1)
  end.

(* The inner fixpoints of `assign_ids`, named.  Same shape as
   `pristine_inner_go` and `undo_pass_inner_go`: Rocq will not let the
   definition mention `assign_ids_list` directly, so the identity is
   proved once here. *)
Lemma assign_ids_inner_go :
  forall ns st,
    (fix go (l : blocks) (s : id_state) : id_state * blocks :=
       match l with
       | [] => (s, [])
       | Node p' a' x :: rest =>
           let (s1, n1) := assign_ids x p' a' s in
           let (s2, rest1) := go rest s1 in
           (s2, n1 :: rest1)
       end) ns st = assign_ids_list ns st.
Proof.
  induction ns as [|[p' a' x] rest IH]; intros st; [reflexivity|].
  cbn. destruct (assign_ids x p' a' st) as [s1 n1]. rewrite IH. reflexivity.
Qed.

Lemma assign_ids_quote :
  forall p a bs st,
    assign_ids (BlockQuote bs) p a st
    = let (st', bs') := assign_ids_list bs (register_id a st) in
      (st', Node p a (BlockQuote bs')).
Proof.
  intros p a bs st. cbn [assign_ids].
  rewrite assign_ids_inner_go. reflexivity.
Qed.

Lemma assign_ids_div :
  forall p a bs st,
    assign_ids (Div bs) p a st
    = let (st', bs') := assign_ids_list bs (register_id a st) in
      (st', Node p a (Div bs')).
Proof.
  intros p a bs st. cbn [assign_ids].
  rewrite assign_ids_inner_go. reflexivity.
Qed.

(* The traversal rewrites items in place, so a list that was nonempty
   still is.  `wf_block (BulletList ...)` needs this. *)
Lemma assign_ids_items_nonempty :
  forall its st, nonempty (snd (assign_ids_items its st)) = nonempty its.
Proof.
  intros [|it rest] st; [reflexivity|].
  cbn [assign_ids_items].
  destruct (assign_ids_list it st) as [s1 it1].
  destruct (assign_ids_items rest s1) as [s2 rest1].
  reflexivity.
Qed.

Lemma assign_ids_blist :
  forall p a sp items st,
    assign_ids (BulletList sp items) p a st
    = let (st', items') := assign_ids_items items (register_id a st) in
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
                             let (s2, n2) := assign_ids x p' a' s' in
                             let (s3, r1) := go r s2 in
                             (s3, n2 :: r1)
                         end) it s in
                    let (s4, rest1) := goit rest s1 in
                    (s4, it1 :: rest1)
                end) its st = assign_ids_items its st).
  { induction its as [|it rest IH]; intros st; [reflexivity|].
    cbn [assign_ids_items]. rewrite assign_ids_inner_go.
    destruct (assign_ids_list it st) as [s1 it1]. rewrite IH. reflexivity. }
  intros p a sp items st. cbn [assign_ids]. rewrite H. reflexivity.
Qed.

(* The ordered arm is the bullet arm with a different wrapper: djot.js
   runs one `list` spec for both, and so does `assign_ids`. *)
Lemma assign_ids_olist :
  forall p a oa sp items st,
    assign_ids (OrderedList oa sp items) p a st
    = let (st', items') := assign_ids_items items (register_id a st) in
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
                             let (s2, n2) := assign_ids x p' a' s' in
                             let (s3, r1) := go r s2 in
                             (s3, n2 :: r1)
                         end) it s in
                    let (s4, rest1) := goit rest s1 in
                    (s4, it1 :: rest1)
                end) its st = assign_ids_items its st).
  { induction its as [|it rest IH]; intros st; [reflexivity|].
    cbn [assign_ids_items]. rewrite assign_ids_inner_go.
    destruct (assign_ids_list it st) as [s1 it1]. rewrite IH. reflexivity. }
  intros p a oa sp items st. cbn [assign_ids]. rewrite H. reflexivity.
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

(* Equation lemmas, as everywhere else in this development: `cbn` on
   close_ge reduces the *recursive* call as well, and an induction
   hypothesis about it then no longer matches. *)
Lemma close_ge_singleton :
  forall lvl pending l a acc,
    close_ge lvl pending [(l, a, acc)] = [(l, a, (pending ++ acc)%list)].
Proof. reflexivity. Qed.

Lemma close_ge_cons :
  forall lvl pending l a acc outer,
    outer <> [] ->
    close_ge lvl pending ((l, a, acc) :: outer)
    = if Nat.leb lvl l
      then close_ge lvl [Node NoPos a (Section (rev (pending ++ acc)))] outer
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
      close_all [Node NoPos a (Section (rev (pending ++ acc)))] outer
  end.

Lemma close_all_cons :
  forall pending l a acc outer,
    outer <> [] ->
    close_all pending ((l, a, acc) :: outer)
    = close_all [Node NoPos a (Section (rev (pending ++ acc)))] outer.
Proof. intros pending l a acc [|e outer] H; [contradiction|reflexivity]. Qed.

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
  sect_bottom (close_all [] (fold_left sect_step bs sect_init)).

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
Erasure
=======

The pass only adds, and what it adds is recoverable: a section is
exactly its heading plus the blocks that followed it, and an
auto-identifier is exactly an "id" attribute on a heading that carried
none.  `undo_pass` takes both back out in one traversal, and
`pass_erase` says it takes out precisely what the pass put in.

That is what keeps Roundtrip.v's theorem meaningful above the block
layer: render, parse, erase is the identity.  It is also the guard on
this file's future — reference definitions and footnotes will add
side-table entries here, and each should either extend `undo_pass` or
be shown not to touch the block tree.
*)

(* Oriented like lookup_attr, so the two compose without an eqb flip. *)
Definition strip_id (a : attr) : attr :=
  filter (fun kv => negb (String.eqb "id" (fst kv))) a.

Lemma strip_id_absent :
  forall a, lookup_attr "id" a = None -> strip_id a = a.
Proof.
  induction a as [|[k v] rest IH]; intros H; [reflexivity|].
  cbn [lookup_attr] in H. cbn [strip_id filter fst].
  destruct (String.eqb "id" k); [discriminate|].
  cbn [negb]. f_equal. apply IH. exact H.
Qed.

Lemma strip_id_cons :
  forall v a, lookup_attr "id" a = None -> strip_id (("id", v) :: a) = a.
Proof.
  intros v a H. cbn [strip_id filter fst].
  rewrite String.eqb_refl. cbn [negb].
  apply strip_id_absent. exact H.
Qed.

(* A section's attributes came off the heading that opened it, which
   sectionize left as its first child. *)
Definition set_first (a : attr) (bs : blocks) : blocks :=
  match bs with
  | [] => []
  | Node p _ x :: rest => Node p a x :: rest
  end.

(* Stripping the id *before* handing the attributes back is what makes
   one traversal enough: the identifier the pass added rides on the
   section, so it has to come off there. *)
Fixpoint undo_pass_block (b : block) (p : pos) (a : attr) {struct b}
  : blocks :=
  let go :=
    fix go (ns : blocks) : blocks :=
      match ns with
      | [] => []
      | Node p' a' x :: rest => (undo_pass_block x p' a' ++ go rest)%list
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
  | BulletList sp items => [Node p a (BulletList sp (goit items))]
  | OrderedList oa sp items => [Node p a (OrderedList oa sp (goit items))]
  | _ => [Node p a b]
  end.

Fixpoint undo_pass (bs : blocks) : blocks :=
  match bs with
  | [] => []
  | Node p a b :: rest => (undo_pass_block b p a ++ undo_pass rest)%list
  end.

Fixpoint undo_pass_items (its : list blocks) : list blocks :=
  match its with
  | [] => []
  | it :: rest => undo_pass it :: undo_pass_items rest
  end.

Lemma undo_pass_inner_go :
  forall ns,
    (fix go (l : blocks) : blocks :=
       match l with
       | [] => []
       | Node p' a' x :: rest => (undo_pass_block x p' a' ++ go rest)%list
       end) ns = undo_pass ns.
Proof.
  induction ns as [|[p' a' x] rest IH]; [reflexivity|].
  cbn [undo_pass]. rewrite IH. reflexivity.
Qed.

Lemma undo_pass_section :
  forall inner p a,
    undo_pass_block (Section inner) p a
    = set_first (strip_id a) (undo_pass inner).
Proof.
  assert (H : forall ns,
             (fix go (l : blocks) : blocks :=
                match l with
                | [] => []
                | Node p' a' x :: rest =>
                    (undo_pass_block x p' a' ++ go rest)%list
                end) ns = undo_pass ns).
  { induction ns as [|[p' a' x] rest IH]; [reflexivity|].
    cbn [undo_pass]. rewrite IH. reflexivity. }
  intros inner p a.
  change (undo_pass_block (Section inner) p a)
    with (set_first (strip_id a)
            ((fix go (l : blocks) : blocks :=
                match l with
                | [] => []
                | Node p' a' x :: rest =>
                    (undo_pass_block x p' a' ++ go rest)%list
                end) inner)).
  rewrite H. reflexivity.
Qed.

Lemma undo_pass_quote :
  forall inner p a,
    undo_pass_block (BlockQuote inner) p a
    = [Node p a (BlockQuote (undo_pass inner))].
Proof.
  assert (H : forall ns,
             (fix go (l : blocks) : blocks :=
                match l with
                | [] => []
                | Node p' a' x :: rest =>
                    (undo_pass_block x p' a' ++ go rest)%list
                end) ns = undo_pass ns).
  { induction ns as [|[p' a' x] rest IH]; [reflexivity|].
    cbn [undo_pass]. rewrite IH. reflexivity. }
  intros inner p a.
  change (undo_pass_block (BlockQuote inner) p a)
    with [Node p a (BlockQuote
            ((fix go (l : blocks) : blocks :=
                match l with
                | [] => []
                | Node p' a' x :: rest =>
                    (undo_pass_block x p' a' ++ go rest)%list
                end) inner))].
  rewrite H. reflexivity.
Qed.

Lemma undo_pass_inner_goit :
  forall its,
    (fix goit (l : list blocks) : list blocks :=
       match l with
       | [] => []
       | it :: rest =>
           (fix go (m : blocks) : blocks :=
              match m with
              | [] => []
              | Node p' a' x :: r => (undo_pass_block x p' a' ++ go r)%list
              end) it :: goit rest
       end) its = undo_pass_items its.
Proof.
  induction its as [|it rest IH]; [reflexivity|].
  cbn [undo_pass_items]. rewrite undo_pass_inner_go, IH. reflexivity.
Qed.

Lemma undo_pass_div :
  forall inner p a,
    undo_pass_block (Div inner) p a = [Node p a (Div (undo_pass inner))].
Proof.
  intros inner p a.
  change (undo_pass_block (Div inner) p a)
    with [Node p a (Div
            ((fix go (l : blocks) : blocks :=
                match l with
                | [] => []
                | Node p' a' x :: rest =>
                    (undo_pass_block x p' a' ++ go rest)%list
                end) inner))].
  rewrite undo_pass_inner_go. reflexivity.
Qed.

Lemma undo_pass_blist :
  forall sp items p a,
    undo_pass_block (BulletList sp items) p a
    = [Node p a (BulletList sp (undo_pass_items items))].
Proof.
  intros sp items p a.
  change (undo_pass_block (BulletList sp items) p a)
    with [Node p a (BulletList sp
            ((fix goit (its : list blocks) : list blocks :=
                match its with
                | [] => []
                | it :: rest =>
                    (fix go (l : blocks) : blocks :=
                       match l with
                       | [] => []
                       | Node p' a' x :: r => (undo_pass_block x p' a' ++ go r)%list
                       end) it :: goit rest
                end) items))].
  rewrite undo_pass_inner_goit. reflexivity.
Qed.

Lemma undo_pass_olist :
  forall oa sp items p a,
    undo_pass_block (OrderedList oa sp items) p a
    = [Node p a (OrderedList oa sp (undo_pass_items items))].
Proof.
  intros oa sp items p a.
  change (undo_pass_block (OrderedList oa sp items) p a)
    with [Node p a (OrderedList oa sp
            ((fix goit (its : list blocks) : list blocks :=
                match its with
                | [] => []
                | it :: rest =>
                    (fix go (l : blocks) : blocks :=
                       match l with
                       | [] => []
                       | Node p' a' x :: r => (undo_pass_block x p' a' ++ go r)%list
                       end) it :: goit rest
                end) items))].
  rewrite undo_pass_inner_goit. reflexivity.
Qed.

Definition undo_pass_node (n : node block) : blocks :=
  match n with Node p a b => undo_pass_block b p a end.

Lemma undo_pass_cons :
  forall n rest, undo_pass (n :: rest) = (undo_pass_node n ++ undo_pass rest)%list.
Proof. intros [p a b] rest. reflexivity. Qed.

Lemma undo_pass_single : forall n, undo_pass [n] = undo_pass_node n.
Proof. intros [p a b]. cbn [undo_pass undo_pass_node]. apply app_nil_r. Qed.

(* Input the pass has not already run on: no sections, and no heading
   carrying an explicit id.  Checked exactly where undo_pass looks — the
   top level and block-quote contents — because those are the only
   places either half of the pass reaches. *)
Fixpoint pristine_block (b : block) (a : attr) {struct b} : bool :=
  let go :=
    fix go (ns : blocks) : bool :=
      match ns with
      | [] => true
      | Node _ a' x :: rest => (pristine_block x a' && go rest)%bool
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
      match lookup_attr "id" a with Some _ => false | None => true end
  | BlockQuote inner | Div inner => go inner
  | BulletList _ items => goit items
  | OrderedList _ _ items => goit items
  | _ => true
  end.

Fixpoint pristine (bs : blocks) : bool :=
  match bs with
  | [] => true
  | Node _ a b :: rest => (pristine_block b a && pristine rest)%bool
  end.

(* A list is pristine when every item is.  Named so the equation lemma
   below has something to be stated against. *)
Fixpoint pristine_items (its : list blocks) : bool :=
  match its with
  | [] => true
  | it :: rest => (pristine it && pristine_items rest)%bool
  end.

(* The inner fixpoints of `pristine_block` are `pristine` and
   `pristine_items`; Rocq will not let them be spelled that way, so each
   arm needs its identity proved once and rewritten with thereafter. *)
Lemma pristine_inner_go :
  forall ns,
    (fix go (l : blocks) : bool :=
       match l with
       | [] => true
       | Node _ a' x :: rest => (pristine_block x a' && go rest)%bool
       end) ns = pristine ns.
Proof.
  induction ns as [|[p' a' x] rest IH]; [reflexivity|].
  cbn [pristine]. rewrite IH. reflexivity.
Qed.

Lemma pristine_quote :
  forall inner a, pristine_block (BlockQuote inner) a = pristine inner.
Proof.
  intros inner a.
  change (pristine_block (BlockQuote inner) a)
    with ((fix go (l : blocks) : bool :=
             match l with
             | [] => true
             | Node _ a' x :: rest => (pristine_block x a' && go rest)%bool
             end) inner).
  rewrite pristine_inner_go. reflexivity.
Qed.

Lemma pristine_div :
  forall inner a, pristine_block (Div inner) a = pristine inner.
Proof.
  intros inner a.
  change (pristine_block (Div inner) a)
    with ((fix go (l : blocks) : bool :=
             match l with
             | [] => true
             | Node _ a' x :: rest => (pristine_block x a' && go rest)%bool
             end) inner).
  rewrite pristine_inner_go. reflexivity.
Qed.

Lemma pristine_blist :
  forall sp items a,
    pristine_block (BulletList sp items) a = pristine_items items.
Proof.
  intros sp items a.
  change (pristine_block (BulletList sp items) a)
    with ((fix goit (its : list blocks) : bool :=
             match its with
             | [] => true
             | it :: rest =>
                 ((fix go (l : blocks) : bool :=
                     match l with
                     | [] => true
                     | Node _ a' x :: r => (pristine_block x a' && go r)%bool
                     end) it && goit rest)%bool
             end) items).
  induction items as [|it rest IH]; [reflexivity|].
  cbn [pristine_items]. rewrite pristine_inner_go, IH. reflexivity.
Qed.

Lemma pristine_olist :
  forall oa sp items a,
    pristine_block (OrderedList oa sp items) a = pristine_items items.
Proof.
  intros oa sp items a.
  change (pristine_block (OrderedList oa sp items) a)
    with ((fix goit (its : list blocks) : bool :=
             match its with
             | [] => true
             | it :: rest =>
                 ((fix go (l : blocks) : bool :=
                     match l with
                     | [] => true
                     | Node _ a' x :: r => (pristine_block x a' && go r)%bool
                     end) it && goit rest)%bool
             end) items).
  induction items as [|it rest IH]; [reflexivity|].
  cbn [pristine_items]. rewrite pristine_inner_go, IH. reflexivity.
Qed.

Lemma pristine_cons :
  forall p a b rest,
    pristine (Node p a b :: rest) = (pristine_block b a && pristine rest)%bool.
Proof. reflexivity. Qed.

Definition pristine_node (n : node block) : bool :=
  match n with Node _ a b => pristine_block b a end.

Lemma pristine_cons_node :
  forall n rest, pristine (n :: rest) = (pristine_node n && pristine rest)%bool.
Proof. intros [p a b] rest. reflexivity. Qed.

(*
Undoing the identifiers
-----------------------
*)

Lemma undo_assign_ids :
  forall b p a st,
    pristine_block b a = true ->
    undo_pass_node (snd (assign_ids b p a st)) = [Node p a b].
Proof.
  intros b.
  induction b using block_ind2 with
    (Q := fun bs => forall st,
            pristine bs = true ->
            undo_pass (snd (assign_ids_list bs st)) = bs)
    (R := fun its => forall st,
            pristine_items its = true ->
            undo_pass_items (snd (assign_ids_items its st)) = its);
    intros; try reflexivity.
  - (* Section: excluded by pristine *)
    discriminate.
  - (* Heading *)
    cbn [pristine_block] in H.
    unfold assign_ids, assign_heading_id.
    destruct (lookup_attr "id" a) as [v|] eqn:Eid; [discriminate|].
    cbn [snd undo_pass_node undo_pass_block].
    rewrite strip_id_cons by exact Eid. reflexivity.
  - (* BlockQuote *)
    rewrite pristine_quote in H.
    rewrite assign_ids_quote.
    destruct (assign_ids_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd undo_pass_node]. rewrite undo_pass_quote.
    change bs' with (snd (st', bs')). rewrite <- E.
    rewrite IHb by exact H. reflexivity.
  - (* Div: the same, one constructor over *)
    rewrite pristine_div in H.
    rewrite assign_ids_div.
    destruct (assign_ids_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd undo_pass_node]. rewrite undo_pass_div.
    change bs' with (snd (st', bs')). rewrite <- E.
    rewrite IHb by exact H. reflexivity.
  - (* OrderedList: the same shape as the bullet case below *)
    rewrite pristine_olist in H.
    rewrite assign_ids_olist.
    destruct (assign_ids_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd undo_pass_node]. rewrite undo_pass_olist.
    change its' with (snd (st', its')). rewrite <- E.
    rewrite IHb by exact H. reflexivity.
  - (* BulletList: the item list, which is what R is for *)
    rewrite pristine_blist in H.
    rewrite assign_ids_blist.
    destruct (assign_ids_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd undo_pass_node]. rewrite undo_pass_blist.
    change its' with (snd (st', its')). rewrite <- E.
    rewrite IHb by exact H. reflexivity.
  - (* Node p a b :: rest ([] is closed by reflexivity above) *)
    rewrite pristine_cons in H. apply andb_true_iff in H as [Hb Hrest].
    cbn [assign_ids_list assign_ids_node].
    destruct (assign_ids b p a st) as [st1 n1] eqn:E1.
    destruct (assign_ids_list rest st1) as [st2 rest1] eqn:E2.
    cbn [snd]. rewrite undo_pass_cons.
    replace n1 with (snd (assign_ids b p a st)) by (rewrite E1; reflexivity).
    rewrite IHb by exact Hb.
    replace rest1 with (snd (assign_ids_list rest st1))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
  - (* R's cons: one item, then the rest *)
    cbn [pristine_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [assign_ids_items].
    destruct (assign_ids_list it st) as [s1 it1] eqn:E1.
    destruct (assign_ids_items rest s1) as [s2 rest1] eqn:E2.
    cbn [snd undo_pass_items].
    replace it1 with (snd (assign_ids_list it st)) by (rewrite E1; reflexivity).
    rewrite IHb by exact Hit.
    replace rest1 with (snd (assign_ids_items rest s1))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
Qed.

(* The list version, as in Wf.v: block_ind2 proves it as its Q, but the
   principle does not hand it back as a lemma. *)
Lemma undo_assign_ids_list :
  forall bs st,
    pristine bs = true -> undo_pass (snd (assign_ids_list bs st)) = bs.
Proof.
  induction bs as [|[p a b] rest IH]; intros st H; [reflexivity|].
  rewrite pristine_cons in H. apply andb_true_iff in H as [Hb Hrest].
  cbn [assign_ids_list assign_ids_node].
  destruct (assign_ids b p a st) as [st1 n1] eqn:E1.
  destruct (assign_ids_list rest st1) as [st2 rest1] eqn:E2.
  cbn [snd]. rewrite undo_pass_cons.
  replace n1 with (snd (assign_ids b p a st)) by (rewrite E1; reflexivity).
  rewrite undo_assign_ids by exact Hb.
  replace rest1 with (snd (assign_ids_list rest st1))
    by (rewrite E2; reflexivity).
  rewrite IH by exact Hrest. reflexivity.
Qed.

(*
Undoing the sections
--------------------

Unconditional: sectionize only ever wraps, and undo_pass unwraps.  A
`Section` already present in the input is flattened the same way on both
sides, so it needs no hypothesis — only the identifier half cares what
the input looked like.
*)

Lemma undo_pass_app :
  forall l1 l2, undo_pass (l1 ++ l2)%list = (undo_pass l1 ++ undo_pass l2)%list.
Proof.
  induction l1 as [|[p a b] rest IH]; intros l2; [reflexivity|].
  cbn [app undo_pass]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma set_first_app :
  forall z X Y,
    nonempty X = true -> set_first z (X ++ Y)%list = (set_first z X ++ Y)%list.
Proof. intros z [|[p a b] X'] Y H; [discriminate|reflexivity]. Qed.

(* The blocks the stack has consumed so far, recovered.  Entries hold
   their accumulators reversed, and every entry above the document's
   carries the attributes that came off its heading — hence the
   set_first, which is why those entries have to erase to something
   nonempty.  That, plus "only the document sits at level 0", is the
   whole invariant. *)
Fixpoint stack_erase (stk : sect_state) : blocks :=
  match stk with
  | [] => []
  | [(_, _, acc)] => undo_pass (rev acc)
  | (_, a, acc) :: outer =>
      (stack_erase outer ++ set_first (strip_id a) (undo_pass (rev acc)))%list
  end.

(* The only thing erasure needs of the stack: every entry above the
   document's erases to something nonempty, so that set_first has a node
   to put the section's attributes back on.  True by construction — such
   an entry always starts with the heading that opened it. *)
Fixpoint sect_ok (stk : sect_state) : bool :=
  match stk with
  | [] => false
  | [_] => true
  | (_, _, acc) :: outer => (nonempty (undo_pass (rev acc)) && sect_ok outer)%bool
  end.

Lemma stack_erase_cons :
  forall l a acc outer,
    outer <> [] ->
    stack_erase ((l, a, acc) :: outer)
    = (stack_erase outer ++ set_first (strip_id a) (undo_pass (rev acc)))%list.
Proof. intros l a acc [|e outer] H; [contradiction|reflexivity]. Qed.

Lemma sect_ok_cons :
  forall l a acc outer,
    outer <> [] ->
    sect_ok ((l, a, acc) :: outer)
    = (nonempty (undo_pass (rev acc)) && sect_ok outer)%bool.
Proof. intros l a acc [|e outer] H; [contradiction|reflexivity]. Qed.

Lemma sect_ok_nonnil : forall stk, sect_ok stk = true -> stk <> [].
Proof. intros [|e stk] H; [discriminate|congruence]. Qed.

Lemma close_ge_ok :
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
    rewrite rev_app_distr, undo_pass_app.
    destruct (undo_pass (rev acc)) as [|x r]; [discriminate|reflexivity].
Qed.

Lemma close_ge_erase :
  forall stk lvl pending,
    sect_ok stk = true ->
    stack_erase (close_ge lvl pending stk)
    = (stack_erase stk ++ undo_pass (rev pending))%list.
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros lvl pending Hs;
    [discriminate|].
  destruct outer as [|e outer'].
  - rewrite close_ge_singleton. cbn [stack_erase].
    rewrite rev_app_distr, undo_pass_app. reflexivity.
  - rewrite sect_ok_cons in Hs by discriminate.
    apply andb_true_iff in Hs as [Hne Houter].
    rewrite stack_erase_cons by discriminate.
    rewrite close_ge_cons by discriminate. destruct (Nat.leb lvl l).
    + rewrite (IH _ _ Houter).
      cbn [undo_pass rev app]. rewrite app_nil_r.
      rewrite undo_pass_section, rev_app_distr, undo_pass_app.
      rewrite set_first_app by exact Hne.
      rewrite app_assoc. reflexivity.
    + rewrite stack_erase_cons by discriminate.
      rewrite rev_app_distr, undo_pass_app.
      rewrite set_first_app by exact Hne.
      rewrite app_assoc. reflexivity.
Qed.

(* close_all always lands on the document entry alone — which is what
   lets sect_bottom read the answer off. *)
Lemma close_all_singleton :
  forall stk pending,
    stk <> [] -> exists l a acc, close_all pending stk = [(l, a, acc)].
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros pending H; [contradiction|].
  destruct outer as [|e outer'].
  - exists l, a, (pending ++ acc)%list. reflexivity.
  - rewrite close_all_cons by discriminate. apply IH. discriminate.
Qed.

Lemma close_all_erase :
  forall stk pending,
    sect_ok stk = true ->
    stack_erase (close_all pending stk)
    = (stack_erase stk ++ undo_pass (rev pending))%list.
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros pending Hs; [discriminate|].
  destruct outer as [|e outer'].
  - cbn [close_all stack_erase].
    rewrite rev_app_distr, undo_pass_app. reflexivity.
  - rewrite sect_ok_cons in Hs by discriminate.
    apply andb_true_iff in Hs as [Hne Houter].
    rewrite stack_erase_cons by discriminate.
    rewrite close_all_cons by discriminate.
    rewrite (IH _ Houter).
    cbn [undo_pass rev app]. rewrite app_nil_r.
    rewrite undo_pass_section, rev_app_distr, undo_pass_app.
    rewrite set_first_app by exact Hne.
    rewrite app_assoc. reflexivity.
Qed.

Lemma sect_push_ok :
  forall stk n, sect_ok stk = true -> sect_ok (sect_push n stk) = true.
Proof.
  intros [|[[l a] acc] outer] n Hs; [discriminate|].
  cbn [sect_push]. destruct outer as [|e outer']; [exact Hs|].
  rewrite sect_ok_cons in Hs |- * by discriminate.
  apply andb_true_iff in Hs as [Hne Houter].
  rewrite Houter, andb_true_r.
  cbn [rev]. rewrite undo_pass_app.
  destruct (undo_pass (rev acc)) as [|x r]; [discriminate|reflexivity].
Qed.

Lemma sect_push_erase :
  forall stk n,
    sect_ok stk = true ->
    stack_erase (sect_push n stk) = (stack_erase stk ++ undo_pass_node n)%list.
Proof.
  intros [|[[l a] acc] outer] n Hs; [discriminate|].
  cbn [sect_push]. destruct outer as [|e outer'].
  - cbn [stack_erase rev]. rewrite undo_pass_app, undo_pass_single.
    reflexivity.
  - rewrite sect_ok_cons in Hs by discriminate.
    apply andb_true_iff in Hs as [Hne _].
    rewrite !stack_erase_cons by discriminate.
    cbn [rev]. rewrite undo_pass_app, undo_pass_single.
    rewrite set_first_app by exact Hne.
    rewrite app_assoc. reflexivity.
Qed.

Lemma sect_step_ok :
  forall stk n, sect_ok stk = true -> sect_ok (sect_step stk n) = true.
Proof.
  intros stk [p a b] Hs. destruct b; try (apply sect_push_ok; exact Hs).
  cbn [sect_step].
  pose proof (close_ge_ok stk level [] Hs) as Hc.
  destruct (close_ge level [] stk) as [|e rest] eqn:E; [discriminate|].
  rewrite sect_ok_cons by discriminate.
  rewrite Hc, andb_true_r.
  (* a heading erases to exactly one block, so the entry is nonempty *)
  cbn [rev undo_pass undo_pass_block app nonempty]. reflexivity.
Qed.

Lemma sect_step_erase :
  forall stk n,
    sect_ok stk = true ->
    stack_erase (sect_step stk n) = (stack_erase stk ++ undo_pass_node n)%list.
Proof.
  intros stk [p a b] Hs. destruct b; try (apply sect_push_erase; exact Hs).
  cbn [sect_step].
  pose proof (close_ge_ok stk level [] Hs) as Hc.
  pose proof (close_ge_erase stk level [] Hs) as He.
  destruct (close_ge level [] stk) as [|e rest] eqn:E; [discriminate|].
  rewrite stack_erase_cons by discriminate.
  rewrite He. cbn [rev undo_pass]. rewrite app_nil_r.
  cbn [rev undo_pass undo_pass_node undo_pass_block strip_id filter
       set_first app].
  reflexivity.
Qed.

Lemma fold_sect_step_ok :
  forall bs stk,
    sect_ok stk = true -> sect_ok (fold_left sect_step bs stk) = true.
Proof.
  induction bs as [|n rest IH]; intros stk Hs; [exact Hs|].
  cbn [fold_left]. apply IH. apply sect_step_ok. exact Hs.
Qed.

Lemma fold_sect_step_erase :
  forall bs stk,
    sect_ok stk = true ->
    stack_erase (fold_left sect_step bs stk)
    = (stack_erase stk ++ undo_pass bs)%list.
Proof.
  induction bs as [|n rest IH]; intros stk Hs.
  - cbn [fold_left undo_pass]. rewrite app_nil_r. reflexivity.
  - cbn [fold_left]. rewrite IH by (apply sect_step_ok; exact Hs).
    rewrite sect_step_erase by exact Hs.
    rewrite undo_pass_cons, app_assoc. reflexivity.
Qed.

(** Sectioning is invisible to erasure: it only wraps, and undo_pass
    unwraps exactly what it wrapped. *)
Lemma undo_sectionize :
  forall bs, undo_pass (sectionize bs) = undo_pass bs.
Proof.
  intros bs. unfold sectionize.
  pose proof (fold_sect_step_ok bs sect_init eq_refl) as Hok.
  pose proof (fold_sect_step_erase bs sect_init eq_refl) as Her.
  cbn [stack_erase rev undo_pass] in Her.
  destruct (close_all_singleton _ [] (sect_ok_nonnil _ Hok)) as [l [a [acc E]]].
  pose proof (close_all_erase _ [] Hok) as Hc.
  rewrite E in Hc. cbn [stack_erase rev undo_pass] in Hc.
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
  forall bs, pristine bs = true -> undo_pass (doc_blocks (doc_pass bs)) = bs.
Proof.
  intros bs H. unfold doc_pass.
  destruct (assign_ids_list bs id_state_init) as [st bs'] eqn:E.
  cbn [doc_blocks]. rewrite undo_sectionize.
  replace bs' with (snd (assign_ids_list bs id_state_init))
    by (rewrite E; reflexivity).
  apply undo_assign_ids_list. exact H.
Qed.

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
