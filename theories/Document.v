(* ai-disclosure: autonomous *)

(** * Whole-document resolution

   The whole-document pass is the part of parsing that is a function of the
   finished block list rather than of a single line.

   It runs strictly *after* `Parser.parse_blocks`, never inside the fold.
   That separation is deliberate and load-bearing: Phase 3's locality
   theorem says inline classification does not depend on the reference and
   note maps, which is only true if those maps are built by a pass the
   line fold cannot see.

   Three computations live here today:

   - Auto-identifiers and implicit heading references, assigned in
     document order because uniqueness suffixes depend on what came
     before (djot.js `getUniqueIdentifier`, parse.ts:193).
   - Section nesting: a level-driven container stack over the top-level
     block list, moving each heading's id onto the section that wraps it
     (djot.js parse.ts:769-792, the id move at :788).

   - Footnote collection: recursively remove definition containers from
     visible block sequences and assign their cleaned bodies into the
     document note map.

   Reference definitions are the same shape of computation — block syntax
   that contributes only a side-table entry — and are read here without
   being removed from the retained parser tree.

   Sectioning is top-level only.  djot.js pushes a section container only
   when the enclosing container tracks a heading level, which the document
   does and a block quote does not, so `> # h` yields a bare
   `<h1 id="h">` (djot.js test/block_quote.test).  Identifiers, by
   contrast, are assigned everywhere and share one counter. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Ast Parser.
Import ListNotations.

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
  (* an autolink carries its region as `text`, which `addStringContent`
     pushes like any other (parse.ts:44) -- so it reaches a heading id
     and an image `alt` *)
  | UrlLink s | EmailLink s => s
  | Symbol _ | NonBreakingSpace => ""
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
   that label is already spoken for.  djot.js checks the explicit
   `references` too; we do not, because `Html.doc_refs` appends the
   implicit map after the explicit one and `alist_lookup` takes the
   first, so an explicit definition wins at lookup instead. *)
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
  let text := inlines_text ils in
  match lookup_attr "id" a with
  (* An explicit id wins, and takes its slot.  The implicit reference is
     registered either way: djot.js reads its destination off
     `attributes?.id || autoAttributes?.id` (parse.ts:764), so `{#foo}`
     over `# Introduction` makes `[Introduction][]` a link to `#foo`. *)
  | Some ident =>
      (add_auto_ref (normalize_label text) ident (register_id a st),
       Node p a (Heading lvl ils))
  | None =>
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
  | FootnoteDef label bs =>
      let (st', bs') := go bs (register_id a st) in
      (st', Node p a (FootnoteDef label bs'))
  (* Its one block is a node, not a list, so the recursion is on the
     payload directly and no list wrapper is needed. *)
  | Keyed label (Node p' a' x) =>
      let (st', n') := assign_ids x p' a' (register_id a st) in
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
  (* The remaining containers -- Section and the task list --
     are not reachable from the line fold yet (`Wf.supported` is the
     record of that).  Each needs its arm here when it lands, or a
     heading inside it silently goes without an identifier.  A table is
     reachable and still belongs here: its cells and its caption hold
     inlines, so there is no heading inside one to find. *)
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

(* The same over definition items, whose term half is carried through
   untouched: it is inlines, and no identifier is assigned inside one. *)
Fixpoint assign_ids_def_items (its : list (inlines * blocks)) (st : id_state)
  : id_state * list (inlines * blocks) :=
  match its with
  | [] => (st, [])
  | (term, it) :: rest =>
      let (s1, it1) := assign_ids_list it st in
      let (s2, rest1) := assign_ids_def_items rest s1 in
      (s2, (term, it1) :: rest1)
  end.

Fixpoint assign_ids_task_items (its : list (task_status * blocks)) (st : id_state)
  : id_state * list (task_status * blocks) :=
  match its with
  | [] => (st, [])
  | (chk, it) :: rest =>
      let (s1, it1) := assign_ids_list it st in
      let (s2, rest1) := assign_ids_task_items rest s1 in
      (s2, (chk, it1) :: rest1)
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

Lemma assign_ids_foot :
  forall p a label bs st,
    assign_ids (FootnoteDef label bs) p a st
    = let (st', bs') := assign_ids_list bs (register_id a st) in
      (st', Node p a (FootnoteDef label bs')).
Proof.
  intros p a label bs st. cbn [assign_ids].
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

(* The definition arm, whose inner fixpoint differs from the bullet's
   only in carrying the term past the traversal. *)
Lemma assign_ids_deflist :
  forall p a sp items st,
    assign_ids (DefinitionList sp items) p a st
    = let (st', items') := assign_ids_def_items items (register_id a st) in
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
                             let (s2, n2) := assign_ids x p' a' s' in
                             let (s3, r1) := go r s2 in
                             (s3, n2 :: r1)
                         end) it s in
                    let (s4, rest1) := god rest s1 in
                    (s4, (term, it1) :: rest1)
                end) its st = assign_ids_def_items its st).
  { induction its as [|[term it] rest IH]; intros st; [reflexivity|].
    cbn [assign_ids_def_items]. rewrite assign_ids_inner_go.
    destruct (assign_ids_list it st) as [s1 it1]. rewrite IH. reflexivity. }
  intros p a sp items st. cbn [assign_ids]. rewrite H. reflexivity.
Qed.

Lemma assign_ids_def_items_nonempty :
  forall its st,
    nonempty (snd (assign_ids_def_items its st)) = nonempty its.
Proof.
  intros [|[term it] rest] st; [reflexivity|].
  cbn [assign_ids_def_items].
  destruct (assign_ids_list it st) as [s1 it1].
  destruct (assign_ids_def_items rest s1) as [s2 rest1].
  reflexivity.
Qed.

Lemma assign_ids_tasklist :
  forall p a sp items st,
    assign_ids (TaskList sp items) p a st
    = let (st', items') := assign_ids_task_items items (register_id a st) in
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
                             let (s2, n2) := assign_ids x p' a' s' in
                             let (s3, r1) := go r s2 in
                             (s3, n2 :: r1)
                         end) it s in
                    let (s4, rest1) := got rest s1 in
                    (s4, (chk, it1) :: rest1)
                end) its st = assign_ids_task_items its st).
  { induction its as [|[chk it] rest IH]; intros st; [reflexivity|].
    cbn [assign_ids_task_items]. rewrite assign_ids_inner_go.
    destruct (assign_ids_list it st) as [s1 it1]. rewrite IH. reflexivity. }
  intros p a sp items st. cbn [assign_ids]. rewrite H. reflexivity.
Qed.

Lemma assign_ids_task_items_nonempty :
  forall its st,
    nonempty (snd (assign_ids_task_items its st)) = nonempty its.
Proof.
  intros [|[chk it] rest] st; [reflexivity|].
  cbn [assign_ids_task_items].
  destruct (assign_ids_list it st) as [s1 it1].
  destruct (assign_ids_task_items rest s1) as [s2 rest1].
  reflexivity.
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
(* The section builder and the pass are the only parts of this file that
   build a node of their own, so they are the only ones the position
   policy reaches.  Closing the section before the lemmas below leaves
   every one of them meaning the semantic instance, which is what they
   were about. *)
Section WithPolicy.
Context {P : PosPolicy}.

Definition sect_state : Type := list (nat * attr * blocks).

Definition sect_init : sect_state := [(0, [], [])].

(* Close every section a level-`lvl` heading interrupts, carrying the
   already-closed nodes inward-out in `pending` so each lands inside the
   section that encloses it.  Recursion is on the stack, so this is
   structural — nesting the current section into its parent *before*
   testing the parent is what the `pending` argument buys. *)
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
Lemma close_ge_singleton :
  forall lvl pending l a acc,
    close_ge lvl pending [(l, a, acc)] = [(l, a, (pending ++ acc)%list)].
Proof. reflexivity. Qed.

Lemma close_ge_cons :
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

(*
Reference definitions
=====================

A definition contributes no HTML and no structure — only an entry in the
document's map, which is why it is collected here rather than in the line
fold, and why `undo_pass` below needs no arm for it: the pass reads the
block tree and does not touch it.

Nesting is not a barrier: a definition inside a quote or a list item
registers with the document all the same (checked against djot.js), so
the traversal descends into every container the fold can build.
*)

(* djot.js keys the map by normalized label and assigns into a JS object,
   so a repeated label keeps the first definition's position and takes the
   last one's value (parse.ts:336).  An *empty* label is dropped there by
   a truthiness test on the raw key, before normalization — so `[ ]: u`,
   whose normalized label is empty, is still recorded. *)
Definition add_ref (p : pos) (a : attr) (b : block) (m : reference_map)
  : reference_map :=
  match b with
  | RefDef label dest =>
      if nonempty_str label
      then alist_set (normalize_label label) (dest, a) m
      else m
  | _ => m
  end.

(* Pre-order, which is document order, with the same inlined list
   recursion `assign_ids` needs and for the same guard-checker reason. *)
Fixpoint collect_refs (b : block) (p : pos) (a : attr) (m : reference_map)
  {struct b} : reference_map :=
  let go :=
    fix go (ns : blocks) (acc : reference_map) {struct ns} : reference_map :=
      match ns with
      | [] => acc
      | Node p' a' x :: rest => go rest (collect_refs x p' a' acc)
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
                        | Node p' a' x :: more => go' more (collect_refs x p' a' acc')
                        end) it acc)
      end in
  match b with
  | BlockQuote bs | Div bs | Section bs | FootnoteDef _ bs => go bs m
  | Keyed _ (Node p' a' x) => collect_refs x p' a' m
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
                          | Node p' a' x :: more => go' more (collect_refs x p' a' acc')
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
                          | Node p' a' x :: more => go' more (collect_refs x p' a' acc')
                          end) it acc)
         end) items m
  | _ => add_ref p a b m
  end.

Fixpoint collect_refs_list (ns : blocks) (m : reference_map) : reference_map :=
  match ns with
  | [] => m
  | Node p a b :: rest => collect_refs_list rest (collect_refs b p a m)
  end.

(** Remove footnote-definition nodes while assigning their recursively
    cleaned bodies into the document table.  A definition is assigned
    after its body, matching the order in which nested containers close. *)
Fixpoint collect_notes (b : block) (p : pos) (a : attr) (m : note_map)
  {struct b} : note_map * option (node block) :=
  let go :=
    fix go (ns : blocks) (acc : note_map) {struct ns} : note_map * blocks :=
      match ns with
      | [] => (acc, [])
      | Node p' a' x :: rest =>
          let (acc1, n1) := collect_notes x p' a' acc in
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
      let (m', o) := collect_notes x p' a' m in
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

Fixpoint collect_notes_list (ns : blocks) (m : note_map) : note_map * blocks :=
  match ns with
  | [] => (m, [])
  | Node p a b :: rest =>
      let (m1, n1) := collect_notes b p a m in
      let (m2, rest1) := collect_notes_list rest m1 in
      match n1 with
      | Some n => (m2, n :: rest1)
      | None => (m2, rest1)
      end
  end.

Fixpoint collect_notes_items (its : list blocks) (m : note_map)
  : note_map * list blocks :=
  match its with
  | [] => (m, [])
  | it :: rest =>
      let (m1, it1) := collect_notes_list it m in
      let (m2, rest1) := collect_notes_items rest m1 in
      (m2, it1 :: rest1)
  end.

Fixpoint collect_notes_def_items (its : list (inlines * blocks)) (m : note_map)
  : note_map * list (inlines * blocks) :=
  match its with
  | [] => (m, [])
  | (term, it) :: rest =>
      let (m1, it1) := collect_notes_list it m in
      let (m2, rest1) := collect_notes_def_items rest m1 in
      (m2, (term, it1) :: rest1)
  end.

Fixpoint collect_notes_task_items (its : list (task_status * blocks)) (m : note_map)
  : note_map * list (task_status * blocks) :=
  match its with
  | [] => (m, [])
  | (chk, it) :: rest =>
      let (m1, it1) := collect_notes_list it m in
      let (m2, rest1) := collect_notes_task_items rest m1 in
      (m2, (chk, it1) :: rest1)
  end.

Lemma collect_notes_items_nonempty :
  forall its m,
    nonempty (snd (collect_notes_items its m)) = nonempty its.
Proof.
  intros [|it rest] m; [reflexivity|].
  cbn [collect_notes_items].
  destruct (collect_notes_list it m) as [m1 it1].
  destruct (collect_notes_items rest m1) as [m2 rest1].
  reflexivity.
Qed.

Lemma collect_notes_inner_go :
  forall ns m,
    (fix go (ns' : blocks) (acc : note_map) {struct ns'}
       : note_map * blocks :=
       match ns' with
       | [] => (acc, [])
       | Node p a b :: rest =>
           let (acc1, n1) := collect_notes b p a acc in
           let (acc2, rest1) := go rest acc1 in
           match n1 with
           | Some n => (acc2, n :: rest1)
           | None => (acc2, rest1)
           end
       end) ns m = collect_notes_list ns m.
Proof.
  induction ns as [|[p a b] rest IH]; intros m; [reflexivity|].
  cbn [collect_notes_list].
  destruct (collect_notes b p a m) as [m1 [n|]] eqn:E;
    rewrite IH; reflexivity.
Qed.

Lemma collect_notes_inner_goit :
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
                    let (acc2, n1) := collect_notes b p a acc0 in
                    let (acc3, more1) := go more acc2 in
                    match n1 with
                    | Some n => (acc3, n :: more1)
                    | None => (acc3, more1)
                    end
                end) it acc in
           let (acc2, rest1) := goit rest acc1 in
           (acc2, it1 :: rest1)
       end) its m = collect_notes_items its m.
Proof.
  induction its as [|it rest IH]; intros m; [reflexivity|].
  cbn [collect_notes_items]. rewrite collect_notes_inner_go.
  destruct (collect_notes_list it m) as [m1 it1]. rewrite IH. reflexivity.
Qed.

Lemma collect_notes_quote :
  forall p a bs m,
    collect_notes (BlockQuote bs) p a m
    = let (m', bs') := collect_notes_list bs m in
      (m', Some (Node p a (BlockQuote bs'))).
Proof.
  intros p a bs m. cbn [collect_notes]. rewrite collect_notes_inner_go.
  reflexivity.
Qed.

Lemma collect_notes_div :
  forall p a bs m,
    collect_notes (Div bs) p a m
    = let (m', bs') := collect_notes_list bs m in
      (m', Some (Node p a (Div bs'))).
Proof.
  intros p a bs m. cbn [collect_notes]. rewrite collect_notes_inner_go.
  reflexivity.
Qed.

Lemma collect_notes_foot :
  forall p a label bs m,
    collect_notes (FootnoteDef label bs) p a m
    = let (m', bs') := collect_notes_list bs m in
      (alist_set (normalize_label label) bs' m', None).
Proof.
  intros p a label bs m. cbn [collect_notes]. rewrite collect_notes_inner_go.
  reflexivity.
Qed.

Lemma collect_notes_blist :
  forall p a sp items m,
    collect_notes (BulletList sp items) p a m
    = let (m', items') := collect_notes_items items m in
      (m', Some (Node p a (BulletList sp items'))).
Proof.
  intros p a sp items m. cbn [collect_notes]. rewrite collect_notes_inner_goit.
  reflexivity.
Qed.

Lemma collect_notes_deflist :
  forall p a sp items m,
    collect_notes (DefinitionList sp items) p a m
    = let (m', items') := collect_notes_def_items items m in
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
                             let (acc2, n1) := collect_notes b p a acc0 in
                             let (acc3, more1) := go more acc2 in
                             match n1 with
                             | Some n => (acc3, n :: more1)
                             | None => (acc3, more1)
                             end
                         end) it acc in
                    let (acc2, rest1) := god rest acc1 in
                    (acc2, (term, it1) :: rest1)
                end) its m = collect_notes_def_items its m).
  { induction its as [|[term it] rest IH]; intros m; [reflexivity|].
    cbn [collect_notes_def_items]. rewrite collect_notes_inner_go.
    destruct (collect_notes_list it m) as [m1 it1]. rewrite IH. reflexivity. }
  intros p a sp items m. cbn [collect_notes]. rewrite H. reflexivity.
Qed.

Lemma collect_notes_def_items_nonempty :
  forall its m,
    nonempty (snd (collect_notes_def_items its m)) = nonempty its.
Proof.
  intros [|[term it] rest] m; [reflexivity|].
  cbn [collect_notes_def_items].
  destruct (collect_notes_list it m) as [m1 it1].
  destruct (collect_notes_def_items rest m1) as [m2 rest1].
  reflexivity.
Qed.

Lemma collect_notes_tasklist :
  forall p a sp items m,
    collect_notes (TaskList sp items) p a m
    = let (m', items') := collect_notes_task_items items m in
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
                             let (acc2, n1) := collect_notes b p a acc0 in
                             let (acc3, more1) := go more acc2 in
                             match n1 with
                             | Some n => (acc3, n :: more1)
                             | None => (acc3, more1)
                             end
                         end) it acc in
                    let (acc2, rest1) := got rest acc1 in
                    (acc2, (chk, it1) :: rest1)
                end) its m = collect_notes_task_items its m).
  { induction its as [|[chk it] rest IH]; intros m; [reflexivity|].
    cbn [collect_notes_task_items]. rewrite collect_notes_inner_go.
    destruct (collect_notes_list it m) as [m1 it1]. rewrite IH. reflexivity. }
  intros p a sp items m. cbn [collect_notes]. rewrite H. reflexivity.
Qed.

Lemma collect_notes_task_items_nonempty :
  forall its m,
    nonempty (snd (collect_notes_task_items its m)) = nonempty its.
Proof.
  intros [|[chk it] rest] m; [reflexivity|].
  cbn [collect_notes_task_items].
  destruct (collect_notes_list it m) as [m1 it1].
  destruct (collect_notes_task_items rest m1) as [m2 rest1].
  reflexivity.
Qed.

Lemma collect_notes_olist :
  forall p a oa sp items m,
    collect_notes (OrderedList oa sp items) p a m
    = let (m', items') := collect_notes_items items m in
      (m', Some (Node p a (OrderedList oa sp items'))).
Proof.
  intros p a oa sp items m. cbn [collect_notes].
  rewrite collect_notes_inner_goit. reflexivity.
Qed.

Definition doc_pass (bs : blocks) : doc :=
  let (st, bs') := assign_ids_list bs id_state_init in
  let (notes, visible) := collect_notes_list bs' [] in
  {| doc_blocks := sectionize visible
   ; doc_footnotes := notes
   ; doc_references := collect_refs_list bs' []
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
  | FootnoteDef label inner => [Node p a (FootnoteDef label (go inner))]
  (* `Section` is the one block whose undo is not a single node, and
     `sectionize` builds none below the top level, so the default is
     unreachable and the payload comes back as itself. *)
  | Keyed label (Node p' a' x) =>
      [Node p a (Keyed label
         (hd (Node p' a' x) (undo_pass_block x p' a')))]
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

Fixpoint undo_pass_def_items (its : list (inlines * blocks))
  : list (inlines * blocks) :=
  match its with
  | [] => []
  | (term, it) :: rest => (term, undo_pass it) :: undo_pass_def_items rest
  end.

Fixpoint undo_pass_task_items (its : list (task_status * blocks))
  : list (task_status * blocks) :=
  match its with
  | [] => []
  | (chk, it) :: rest => (chk, undo_pass it) :: undo_pass_task_items rest
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

Lemma undo_pass_foot :
  forall label inner p a,
    undo_pass_block (FootnoteDef label inner) p a
    = [Node p a (FootnoteDef label (undo_pass inner))].
Proof.
  intros label inner p a.
  change (undo_pass_block (FootnoteDef label inner) p a)
    with [Node p a (FootnoteDef label
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

(* Convertible, where the bullet arm needs `undo_pass_inner_goit`: the
   definition traversal has one inner fixpoint and `undo_pass_def_items`
   is spelled as that fixpoint, so nothing has to be identified. *)
Lemma undo_pass_deflist :
  forall sp items p a,
    undo_pass_block (DefinitionList sp items) p a
    = [Node p a (DefinitionList sp (undo_pass_def_items items))].
Proof. reflexivity. Qed.

Lemma undo_pass_tasklist :
  forall sp items p a,
    undo_pass_block (TaskList sp items) p a
    = [Node p a (TaskList sp (undo_pass_task_items items))].
Proof. reflexivity. Qed.

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
  | FootnoteDef _ _ => false
  | BlockQuote inner | Div inner => go inner
  | Keyed _ (Node _ a' x) => pristine_block x a'
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

Fixpoint pristine_def_items (its : list (inlines * blocks)) : bool :=
  match its with
  | [] => true
  | (_, it) :: rest => (pristine it && pristine_def_items rest)%bool
  end.

Fixpoint pristine_task_items (its : list (task_status * blocks)) : bool :=
  match its with
  | [] => true
  | (_, it) :: rest => (pristine it && pristine_task_items rest)%bool
  end.

(* Splitting the term off keeps an item pristine: the block that leaves
   is a paragraph, and `pristine_block` asks nothing of one. *)
Lemma pristine_def_split :
  forall bs ils def,
    pristine bs = true -> def_split bs = Some (ils, def) -> pristine def = true.
Proof.
  induction bs as [|[q b x] rest IH]; intros ils def H E; [discriminate|].
  cbn [pristine] in H. apply andb_true_iff in H as [Hx Hrest].
  cbn [def_split] in E. destruct x; try discriminate E.
  - injection E as <- <-. exact Hrest.
  - destruct (def_split rest) as [[ils' more]|] eqn:Es; [|discriminate E].
    injection E as <- <-.
    cbn [pristine]. rewrite Hx. exact (IH ils' more Hrest eq_refl).
  - destruct (def_split rest) as [[ils' more]|] eqn:Es; [|discriminate E].
    injection E as <- <-.
    cbn [pristine]. rewrite Hx. exact (IH ils' more Hrest eq_refl).
Qed.

Lemma pristine_def_items_split :
  forall its,
    pristine_items its = true -> pristine_def_items (def_items its) = true.
Proof.
  unfold def_items. induction its as [|it rest IH]; [reflexivity|].
  cbn [pristine_items map pristine_def_items]. intros H.
  apply andb_true_iff in H as [Hit Hrest].
  destruct (def_split it) as [[ils def]|] eqn:E.
  - rewrite (def_item_some it _ E). cbn [snd].
    rewrite (pristine_def_split it ils def Hit E), (IH Hrest). reflexivity.
  - rewrite (def_item_none it E). cbn [snd].
    rewrite Hit, (IH Hrest). reflexivity.
Qed.

(* The collection pass needs only this projection of pristine: there is
   no definition node to remove.  Unlike pristine, assigned heading ids
   do not affect it, so it survives assign_ids. *)
Fixpoint notes_free_block (b : block) {struct b} : bool :=
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

Fixpoint notes_free (bs : blocks) : bool :=
  match bs with
  | [] => true
  | Node _ _ b :: rest => (notes_free_block b && notes_free rest)%bool
  end.

Fixpoint notes_free_items (its : list blocks) : bool :=
  match its with
  | [] => true
  | it :: rest => (notes_free it && notes_free_items rest)%bool
  end.

Fixpoint notes_free_def_items (its : list (inlines * blocks)) : bool :=
  match its with
  | [] => true
  | (_, it) :: rest => (notes_free it && notes_free_def_items rest)%bool
  end.

Fixpoint notes_free_task_items (its : list (task_status * blocks)) : bool :=
  match its with
  | [] => true
  | (_, it) :: rest => (notes_free it && notes_free_task_items rest)%bool
  end.

Lemma notes_free_inner_go :
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

Lemma notes_free_inner_goit :
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

Lemma notes_free_quote :
  forall bs, notes_free_block (BlockQuote bs) = notes_free bs.
Proof. intros bs. cbn [notes_free_block]. apply notes_free_inner_go. Qed.

Lemma notes_free_section :
  forall bs, notes_free_block (Section bs) = notes_free bs.
Proof. intros bs. cbn [notes_free_block]. apply notes_free_inner_go. Qed.

Lemma notes_free_div :
  forall bs, notes_free_block (Div bs) = notes_free bs.
Proof. intros bs. cbn [notes_free_block]. apply notes_free_inner_go. Qed.

Lemma notes_free_deflist :
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

Lemma notes_free_tasklist :
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

Lemma notes_free_blist :
  forall sp items,
    notes_free_block (BulletList sp items) = notes_free_items items.
Proof. intros sp items. cbn [notes_free_block]. apply notes_free_inner_goit. Qed.

Lemma notes_free_olist :
  forall oa sp items,
    notes_free_block (OrderedList oa sp items) = notes_free_items items.
Proof. intros oa sp items. cbn [notes_free_block]. apply notes_free_inner_goit. Qed.

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

Lemma pristine_deflist :
  forall sp items a,
    pristine_block (DefinitionList sp items) a = pristine_def_items items.
Proof.
  intros sp items a.
  change (pristine_block (DefinitionList sp items) a)
    with ((fix god (its : list (inlines * blocks)) : bool :=
             match its with
             | [] => true
             | (_, it) :: rest =>
                 ((fix go (l : blocks) : bool :=
                     match l with
                     | [] => true
                     | Node _ a' x :: r => (pristine_block x a' && go r)%bool
                     end) it && god rest)%bool
             end) items).
  induction items as [|[term it] rest IH]; [reflexivity|].
  cbn [pristine_def_items]. rewrite pristine_inner_go, IH. reflexivity.
Qed.

Lemma pristine_tasklist :
  forall sp items a,
    pristine_block (TaskList sp items) a = pristine_task_items items.
Proof.
  intros sp items a.
  change (pristine_block (TaskList sp items) a)
    with ((fix got (its : list (task_status * blocks)) : bool :=
             match its with
             | [] => true
             | (_, it) :: rest =>
                 ((fix go (l : blocks) : bool :=
                     match l with
                     | [] => true
                     | Node _ a' x :: r => (pristine_block x a' && go r)%bool
                     end) it && got rest)%bool
             end) items).
  induction items as [|[chk it] rest IH]; [reflexivity|].
  cbn [pristine_task_items]. rewrite pristine_inner_go, IH. reflexivity.
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
            undo_pass_items (snd (assign_ids_items its st)) = its)
    (D := fun its => forall st,
            pristine_def_items its = true ->
            undo_pass_def_items (snd (assign_ids_def_items its st)) = its)
    (K := fun its => forall st,
            pristine_task_items its = true ->
            undo_pass_task_items (snd (assign_ids_task_items its st)) = its);
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
  - (* TaskList: the same over K's *)
    rewrite pristine_tasklist in H.
    rewrite assign_ids_tasklist.
    destruct (assign_ids_task_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd undo_pass_node]. rewrite undo_pass_tasklist.
    change its' with (snd (st', its')). rewrite <- E.
    rewrite IHb by exact H. reflexivity.
  - (* DefinitionList: the bullet case again, over D's item list *)
    rewrite pristine_deflist in H.
    rewrite assign_ids_deflist.
    destruct (assign_ids_def_items items (register_id a st)) as [st' its'] eqn:E.
    cbn [snd undo_pass_node]. rewrite undo_pass_deflist.
    change its' with (snd (st', its')). rewrite <- E.
    rewrite IHb by exact H. reflexivity.
  - (* FootnoteDef: collection removes it, so pristine excludes it. *)
    discriminate.
  - (* Keyed: its one block, through Q at the singleton. *)
    destruct b as [p' a' x].
    cbn [pristine_block] in H.
    specialize (IHb (register_id a st)).
    cbn [assign_ids assign_ids_list assign_ids_node undo_pass undo_pass_node
      snd] in *.
    destruct (assign_ids x p' a' (register_id a st)) as [st1 n1] eqn:E1.
    cbn [snd] in *.
    assert (Hu : undo_pass [n1] = [Node p' a' x])
      by (apply IHb; cbn [pristine pristine_node]; rewrite H; reflexivity).
    destruct n1 as [q b1 y].
    cbn [undo_pass undo_pass_node] in Hu. rewrite app_nil_r in Hu.
    cbn [undo_pass_node undo_pass_block]. rewrite Hu. reflexivity.
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
  - (* D's cons: the term rides through untouched *)
    cbn [pristine_def_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [assign_ids_def_items].
    destruct (assign_ids_list it st) as [s1 it1] eqn:E1.
    destruct (assign_ids_def_items rest s1) as [s2 rest1] eqn:E2.
    cbn [snd undo_pass_def_items].
    replace it1 with (snd (assign_ids_list it st)) by (rewrite E1; reflexivity).
    rewrite IHb by exact Hit.
    replace rest1 with (snd (assign_ids_def_items rest s1))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
  - (* K's cons: the status rides through untouched *)
    cbn [pristine_task_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [assign_ids_task_items].
    destruct (assign_ids_list it st) as [s1 it1] eqn:E1.
    destruct (assign_ids_task_items rest s1) as [s2 rest1] eqn:E2.
    cbn [snd undo_pass_task_items].
    replace it1 with (snd (assign_ids_list it st)) by (rewrite E1; reflexivity).
    rewrite IHb by exact Hit.
    replace rest1 with (snd (assign_ids_task_items rest s1))
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

Lemma collect_notes_pristine_block :
  forall b p a m,
    notes_free_block b = true ->
    collect_notes b p a m = (m, Some (Node p a b)).
Proof.
  intros b. induction b using block_ind2 with
    (Q := fun bs => forall m,
        notes_free bs = true -> collect_notes_list bs m = (m, bs))
    (R := fun its => forall m,
        notes_free_items its = true -> collect_notes_items its m = (m, its))
    (D := fun its => forall m,
        notes_free_def_items its = true ->
        collect_notes_def_items its m = (m, its))
    (K := fun its => forall m,
        notes_free_task_items its = true ->
        collect_notes_task_items its m = (m, its));
    intros; try reflexivity.
  - rewrite notes_free_quote in H. rewrite collect_notes_quote, IHb by exact H.
    reflexivity.
  - rewrite notes_free_div in H. rewrite collect_notes_div, IHb by exact H.
    reflexivity.
  - rewrite notes_free_olist in H. rewrite collect_notes_olist, IHb by exact H.
    reflexivity.
  - rewrite notes_free_blist in H. rewrite collect_notes_blist, IHb by exact H.
    reflexivity.
  - rewrite notes_free_tasklist in H.
    rewrite collect_notes_tasklist, IHb by exact H. reflexivity.
  - rewrite notes_free_deflist in H.
    rewrite collect_notes_deflist, IHb by exact H. reflexivity.
  - discriminate.
  - (* Keyed: `Q` at the singleton says the block survives collection,
       and a key with a surviving block survives with it. *)
    destruct b as [p' a' x]. cbn [notes_free_block] in H.
    specialize (IHb m). cbn [notes_free] in IHb.
    rewrite H in IHb. cbn [collect_notes_list] in IHb.
    destruct (collect_notes x p' a' m) as [m1 n1] eqn:E1.
    destruct n1 as [n0|].
    + injection (IHb eq_refl) as <- ->.
      cbn [collect_notes]. rewrite E1. reflexivity.
    + discriminate (f_equal snd (IHb eq_refl)).
  - cbn [notes_free] in H. apply andb_true_iff in H as [Hb Hrest].
    cbn [collect_notes_list]. rewrite IHb by exact Hb.
    rewrite IHb0 by exact Hrest. reflexivity.
  - cbn [notes_free_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [collect_notes_items]. rewrite IHb by exact Hit.
    rewrite IHb0 by exact Hrest. reflexivity.
  - cbn [notes_free_def_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [collect_notes_def_items]. rewrite IHb by exact Hit.
    rewrite IHb0 by exact Hrest. reflexivity.
  - cbn [notes_free_task_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [collect_notes_task_items]. rewrite IHb by exact Hit.
    rewrite IHb0 by exact Hrest. reflexivity.
Qed.

Lemma collect_notes_list_pristine :
  forall bs m,
    notes_free bs = true -> collect_notes_list bs m = (m, bs).
Proof.
  induction bs as [|[p a b] rest IH]; intros m H; [reflexivity|].
  cbn [notes_free] in H. apply andb_true_iff in H as [Hb Hrest].
  cbn [collect_notes_list]. rewrite collect_notes_pristine_block by exact Hb.
  rewrite IH by exact Hrest. reflexivity.
Qed.

Lemma pristine_notes_free_block :
  forall b a, pristine_block b a = true -> notes_free_block b = true.
Proof.
  intros b. induction b using block_ind2 with
    (Q := fun bs => pristine bs = true -> notes_free bs = true)
    (R := fun its => pristine_items its = true -> notes_free_items its = true)
    (D := fun its =>
            pristine_def_items its = true -> notes_free_def_items its = true)
    (K := fun its =>
            pristine_task_items its = true -> notes_free_task_items its = true);
    intros; try reflexivity.
  - discriminate.
  - rewrite pristine_quote in H. rewrite notes_free_quote. apply IHb. exact H.
  - rewrite pristine_div in H. rewrite notes_free_div. apply IHb. exact H.
  - rewrite pristine_olist in H. rewrite notes_free_olist. apply IHb. exact H.
  - rewrite pristine_blist in H. rewrite notes_free_blist. apply IHb. exact H.
  - rewrite pristine_tasklist in H. rewrite notes_free_tasklist.
    apply IHb. exact H.
  - rewrite pristine_deflist in H. rewrite notes_free_deflist.
    apply IHb. exact H.
  - discriminate.
  - (* Keyed: both predicates read straight through to the one block. *)
    destruct b as [p' a' x]. cbn [pristine_block notes_free_block] in *.
    cbn [pristine notes_free] in IHb. rewrite H in IHb.
    specialize (IHb eq_refl). rewrite andb_true_r in IHb. exact IHb.
  - rewrite pristine_cons in H. apply andb_true_iff in H as [Hb Hrest].
    cbn [notes_free]. rewrite (IHb _ Hb), (IHb0 Hrest). reflexivity.
  - cbn [pristine_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [notes_free_items]. rewrite (IHb Hit), (IHb0 Hrest). reflexivity.
  - cbn [pristine_def_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [notes_free_def_items]. rewrite (IHb Hit), (IHb0 Hrest). reflexivity.
  - cbn [pristine_task_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [notes_free_task_items]. rewrite (IHb Hit), (IHb0 Hrest). reflexivity.
Qed.

Lemma pristine_notes_free :
  forall bs, pristine bs = true -> notes_free bs = true.
Proof.
  induction bs as [|[p a b] rest IH]; intros H; [reflexivity|].
  rewrite pristine_cons in H. apply andb_true_iff in H as [Hb Hrest].
  cbn [notes_free]. rewrite (pristine_notes_free_block b a Hb), (IH Hrest).
  reflexivity.
Qed.

Lemma assign_ids_notes_free :
  forall b p a st,
    notes_free_block b = true ->
    notes_free_block (node_contents (snd (assign_ids b p a st))) = true.
Proof.
  intros b. induction b using block_ind2 with
    (Q := fun bs => forall st,
        notes_free bs = true ->
        notes_free (snd (assign_ids_list bs st)) = true)
    (R := fun its => forall st,
        notes_free_items its = true ->
        notes_free_items (snd (assign_ids_items its st)) = true)
    (D := fun its => forall st,
        notes_free_def_items its = true ->
        notes_free_def_items (snd (assign_ids_def_items its st)) = true)
    (K := fun its => forall st,
        notes_free_task_items its = true ->
        notes_free_task_items (snd (assign_ids_task_items its st)) = true);
    intros; try exact H; try reflexivity.
  - unfold assign_ids, assign_heading_id.
    destruct (lookup_attr "id" a); cbn [snd node_contents notes_free_block];
      reflexivity.
  - rewrite notes_free_quote in H. rewrite assign_ids_quote.
    destruct (assign_ids_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd node_contents]. rewrite notes_free_quote.
    change bs' with (snd (st', bs')). rewrite <- E. apply IHb. exact H.
  - rewrite notes_free_div in H. rewrite assign_ids_div.
    destruct (assign_ids_list bs (register_id a st)) as [st' bs'] eqn:E.
    cbn [snd node_contents]. rewrite notes_free_div.
    change bs' with (snd (st', bs')). rewrite <- E. apply IHb. exact H.
  - rewrite notes_free_olist in H. rewrite assign_ids_olist.
    destruct (assign_ids_items items (register_id a st)) as [st' items'] eqn:E.
    cbn [snd node_contents]. rewrite notes_free_olist.
    change items' with (snd (st', items')). rewrite <- E. apply IHb. exact H.
  - rewrite notes_free_blist in H. rewrite assign_ids_blist.
    destruct (assign_ids_items items (register_id a st)) as [st' items'] eqn:E.
    cbn [snd node_contents]. rewrite notes_free_blist.
    change items' with (snd (st', items')). rewrite <- E. apply IHb. exact H.
  - rewrite notes_free_tasklist in H. rewrite assign_ids_tasklist.
    destruct (assign_ids_task_items items (register_id a st)) as [st' items']
      eqn:E.
    cbn [snd node_contents]. rewrite notes_free_tasklist.
    change items' with (snd (st', items')). rewrite <- E. apply IHb. exact H.
  - rewrite notes_free_deflist in H. rewrite assign_ids_deflist.
    destruct (assign_ids_def_items items (register_id a st)) as [st' items']
      eqn:E.
    cbn [snd node_contents]. rewrite notes_free_deflist.
    change items' with (snd (st', items')). rewrite <- E. apply IHb. exact H.
  - discriminate.
  - (* Keyed: the payload is one node, so `Q` at the singleton is the
       statement about it with a `&& true` on the end. *)
    destruct b as [p' a' x]. cbn [notes_free_block] in H.
    specialize (IHb (register_id a st)). cbn [notes_free] in IHb.
    rewrite H in IHb. specialize (IHb eq_refl).
    cbn [assign_ids assign_ids_list assign_ids_node] in *.
    destruct (assign_ids x p' a' (register_id a st)) as [st1 n1] eqn:E1.
    cbn [snd notes_free node_contents] in *.
    destruct n1 as [q b1 y]. cbn [notes_free_block] in *.
    rewrite andb_true_r in IHb. exact IHb.
  - cbn [notes_free] in H. apply andb_true_iff in H as [Hb Hrest].
    cbn [assign_ids_list assign_ids_node].
    destruct (assign_ids b p a st) as [st1 n1] eqn:E1.
    destruct n1 as [np na nb].
    destruct (assign_ids_list rest st1) as [st2 rest1] eqn:E2.
    cbn [snd notes_free].
    pose proof (IHb p a st Hb) as Hnode.
    rewrite E1 in Hnode. cbn [snd node_contents] in Hnode. rewrite Hnode.
    replace (notes_free rest1) with
      (notes_free (snd (assign_ids_list rest st1)))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
  - cbn [notes_free_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [assign_ids_items].
    destruct (assign_ids_list it st) as [st1 it1] eqn:E1.
    destruct (assign_ids_items rest st1) as [st2 rest1] eqn:E2.
    cbn [snd notes_free_items].
    replace (notes_free it1) with (notes_free (snd (assign_ids_list it st)))
      by (rewrite E1; reflexivity).
    rewrite IHb by exact Hit.
    replace (notes_free_items rest1) with
      (notes_free_items (snd (assign_ids_items rest st1)))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
  - cbn [notes_free_def_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [assign_ids_def_items].
    destruct (assign_ids_list it st) as [st1 it1] eqn:E1.
    destruct (assign_ids_def_items rest st1) as [st2 rest1] eqn:E2.
    cbn [snd notes_free_def_items].
    replace (notes_free it1) with (notes_free (snd (assign_ids_list it st)))
      by (rewrite E1; reflexivity).
    rewrite IHb by exact Hit.
    replace (notes_free_def_items rest1) with
      (notes_free_def_items (snd (assign_ids_def_items rest st1)))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
  - cbn [notes_free_task_items] in H. apply andb_true_iff in H as [Hit Hrest].
    cbn [assign_ids_task_items].
    destruct (assign_ids_list it st) as [st1 it1] eqn:E1.
    destruct (assign_ids_task_items rest st1) as [st2 rest1] eqn:E2.
    cbn [snd notes_free_task_items].
    replace (notes_free it1) with (notes_free (snd (assign_ids_list it st)))
      by (rewrite E1; reflexivity).
    rewrite IHb by exact Hit.
    replace (notes_free_task_items rest1) with
      (notes_free_task_items (snd (assign_ids_task_items rest st1)))
      by (rewrite E2; reflexivity).
    rewrite IHb0 by exact Hrest. reflexivity.
Qed.

Lemma assign_ids_list_notes_free :
  forall bs st,
    notes_free bs = true -> notes_free (snd (assign_ids_list bs st)) = true.
Proof.
  induction bs as [|[p a b] rest IH]; intros st H; [reflexivity|].
  cbn [notes_free] in H. apply andb_true_iff in H as [Hb Hrest].
  cbn [assign_ids_list assign_ids_node].
  destruct (assign_ids b p a st) as [st1 n1] eqn:E1.
  destruct n1 as [np na nb].
  destruct (assign_ids_list rest st1) as [st2 rest1] eqn:E2.
  cbn [snd notes_free].
  pose proof (assign_ids_notes_free b p a st Hb) as Hnode.
  rewrite E1 in Hnode. cbn [snd node_contents] in Hnode. rewrite Hnode.
  replace (notes_free rest1) with (notes_free (snd (assign_ids_list rest st1)))
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
      nosect. cbn [undo_pass rev app]. rewrite app_nil_r.
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
    nosect. cbn [undo_pass rev app]. rewrite app_nil_r.
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
  pose proof (pristine_notes_free bs H) as Hfree.
  pose proof (assign_ids_list_notes_free bs id_state_init Hfree) as Hfree'.
  destruct (assign_ids_list bs id_state_init) as [st bs'] eqn:E.
  cbn [snd] in Hfree'.
  rewrite (collect_notes_list_pristine bs' [] Hfree').
  cbn [doc_blocks]. rewrite undo_sectionize.
  replace bs' with (snd (assign_ids_list bs id_state_init))
    by (rewrite E; reflexivity).
  apply undo_assign_ids_list. exact H.
Qed.

(*
Erasure of the side tables
==========================

The document pass reads the tree and writes two side tables; erasing a
located tree's positions has to give the document the pass produces on
the erased tree.  The traversals below are the pos-blind half of that:
none of `assign_ids`, `collect_notes` or `collect_refs` reads a
position, so each commutes with `erase_blocks` structurally.  The
sectionizer is the other half and is not here.

`erase_note_map` and `erase_doc` are the erasure of the two maps and of
the record; `doc_references`, `doc_auto_references` and
`doc_auto_identifiers` hold no nodes, so they are carried through.
*)

Lemma inlines_text_cons : forall (n : node inline) (rest : inlines),
  inlines_text (n :: rest)%list
  = (inline_text (node_contents n) ++ inlines_text rest)%string.
Proof.
  intros n rest. unfold inlines_text. cbn [map].
  destruct rest as [|y rest].
  - cbn [String.concat]. symmetry. apply append_empty_r.
  - reflexivity.
Qed.

Lemma inline_text_go : forall ns,
  (fix go (ns : list (node inline)) : string :=
     match ns with
     | [] => ""
     | Node _ _ x :: rest => (inline_text x ++ go rest)%string
     end) ns = inlines_text ns.
Proof.
  induction ns as [|[p a x] rest IH]; [reflexivity|].
  rewrite inlines_text_cons. cbn [inline_text]. rewrite IH. reflexivity.
Qed.

Lemma inline_text_erase : forall il,
  inline_text (erase_inline il) = inline_text il.
Proof.
  induction il using inline_ind2 with
    (Q := fun ils =>
       (fix go (ns : list (node inline)) : string :=
          match ns with
          | [] => ""
          | Node _ _ x :: rest => (inline_text x ++ go rest)%string
          end) (erase_inlines ils)
       = (fix go (ns : list (node inline)) : string :=
          match ns with
          | [] => ""
          | Node _ _ x :: rest => (inline_text x ++ go rest)%string
          end) ils);
    cbn [erase_inline inline_text].
  all: try reflexivity.
  all: try (rewrite erase_inline_children; assumption).
  - (* hcons *)
    rewrite erase_inlines_cons. cbn [erase_inode inline_text].
    congruence.
Qed.

Lemma inlines_text_erase : forall ils,
  inlines_text (erase_inlines ils) = inlines_text ils.
Proof.
  induction ils as [|[p a x] rest IH]; [reflexivity|].
  rewrite erase_inlines_cons. cbn [erase_inode node_contents].
  rewrite inlines_text_cons. cbn [node_contents].
  rewrite inlines_text_cons. cbn [node_contents].
  rewrite IH, inline_text_erase. reflexivity.
Qed.

Definition erase_note_map (m : note_map) : note_map :=
  map (fun kv => (fst kv, erase_blocks (snd kv))) m.

Definition erase_doc (d : doc) : doc :=
  {| doc_blocks := erase_blocks (doc_blocks d)
   ; doc_footnotes := erase_note_map (doc_footnotes d)
   ; doc_references := doc_references d
   ; doc_auto_references := doc_auto_references d
   ; doc_auto_identifiers := doc_auto_identifiers d |}.

Lemma erase_note_map_alist_set : forall k v m,
  erase_note_map (alist_set k v m)
  = alist_set k (erase_blocks v) (erase_note_map m).
Proof.
  intros k v m. induction m as [|[k' v'] rest IH];
    cbn [alist_set fst snd]; [reflexivity|].
  destruct (String.eqb k k') eqn:E.
  - cbn [erase_note_map map alist_set fst snd]. rewrite E. reflexivity.
  - cbn [erase_note_map map alist_set fst snd]. rewrite E.
    change ((k', erase_blocks v') :: erase_note_map (alist_set k v rest)
            = (k', erase_blocks v') :: alist_set k (erase_blocks v)
                (erase_note_map rest)).
    rewrite IH. reflexivity.
Qed.

(* The item erasures as `erase_block` spells them internally, bridged to
   the map form the statements below use. *)
Lemma erase_items_fix : forall its,
  (fix goitems (its : list blocks) : list blocks :=
     match its with
     | [] => []
     | item :: rest => erase_blocks item :: goitems rest
     end) its = map erase_blocks its.
Proof.
  induction its as [|it rest IH]; [reflexivity|].
  cbn [map]. rewrite IH. reflexivity.
Qed.

Lemma erase_def_items_fix : forall its,
  (fix godefs (its : list (inlines * blocks)) : list (inlines * blocks) :=
     match its with
     | [] => []
     | (term, item) :: rest =>
         (erase_inlines term, erase_blocks item) :: godefs rest
     end) its
  = map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv))) its.
Proof.
  induction its as [|[term it] rest IH]; [reflexivity|].
  cbn [map fst snd]. rewrite IH. reflexivity.
Qed.

Lemma erase_task_items_fix : forall its,
  (fix gotasks (its : list (task_status * blocks))
      : list (task_status * blocks) :=
     match its with
     | [] => []
     | (status, item) :: rest =>
         (status, erase_blocks item) :: gotasks rest
     end) its
  = map (fun kv => (fst kv, erase_blocks (snd kv))) its.
Proof.
  induction its as [|[status it] rest IH]; [reflexivity|].
  cbn [map fst snd]. rewrite IH. reflexivity.
Qed.

(*
assign_ids
*)

Lemma assign_ids_erase :
  forall b p a st,
    fst (assign_ids (erase_block b) NoPos a st) = fst (assign_ids b p a st)
    /\ erase_blocks [snd (assign_ids b p a st)]
       = [snd (assign_ids (erase_block b) NoPos a st)].
Proof.
  intros b.
  induction b using block_ind2 with
    (Q := fun bs => forall st,
        fst (assign_ids_list (erase_blocks bs) st) = fst (assign_ids_list bs st)
        /\ erase_blocks (snd (assign_ids_list bs st))
           = snd (assign_ids_list (erase_blocks bs) st))
    (R := fun its => forall st,
        fst (assign_ids_items (map erase_blocks its) st)
          = fst (assign_ids_items its st)
        /\ map erase_blocks (snd (assign_ids_items its st))
           = snd (assign_ids_items (map erase_blocks its) st))
    (D := fun its => forall st,
        fst (assign_ids_def_items
               (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv)))
                  its) st)
          = fst (assign_ids_def_items its st)
        /\ map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv)))
               (snd (assign_ids_def_items its st))
           = snd (assign_ids_def_items
                    (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv)))
                       its) st))
    (K := fun its => forall st,
        fst (assign_ids_task_items
               (map (fun kv => (fst kv, erase_blocks (snd kv))) its) st)
          = fst (assign_ids_task_items its st)
        /\ map (fun kv => (fst kv, erase_blocks (snd kv)))
               (snd (assign_ids_task_items its st))
           = snd (assign_ids_task_items
                    (map (fun kv => (fst kv, erase_blocks (snd kv))) its) st));
    intros; try solve [split; reflexivity].
  - (* Heading *)
    cbn [erase_block assign_ids]. unfold assign_heading_id. rewrite inlines_text_erase.
    destruct (lookup_attr "id" a) as [v|] eqn:E;
      cbn [fst snd erase_blocks erase_block]; split; reflexivity.
  - (* BlockQuote *)
    cbn [erase_block]. fold erase_blocks. rewrite !assign_ids_quote.
    destruct (assign_ids_list (erase_blocks bs) (register_id a st)) as [st2 bs2] eqn:E2.
    destruct (assign_ids_list bs (register_id a st)) as [st1 bs1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [erase_blocks erase_block]. fold erase_blocks.
    rewrite He. reflexivity.
  - (* Div *)
    cbn [erase_block]. fold erase_blocks. rewrite !assign_ids_div.
    destruct (assign_ids_list (erase_blocks bs) (register_id a st)) as [st2 bs2] eqn:E2.
    destruct (assign_ids_list bs (register_id a st)) as [st1 bs1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [erase_blocks erase_block]. fold erase_blocks.
    rewrite He. reflexivity.
  - (* OrderedList *)
    cbn [erase_block]. fold erase_blocks. rewrite erase_items_fix.
    rewrite !assign_ids_olist.
    destruct (assign_ids_items (map erase_blocks items) (register_id a st)) as [st2 its2] eqn:E2.
    destruct (assign_ids_items items (register_id a st)) as [st1 its1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [erase_blocks erase_block]. fold erase_blocks.
    rewrite erase_items_fix. rewrite He. reflexivity.
  - (* BulletList *)
    cbn [erase_block]. fold erase_blocks. rewrite erase_items_fix.
    rewrite !assign_ids_blist.
    destruct (assign_ids_items (map erase_blocks items) (register_id a st)) as [st2 its2] eqn:E2.
    destruct (assign_ids_items items (register_id a st)) as [st1 its1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [erase_blocks erase_block]. fold erase_blocks.
    rewrite erase_items_fix. rewrite He. reflexivity.
  - (* TaskList *)
    cbn [erase_block]. fold erase_blocks. rewrite erase_task_items_fix.
    rewrite !assign_ids_tasklist.
    destruct (assign_ids_task_items
      (map (fun kv => (fst kv, erase_blocks (snd kv))) items)
      (register_id a st)) as [st2 its2] eqn:E2.
    destruct (assign_ids_task_items items (register_id a st)) as [st1 its1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [erase_blocks erase_block]. fold erase_blocks.
    rewrite erase_task_items_fix. rewrite He. reflexivity.
  - (* DefinitionList *)
    cbn [erase_block]. fold erase_blocks. rewrite erase_def_items_fix.
    rewrite !assign_ids_deflist.
    destruct (assign_ids_def_items
      (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv))) items)
      (register_id a st)) as [st2 its2] eqn:E2.
    destruct (assign_ids_def_items items (register_id a st)) as [st1 its1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [erase_blocks erase_block]. fold erase_blocks.
    rewrite erase_def_items_fix. rewrite He. reflexivity.
  - (* FootnoteDef *)
    cbn [erase_block]. fold erase_blocks. rewrite !assign_ids_foot.
    destruct (assign_ids_list (erase_blocks bs) (register_id a st)) as [st2 bs2] eqn:E2.
    destruct (assign_ids_list bs (register_id a st)) as [st1 bs1] eqn:E1.
    destruct (IHb (register_id a st)) as [Hf He].
    rewrite E1, E2 in Hf. cbn [fst snd] in Hf.
    rewrite E1, E2 in He. cbn [fst snd] in He.
    split; [exact Hf|].
    cbn [snd fst]. cbn [erase_blocks erase_block]. fold erase_blocks.
    rewrite He. reflexivity.
  - (* Keyed *)
    destruct b as [p' a' x]. cbn [erase_block assign_ids].
    destruct (assign_ids x p' a' (register_id a st)) as [st1 n1] eqn:E1.
    destruct (assign_ids (erase_block x) NoPos a' (register_id a st)) as [st2 n2] eqn:E2.
    pose proof (IHb (register_id a st)) as Hk.
    cbn [erase_blocks assign_ids_list assign_ids_node] in Hk.
    rewrite E1, E2 in Hk. cbn [fst snd] in Hk.
    destruct Hk as [Hf He].
    destruct n1 as [np na nb].
    cbn [erase_blocks erase_block] in He. injection He as Hn2.
    split; [exact Hf|]. subst n2. reflexivity.
  - (* Q cons *)
    cbn [erase_blocks assign_ids_list assign_ids_node].
    destruct (assign_ids b p a st) as [st1 n1] eqn:E1.
    destruct (assign_ids (erase_block b) NoPos a st) as [st2 n2] eqn:E2.
    destruct (assign_ids_list rest st1) as [st3 rest1] eqn:E3.
    destruct (assign_ids_list (erase_blocks rest) st2) as [st4 rest2] eqn:E4.
    destruct n1 as [np na nb].
    destruct (IHb p a st) as [Hf He]. rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
    destruct (IHb0 st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
    cbn [erase_blocks erase_block] in He. fold erase_blocks in He. injection He as Hn2.
    split; [exact Hf2|].
    cbn [snd fst]. cbn [erase_blocks erase_block]. fold erase_blocks.
    rewrite He2. subst n2. reflexivity.
  - (* R cons *)
    cbn [assign_ids_items map].
    destruct (assign_ids_list it st) as [st1 it1] eqn:E1.
    destruct (assign_ids_list (erase_blocks it) st) as [st2 it2] eqn:E2.
    destruct (assign_ids_items rest st1) as [st3 rest1] eqn:E3.
    destruct (assign_ids_items (map erase_blocks rest) st2) as [st4 rest2] eqn:E4.
    destruct (IHb st) as [Hf He]. rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
    destruct (IHb0 st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
    split; [exact Hf2|].
    cbn [snd fst map]. rewrite He, He2. reflexivity.
  - (* D cons *)
    cbn [assign_ids_def_items map fst snd].
    destruct (assign_ids_list it st) as [st1 it1] eqn:E1.
    destruct (assign_ids_list (erase_blocks it) st) as [st2 it2] eqn:E2.
    destruct (assign_ids_def_items rest st1) as [st3 rest1] eqn:E3.
    destruct (assign_ids_def_items
      (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv))) rest)
      st2) as [st4 rest2] eqn:E4.
    destruct (IHb st) as [Hf He]. rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
    destruct (IHb0 st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
    split; [exact Hf2|].
    cbn [snd fst map fst snd]. rewrite He, He2. reflexivity.
  - (* K cons *)
    cbn [assign_ids_task_items map fst snd].
    destruct (assign_ids_list it st) as [st1 it1] eqn:E1.
    destruct (assign_ids_list (erase_blocks it) st) as [st2 it2] eqn:E2.
    destruct (assign_ids_task_items rest st1) as [st3 rest1] eqn:E3.
    destruct (assign_ids_task_items
      (map (fun kv => (fst kv, erase_blocks (snd kv))) rest) st2) as [st4 rest2] eqn:E4.
    destruct (IHb st) as [Hf He]. rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
    destruct (IHb0 st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
    split; [exact Hf2|].
    cbn [snd fst map fst snd]. rewrite He, He2. reflexivity.
Qed.

Lemma assign_ids_list_erase : forall bs st,
  fst (assign_ids_list (erase_blocks bs) st) = fst (assign_ids_list bs st)
  /\ erase_blocks (snd (assign_ids_list bs st))
     = snd (assign_ids_list (erase_blocks bs) st).
Proof.
  induction bs as [|[p a b] rest IH]; intros st; [split; reflexivity|].
  cbn [erase_blocks assign_ids_list assign_ids_node].
  destruct (assign_ids b p a st) as [st1 n1] eqn:E1.
  destruct (assign_ids (erase_block b) NoPos a st) as [st2 n2] eqn:E2.
  destruct (assign_ids_list rest st1) as [st3 rest1] eqn:E3.
  destruct (assign_ids_list (erase_blocks rest) st2) as [st4 rest2] eqn:E4.
  destruct n1 as [np na nb].
  destruct (assign_ids_erase b p a st) as [Hf He].
  rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
  destruct (IH st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
  cbn [erase_blocks erase_block] in He. fold erase_blocks in He. injection He as Hn2.
  split; [exact Hf2|].
  cbn [snd fst]. cbn [erase_blocks erase_block]. fold erase_blocks.
  rewrite He2. subst n2. reflexivity.
Qed.

Lemma assign_ids_items_erase : forall its st,
  fst (assign_ids_items (map erase_blocks its) st)
    = fst (assign_ids_items its st)
  /\ map erase_blocks (snd (assign_ids_items its st))
     = snd (assign_ids_items (map erase_blocks its) st).
Proof.
  induction its as [|it rest IH]; intros st; [split; reflexivity|].
  cbn [assign_ids_items map].
  destruct (assign_ids_list it st) as [st1 it1] eqn:E1.
  destruct (assign_ids_list (erase_blocks it) st) as [st2 it2] eqn:E2.
  destruct (assign_ids_items rest st1) as [st3 rest1] eqn:E3.
  destruct (assign_ids_items (map erase_blocks rest) st2) as [st4 rest2] eqn:E4.
  destruct (assign_ids_list_erase it st) as [Hf He].
  rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
  destruct (IH st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
  split; [exact Hf2|].
  cbn [snd fst map]. rewrite He, He2. reflexivity.
Qed.

Lemma assign_ids_def_items_erase : forall its st,
  fst (assign_ids_def_items
         (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv))) its)
         st)
    = fst (assign_ids_def_items its st)
  /\ map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv)))
       (snd (assign_ids_def_items its st))
     = snd (assign_ids_def_items
              (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv))) its)
              st).
Proof.
  induction its as [|[term it] rest IH]; intros st; [split; reflexivity|].
  cbn [assign_ids_def_items map fst snd].
  destruct (assign_ids_list it st) as [st1 it1] eqn:E1.
  destruct (assign_ids_list (erase_blocks it) st) as [st2 it2] eqn:E2.
  destruct (assign_ids_def_items rest st1) as [st3 rest1] eqn:E3.
  destruct (assign_ids_def_items
    (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv))) rest)
    st2) as [st4 rest2] eqn:E4.
  destruct (assign_ids_list_erase it st) as [Hf He].
  rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
  destruct (IH st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
  split; [exact Hf2|].
  cbn [snd fst map fst snd]. rewrite He, He2. reflexivity.
Qed.

Lemma assign_ids_task_items_erase : forall its st,
  fst (assign_ids_task_items
         (map (fun kv => (fst kv, erase_blocks (snd kv))) its) st)
    = fst (assign_ids_task_items its st)
  /\ map (fun kv => (fst kv, erase_blocks (snd kv)))
       (snd (assign_ids_task_items its st))
     = snd (assign_ids_task_items
              (map (fun kv => (fst kv, erase_blocks (snd kv))) its) st).
Proof.
  induction its as [|[chk it] rest IH]; intros st; [split; reflexivity|].
  cbn [assign_ids_task_items map fst snd].
  destruct (assign_ids_list it st) as [st1 it1] eqn:E1.
  destruct (assign_ids_list (erase_blocks it) st) as [st2 it2] eqn:E2.
  destruct (assign_ids_task_items rest st1) as [st3 rest1] eqn:E3.
  destruct (assign_ids_task_items
    (map (fun kv => (fst kv, erase_blocks (snd kv))) rest) st2) as [st4 rest2] eqn:E4.
  destruct (assign_ids_list_erase it st) as [Hf He].
  rewrite E1, E2 in Hf, He. cbn [fst snd] in Hf, He.
  destruct (IH st2) as [Hf2 He2]. rewrite E4, Hf, E3 in Hf2, He2. cbn [fst snd] in Hf2, He2.
  split; [exact Hf2|].
  cbn [snd fst map fst snd]. rewrite He, He2. reflexivity.
Qed.

(*
collect_notes
*)

Lemma collect_notes_erase : forall b p a m,
  collect_notes (erase_block b) NoPos a (erase_note_map m)
  = (erase_note_map (fst (collect_notes b p a m)),
     option_map (fun n => match n with
                          | Node _ a' x => Node NoPos a' (erase_block x)
                          end)
       (snd (collect_notes b p a m))).
Proof.
  intros b.
  induction b using block_ind2 with
    (Q := fun ns => forall m,
        collect_notes_list (erase_blocks ns) (erase_note_map m)
        = (erase_note_map (fst (collect_notes_list ns m)),
           erase_blocks (snd (collect_notes_list ns m))))
    (R := fun its => forall m,
        collect_notes_items (map erase_blocks its) (erase_note_map m)
        = (erase_note_map (fst (collect_notes_items its m)),
           map erase_blocks (snd (collect_notes_items its m))))
    (D := fun its => forall m,
        collect_notes_def_items
          (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv))) its)
          (erase_note_map m)
        = (erase_note_map (fst (collect_notes_def_items its m)),
           map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv)))
             (snd (collect_notes_def_items its m))))
    (K := fun its => forall m,
        collect_notes_task_items
          (map (fun kv => (fst kv, erase_blocks (snd kv))) its)
          (erase_note_map m)
        = (erase_note_map (fst (collect_notes_task_items its m)),
           map (fun kv => (fst kv, erase_blocks (snd kv)))
             (snd (collect_notes_task_items its m))));
    intros; try reflexivity.
  - (* BlockQuote *)
    cbn [erase_block]. fold erase_blocks. rewrite !collect_notes_quote.
    destruct (collect_notes_list (erase_blocks bs) (erase_note_map m)) as [m2 bs2] eqn:E2.
    destruct (collect_notes_list bs m) as [m1 bs1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 bs2.
    cbn [erase_block]. reflexivity.
  - (* Div *)
    cbn [erase_block]. fold erase_blocks. rewrite !collect_notes_div.
    destruct (collect_notes_list (erase_blocks bs) (erase_note_map m)) as [m2 bs2] eqn:E2.
    destruct (collect_notes_list bs m) as [m1 bs1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 bs2.
    cbn [erase_block]. reflexivity.
  - (* OrderedList *)
    cbn [erase_block]. fold erase_blocks. rewrite erase_items_fix.
    rewrite !collect_notes_olist.
    destruct (collect_notes_items (map erase_blocks items) (erase_note_map m)) as [m2 its2] eqn:E2.
    destruct (collect_notes_items items m) as [m1 its1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 its2.
    cbn [erase_block]. reflexivity.
  - (* BulletList *)
    cbn [erase_block]. fold erase_blocks. rewrite erase_items_fix.
    rewrite !collect_notes_blist.
    destruct (collect_notes_items (map erase_blocks items) (erase_note_map m)) as [m2 its2] eqn:E2.
    destruct (collect_notes_items items m) as [m1 its1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 its2.
    cbn [erase_block]. reflexivity.
  - (* TaskList *)
    cbn [erase_block]. fold erase_blocks. rewrite erase_task_items_fix.
    rewrite !collect_notes_tasklist.
    destruct (collect_notes_task_items
      (map (fun kv => (fst kv, erase_blocks (snd kv))) items)
      (erase_note_map m)) as [m2 its2] eqn:E2.
    destruct (collect_notes_task_items items m) as [m1 its1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 its2.
    cbn [snd fst option_map erase_block]. rewrite erase_task_items_fix. reflexivity.
  - (* DefinitionList *)
    cbn [erase_block]. fold erase_blocks. rewrite erase_def_items_fix.
    rewrite !collect_notes_deflist.
    destruct (collect_notes_def_items
      (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv))) items)
      (erase_note_map m)) as [m2 its2] eqn:E2.
    destruct (collect_notes_def_items items m) as [m1 its1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 its2.
    cbn [snd fst option_map erase_block]. rewrite erase_def_items_fix. reflexivity.
  - (* FootnoteDef *)
    cbn [erase_block]. fold erase_blocks. rewrite !collect_notes_foot.
    destruct (collect_notes_list (erase_blocks bs) (erase_note_map m)) as [m2 bs2] eqn:E2.
    destruct (collect_notes_list bs m) as [m1 bs1] eqn:E1.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 bs2.
    rewrite <- erase_note_map_alist_set. reflexivity.
  - (* Keyed *)
    destruct b as [p' a' x]. cbn [erase_block collect_notes].
    destruct (collect_notes x p' a' m) as [m1 o1] eqn:E1.
    destruct (collect_notes (erase_block x) NoPos a' (erase_note_map m)) as [m2 o2] eqn:E2.
    pose proof (IHb m) as Hq.
    cbn [erase_blocks collect_notes_list] in Hq.
    rewrite E1, E2 in Hq. cbn [fst snd] in Hq.
    destruct o1 as [n1|]; destruct o2 as [n2|]; cbn [fst snd] in Hq.
    + destruct n1 as [np na nb]. cbn [erase_blocks erase_block] in Hq.
      injection Hq as Hm Hn. subst m2 n2. reflexivity.
    + destruct n1 as [np na nb]. cbn [erase_blocks erase_block] in Hq.
      discriminate Hq.
    + discriminate Hq.
    + injection Hq as Hm. subst m2. reflexivity.
  - (* Q cons *)
    cbn [erase_blocks collect_notes_list].
    destruct (collect_notes b p a m) as [m1 n1] eqn:E1.
    destruct (collect_notes (erase_block b) NoPos a (erase_note_map m)) as [m0 n0] eqn:E0.
    pose proof (IHb p a m) as Hq. rewrite E1, E0 in Hq.
    destruct n1 as [n1|]; destruct n0 as [n0|];
      cbn [fst snd option_map] in Hq.
    + destruct n1 as [np na nb]. cbn [erase_blocks erase_block] in Hq.
      injection Hq as Hm Hn. subst m0 n0.
      destruct (collect_notes_list rest m1) as [m3 rest1] eqn:E3.
      destruct (collect_notes_list (erase_blocks rest) (erase_note_map m1)) as [m4 rest2] eqn:E4.
      pose proof (IHb0 m1) as Hq2. rewrite E3, E4 in Hq2.
      injection Hq2 as Hm2 Hb2. subst m4 rest2. reflexivity.
    + discriminate Hq.
    + discriminate Hq.
    + injection Hq as Hm. subst m0.
      destruct (collect_notes_list rest m1) as [m3 rest1] eqn:E3.
      destruct (collect_notes_list (erase_blocks rest) (erase_note_map m1)) as [m4 rest2] eqn:E4.
      pose proof (IHb0 m1) as Hq2. rewrite E3, E4 in Hq2.
      injection Hq2 as Hm2 Hb2. subst m4 rest2. reflexivity.
  - (* R cons *)
    cbn [collect_notes_items map].
    destruct (collect_notes_list it m) as [m1 it1] eqn:E1.
    destruct (collect_notes_list (erase_blocks it) (erase_note_map m)) as [m2 it2] eqn:E2.
    destruct (collect_notes_items rest m1) as [m3 rest1] eqn:E3.
    destruct (collect_notes_items (map erase_blocks rest) m2) as [m4 rest2] eqn:E4.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 it2.
    pose proof (IHb0 m1) as Hq2. rewrite E3, E4 in Hq2.
    injection Hq2 as Hm2 Hb2. subst m4 rest2.
    cbn [fst snd map]. reflexivity.
  - (* D cons *)
    cbn [collect_notes_def_items map fst snd].
    destruct (collect_notes_list it m) as [m1 it1] eqn:E1.
    destruct (collect_notes_list (erase_blocks it) (erase_note_map m)) as [m2 it2] eqn:E2.
    destruct (collect_notes_def_items rest m1) as [m3 rest1] eqn:E3.
    destruct (collect_notes_def_items
      (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv))) rest)
      m2) as [m4 rest2] eqn:E4.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 it2.
    pose proof (IHb0 m1) as Hq2. rewrite E3, E4 in Hq2.
    injection Hq2 as Hm2 Hb2. subst m4 rest2.
    cbn [fst snd map]. reflexivity.
  - (* K cons *)
    cbn [collect_notes_task_items map fst snd].
    destruct (collect_notes_list it m) as [m1 it1] eqn:E1.
    destruct (collect_notes_list (erase_blocks it) (erase_note_map m)) as [m2 it2] eqn:E2.
    destruct (collect_notes_task_items rest m1) as [m3 rest1] eqn:E3.
    destruct (collect_notes_task_items
      (map (fun kv => (fst kv, erase_blocks (snd kv))) rest) m2) as [m4 rest2] eqn:E4.
    pose proof (IHb m) as Hq. rewrite E1, E2 in Hq.
    injection Hq as Hm Hb. subst m2 it2.
    pose proof (IHb0 m1) as Hq2. rewrite E3, E4 in Hq2.
    injection Hq2 as Hm2 Hb2. subst m4 rest2.
    cbn [fst snd map]. reflexivity.
Qed.

Lemma collect_notes_list_erase : forall ns m,
  collect_notes_list (erase_blocks ns) (erase_note_map m)
  = (erase_note_map (fst (collect_notes_list ns m)),
     erase_blocks (snd (collect_notes_list ns m))).
Proof.
  induction ns as [|[p a b] rest IH]; intros m; [reflexivity|].
  cbn [erase_blocks collect_notes_list].
  destruct (collect_notes b p a m) as [m1 n1] eqn:E1.
  destruct (collect_notes (erase_block b) NoPos a (erase_note_map m)) as [m0 n0] eqn:E0.
  pose proof (collect_notes_erase b p a m) as Hq. rewrite E1, E0 in Hq.
  destruct n1 as [n1|]; destruct n0 as [n0|]; cbn [fst snd option_map] in Hq.
  + destruct n1 as [np na nb]. cbn [erase_blocks erase_block] in Hq.
    injection Hq as Hm Hn. subst m0 n0.
    destruct (collect_notes_list rest m1) as [m3 rest1] eqn:E3.
    destruct (collect_notes_list (erase_blocks rest) (erase_note_map m1)) as [m4 rest2] eqn:E4.
    pose proof (IH m1) as Hq2. rewrite E3, E4 in Hq2.
    injection Hq2 as Hm2 Hb2. subst m4 rest2. reflexivity.
  + discriminate Hq.
  + discriminate Hq.
  + injection Hq as Hm. subst m0.
    destruct (collect_notes_list rest m1) as [m3 rest1] eqn:E3.
    destruct (collect_notes_list (erase_blocks rest) (erase_note_map m1)) as [m4 rest2] eqn:E4.
    pose proof (IH m1) as Hq2. rewrite E3, E4 in Hq2.
    injection Hq2 as Hm2 Hb2. subst m4 rest2. reflexivity.
Qed.

Lemma collect_notes_items_erase : forall its m,
  collect_notes_items (map erase_blocks its) (erase_note_map m)
  = (erase_note_map (fst (collect_notes_items its m)),
     map erase_blocks (snd (collect_notes_items its m))).
Proof.
  induction its as [|it rest IH]; intros m; [reflexivity|].
  cbn [collect_notes_items map].
  destruct (collect_notes_list it m) as [m1 it1] eqn:E1.
  destruct (collect_notes_list (erase_blocks it) (erase_note_map m)) as [m2 it2] eqn:E2.
  pose proof (collect_notes_list_erase it m) as Hq. rewrite E1, E2 in Hq.
  injection Hq as Hm Hb. subst m2 it2.
  destruct (collect_notes_items rest m1) as [m3 rest1] eqn:E3.
  destruct (collect_notes_items (map erase_blocks rest) (erase_note_map m1)) as [m4 rest2] eqn:E4.
  pose proof (IH m1) as Hq2. rewrite E3, E4 in Hq2.
  injection Hq2 as Hm2 Hb2. subst m4 rest2.
  cbn [fst snd map]. reflexivity.
Qed.

Lemma collect_notes_def_items_erase : forall its m,
  collect_notes_def_items
    (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv))) its)
    (erase_note_map m)
  = (erase_note_map (fst (collect_notes_def_items its m)),
     map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv)))
       (snd (collect_notes_def_items its m))).
Proof.
  induction its as [|[term it] rest IH]; intros m; [reflexivity|].
  cbn [collect_notes_def_items map fst snd].
  destruct (collect_notes_list it m) as [m1 it1] eqn:E1.
  destruct (collect_notes_list (erase_blocks it) (erase_note_map m)) as [m2 it2] eqn:E2.
  pose proof (collect_notes_list_erase it m) as Hq. rewrite E1, E2 in Hq.
  injection Hq as Hm Hb. subst m2 it2.
  destruct (collect_notes_def_items rest m1) as [m3 rest1] eqn:E3.
  destruct (collect_notes_def_items
    (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv))) rest)
    (erase_note_map m1)) as [m4 rest2] eqn:E4.
  pose proof (IH m1) as Hq2. rewrite E3, E4 in Hq2.
  injection Hq2 as Hm2 Hb2. subst m4 rest2.
  cbn [fst snd map fst snd]. reflexivity.
Qed.

Lemma collect_notes_task_items_erase : forall its m,
  collect_notes_task_items
    (map (fun kv => (fst kv, erase_blocks (snd kv))) its)
    (erase_note_map m)
  = (erase_note_map (fst (collect_notes_task_items its m)),
     map (fun kv => (fst kv, erase_blocks (snd kv)))
       (snd (collect_notes_task_items its m))).
Proof.
  induction its as [|[chk it] rest IH]; intros m; [reflexivity|].
  cbn [collect_notes_task_items map fst snd].
  destruct (collect_notes_list it m) as [m1 it1] eqn:E1.
  destruct (collect_notes_list (erase_blocks it) (erase_note_map m)) as [m2 it2] eqn:E2.
  pose proof (collect_notes_list_erase it m) as Hq. rewrite E1, E2 in Hq.
  injection Hq as Hm Hb. subst m2 it2.
  destruct (collect_notes_task_items rest m1) as [m3 rest1] eqn:E3.
  destruct (collect_notes_task_items
    (map (fun kv => (fst kv, erase_blocks (snd kv))) rest)
    (erase_note_map m1)) as [m4 rest2] eqn:E4.
  pose proof (IH m1) as Hq2. rewrite E3, E4 in Hq2.
  injection Hq2 as Hm2 Hb2. subst m4 rest2.
  cbn [fst snd map fst snd]. reflexivity.
Qed.

(*
collect_refs
*)

Lemma collect_refs_go : forall ns m,
  (fix go (ns : blocks) (acc : reference_map) : reference_map :=
     match ns with
     | [] => acc
     | Node p' a' x :: rest => go rest (collect_refs x p' a' acc)
     end) ns m = collect_refs_list ns m.
Proof.
  induction ns as [|[p a b] rest IH]; intros m; [reflexivity|].
  cbn [collect_refs_list]. rewrite IH. reflexivity.
Qed.

Lemma collect_refs_goit : forall its m,
  (fix goit (its : list blocks) (acc : reference_map) : reference_map :=
     match its with
     | [] => acc
     | it :: rest =>
         goit rest
           ((fix go (ns : blocks) (acc' : reference_map) : reference_map :=
               match ns with
               | [] => acc'
               | Node p' a' x :: more => go more (collect_refs x p' a' acc')
               end) it acc)
     end) its m
  = fold_left (fun acc it => collect_refs_list it acc) its m.
Proof.
  induction its as [|it rest IH]; intros m; [reflexivity|].
  cbn [fold_left]. rewrite collect_refs_go, IH. reflexivity.
Qed.

Lemma collect_refs_god : forall its m,
  (fix god (its : list (inlines * blocks)) (acc : reference_map)
      : reference_map :=
     match its with
     | [] => acc
     | (_, it) :: rest =>
         god rest
           ((fix go (ns : blocks) (acc' : reference_map) : reference_map :=
               match ns with
               | [] => acc'
               | Node p' a' x :: more => go more (collect_refs x p' a' acc')
               end) it acc)
     end) its m
  = fold_left (fun acc kv => collect_refs_list (snd kv) acc) its m.
Proof.
  induction its as [|[term it] rest IH]; intros m; [reflexivity|].
  cbn [fold_left]. rewrite collect_refs_go, IH. reflexivity.
Qed.

Lemma collect_refs_got : forall its m,
  (fix got (its : list (task_status * blocks)) (acc : reference_map)
      : reference_map :=
     match its with
     | [] => acc
     | (_, it) :: rest =>
         got rest
           ((fix go (ns : blocks) (acc' : reference_map) : reference_map :=
               match ns with
               | [] => acc'
               | Node p' a' x :: more => go more (collect_refs x p' a' acc')
               end) it acc)
     end) its m
  = fold_left (fun acc kv => collect_refs_list (snd kv) acc) its m.
Proof.
  induction its as [|[chk it] rest IH]; intros m; [reflexivity|].
  cbn [fold_left]. rewrite collect_refs_go, IH. reflexivity.
Qed.

Lemma collect_refs_erase : forall b p a m,
  collect_refs (erase_block b) NoPos a m = collect_refs b p a m.
Proof.
  intros b.
  induction b using block_ind2 with
    (Q := fun ns => forall m,
        collect_refs_list (erase_blocks ns) m = collect_refs_list ns m)
    (R := fun its => forall m,
        fold_left (fun acc it => collect_refs_list it acc)
          (map erase_blocks its) m
        = fold_left (fun acc it => collect_refs_list it acc) its m)
    (D := fun its => forall m,
        fold_left (fun acc kv => collect_refs_list (snd kv) acc)
          (map (fun kv => (erase_inlines (fst kv), erase_blocks (snd kv))) its) m
        = fold_left (fun acc kv => collect_refs_list (snd kv) acc) its m)
    (K := fun its => forall m,
        fold_left (fun acc kv => collect_refs_list (snd kv) acc)
          (map (fun kv => (fst kv, erase_blocks (snd kv))) its) m
        = fold_left (fun acc kv => collect_refs_list (snd kv) acc) its m);
    intros; try (cbn [erase_block collect_refs]; reflexivity).
  all: try solve [cbn [erase_block collect_refs]; fold erase_blocks;
                  rewrite !collect_refs_go; exact (IHb m)].
  all: try solve [cbn [erase_block collect_refs]; fold erase_blocks;
                  rewrite erase_items_fix; rewrite !collect_refs_goit;
                  exact (IHb m)].
  all: try solve [cbn [erase_block collect_refs]; fold erase_blocks;
                  rewrite erase_task_items_fix; rewrite !collect_refs_got;
                  exact (IHb m)].
  all: try solve [cbn [erase_block collect_refs]; fold erase_blocks;
                  rewrite erase_def_items_fix; rewrite !collect_refs_god;
                  exact (IHb m)].
  all: try solve [destruct b as [p' a' x]; cbn [erase_block collect_refs];
                  pose proof (IHb m) as Hk;
                  cbn [erase_blocks collect_refs_list] in Hk; exact Hk].
  - (* Q cons *)
    cbn [erase_blocks collect_refs_list].
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

Lemma collect_refs_list_erase : forall ns m,
  collect_refs_list (erase_blocks ns) m = collect_refs_list ns m.
Proof.
  induction ns as [|[p a b] rest IH]; intros m; [reflexivity|].
  cbn [erase_blocks collect_refs_list].
  rewrite (collect_refs_erase b p a m), IH. reflexivity.
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
