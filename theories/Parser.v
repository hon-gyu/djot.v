(* ai-disclosure: ai-generated *)

(* Block parsing: a fold over classified lines with an explicit state.

   The state is a *container stack*, growing inward: an open paragraph
   accumulator (empty = idle), an open code fence collecting verbatim
   lines, or a block quote holding the blocks it has closed so far plus
   the state of its contents.  Per line:
   - inside a fence, only the close test applies — no classification;
   - otherwise KBlank ends any open paragraph, KThematic/KFence start
     blocks only when no paragraph is open (paragraphs can never be
     interrupted — spec), and KText extends or opens a paragraph;
   - KQuote strips its prefix and re-enters `step` on the enclosed line,
     which is where nesting and uniformity both come from: a quote's
     contents run the same transition as the top level.

   `step` is the whole per-line transition (Phase 2's `continue`/`close`/
   `finalize` rolled into one function) and `finish` closes the stack at
   end of input.  `parse_lines` is then a plain fold.

   The equation lemmas at the bottom are the interface the wf and
   roundtrip proofs use; keep them in sync with the definition. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast.
Import ListNotations.

Local Open Scope string_scope.

(*
Paragraph assembly
==================
*)

(* Trailing whitespace is stripped at the end of a paragraph (but kept on
   interior lines) — observed djot.js/djoths behavior on para.test. *)

(* Turn a paragraph's source lines (in order) into inlines: one Str per
   line, SoftBreak between.  Render.inline_lines is the inverse. *)
Fixpoint para_inlines (l : list string) : inlines :=
  match l with
  | [] => []
  | [x] => [mk (Str (strip_trailing_ws x))]
  | x :: rest => mk (Str x) :: mk SoftBreak :: para_inlines rest
  end.

(*
Fenced block assembly
=====================
*)

(* Content is the lines rejoined, each with its newline.  An info string
   starting with '=' makes a raw block (=FORMAT); otherwise it is the
   language of a code block. *)

Definition fence_block (f : fence) (content : list string) : node block :=
  let text := join_nl content in
  match f_info f with
  | String "="%char fmt => mk (RawBlock fmt text)
  | info => mk (CodeBlock info text)
  end.

(*
The line fold
=============
*)

(* A bullet list, mid-parse.  `ls_indent` is the column its markers sit
   at: continuation is "indented past the marker", djot.js's
   `this.indent > container.extra.indent`.  `ls_marker` is the style — a
   different bullet character starts a new list rather than continuing
   this one.

   Tight/loose is a stateful rule, and djot.js decides it on the *event*
   stream rather than on the finished tree: a blank line arms
   `ls_blanks`, and the next event that is neither a blank nor a list
   boundary turns the list loose (parse.ts ~line 1237).  That is why
   `- a`, blank, `  - b` stays tight even though a blank line separates
   the item's two children — the next event opens a list.  The textbook
   "blank line between block children" rule gets that case wrong.

   Carried in the state because the list is only emitted when it closes,
   so nothing is ever revised retroactively. *)
Record list_state : Type := LSt
  { ls_indent : nat
  ; ls_marker : ascii
  ; ls_loose : bool
  ; ls_blanks : bool
  ; ls_items : list blocks }.   (* finished items, reversed *)

(* The fold's state: a container stack.  Every accumulator holds its
   items in *reverse* order, hence the `rev` at each use site. *)
Inductive pstate : Type :=
  | PPara (cur : list string)              (* [] = no open block *)
  | PHeading (level : nat) (cur : list string)
  | PFence (f : fence) (acc : list string)
  | PQuote (done : blocks) (inner : pstate)
  (* done/inner are the *current item*'s state, exactly as for a quote;
     ls_items holds the items already closed. *)
  | PList (ls : list_state) (done : blocks) (inner : pstate).

(* Container nesting depth.  Half of the parser's termination measure:
   a quote descent shortens the line, but a list descent hands the line
   to the inner container unchanged and shortens *this* instead. *)
Fixpoint pstate_depth (st : pstate) : nat :=
  match st with
  | PPara _ | PHeading _ _ | PFence _ _ => 0
  | PQuote _ inner => S (pstate_depth inner)
  | PList _ _ inner => S (pstate_depth inner)
  end.

(* End of input (or of an enclosing container): close everything still
   open, outermost result first. *)
(* A heading's text lines become its inlines exactly as a paragraph's do
   — same assembly, different wrapper. *)
Definition heading_block (lvl : nat) (cur : list string) : node block :=
  mk (Heading lvl (para_inlines (rev cur))).

Fixpoint finish (st : pstate) : blocks :=
  match st with
  | PPara [] => []
  | PPara cur => [mk (Para (para_inlines (rev cur)))]
  | PHeading lvl cur => [heading_block lvl cur]
  | PFence f acc => [fence_block f (rev acc)]
  | PQuote done inner => [mk (BlockQuote (rev done ++ finish inner)%list)]
  | PList ls done inner =>
      [mk (BulletList (if ls_loose ls then Loose else Tight)
             (rev ((rev done ++ finish inner)%list :: ls_items ls)))]
  end.

(* Lazy continuation (djot.js: `isLazy`).  A nonblank, otherwise
   featureless line that is missing its container prefixes still
   continues the innermost open *inline* container — a paragraph or a
   heading — but nothing else, which is why fence content is excluded.
   An empty PPara is the idle state, not an open block; a PHeading is
   always open, even with no text yet. *)
Fixpoint lazy_ok (st : pstate) : bool :=
  match st with
  | PPara [] => false
  | PPara (_ :: _) => true
  | PHeading _ _ => true
  | PFence _ _ => false
  | PQuote _ inner => lazy_ok inner
  | PList _ _ inner => lazy_ok inner
  end.

Definition is_lazy (k : line_kind) (inner : pstate) : bool :=
  match k with KText => lazy_ok inner | _ => false end.

(* Append a lazy line to the innermost paragraph, prefixes and all. *)
Fixpoint feed_lazy (l : string) (st : pstate) : pstate :=
  match st with
  | PPara cur => PPara (l :: cur)
  | PHeading lvl cur => PHeading lvl (l :: cur)
  | PFence f acc => PFence f acc      (* excluded by lazy_ok *)
  | PQuote done inner => PQuote done (feed_lazy l inner)
  | PList ls done inner => PList ls done (feed_lazy l inner)
  end.

(* A heading's text, pushed onto its accumulator.  `# ` with nothing
   after it opens a heading with no text rather than a blank line of it,
   which is what keeps the accumulator's nonblank invariant. *)
Definition push_text (rest : string) (cur : list string) : list string :=
  if is_blank rest then cur else drop_leading_ws rest :: cur.

(* What a line opens, for every kind but KQuote — a quote has to parse
   the line it encloses, which is the parser's one recursion, so it stays
   inside `step_fuel`.  The split is deliberate: every equation lemma
   downstream is stated over `open_kind`, which is exactly why no
   statement outside this file mentions fuel. *)
Definition open_kind (l : string) (k : line_kind) : blocks * pstate :=
  match k with
  | KBlank => ([], PPara [])
  | KThematic => ([mk ThematicBreak], PPara [])
  | KFence f => ([], PFence f [])
  | KHeading lvl rest => ([], PHeading lvl (push_text rest []))
  | KText => ([], PPara [drop_leading_ws l])
  | KQuote _ => ([], PPara [])        (* unreachable: see open_quote *)
  | KList _ _ => ([], PPara [])       (* unreachable: see open_list *)
  end.

(* The other half of the per-line rule: this line does not continue the
   open container, so the container's blocks close and the line is
   reprocessed at the enclosing level.  Every state answers a line one of
   these two ways — continue, or close-and-reopen — which is the
   `continue`/`close`/`finalize` split of Phase 2's BlockSpec, with
   `finish` supplying finalize.  A new container gets its continuation
   rule and nothing else; this rule it inherits.

   Both wrappers take the opening *already computed* rather than
   computing it, so neither joins the recursion — which is what keeps
   `step`'s fuel decrementing once per nesting level and no more. *)
Definition close_reopen (st : pstate) (opened : blocks * pstate)
  : blocks * pstate :=
  let (bs, st') := opened in ((finish st ++ bs)%list, st').

(* A quote prefix opens a fresh quote around whatever its enclosed line
   parsed to. *)
Definition open_quote (descended : blocks * pstate) : blocks * pstate :=
  let (bs, inner) := descended in ([], PQuote (rev bs) inner).

(* A bullet marker opens a fresh list, whose first item holds whatever
   the rest of the line parsed to.  A new list is tight until something
   makes it loose. *)
Definition open_list (ind : nat) (m : ascii) (descended : blocks * pstate)
  : blocks * pstate :=
  let (bs, inner) := descended in
  ([], PList (LSt ind m false false []) (rev bs) inner).

(*
Tight/loose bookkeeping
-----------------------

Three events move the flags, mirroring djot.js's annot tests. *)

(* A blank line inside the list arms the flag. *)
Definition list_blank (ls : list_state) : list_state :=
  LSt (ls_indent ls) (ls_marker ls) (ls_loose ls) true (ls_items ls).

(* Content within the current item.  A line that opens a nested list is
   a `+list` event, which djot.js excludes from loosening; anything else
   loosens the list if a blank line is armed.  Either way the flag is
   spent. *)
Definition list_content (ls : list_state) (k : line_kind) : list_state :=
  let loose :=
    match k with
    | KList _ _ => ls_loose ls
    | _ => (ls_loose ls || ls_blanks ls)%bool
    end in
  LSt (ls_indent ls) (ls_marker ls) loose false (ls_items ls).

(* A sibling marker closes the current item and opens the next.  The
   boundary itself neither loosens nor spends the flag (djot.js keeps
   `blanklines` across `+list_item`); the content that follows on the
   same line does, which is what makes `- a`, blank, `- b` loose. *)
Definition list_next (ls : list_state) (item : blocks) (rest : string)
  : list_state :=
  let items := item :: ls_items ls in
  if is_blank rest
  then LSt (ls_indent ls) (ls_marker ls) (ls_loose ls) (ls_blanks ls) items
  else LSt (ls_indent ls) (ls_marker ls)
         (ls_loose ls || ls_blanks ls)%bool false items.

(* The per-line transition, on fuel.  The only recursion is into a
   stripped quote prefix, and `classify_quote_length` says that line is
   strictly shorter — so the line's own length is always enough fuel.
   `step` below fixes it there, and `step_fuel_enough` retires it, so no
   downstream statement mentions fuel. *)
Fixpoint step_fuel (n : nat) (l : string) (st : pstate) {struct n}
  : blocks * pstate :=
  match n with
  | O => ([], st)                     (* unreachable from step *)
  | S n' =>
      match st with
      | PFence f acc =>
          (* Verbatim: only the close test, and the closing line is
             consumed rather than reprocessed — the one state that is
             not "continue or close-and-reopen". *)
          if fence_close f l
          then ([fence_block f (rev acc)], PPara [])
          else ([], PFence f (l :: acc))
      | PPara [] =>
          (* Idle: nothing to close, so the line just opens its block. *)
          match classify l with
          | KQuote rest => open_quote (step_fuel n' rest (PPara []))
          | KList m rest =>
              open_list (indent_of l) m (step_fuel n' rest (PPara []))
          | k => open_kind l k
          end
      | PPara (c :: cur') =>
          match classify l with
          | KBlank => close_reopen (PPara (c :: cur')) (open_kind l KBlank)
          | _ => ([], PPara (drop_leading_ws l :: c :: cur'))   (* paragraphs never interrupt *)
          end
      | PHeading lvl cur =>
          (* Unlike a paragraph, a heading *is* interruptible: only a
             matching-level marker or a lazy text line continues it. *)
          match classify l with
          | KHeading lvl' rest =>
              if Nat.eqb lvl' lvl
              then ([], PHeading lvl (push_text rest cur))
              else close_reopen (PHeading lvl cur)
                     (open_kind l (KHeading lvl' rest))
          | KText => ([], PHeading lvl (drop_leading_ws l :: cur))
          | KQuote rest =>
              close_reopen (PHeading lvl cur)
                (open_quote (step_fuel n' rest (PPara [])))
          | KList m rest =>
              close_reopen (PHeading lvl cur)
                (open_list (indent_of l) m (step_fuel n' rest (PPara [])))
          | k => close_reopen (PHeading lvl cur) (open_kind l k)
          end
      | PQuote done inner =>
          match classify l with
          | KQuote rest =>
              (* continue: descend into the quote already open, keeping
                 what it has closed so far *)
              let (bs, inner') := step_fuel n' rest inner in
              ([], PQuote (rev bs ++ done)%list inner')
          | KList m rest =>
              close_reopen (PQuote done inner)
                (open_list (indent_of l) m (step_fuel n' rest (PPara [])))
          | k =>
              if is_lazy k inner
              then ([], PQuote done (feed_lazy l inner))
              else close_reopen (PQuote done inner) (open_kind l k)
          end
      | PList ls done inner =>
          match classify l with
          | KBlank =>
              (* a blank arms the loose flag but closes nothing: it goes
                 to the item's contents, where it ends any open
                 paragraph *)
              let (bs, inner') := step_fuel n' l inner in
              ([], PList (list_blank ls) (rev bs ++ done)%list inner')
          | k =>
              if Nat.ltb (ls_indent ls) (indent_of l)
              then
                (* indented past the marker: contents of the current
                   item.  The line is passed down unchanged — every
                   recognizer already skips leading whitespace, so block
                   structure is right; what the extra indent still costs
                   is inline and verbatim text, the same open indentation
                   gap quotes and headings have. *)
                let (bs, inner') := step_fuel n' l inner in
                ([], PList (list_content ls k) (rev bs ++ done)%list inner')
              else
                match k with
                | KList m rest =>
                    if Ascii.eqb m (ls_marker ls)
                    then
                      (* a sibling item: close the current one, open the
                         next around the rest of the line *)
                      let item := (rev done ++ finish inner)%list in
                      let (bs, inner') := step_fuel n' rest (PPara []) in
                      ([], PList (list_next ls item rest) (rev bs) inner')
                    else
                      (* a different bullet style is a different list *)
                      close_reopen (PList ls done inner)
                        (open_list (indent_of l) m
                           (step_fuel n' rest (PPara [])))
                | KQuote rest =>
                    close_reopen (PList ls done inner)
                      (open_quote (step_fuel n' rest (PPara [])))
                | _ =>
                    if is_lazy k inner
                    then ([], PList ls done (feed_lazy l inner))
                    else close_reopen (PList ls done inner) (open_kind l k)
                end
          end
      end
  end.

(* The transition proper.  Each descent either shortens the line (a
   quote prefix, a list marker) or drops a container from the state (a
   list item's contents), so line length plus nesting depth strictly
   decreases and this much fuel is always enough — `step_fuel_enough`
   retires it, and no statement outside this file mentions it. *)
Definition step (l : string) (st : pstate) : blocks * pstate :=
  step_fuel (S (String.length l + pstate_depth st)) l st.

(* The parser: fold the transition over the lines, then close the stack.
   Structurally recursive on `lines`, so it always terminates and proofs
   can step it one line at a time. *)
Fixpoint parse_lines (lines : list string) (st : pstate) : blocks :=
  match lines with
  | [] => finish st
  | l :: rest =>
      let (bs, st') := step l st in
      (bs ++ parse_lines rest st')%list
  end.

(* Entry point of the line fold: split the source into lines and fold from
   the idle state.  This is the whole block structure, and the layer every
   theorem in Wf.v and Roundtrip.v is stated against.  Document.parse_doc
   composes the whole-document pass on top to build the `doc` record. *)
Definition parse_blocks (s : string) : blocks :=
  parse_lines (split_lines s) (PPara []).

(*
Equation lemmas
===============

One lemma per branch of `step`, each proved by `cbn` + `rewrite` on the
classification, then lifted to `parse_lines`.  Downstream proofs rewrite
with these instead of calling `simpl` on the parser, which otherwise
unfolds into an unusable match tower. *)

(*
Retiring the fuel
-----------------

Fuel is an implementation detail of `step_fuel`: any amount past the
line's length gives the same answer, so `step` can fix it and no
downstream statement ever mentions it. *)

Lemma step_fuel_stable :
  forall bound n l st,
    n <= bound -> S (String.length l + pstate_depth st) <= n ->
    step_fuel n l st = step_fuel (S (String.length l + pstate_depth st)) l st.
Proof.
  induction bound as [|bound IH]; intros n l st Hb Hn; [lia|].
  destruct n as [|n']; [lia|].
  cbn [step_fuel].
  destruct st as [cur|hlvl hcur|f acc|done inner|ls done inner].
  - (* idle, or an open paragraph *)
    cbn [pstate_depth] in Hn |- *.
    destruct cur as [|c cur'].
    + destruct (classify l) as [| |g|rest|kl kr|m mr|] eqn:E; try reflexivity.
      * pose proof (classify_quote_length _ _ E) as Hlt.
        cbn [pstate_depth]; rewrite ?Nat.add_0_r.
        rewrite (IH n' rest (PPara [])) by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l) rest (PPara [])) by (cbn [pstate_depth]; lia).
        reflexivity.
      * pose proof (classify_list_length _ _ _ E) as Hlt.
        cbn [pstate_depth]; rewrite ?Nat.add_0_r.
        rewrite (IH n' mr (PPara [])) by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l) mr (PPara [])) by (cbn [pstate_depth]; lia).
        reflexivity.
    + destruct (classify l); reflexivity.
  - (* an open heading: the quote and list branches recurse *)
    cbn [pstate_depth] in Hn |- *.
    destruct (classify l) as [| |g|rest|kl kr|m mr|] eqn:E; try reflexivity.
    + pose proof (classify_quote_length _ _ E) as Hlt.
      cbn [pstate_depth]; rewrite ?Nat.add_0_r.
      rewrite (IH n' rest (PPara [])) by (cbn [pstate_depth]; lia).
      rewrite (IH (String.length l) rest (PPara [])) by (cbn [pstate_depth]; lia).
      reflexivity.
    + pose proof (classify_list_length _ _ _ E) as Hlt.
      cbn [pstate_depth]; rewrite ?Nat.add_0_r.
      rewrite (IH n' mr (PPara [])) by (cbn [pstate_depth]; lia).
      rewrite (IH (String.length l) mr (PPara [])) by (cbn [pstate_depth]; lia).
      reflexivity.
  - destruct (fence_close f l); reflexivity.
  - (* inside a quote: continuing descends with the same inner state *)
    cbn [pstate_depth] in Hn |- *.
    destruct (classify l) as [| |g|rest|kl kr|m mr|] eqn:E; try reflexivity.
    + pose proof (classify_quote_length _ _ E) as Hlt.
      rewrite (IH n' rest inner) by lia.
      rewrite (IH (String.length l + S (pstate_depth inner)) rest inner) by lia.
      reflexivity.
    + pose proof (classify_list_length _ _ _ E) as Hlt.
      rewrite (IH n' mr (PPara [])) by (cbn [pstate_depth]; lia).
      rewrite (IH (String.length l + S (pstate_depth inner)) mr (PPara []))
        by (cbn [pstate_depth]; lia).
      reflexivity.
  - (* inside a list: an item's contents keep the line and drop a level *)
    cbn [pstate_depth] in Hn |- *.
    destruct (classify l) as [| |g|rest|kl kr|m mr|] eqn:E.
    6: { (* a bullet marker: a sibling item, or a list of another style *)
      pose proof (classify_list_length _ _ _ E) as Hlt.
      destruct (Nat.ltb (ls_indent ls) (indent_of l)).
      - rewrite (IH n' l inner) by lia.
        rewrite (IH (String.length l + S (pstate_depth inner)) l inner) by lia.
        reflexivity.
      - destruct (Ascii.eqb m (ls_marker ls));
          rewrite (IH n' mr (PPara [])) by (cbn [pstate_depth]; lia);
          rewrite (IH (String.length l + S (pstate_depth inner)) mr (PPara []))
            by (cbn [pstate_depth]; lia);
          reflexivity. }
    1: { (* a blank line goes to the item's contents *)
      rewrite (IH n' l inner) by lia.
      rewrite (IH (String.length l + S (pstate_depth inner)) l inner) by lia.
      reflexivity. }
    3: { (* an unindented quote closes the list and opens outside it *)
      destruct (Nat.ltb (ls_indent ls) (indent_of l)).
      - rewrite (IH n' l inner) by lia.
        rewrite (IH (String.length l + S (pstate_depth inner)) l inner) by lia.
        reflexivity.
      - pose proof (classify_quote_length _ _ E) as Hlt.
        rewrite (IH n' rest (PPara [])) by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l + S (pstate_depth inner)) rest (PPara []))
          by (cbn [pstate_depth]; lia).
        reflexivity. }
    (* every other kind: contents of the item when indented past the
       marker, and otherwise nothing that recurses *)
    all: destruct (Nat.ltb (ls_indent ls) (indent_of l));
         [ rewrite (IH n' l inner) by lia;
           rewrite (IH (String.length l + S (pstate_depth inner)) l inner) by lia;
           reflexivity
         | reflexivity ].
Qed.

Lemma step_fuel_enough :
  forall n l st,
    S (String.length l + pstate_depth st) <= n -> step_fuel n l st = step l st.
Proof. intros n l st H. apply (step_fuel_stable n); lia. Qed.

(*
The transition, branch by branch
--------------------------------
*)

(* Kinds `open_kind` handles: everything but the two that open a
   container by parsing part of the line again. *)
Definition direct_open (k : line_kind) : bool :=
  match k with KQuote _ | KList _ _ => false | _ => true end.

Lemma step_fence_close :
  forall l f acc, fence_close f l = true ->
  step l (PFence f acc) = ([fence_block f (rev acc)], PPara []).
Proof. intros l f acc H. unfold step. cbn [step_fuel]. rewrite H. reflexivity. Qed.

Lemma step_fence_content :
  forall l f acc, fence_close f l = false ->
  step l (PFence f acc) = ([], PFence f (l :: acc)).
Proof. intros l f acc H. unfold step. cbn [step_fuel]. rewrite H. reflexivity. Qed.

(* At an idle state every non-quote kind opens its block. *)
Lemma step_idle :
  forall l k, classify l = k -> direct_open k = true ->
  step l (PPara []) = open_kind l k.
Proof.
  intros l k H Hk. unfold step. cbn [step_fuel]. rewrite H.
  destruct k; (reflexivity || discriminate).
Qed.

(* An open paragraph is flushed by a blank line and by nothing else. *)
Lemma step_para_flush :
  forall l c cur', classify l = KBlank ->
  step l (PPara (c :: cur')) =
  ([mk (Para (para_inlines (rev (c :: cur'))))], PPara []).
Proof. intros l c cur' H. unfold step. cbn [step_fuel]. rewrite H. reflexivity. Qed.

Lemma step_para_cont :
  forall l c cur', classify l <> KBlank ->
  step l (PPara (c :: cur')) = ([], PPara (drop_leading_ws l :: c :: cur')).
Proof.
  intros l c cur' H. unfold step. cbn [step_fuel].
  destruct (classify l); (congruence || reflexivity).
Qed.

(*
Quote transitions
-----------------

Opening and continuing both recurse on the enclosed line; the fuel bound
discharges via classify_quote_length. *)

Lemma step_quote_open :
  forall l rest bs inner,
    classify l = KQuote rest ->
    step rest (PPara []) = (bs, inner) ->
    step l (PPara []) = ([], PQuote (rev bs) inner).
Proof.
  intros l rest bs inner H Hr. unfold step at 1. cbn [step_fuel]. rewrite H.
  rewrite step_fuel_enough by (pose proof (classify_quote_length _ _ H); lia).
  rewrite Hr. reflexivity.
Qed.

Lemma step_quote_cont :
  forall l rest done inner bs inner',
    classify l = KQuote rest ->
    step rest inner = (bs, inner') ->
    step l (PQuote done inner) = ([], PQuote (rev bs ++ done)%list inner').
Proof.
  intros l rest done inner bs inner' H Hr. unfold step at 1.
  cbn [step_fuel pstate_depth]. rewrite H.
  rewrite step_fuel_enough
    by (cbn [pstate_depth]; pose proof (classify_quote_length _ _ H); lia).
  rewrite Hr. reflexivity.
Qed.

(* A prefix-less text line still continues the innermost paragraph. *)
Lemma step_quote_lazy :
  forall l done inner,
    classify l = KText -> lazy_ok inner = true ->
    step l (PQuote done inner) = ([], PQuote done (feed_lazy l inner)).
Proof.
  intros l done inner H Hl. unfold step. cbn [step_fuel]. rewrite H.
  cbn [is_lazy]. rewrite Hl. reflexivity.
Qed.

(* Anything else closes the quote, and the line is then reprocessed
   outside it — the same `open_kind` the idle state uses. *)
Lemma step_quote_close :
  forall l k done inner bs st',
    classify l = k -> direct_open k = true -> is_lazy k inner = false ->
    open_kind l k = (bs, st') ->
    step l (PQuote done inner) =
    (mk (BlockQuote (rev done ++ finish inner)%list) :: bs, st').
Proof.
  intros l k done inner bs st' H Hk Hlz Ho. unfold step. cbn [step_fuel].
  rewrite H.
  destruct k; try discriminate; rewrite Hlz; rewrite Ho; reflexivity.
Qed.

(*
List transitions
----------------

A blank line always recurses into the item's own state, regardless of
indent (it can never close the list itself — only a later non-blank,
non-indented, non-matching-marker line can).  Everything else checks
indent first: indented past the marker keeps it item content; otherwise
a matching marker is a sibling, a different marker opens a new list, and
   anything else is lazy continuation or a close, exactly as for a quote. *)

Lemma step_list_open :
  forall l m rest bs inner,
    classify l = KList m rest ->
    step rest (PPara []) = (bs, inner) ->
    step l (PPara []) =
      ([], PList (LSt (indent_of l) m false false []) (rev bs) inner).
Proof.
  intros l m rest bs inner H Hr. unfold step at 1. cbn [step_fuel]. rewrite H.
  rewrite step_fuel_enough
    by (cbn [pstate_depth]; pose proof (classify_list_length _ _ _ H); lia).
  rewrite Hr. reflexivity.
Qed.

Lemma step_list_blank :
  forall l ls done inner bs inner',
    classify l = KBlank ->
    step l inner = (bs, inner') ->
    step l (PList ls done inner) =
    ([], PList (list_blank ls) (rev bs ++ done)%list inner').
Proof.
  intros l ls done inner bs inner' H Hr. unfold step at 1.
  cbn [step_fuel pstate_depth]. rewrite H.
  rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
  rewrite Hr. reflexivity.
Qed.

Lemma step_list_indented :
  forall l k ls done inner bs inner',
    classify l = k -> k <> KBlank ->
    Nat.ltb (ls_indent ls) (indent_of l) = true ->
    step l inner = (bs, inner') ->
    step l (PList ls done inner) =
    ([], PList (list_content ls k) (rev bs ++ done)%list inner').
Proof.
  intros l k ls done inner bs inner' H Hk Hind Hr. unfold step at 1.
  cbn [step_fuel pstate_depth]. rewrite H.
  destruct k eqn:Ek; [congruence| | | | | | ];
    rewrite Hind;
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia);
    rewrite Hr; reflexivity.
Qed.

Lemma step_list_sibling :
  forall l m rest ls done inner bs inner',
    classify l = KList m rest ->
    Ascii.eqb m (ls_marker ls) = true ->
    Nat.ltb (ls_indent ls) (indent_of l) = false ->
    step rest (PPara []) = (bs, inner') ->
    step l (PList ls done inner) =
    ([], PList (list_next ls (rev done ++ finish inner)%list rest) (rev bs) inner').
Proof.
  intros l m rest ls done inner bs inner' H Hm Hind Hr. unfold step at 1.
  cbn [step_fuel pstate_depth]. rewrite H, Hind, Hm.
  rewrite step_fuel_enough
    by (cbn [pstate_depth]; pose proof (classify_list_length _ _ _ H); lia).
  rewrite Hr. reflexivity.
Qed.

Lemma step_list_diffstyle :
  forall l m rest ls done inner bs inner',
    classify l = KList m rest ->
    Ascii.eqb m (ls_marker ls) = false ->
    Nat.ltb (ls_indent ls) (indent_of l) = false ->
    step rest (PPara []) = (bs, inner') ->
    step l (PList ls done inner) =
    (finish (PList ls done inner),
     PList (LSt (indent_of l) m false false []) (rev bs) inner').
Proof.
  intros l m rest ls done inner bs inner' H Hm Hind Hr. unfold step at 1.
  cbn [step_fuel pstate_depth]. rewrite H, Hind, Hm.
  rewrite step_fuel_enough
    by (cbn [pstate_depth]; pose proof (classify_list_length _ _ _ H); lia).
  rewrite Hr. reflexivity.
Qed.

Lemma step_list_quote_close :
  forall l rest ls done inner bs inner',
    classify l = KQuote rest ->
    Nat.ltb (ls_indent ls) (indent_of l) = false ->
    step rest (PPara []) = (bs, inner') ->
    step l (PList ls done inner) =
      (finish (PList ls done inner), PQuote (rev bs) inner').
Proof.
  intros l rest ls done inner bs inner' H Hind Hr.
  unfold step at 1. cbn [step_fuel pstate_depth]. rewrite H, Hind.
  rewrite step_fuel_enough
    by (cbn [pstate_depth]; pose proof (classify_quote_length _ _ H); lia).
  rewrite Hr. cbn [close_reopen open_quote]. rewrite app_nil_r. reflexivity.
Qed.

Lemma step_list_lazy :
  forall l ls done inner,
    classify l = KText -> Nat.ltb (ls_indent ls) (indent_of l) = false ->
    lazy_ok inner = true ->
    step l (PList ls done inner) = ([], PList ls done (feed_lazy l inner)).
Proof.
  intros l ls done inner H Hind Hl. unfold step. cbn [step_fuel].
  rewrite H, Hind. cbn [is_lazy]. rewrite Hl. reflexivity.
Qed.

Lemma step_list_close :
  forall l k ls done inner bs st',
    classify l = k -> direct_open k = true -> k <> KBlank ->
    Nat.ltb (ls_indent ls) (indent_of l) = false ->
    is_lazy k inner = false ->
    open_kind l k = (bs, st') ->
    step l (PList ls done inner) = (finish (PList ls done inner) ++ bs, st')%list.
Proof.
  intros l k ls done inner bs st' H Hk Hnb Hind Hlz Ho. unfold step. cbn [step_fuel].
  rewrite H.
  destruct k; [congruence | idtac | idtac | discriminate | idtac | discriminate | idtac];
    rewrite Hind; cbn [is_lazy] in Hlz |- *; try rewrite Hlz; rewrite Ho; reflexivity.
Qed.

(*
Lifting to the fold
-------------------
*)

Lemma parse_lines_nil : forall st, parse_lines [] st = finish st.
Proof. reflexivity. Qed.

(* The workhorse: one transition, one prefix of emitted blocks. *)
Lemma parse_lines_step :
  forall l rest st bs st',
    step l st = (bs, st') ->
    parse_lines (l :: rest) st = (bs ++ parse_lines rest st')%list.
Proof. intros l rest st bs st' H. cbn [parse_lines]. rewrite H. reflexivity. Qed.

Lemma para_inlines_one :
  forall x, para_inlines [x] = [mk (Str (strip_trailing_ws x))].
Proof. reflexivity. Qed.

Lemma para_inlines_cons2 :
  forall x y rest,
    para_inlines (x :: y :: rest) =
    mk (Str x) :: mk SoftBreak :: para_inlines (y :: rest).
Proof. reflexivity. Qed.

Lemma parse_lines_nil_cons :
  forall c cur',
    parse_lines [] (PPara (c :: cur')) =
    [mk (Para (para_inlines (rev (c :: cur'))))].
Proof. reflexivity. Qed.

Lemma parse_lines_blank_nil :
  forall l rest, classify l = KBlank ->
  parse_lines (l :: rest) (PPara []) = parse_lines rest (PPara []).
Proof.
  intros l rest H.
  rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
Qed.

Lemma parse_lines_blank_cons :
  forall l rest c cur', classify l = KBlank ->
  parse_lines (l :: rest) (PPara (c :: cur')) =
  mk (Para (para_inlines (rev (c :: cur')))) :: parse_lines rest (PPara []).
Proof.
  intros l rest c cur' H.
  rewrite (parse_lines_step _ _ _ _ _ (step_para_flush _ _ _ H)). reflexivity.
Qed.

Lemma parse_lines_thematic_nil :
  forall l rest, classify l = KThematic ->
  parse_lines (l :: rest) (PPara []) =
  mk ThematicBreak :: parse_lines rest (PPara []).
Proof.
  intros l rest H.
  rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
Qed.

Lemma parse_lines_fence_open :
  forall l rest f, classify l = KFence f ->
  parse_lines (l :: rest) (PPara []) = parse_lines rest (PFence f []).
Proof.
  intros l rest f H.
  rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
Qed.

Lemma parse_lines_text :
  forall l rest cur, classify l = KText ->
  parse_lines (l :: rest) (PPara cur) =
  parse_lines rest (PPara (drop_leading_ws l :: cur)).
Proof.
  intros l rest cur H. destruct cur as [|c cur'].
  - rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
  - rewrite (parse_lines_step _ _ _ _ _
               (step_para_cont _ _ _ (fun E => ltac:(rewrite H in E; discriminate)))).
    reflexivity.
Qed.

(* Any nonblank line continues an open paragraph. *)
Lemma parse_lines_cont :
  forall l rest c cur', classify l <> KBlank ->
  parse_lines (l :: rest) (PPara (c :: cur')) =
  parse_lines rest (PPara (drop_leading_ws l :: c :: cur')).
Proof.
  intros l rest c cur' H.
  rewrite (parse_lines_step _ _ _ _ _ (step_para_cont _ _ _ H)). reflexivity.
Qed.

(*
Fence equations
---------------
*)

Lemma parse_lines_fence_eof :
  forall f acc, parse_lines [] (PFence f acc) = [fence_block f (rev acc)].
Proof. reflexivity. Qed.

Lemma parse_lines_fence_close :
  forall l rest f acc, fence_close f l = true ->
  parse_lines (l :: rest) (PFence f acc) =
  fence_block f (rev acc) :: parse_lines rest (PPara []).
Proof.
  intros l rest f acc H.
  rewrite (parse_lines_step _ _ _ _ _ (step_fence_close _ _ _ H)). reflexivity.
Qed.

Lemma parse_lines_fence_content :
  forall l rest f acc, fence_close f l = false ->
  parse_lines (l :: rest) (PFence f acc) =
  parse_lines rest (PFence f (l :: acc)).
Proof.
  intros l rest f acc H.
  rewrite (parse_lines_step _ _ _ _ _ (step_fence_content _ _ _ H)). reflexivity.
Qed.

(*
Seed lemmas: feeding runs of lines
----------------------------------
*)

(* A run of nonblank lines accumulates (reversed, leading whitespace
   stripped) onto an open paragraph. *)
Lemma parse_lines_cont_seed :
  forall ls tail c cur',
    forallb nonblank ls = true ->
    parse_lines (ls ++ tail)%list (PPara (c :: cur')) =
    parse_lines tail (PPara (rev (map drop_leading_ws ls) ++ (c :: cur'))%list).
Proof.
  induction ls as [|l ls IH]; intros tail c cur' H.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hl Hls].
    unfold nonblank in Hl. apply negb_true_iff in Hl.
    change ((l :: ls) ++ tail)%list with (l :: (ls ++ tail))%list.
    rewrite parse_lines_cont
      by (intros E; rewrite (classify_kblank_blank _ E) in Hl; discriminate).
    rewrite IH by exact Hls.
    simpl rev. rewrite <- app_assoc. reflexivity.
Qed.

(* Opening a paragraph with a text line, then feeding its remaining lines. *)
Lemma parse_lines_para_seed :
  forall a ls tail,
    classify a = KText ->
    forallb nonblank ls = true ->
    parse_lines ((a :: ls) ++ tail)%list (PPara []) =
    parse_lines tail (PPara (rev (map drop_leading_ws (a :: ls)))).
Proof.
  intros a ls tail Ha Hls.
  change ((a :: ls) ++ tail)%list with (a :: (ls ++ tail))%list.
  rewrite parse_lines_text by exact Ha.
  rewrite parse_lines_cont_seed by exact Hls.
  reflexivity.
Qed.

(* A run of non-closing lines accumulates (reversed) into an open fence. *)
Lemma parse_lines_fence_seed :
  forall ls tail f acc,
    forallb (fun l => negb (fence_close f l)) ls = true ->
    parse_lines (ls ++ tail)%list (PFence f acc) =
    parse_lines tail (PFence f (rev ls ++ acc)%list).
Proof.
  induction ls as [|l ls IH]; intros tail f acc H.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hl Hls].
    apply negb_true_iff in Hl.
    change ((l :: ls) ++ tail)%list with (l :: (ls ++ tail))%list.
    rewrite parse_lines_fence_content by exact Hl.
    rewrite IH by exact Hls.
    simpl rev. rewrite <- app_assoc. reflexivity.
Qed.

(*
Heading equations
-----------------
*)

Lemma step_heading_cont :
  forall l lvl txt cur,
    classify l = KHeading lvl txt ->
    step l (PHeading lvl cur) = ([], PHeading lvl (push_text txt cur)).
Proof.
  intros l lvl txt cur H. unfold step. cbn [step_fuel]. rewrite H.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma step_heading_close :
  forall l lvl cur,
    classify l = KBlank ->
    step l (PHeading lvl cur) = ([heading_block lvl cur], PPara []).
Proof.
  intros l lvl cur H. unfold step. cbn [step_fuel]. rewrite H. reflexivity.
Qed.

Lemma parse_lines_heading_open :
  forall l rest lvl txt,
    classify l = KHeading lvl txt ->
    parse_lines (l :: rest) (PPara []) =
    parse_lines rest (PHeading lvl (push_text txt [])).
Proof.
  intros l rest lvl txt H.
  rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
Qed.

Lemma parse_lines_heading_cont :
  forall l rest lvl txt cur,
    classify l = KHeading lvl txt ->
    parse_lines (l :: rest) (PHeading lvl cur) =
    parse_lines rest (PHeading lvl (push_text txt cur)).
Proof.
  intros l rest lvl txt cur H.
  rewrite (parse_lines_step _ _ _ _ _ (step_heading_cont _ _ _ _ H)).
  reflexivity.
Qed.

Lemma parse_lines_heading_close :
  forall l rest lvl cur,
    classify l = KBlank ->
    parse_lines (l :: rest) (PHeading lvl cur) =
    heading_block lvl cur :: parse_lines rest (PPara []).
Proof.
  intros l rest lvl cur H.
  rewrite (parse_lines_step _ _ _ _ _ (step_heading_close _ _ _ H)).
  reflexivity.
Qed.

(* A run of canonically-rendered heading lines accumulates (reversed,
   leading whitespace stripped) onto the open heading, exactly as
   paragraph lines do. *)
Lemma parse_lines_heading_seed :
  forall lvl ls tail cur,
    1 <= lvl ->
    forallb nonblank ls = true ->
    parse_lines (map (heading_line lvl) ls ++ tail)%list (PHeading lvl cur) =
    parse_lines tail (PHeading lvl (rev (map drop_leading_ws ls) ++ cur)%list).
Proof.
  intros lvl ls. induction ls as [|a ls IH]; intros tail cur Hlvl H.
  - reflexivity.
  - cbn [forallb] in H. apply andb_true_iff in H as [Ha Hls].
    unfold nonblank in Ha. apply negb_true_iff in Ha.
    cbn [map app].
    rewrite (parse_lines_heading_cont _ _ _ a _
               (classify_canonical_heading lvl a Hlvl)).
    unfold push_text. rewrite Ha.
    rewrite IH by assumption.
    cbn [rev map]. rewrite <- app_assoc. reflexivity.
Qed.

(* Same, seen through an all-whitespace pad: classify_canonical_heading_pad
   still extracts a clean, pad-free `a`, so push_text's own drop_leading_ws
   erases whatever's left the same as in the unpadded case — no new
   argument, just classify_canonical_heading_pad in place of
   classify_canonical_heading. *)
Lemma parse_lines_heading_seed_pad :
  forall pad, is_blank pad = true ->
  forall lvl ls tail cur,
    1 <= lvl ->
    forallb nonblank ls = true ->
    parse_lines (map (fun l => (pad ++ heading_line lvl l)%string) ls ++ tail)%list
                (PHeading lvl cur) =
    parse_lines tail (PHeading lvl (rev (map drop_leading_ws ls) ++ cur)%list).
Proof.
  intros pad Hpad lvl ls. induction ls as [|a ls IH]; intros tail cur Hlvl H.
  - reflexivity.
  - cbn [forallb] in H. apply andb_true_iff in H as [Ha Hls].
    unfold nonblank in Ha. apply negb_true_iff in Ha.
    cbn [map app].
    rewrite (parse_lines_heading_cont _ _ _ a _
               (classify_canonical_heading_pad pad lvl a Hpad Hlvl)).
    unfold push_text. rewrite Ha.
    rewrite IH by assumption.
    cbn [rev map]. rewrite <- app_assoc. reflexivity.
Qed.

(*
Uniformity of block quotes
--------------------------

The payoff of routing a quote's contents back through `step`: prefixing
every line of a document with "> " parses to exactly that document,
wrapped in a quote.  Nothing about the contents is assumed — this holds
for every construct the parser knows, including future ones and nested
quotes. *)

(* Inside an open quote, the prefixed lines drive the inner state and
   the blank line that follows closes the quote. *)
Lemma parse_lines_quote_cont :
  forall lines tail done inner,
    parse_lines (map (fun l => ("> " ++ l)%string) lines ++ EmptyString :: tail)%list
                (PQuote done inner)
    = mk (BlockQuote (rev done ++ parse_lines lines inner)%list)
      :: parse_lines tail (PPara []).
Proof.
  induction lines as [|l lines IH]; intros tail done inner.
  - cbn [map app].
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_close _ KBlank _ _ _ _
                  (classify_blank EmptyString eq_refl) eq_refl eq_refl eq_refl)).
    reflexivity.
  - cbn [map app].
    destruct (step l inner) as [bs inner'] eqn:Es.
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _ (classify_canonical_quote l) Es)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

(* ...and the same when the input simply ends. *)
Lemma parse_lines_quote_cont_eof :
  forall lines done inner,
    parse_lines (map (fun l => ("> " ++ l)%string) lines) (PQuote done inner)
    = [mk (BlockQuote (rev done ++ parse_lines lines inner)%list)].
Proof.
  induction lines as [|l lines IH]; intros done inner.
  - reflexivity.
  - cbn [map].
    destruct (step l inner) as [bs inner'] eqn:Es.
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _ (classify_canonical_quote l) Es)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

Lemma parse_lines_quote :
  forall l lines tail,
    parse_lines
      (map (fun x => ("> " ++ x)%string) (l :: lines) ++ EmptyString :: tail)%list
      (PPara [])
    = mk (BlockQuote (parse_lines (l :: lines) (PPara [])))
      :: parse_lines tail (PPara []).
Proof.
  intros l lines tail. cbn [map app].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote l) Es)).
  cbn [app]. rewrite parse_lines_quote_cont, rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.

(** Uniformity for block quotes: a quote's contents parse exactly as
    they would at top level.  One proof, every construct. *)
Theorem quote_uniformity :
  forall l lines,
    parse_lines (map (fun x => ("> " ++ x)%string) (l :: lines)) (PPara [])
    = [mk (BlockQuote (parse_lines (l :: lines) (PPara [])))].
Proof.
  intros l lines. cbn [map].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote l) Es)).
  cbn [app]. rewrite parse_lines_quote_cont_eof, rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.

(* The same four lemmas, seen through an all-whitespace pad in front of
   every "> " — verbatim copies of the proofs above with
   classify_canonical_quote_pad in place of classify_canonical_quote.
   This is what lets a quote nested inside a list item ignore the
   item's own indent entirely: the pad never reaches `rest`, so the
   recursion into the quote's contents is byte-identical to the
   unpadded case. Render.list_content_safe's comment explains why lists
   don't get the same free ride. *)
Lemma parse_lines_quote_cont_pad :
  forall pad, is_blank pad = true ->
  forall sep, classify sep = KBlank ->
  forall lines tail done inner,
    parse_lines (map (fun l => pad ++ "> " ++ l)%string lines ++ sep :: tail)%list
                (PQuote done inner)
    = mk (BlockQuote (rev done ++ parse_lines lines inner)%list)
      :: parse_lines tail (PPara []).
Proof.
  intros pad Hpad sep Hsep. induction lines as [|l lines IH]; intros tail done inner.
  - cbn [map app].
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_close _ KBlank _ _ _ _ Hsep eq_refl eq_refl eq_refl)).
    reflexivity.
  - cbn [map app].
    destruct (step l inner) as [bs inner'] eqn:Es.
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _ (classify_canonical_quote_pad pad l Hpad) Es)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

Lemma parse_lines_quote_cont_eof_pad :
  forall pad, is_blank pad = true ->
  forall lines done inner,
    parse_lines (map (fun l => pad ++ "> " ++ l)%string lines) (PQuote done inner)
    = [mk (BlockQuote (rev done ++ parse_lines lines inner)%list)].
Proof.
  intros pad Hpad. induction lines as [|l lines IH]; intros done inner.
  - reflexivity.
  - cbn [map].
    destruct (step l inner) as [bs inner'] eqn:Es.
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _ (classify_canonical_quote_pad pad l Hpad) Es)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

Lemma parse_lines_quote_pad :
  forall pad, is_blank pad = true ->
  forall sep, classify sep = KBlank ->
  forall l lines tail,
    parse_lines
      (map (fun x => pad ++ "> " ++ x)%string (l :: lines) ++ sep :: tail)%list
      (PPara [])
    = mk (BlockQuote (parse_lines (l :: lines) (PPara [])))
      :: parse_lines tail (PPara []).
Proof.
  intros pad Hpad sep Hsep l lines tail. cbn [map app].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote_pad pad l Hpad) Es)).
  cbn [app]. rewrite (parse_lines_quote_cont_pad pad Hpad sep Hsep), rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.

Theorem quote_uniformity_pad :
  forall pad, is_blank pad = true ->
  forall l lines,
    parse_lines (map (fun x => pad ++ "> " ++ x)%string (l :: lines)) (PPara [])
    = [mk (BlockQuote (parse_lines (l :: lines) (PPara [])))].
Proof.
  intros pad Hpad l lines. cbn [map].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote_pad pad l Hpad) Es)).
  cbn [app]. rewrite (parse_lines_quote_cont_eof_pad pad Hpad), rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.

(*
Sanity checks
=============
*)

Example parse_two_paras :
  parse_blocks "hi
there

bye" =
  [ mk (Para [mk (Str "hi"); mk SoftBreak; mk (Str "there")])
  ; mk (Para [mk (Str "bye")]) ].
Proof. reflexivity. Qed.

Example parse_thematic :
  parse_blocks "one

  * * * *

two" =
  [ mk (Para [mk (Str "one")])
  ; mk ThematicBreak
  ; mk (Para [mk (Str "two")]) ].
Proof. reflexivity. Qed.

(* Paragraphs are never interrupted: thematic-break- or fence-shaped
   lines inside a paragraph are text. *)
Example parse_no_interrupt :
  parse_blocks "one
---" =
  [ mk (Para [mk (Str "one"); mk SoftBreak; mk (Str "---")]) ].
Proof. reflexivity. Qed.

Example parse_code_block :
  parse_blocks "``` ruby
x = 5
```" =
  [ mk (CodeBlock "ruby" ("x = 5" ++ nl)) ].
Proof. reflexivity. Qed.

Example parse_raw_block :
  parse_blocks "``` =html
<hr>
```" =
  [ mk (RawBlock "html" ("<hr>" ++ nl)) ].
Proof. reflexivity. Qed.

(* Unclosed fences extend to end of input; content is never classified. *)
Example parse_unclosed_fence :
  parse_blocks "~~~
* * *
para" =
  [ mk (CodeBlock "" ("* * *" ++ nl ++ "para" ++ nl)) ].
Proof. reflexivity. Qed.

Example parse_blank_only : parse_blocks "  " = [].
Proof. reflexivity. Qed.

(*
Block quotes
------------

Each example is a case from djot.js/test/block_quote.test or a probe
against djot.js; the comment gives the behaviour being pinned. *)

Example parse_quote_basic :
  parse_blocks "> Basic
> quote." =
  [ mk (BlockQuote [mk (Para [mk (Str "Basic"); mk SoftBreak; mk (Str "quote.")])]) ].
Proof. reflexivity. Qed.

(* A bare ">" is a quote with no content — the reason wf_block lets
   BlockQuote be empty. *)
Example parse_quote_empty :
  parse_blocks ">" = [mk (BlockQuote [])].
Proof. reflexivity. Qed.

(* ">" without following whitespace is not a prefix at all. *)
Example parse_quote_needs_ws :
  parse_blocks ">not a quote" =
  [ mk (Para [mk (Str ">not a quote")]) ].
Proof. reflexivity. Qed.

(* A blank prefixed line ends the inner paragraph without ending the
   quote; a truly blank line ends the quote. *)
Example parse_quote_two_paras :
  parse_blocks "> a
>
> b" =
  [ mk (BlockQuote [ mk (Para [mk (Str "a")]); mk (Para [mk (Str "b")]) ]) ].
Proof. reflexivity. Qed.

Example parse_quote_split :
  parse_blocks "> a

> b" =
  [ mk (BlockQuote [mk (Para [mk (Str "a")])])
  ; mk (BlockQuote [mk (Para [mk (Str "b")])]) ].
Proof. reflexivity. Qed.

(* Nesting comes from re-entering the classifier on the stripped line. *)
Example parse_quote_nested :
  parse_blocks "> > > deep" =
  [ mk (BlockQuote [mk (BlockQuote [mk (BlockQuote
      [mk (Para [mk (Str "deep")])])])]) ].
Proof. reflexivity. Qed.

(* Lazy continuation: a prefix-less text line still joins the innermost
   open paragraph, at any depth. *)
Example parse_quote_lazy :
  parse_blocks "> > deep
lazy" =
  [ mk (BlockQuote [mk (BlockQuote
      [mk (Para [mk (Str "deep"); mk SoftBreak; mk (Str "lazy")])])]) ].
Proof. reflexivity. Qed.

(* ...but only into a paragraph.  Verbatim content is not lazily
   continued, so the quote closes and a new paragraph starts. *)
Example parse_quote_no_lazy_fence :
  parse_blocks "> ```
> x
y" =
  [ mk (BlockQuote [mk (CodeBlock "" ("x" ++ nl))])
  ; mk (Para [mk (Str "y")]) ].
Proof. reflexivity. Qed.

(* Nor is a line that starts a block of its own: the quote closes. *)
Example parse_quote_closed_by_thematic :
  parse_blocks "> a
* * * *" =
  [ mk (BlockQuote [mk (Para [mk (Str "a")])]); mk ThematicBreak ].
Proof. reflexivity. Qed.

(*
Headings
--------

Pinned against djot.js probes, as above.  Section wrapping and
auto-identifiers are deliberately absent: they are a whole-document
pass, not part of the line fold. *)

Example parse_heading_basic :
  parse_blocks "## hi" = [mk (Heading 2 [mk (Str "hi")])].
Proof. reflexivity. Qed.

(* The whitespace after the hashes is required. *)
Example parse_heading_needs_ws :
  parse_blocks "#hi" = [mk (Para [mk (Str "#hi")])].
Proof. reflexivity. Qed.

Example parse_heading_empty :
  parse_blocks "#" = [mk (Heading 1 [])].
Proof. reflexivity. Qed.

(* Same level continues the heading; the text joins with a SoftBreak. *)
Example parse_heading_multiline :
  parse_blocks "# a
# b" =
  [mk (Heading 1 [mk (Str "a"); mk SoftBreak; mk (Str "b")])].
Proof. reflexivity. Qed.

(* ...and so does a bare text line, lazily. *)
Example parse_heading_lazy :
  parse_blocks "# a
b" =
  [mk (Heading 1 [mk (Str "a"); mk SoftBreak; mk (Str "b")])].
Proof. reflexivity. Qed.

(* A different level starts a new heading rather than continuing. *)
Example parse_heading_level_change :
  parse_blocks "# a
## b" =
  [mk (Heading 1 [mk (Str "a")]); mk (Heading 2 [mk (Str "b")])].
Proof. reflexivity. Qed.

(* Unlike a paragraph, a heading *is* interrupted by a block start. *)
Example parse_heading_interrupted :
  parse_blocks "# a
* * * *" =
  [mk (Heading 1 [mk (Str "a")]); mk ThematicBreak].
Proof. reflexivity. Qed.

Example parse_heading_interrupted_quote :
  parse_blocks "# a
> q" =
  [ mk (Heading 1 [mk (Str "a")])
  ; mk (BlockQuote [mk (Para [mk (Str "q")])]) ].
Proof. reflexivity. Qed.

(* Heading content is inline: it is never reclassified, so a quote
   marker inside one is just text. *)
Example parse_heading_content_not_reclassified :
  parse_blocks "# > q" = [mk (Heading 1 [mk (Str "> q")])].
Proof. reflexivity. Qed.

(* Containers compose for free: the quote strips, then the classifier
   sees a heading. *)
(*
Bullet lists
------------
*)

Example parse_list_tight :
  parse_blocks "- a
- b" = [mk (BulletList Tight
              [ [mk (Para [mk (Str "a")])]; [mk (Para [mk (Str "b")])] ])].
Proof. reflexivity. Qed.

(* A blank line between items, with content after it, loosens the list. *)
Example parse_list_loose :
  parse_blocks "- a

- b" = [mk (BulletList Loose
              [ [mk (Para [mk (Str "a")])]; [mk (Para [mk (Str "b")])] ])].
Proof. reflexivity. Qed.

(* A trailing blank does not: the next event closes the list. *)
Example parse_list_trailing_blank :
  parse_blocks "- a
" = [mk (BulletList Tight [[mk (Para [mk (Str "a")])]])].
Proof. reflexivity. Qed.

(* Thematic breaks win over bullet markers, matching djot.js spec order. *)
Example parse_list_not_thematic :
  parse_blocks "* * *" = [mk ThematicBreak].
Proof. reflexivity. Qed.

(* A marker never interrupts an open paragraph, so this is one item whose
   paragraph runs on — not a nested list. *)
Example parse_list_no_interrupt :
  parse_blocks "- a
  - b"
  = [mk (BulletList Tight
           [[mk (Para [mk (Str "a"); mk SoftBreak; mk (Str "- b")])]])].
Proof. reflexivity. Qed.

(* A different bullet character is a different list. *)
Example parse_list_style_change :
  parse_blocks "- a
* b"
  = [ mk (BulletList Tight [[mk (Para [mk (Str "a")])]])
    ; mk (BulletList Tight [[mk (Para [mk (Str "b")])]]) ].
Proof. reflexivity. Qed.

(* Lazy continuation reaches into the item's paragraph. *)
Example parse_list_lazy :
  parse_blocks "- a
b"
  = [mk (BulletList Tight
           [[mk (Para [mk (Str "a"); mk SoftBreak; mk (Str "b")])]])].
Proof. reflexivity. Qed.

(* A bare marker opens an item with no content. *)
Example parse_list_empty_item :
  parse_blocks "-
- b"
  = [mk (BulletList Tight [ []; [mk (Para [mk (Str "b")])] ])].
Proof. reflexivity. Qed.

Example parse_heading_in_quote :
  parse_blocks "> # a" =
  [mk (BlockQuote [mk (Heading 1 [mk (Str "a")])])].
Proof. reflexivity. Qed.

(* Paragraphs are never interrupted, quotes included. *)
Example parse_quote_no_interrupt :
  parse_blocks "a
> b" =
  [ mk (Para [mk (Str "a"); mk SoftBreak; mk (Str "> b")]) ].
Proof. reflexivity. Qed.
