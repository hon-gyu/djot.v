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

(* Append a lazy line to the innermost paragraph.  Its leading whitespace
   goes, exactly as on a non-lazy continuation line: a lazy line *is* a
   continuation line, distinguished only by the container prefixes it
   omits, and djot.js strips it either way (checked against the oracle on
   both a quote and a list).  Canonical renderings never produce a lazy
   line, so no roundtrip proof can observe this; it matters for the
   parser's agreement with the oracle on hand-written input, and it is
   what makes the state's content independent of ambient indentation. *)
Fixpoint feed_lazy (l : string) (st : pstate) : pstate :=
  match st with
  | PPara cur => PPara (drop_leading_ws l :: cur)
  | PHeading lvl cur => PHeading lvl (drop_leading_ws l :: cur)
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
(* Columns a container prefix ate before handing down its residue.  The
   parser measures indentation in the original line's coordinates, so a
   nested marker's column survives the descent -- see the nested-list
   entry in .project/oracle-disagreements.md. *)
Definition consumed (l rest : string) : nat :=
  String.length l - String.length rest.

Fixpoint step_fuel (n : nat) (off : nat) (l : string) (st : pstate) {struct n}
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
          | KQuote rest => open_quote (step_fuel n' (off + consumed l rest) rest (PPara []))
          | KList m rest =>
              open_list (off + indent_of l) m
                (step_fuel n' (off + consumed l rest) rest (PPara []))
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
                (open_quote (step_fuel n' (off + consumed l rest) rest (PPara [])))
          | KList m rest =>
              close_reopen (PHeading lvl cur)
                (open_list (off + indent_of l) m
                   (step_fuel n' (off + consumed l rest) rest (PPara [])))
          | k => close_reopen (PHeading lvl cur) (open_kind l k)
          end
      | PQuote done inner =>
          match classify l with
          | KQuote rest =>
              (* continue: descend into the quote already open, keeping
                 what it has closed so far *)
              let (bs, inner') := step_fuel n' (off + consumed l rest) rest inner in
              ([], PQuote (rev bs ++ done)%list inner')
          | KList m rest =>
              close_reopen (PQuote done inner)
                (open_list (off + indent_of l) m
                   (step_fuel n' (off + consumed l rest) rest (PPara [])))
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
              let (bs, inner') := step_fuel n' off l inner in
              ([], PList (list_blank ls) (rev bs ++ done)%list inner')
          | k =>
              if Nat.ltb (ls_indent ls) (off + indent_of l)
              then
                (* indented past the marker: contents of the current
                   item.  The line is passed down unchanged — every
                   recognizer already skips leading whitespace, so block
                   structure is right; what the extra indent still costs
                   is inline and verbatim text, the same open indentation
                   gap quotes and headings have. *)
                let (bs, inner') := step_fuel n' off l inner in
                ([], PList (list_content ls k) (rev bs ++ done)%list inner')
              else
                match k with
                | KList m rest =>
                    if Ascii.eqb m (ls_marker ls)
                    then
                      (* a sibling item: close the current one, open the
                         next around the rest of the line *)
                      let item := (rev done ++ finish inner)%list in
                      let (bs, inner') :=
                        step_fuel n' (off + consumed l rest) rest (PPara []) in
                      ([], PList (list_next ls item rest) (rev bs) inner')
                    else
                      (* a different bullet style is a different list *)
                      close_reopen (PList ls done inner)
                        (open_list (off + indent_of l) m
                           (step_fuel n' (off + consumed l rest) rest (PPara [])))
                | KQuote rest =>
                    close_reopen (PList ls done inner)
                      (open_quote (step_fuel n' (off + consumed l rest) rest (PPara [])))
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
  step_fuel (S (String.length l + pstate_depth st)) 0 l st.

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
  forall bound n off l st,
    n <= bound -> S (String.length l + pstate_depth st) <= n ->
    step_fuel n off l st
    = step_fuel (S (String.length l + pstate_depth st)) off l st.
Proof.
  induction bound as [|bound IH]; intros n off l st Hb Hn; [lia|].
  destruct n as [|n']; [lia|].
  cbn [step_fuel].
  destruct st as [cur|hlvl hcur|f acc|done inner|ls done inner].
  - (* idle, or an open paragraph *)
    cbn [pstate_depth] in Hn |- *.
    destruct cur as [|c cur'].
    + destruct (classify l) as [| |g|rest|kl kr|m mr|] eqn:E; try reflexivity.
      * pose proof (classify_quote_length _ _ E) as Hlt.
        cbn [pstate_depth]; rewrite ?Nat.add_0_r.
        rewrite (IH n' _ rest (PPara [])) by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l) _ rest (PPara [])) by (cbn [pstate_depth]; lia).
        reflexivity.
      * pose proof (classify_list_length _ _ _ E) as Hlt.
        cbn [pstate_depth]; rewrite ?Nat.add_0_r.
        rewrite (IH n' _ mr (PPara [])) by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l) _ mr (PPara [])) by (cbn [pstate_depth]; lia).
        reflexivity.
    + destruct (classify l); reflexivity.
  - (* an open heading: the quote and list branches recurse *)
    cbn [pstate_depth] in Hn |- *.
    destruct (classify l) as [| |g|rest|kl kr|m mr|] eqn:E; try reflexivity.
    + pose proof (classify_quote_length _ _ E) as Hlt.
      cbn [pstate_depth]; rewrite ?Nat.add_0_r.
      rewrite (IH n' _ rest (PPara [])) by (cbn [pstate_depth]; lia).
      rewrite (IH (String.length l) _ rest (PPara [])) by (cbn [pstate_depth]; lia).
      reflexivity.
    + pose proof (classify_list_length _ _ _ E) as Hlt.
      cbn [pstate_depth]; rewrite ?Nat.add_0_r.
      rewrite (IH n' _ mr (PPara [])) by (cbn [pstate_depth]; lia).
      rewrite (IH (String.length l) _ mr (PPara [])) by (cbn [pstate_depth]; lia).
      reflexivity.
  - destruct (fence_close f l); reflexivity.
  - (* inside a quote: continuing descends with the same inner state *)
    cbn [pstate_depth] in Hn |- *.
    destruct (classify l) as [| |g|rest|kl kr|m mr|] eqn:E; try reflexivity.
    + pose proof (classify_quote_length _ _ E) as Hlt.
      rewrite (IH n' _ rest inner) by lia.
      rewrite (IH (String.length l + S (pstate_depth inner)) _ rest inner) by lia.
      reflexivity.
    + pose proof (classify_list_length _ _ _ E) as Hlt.
      rewrite (IH n' _ mr (PPara [])) by (cbn [pstate_depth]; lia).
      rewrite (IH (String.length l + S (pstate_depth inner)) _ mr (PPara []))
        by (cbn [pstate_depth]; lia).
      reflexivity.
  - (* inside a list: an item's contents keep the line and drop a level *)
    cbn [pstate_depth] in Hn |- *.
    destruct (classify l) as [| |g|rest|kl kr|m mr|] eqn:E.
    6: { (* a bullet marker: a sibling item, or a list of another style *)
      pose proof (classify_list_length _ _ _ E) as Hlt.
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - rewrite (IH n' _ l inner) by lia.
        rewrite (IH (String.length l + S (pstate_depth inner)) _ l inner) by lia.
        reflexivity.
      - destruct (Ascii.eqb m (ls_marker ls));
          rewrite (IH n' _ mr (PPara [])) by (cbn [pstate_depth]; lia);
          rewrite (IH (String.length l + S (pstate_depth inner)) _ mr (PPara []))
            by (cbn [pstate_depth]; lia);
          reflexivity. }
    1: { (* a blank line goes to the item's contents *)
      rewrite (IH n' _ l inner) by lia.
      rewrite (IH (String.length l + S (pstate_depth inner)) _ l inner) by lia.
      reflexivity. }
    3: { (* an unindented quote closes the list and opens outside it *)
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - rewrite (IH n' _ l inner) by lia.
        rewrite (IH (String.length l + S (pstate_depth inner)) _ l inner) by lia.
        reflexivity.
      - pose proof (classify_quote_length _ _ E) as Hlt.
        rewrite (IH n' _ rest (PPara [])) by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l + S (pstate_depth inner)) _ rest (PPara []))
          by (cbn [pstate_depth]; lia).
        reflexivity. }
    (* every other kind: contents of the item when indented past the
       marker, and otherwise nothing that recurses *)
    all: destruct (Nat.ltb (ls_indent ls) (off + indent_of l));
         [ rewrite (IH n' _ l inner) by lia;
           rewrite (IH (String.length l + S (pstate_depth inner)) _ l inner) by lia;
           reflexivity
         | reflexivity ].
Qed.

Lemma step_fuel_enough :
  forall n l st,
    S (String.length l + pstate_depth st) <= n -> step_fuel n 0 l st = step l st.
Proof. intros n l st H. apply (step_fuel_stable n); lia. Qed.

(* The same, at an arbitrary offset: descents need it, since only the
   outermost call runs at offset 0. *)
Lemma step_fuel_enough_off :
  forall n off l st,
    S (String.length l + pstate_depth st) <= n ->
    step_fuel n off l st
    = step_fuel (S (String.length l + pstate_depth st)) off l st.
Proof. intros n off l st H. apply (step_fuel_stable n); lia. Qed.

(*
Shifting a run sideways
-----------------------

`off` is the column the line's first character sits at, so a list's
recorded indent is `off + indent_of l` -- an absolute column, invariant
under how many container prefixes were peeled off to reach it.  Adding a
constant `k` to the offset therefore adds `k` to every indent the run
records, and changes nothing else: `Nat.ltb` is invariant under adding the
same amount to both sides, and no other part of the state or of the
emitted blocks mentions a column.

That is `step_fuel_shift`, and it is the parser's uniformity statement for
indentation.  Note what it does *not* exclude: an open fence is fine here,
because `PFence` stores lines verbatim and records no column at all.
Fences only become a problem for `step_pad` below, which pads the line
itself rather than moving the offset. *)

(* The shift, on the state: every recorded column moves by n. *)
Fixpoint pad_state (n : nat) (st : pstate) : pstate :=
  match st with
  | PQuote done inner => PQuote done (pad_state n inner)
  | PList ls done inner =>
      PList (LSt (n + ls_indent ls) (ls_marker ls) (ls_loose ls)
                 (ls_blanks ls) (ls_items ls))
            done (pad_state n inner)
  | _ => st
  end.

Lemma ltb_add_mono_l :
  forall n a b, Nat.ltb (n + a) (n + b) = Nat.ltb a b.
Proof.
  intros n a b. destruct (Nat.ltb a b) eqn:E.
  - apply Nat.ltb_lt. apply Nat.ltb_lt in E. lia.
  - apply Nat.ltb_ge. apply Nat.ltb_ge in E. lia.
Qed.

Lemma pad_state_depth :
  forall n st, pstate_depth (pad_state n st) = pstate_depth st.
Proof.
  intros n st. induction st as [| | |done inner IH|ls done inner IH];
    try reflexivity; cbn [pad_state pstate_depth]; rewrite IH; reflexivity.
Qed.

(* finish reads a list's spacing and items, never its column. *)
Lemma pad_state_finish :
  forall n st, finish (pad_state n st) = finish st.
Proof.
  intros n st. induction st as [| | |done inner IH|ls done inner IH];
    try reflexivity; cbn [pad_state finish]; rewrite IH; reflexivity.
Qed.

Lemma pad_state_lazy_ok :
  forall n st, lazy_ok (pad_state n st) = lazy_ok st.
Proof.
  intros n st. induction st as [cur| | |done inner IH|ls done inner IH];
    try reflexivity; cbn [pad_state lazy_ok]; exact IH.
Qed.

Lemma pad_state_feed_lazy :
  forall n l st, feed_lazy l (pad_state n st) = pad_state n (feed_lazy l st).
Proof.
  intros n l st.
  induction st as [cur|lvl cur| |done inner IH|ls done inner IH];
    cbn [pad_state feed_lazy]; try reflexivity; rewrite IH; reflexivity.
Qed.

(* The three flag updates preserve ls_indent, so each commutes with the
   shift. *)
Lemma pad_list_blank :
  forall n ls,
    list_blank (LSt (n + ls_indent ls) (ls_marker ls) (ls_loose ls)
                    (ls_blanks ls) (ls_items ls))
    = LSt (n + ls_indent (list_blank ls)) (ls_marker (list_blank ls))
          (ls_loose (list_blank ls)) (ls_blanks (list_blank ls))
          (ls_items (list_blank ls)).
Proof. intros n ls. destruct ls. reflexivity. Qed.

Lemma pad_list_content :
  forall n ls k,
    list_content (LSt (n + ls_indent ls) (ls_marker ls) (ls_loose ls)
                      (ls_blanks ls) (ls_items ls)) k
    = LSt (n + ls_indent (list_content ls k)) (ls_marker (list_content ls k))
          (ls_loose (list_content ls k)) (ls_blanks (list_content ls k))
          (ls_items (list_content ls k)).
Proof. intros n ls k. destruct ls; destruct k; reflexivity. Qed.

Lemma pad_list_next :
  forall n ls item rest,
    list_next (LSt (n + ls_indent ls) (ls_marker ls) (ls_loose ls)
                   (ls_blanks ls) (ls_items ls)) item rest
    = LSt (n + ls_indent (list_next ls item rest))
          (ls_marker (list_next ls item rest))
          (ls_loose (list_next ls item rest))
          (ls_blanks (list_next ls item rest))
          (ls_items (list_next ls item rest)).
Proof.
  intros n ls item rest. unfold list_next.
  destruct ls; destruct (is_blank rest); reflexivity.
Qed.

(* The two shapes `pad_state` leaves behind, as `close_reopen` sees them. *)
Lemma finish_pad_list :
  forall n ls done inner,
    finish (PList (LSt (n + ls_indent ls) (ls_marker ls) (ls_loose ls)
                       (ls_blanks ls) (ls_items ls)) done (pad_state n inner))
    = finish (PList ls done inner).
Proof.
  intros n ls done inner. cbn [finish].
  rewrite (pad_state_finish n inner). destruct ls. reflexivity.
Qed.

Lemma finish_pad_quote :
  forall n done inner,
    finish (PQuote done (pad_state n inner)) = finish (PQuote done inner).
Proof.
  intros n done inner. cbn [finish]. rewrite (pad_state_finish n inner).
  reflexivity.
Qed.

(** Moving the whole run `k` columns to the right moves every recorded
    column by `k` and changes nothing else -- not the blocks, not the
    tight/loose flags, not which branch any line takes. *)
Lemma step_fuel_shift :
  forall n k off l st,
    step_fuel n (k + off) l (pad_state k st)
    = (fst (step_fuel n off l st), pad_state k (snd (step_fuel n off l st))).
Proof.
  induction n as [|n IH]; intros k off l st; [reflexivity|].
  destruct st as [cur|hlvl hcur|f acc|done inner|ls done inner].
  (* idle, or an open paragraph *)
  { cbn [pad_state step_fuel].
    destruct cur as [|c cur'].
    { destruct (classify l) as [| |g|rest|klvl krest|m mr|] eqn:E;
        try reflexivity.
      { rewrite <- Nat.add_assoc.
        pose proof (IH k (off + consumed l rest) rest (PPara [])) as H;
          cbn [pad_state] in H; rewrite H.
        destruct (step_fuel n (off + consumed l rest) rest (PPara []))
          as [bs inner'] eqn:Ed.
        cbn [open_quote fst snd pad_state]. reflexivity. }
      { rewrite <- !Nat.add_assoc.
        pose proof (IH k (off + consumed l mr) mr (PPara [])) as H;
          cbn [pad_state] in H; rewrite H.
        destruct (step_fuel n (off + consumed l mr) mr (PPara []))
          as [bs inner'] eqn:Ed.
        cbn [open_list fst snd pad_state]. reflexivity. } }
    { destruct (classify l); reflexivity. } }
  (* heading *)
  { cbn [pad_state step_fuel].
    destruct (classify l) as [| |g|rest|klvl krest|m mr|] eqn:E.
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { rewrite <- Nat.add_assoc.
      pose proof (IH k (off + consumed l rest) rest (PPara [])) as H;
        cbn [pad_state] in H; rewrite H.
      destruct (step_fuel n (off + consumed l rest) rest (PPara []))
        as [bs inner'] eqn:Ed.
      cbn [close_reopen open_quote fst snd pad_state]. reflexivity. }
    { destruct (klvl =? hlvl)%nat; reflexivity. }
    { rewrite <- !Nat.add_assoc.
      pose proof (IH k (off + consumed l mr) mr (PPara [])) as H;
        cbn [pad_state] in H; rewrite H.
      destruct (step_fuel n (off + consumed l mr) mr (PPara []))
        as [bs inner'] eqn:Ed.
      cbn [close_reopen open_list fst snd pad_state]. reflexivity. }
    { reflexivity. } }
  (* fence: verbatim, and it records no column *)
  { cbn [pad_state step_fuel]. destruct (fence_close f l); reflexivity. }
  (* quote *)
  { cbn [pad_state step_fuel].
    destruct (classify l) as [| |g|rest|klvl krest|m mr|] eqn:E.
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      rewrite finish_pad_quote. reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      rewrite finish_pad_quote. reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      rewrite finish_pad_quote. reflexivity. }
    { rewrite <- Nat.add_assoc.
      rewrite (IH k (off + consumed l rest) rest inner).
      destruct (step_fuel n (off + consumed l rest) rest inner)
        as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      rewrite finish_pad_quote. reflexivity. }
    { rewrite <- !Nat.add_assoc.
      pose proof (IH k (off + consumed l mr) mr (PPara [])) as H;
        cbn [pad_state] in H; rewrite H.
      destruct (step_fuel n (off + consumed l mr) mr (PPara []))
        as [bs inner'] eqn:Ed.
      cbn [close_reopen open_list fst snd pad_state].
      rewrite finish_pad_quote. reflexivity. }
    { cbn [is_lazy]. rewrite pad_state_lazy_ok.
      destruct (lazy_ok inner) eqn:El.
      { cbn [pad_state]. rewrite pad_state_feed_lazy. reflexivity. }
      { cbn [close_reopen open_kind fst snd pad_state].
        rewrite finish_pad_quote. reflexivity. } } }
  (* list: every recorded column lives here *)
  { cbn [pad_state step_fuel].
    destruct (classify l) as [| |g|rest|klvl krest|m mr|] eqn:E.
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_list_blank. reflexivity. }
    all: cbn [ls_indent]; rewrite <- Nat.add_assoc, ltb_add_mono_l.
    all: destruct (Nat.ltb (ls_indent ls) (off + indent_of l)) eqn:Elt.
    (* thematic *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      rewrite finish_pad_list. reflexivity. }
    (* fence *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      rewrite finish_pad_list. reflexivity. }
    (* quote *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
    { rewrite <- Nat.add_assoc.
      pose proof (IH k (off + consumed l rest) rest (PPara [])) as H;
        cbn [pad_state] in H; rewrite H.
      destruct (step_fuel n (off + consumed l rest) rest (PPara []))
        as [bs inner'] eqn:Ed.
      cbn [close_reopen open_quote fst snd pad_state].
      rewrite finish_pad_list. reflexivity. }
    (* heading *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      rewrite finish_pad_list. reflexivity. }
    (* list marker *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
    { cbn [ls_marker]. destruct (Ascii.eqb m (ls_marker ls)) eqn:Em.
      { rewrite <- Nat.add_assoc, (pad_state_finish k inner).
        pose proof (IH k (off + consumed l mr) mr (PPara [])) as H;
          cbn [pad_state] in H; rewrite H.
        destruct (step_fuel n (off + consumed l mr) mr (PPara []))
          as [bs inner'] eqn:Ed.
        cbn [fst snd pad_state]. rewrite pad_list_next. reflexivity. }
      { rewrite <- !Nat.add_assoc.
        pose proof (IH k (off + consumed l mr) mr (PPara [])) as H;
          cbn [pad_state] in H; rewrite H.
        destruct (step_fuel n (off + consumed l mr) mr (PPara []))
          as [bs inner'] eqn:Ed.
        cbn [close_reopen open_list fst snd pad_state].
        rewrite finish_pad_list. reflexivity. } }
    (* text *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
    { cbn [is_lazy]. rewrite pad_state_lazy_ok.
      destruct (lazy_ok inner) eqn:El.
      { cbn [pad_state]. rewrite pad_state_feed_lazy. reflexivity. }
      { cbn [close_reopen open_kind fst snd pad_state].
        rewrite finish_pad_list. reflexivity. } } }
Qed.

(* `step` at a nonzero column.  Descents run here: only the outermost
   call sees column 0. *)
Definition step_at (off : nat) (l : string) (st : pstate) : blocks * pstate :=
  step_fuel (S (String.length l + pstate_depth st)) off l st.

Lemma step_at_zero : forall l st, step_at 0 l st = step l st.
Proof. reflexivity. Qed.

Lemma step_at_shift :
  forall k off l st,
    step_at (k + off) l (pad_state k st)
    = (fst (step_at off l st), pad_state k (snd (step_at off l st))).
Proof.
  intros k off l st. unfold step_at. rewrite pad_state_depth.
  apply step_fuel_shift.
Qed.

(* Descending from idle is the common case: the residue starts a fresh
   run, so its whole state is the shift of the run at column 0. *)
Lemma step_at_idle :
  forall k l,
    step_at k l (PPara [])
    = (fst (step l (PPara [])), pad_state k (snd (step l (PPara [])))).
Proof.
  intros k l. rewrite <- (step_at_zero l (PPara [])).
  rewrite <- (Nat.add_0_r k) at 1.
  exact (step_at_shift k 0 l (PPara [])).
Qed.

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
    step l (PPara [])
    = ([], PQuote (rev bs) (pad_state (consumed l rest) inner)).
Proof.
  intros l rest bs inner H Hr. unfold step at 1. cbn [step_fuel]. rewrite H.
  change (step_fuel ?n (0 + consumed l rest) rest (PPara []))
    with (step_fuel n (consumed l rest) rest (PPara [])).
  rewrite (step_fuel_enough_off _ (consumed l rest) rest (PPara []))
    by (cbn [pstate_depth]; pose proof (classify_quote_length _ _ H); lia).
  change (step_fuel (S (String.length rest + pstate_depth (PPara [])))
            (consumed l rest) rest (PPara []))
    with (step_at (consumed l rest) rest (PPara [])).
  rewrite step_at_idle, Hr. reflexivity.
Qed.

Lemma step_quote_cont :
  forall l rest done inner bs inner',
    classify l = KQuote rest ->
    step_at (consumed l rest) rest inner = (bs, inner') ->
    step l (PQuote done inner) = ([], PQuote (rev bs ++ done)%list inner').
Proof.
  intros l rest done inner bs inner' H Hr. unfold step at 1.
  cbn [step_fuel pstate_depth]. rewrite H.
  change (step_fuel ?n (0 + consumed l rest) rest inner)
    with (step_fuel n (consumed l rest) rest inner).
  rewrite (step_fuel_enough_off _ (consumed l rest) rest inner)
    by (cbn [pstate_depth]; pose proof (classify_quote_length _ _ H); lia).
  change (step_fuel (S (String.length rest + pstate_depth inner))
            (consumed l rest) rest inner)
    with (step_at (consumed l rest) rest inner).
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
      ([], PList (LSt (indent_of l) m false false []) (rev bs)
             (pad_state (consumed l rest) inner)).
Proof.
  intros l m rest bs inner H Hr. unfold step at 1. cbn [step_fuel]. rewrite H.
  change (step_fuel ?n (0 + consumed l rest) rest (PPara []))
    with (step_fuel n (consumed l rest) rest (PPara [])).
  rewrite (step_fuel_enough_off _ (consumed l rest) rest (PPara []))
    by (cbn [pstate_depth]; pose proof (classify_list_length _ _ _ H); lia).
  change (step_fuel (S (String.length rest + pstate_depth (PPara [])))
            (consumed l rest) rest (PPara []))
    with (step_at (consumed l rest) rest (PPara [])).
  rewrite step_at_idle, Hr. reflexivity.
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
  cbn [step_fuel pstate_depth]. rewrite H, !Nat.add_0_l.
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
    ([], PList (list_next ls (rev done ++ finish inner)%list rest) (rev bs)
           (pad_state (consumed l rest) inner')).
Proof.
  intros l m rest ls done inner bs inner' H Hm Hind Hr. unfold step at 1.
  cbn [step_fuel pstate_depth]. rewrite H, !Nat.add_0_l, Hind, Hm.
  change (step_fuel ?n (0 + consumed l rest) rest (PPara []))
    with (step_fuel n (consumed l rest) rest (PPara [])).
  rewrite (step_fuel_enough_off _ (consumed l rest) rest (PPara []))
    by (cbn [pstate_depth]; pose proof (classify_list_length _ _ _ H); lia).
  change (step_fuel (S (String.length rest + pstate_depth (PPara [])))
            (consumed l rest) rest (PPara []))
    with (step_at (consumed l rest) rest (PPara [])).
  rewrite step_at_idle, Hr. reflexivity.
Qed.

Lemma step_list_diffstyle :
  forall l m rest ls done inner bs inner',
    classify l = KList m rest ->
    Ascii.eqb m (ls_marker ls) = false ->
    Nat.ltb (ls_indent ls) (indent_of l) = false ->
    step rest (PPara []) = (bs, inner') ->
    step l (PList ls done inner) =
    (finish (PList ls done inner),
     PList (LSt (indent_of l) m false false []) (rev bs)
       (pad_state (consumed l rest) inner')).
Proof.
  intros l m rest ls done inner bs inner' H Hm Hind Hr. unfold step at 1.
  cbn [step_fuel pstate_depth]. rewrite H, !Nat.add_0_l, Hind, Hm.
  change (step_fuel ?n (0 + consumed l rest) rest (PPara []))
    with (step_fuel n (consumed l rest) rest (PPara [])).
  rewrite (step_fuel_enough_off _ (consumed l rest) rest (PPara []))
    by (cbn [pstate_depth]; pose proof (classify_list_length _ _ _ H); lia).
  change (step_fuel (S (String.length rest + pstate_depth (PPara [])))
            (consumed l rest) rest (PPara []))
    with (step_at (consumed l rest) rest (PPara [])).
  rewrite step_at_idle, Hr. reflexivity.
Qed.

Lemma step_list_quote_close :
  forall l rest ls done inner bs inner',
    classify l = KQuote rest ->
    Nat.ltb (ls_indent ls) (indent_of l) = false ->
    step rest (PPara []) = (bs, inner') ->
    step l (PList ls done inner) =
      (finish (PList ls done inner),
       PQuote (rev bs) (pad_state (consumed l rest) inner')).
Proof.
  intros l rest ls done inner bs inner' H Hind Hr.
  unfold step at 1. cbn [step_fuel pstate_depth].
  rewrite H, !Nat.add_0_l, Hind.
  change (step_fuel ?n (0 + consumed l rest) rest (PPara []))
    with (step_fuel n (consumed l rest) rest (PPara [])).
  rewrite (step_fuel_enough_off _ (consumed l rest) rest (PPara []))
    by (cbn [pstate_depth]; pose proof (classify_quote_length _ _ H); lia).
  change (step_fuel (S (String.length rest + pstate_depth (PPara [])))
            (consumed l rest) rest (PPara []))
    with (step_at (consumed l rest) rest (PPara [])).
  rewrite step_at_idle, Hr. cbn [close_reopen open_quote].
  rewrite app_nil_r. reflexivity.
Qed.

Lemma step_list_lazy :
  forall l ls done inner,
    classify l = KText -> Nat.ltb (ls_indent ls) (indent_of l) = false ->
    lazy_ok inner = true ->
    step l (PList ls done inner) = ([], PList ls done (feed_lazy l inner)).
Proof.
  intros l ls done inner H Hind Hl. unfold step. cbn [step_fuel].
  rewrite H, !Nat.add_0_l, Hind. cbn [is_lazy]. rewrite Hl. reflexivity.
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
  rewrite H, !Nat.add_0_l.
  destruct k; [congruence | idtac | idtac | discriminate | idtac | discriminate | idtac];
    rewrite Hind; cbn [is_lazy] in Hlz |- *; try rewrite Hlz; rewrite Ho; reflexivity.
Qed.

(*
Padding a line
--------------

Putting a blank prefix in front of a line is the same as starting that
line further right: `classify`, `is_thematic`, `is_blank` and
`drop_leading_ws` all ignore a leading blank prefix, `indent_of` adds its
length, and every descent consumes exactly that much more.  So padding
needs no theorem of its own -- it reduces to the offset, and
`step_fuel_shift` does the rest.

The one state that notices is `PFence`, which stores its lines verbatim
and so keeps the pad in the block's content.  `pad_safe` names that
exclusion; it stops at `PQuote` because a quote prefix absorbs the pad
before handing down its residue. *)

(* A lazy line's pad is dropped wherever the line comes to rest -- the
   reason feed_lazy strips leading whitespace at all. *)
Lemma feed_lazy_ws_prefix :
  forall p l st,
    is_blank p = true -> feed_lazy (p ++ l) st = feed_lazy l st.
Proof.
  intros p l st Hp.
  induction st as [cur|lvl cur| |done inner IH|ls done inner IH];
    cbn [feed_lazy];
    try (rewrite (drop_leading_ws_ws_prefix p l Hp); reflexivity);
    try (rewrite IH; reflexivity).
  reflexivity.
Qed.

Fixpoint pad_safe (st : pstate) : bool :=
  match st with
  | PFence _ _ => false
  | PList _ _ inner => pad_safe inner
  | _ => true
  end.

Lemma step_fuel_pad :
  forall n p off l st,
    is_blank p = true ->
    pad_safe st = true ->
    step_fuel n off (p ++ l) st = step_fuel n (String.length p + off) l st.
Proof.
  induction n as [|n IH]; intros p off l st Hp Hsafe; [reflexivity|].
  (* natural subtraction truncates, so this needs the residue to be no
     longer than the line -- which classify always gives *)
  assert (Hc : forall rest, String.length rest <= String.length l ->
                 consumed (p ++ l) rest = String.length p + consumed l rest).
  { intros rest Hle. unfold consumed. rewrite length_append. lia. }
  destruct st as [cur|hlvl hcur|f acc|done inner|ls done inner].
  { cbn [step_fuel]. rewrite (classify_ws_prefix p l Hp).
    destruct cur as [|c cur'].
    { destruct (classify l) as [| |g|rest|klvl krest|m mr|] eqn:E;
        try reflexivity.
      { rewrite (Hc rest ltac:(pose proof (classify_quote_length _ _ E); lia)),
                Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
      { rewrite (Hc mr ltac:(pose proof (classify_list_length _ _ _ E); lia)),
                (indent_of_ws_prefix p l Hp), !Nat.add_assoc, (Nat.add_comm off (String.length p)).
        reflexivity. }
      { cbn [open_kind]. rewrite (drop_leading_ws_ws_prefix p l Hp).
        reflexivity. } }
    { destruct (classify l);
        try (cbn [open_kind close_reopen];
           rewrite (drop_leading_ws_ws_prefix p l Hp); reflexivity).
      reflexivity. } }
  { cbn [step_fuel]. rewrite (classify_ws_prefix p l Hp).
    destruct (classify l) as [| |g|rest|klvl krest|m mr|] eqn:E;
      try reflexivity.
    { rewrite (Hc rest ltac:(pose proof (classify_quote_length _ _ E); lia)),
              Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { rewrite (Hc mr ltac:(pose proof (classify_list_length _ _ _ E); lia)),
              (indent_of_ws_prefix p l Hp), !Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [open_kind]. rewrite (drop_leading_ws_ws_prefix p l Hp).
        reflexivity. } }
  { discriminate Hsafe. }
  { cbn [step_fuel]. rewrite (classify_ws_prefix p l Hp).
    destruct (classify l) as [| |g|rest|klvl krest|m mr|] eqn:E;
      try reflexivity.
    { rewrite (Hc rest ltac:(pose proof (classify_quote_length _ _ E); lia)),
              Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { rewrite (Hc mr ltac:(pose proof (classify_list_length _ _ _ E); lia)),
              (indent_of_ws_prefix p l Hp), !Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [is_lazy]. destruct (lazy_ok inner);
        [rewrite (feed_lazy_ws_prefix p l _ Hp)|
         cbn [close_reopen open_kind];
         rewrite (drop_leading_ws_ws_prefix p l Hp)]; reflexivity. } }
  { cbn [pad_safe] in Hsafe. cbn [step_fuel].
    rewrite (classify_ws_prefix p l Hp).
    destruct (classify l) as [| |g|rest|klvl krest|m mr|] eqn:E.
    { rewrite (IH p off l inner Hp Hsafe). reflexivity. }
    all: rewrite (indent_of_ws_prefix p l Hp), Nat.add_assoc,
                 (Nat.add_comm off (String.length p)).
    all: destruct (Nat.ltb (ls_indent ls) (String.length p + off + indent_of l))
           eqn:Elt;
         try (rewrite (IH p off l inner Hp Hsafe); reflexivity).
    { reflexivity. }
    { reflexivity. }
    { rewrite (Hc rest ltac:(pose proof (classify_quote_length _ _ E); lia)),
              Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { reflexivity. }
    { destruct (Ascii.eqb m (ls_marker ls));
        rewrite (Hc mr ltac:(pose proof (classify_list_length _ _ _ E); lia)),
                !Nat.add_assoc, (Nat.add_comm off (String.length p));
        reflexivity. }
    { cbn [is_lazy]. destruct (lazy_ok inner);
        [rewrite (feed_lazy_ws_prefix p l _ Hp)|
         cbn [close_reopen open_kind];
         rewrite (drop_leading_ws_ws_prefix p l Hp)]; reflexivity. } }
Qed.

(** A blank prefix in front of a line is exactly a shift of its starting
    column. *)
Lemma step_pad :
  forall p l st,
    is_blank p = true -> pad_safe st = true ->
    step (p ++ l) st = step_at (String.length p) l st.
Proof.
  intros p l st Hp Hsafe. unfold step, step_at.
  rewrite (step_fuel_pad _ p 0 l st Hp Hsafe), Nat.add_0_r.
  apply step_fuel_enough_off. rewrite length_append. lia.
Qed.

(*
Lifting to the fold
-------------------
*)

(* The fold at a nonzero column.  Only quote and list *content* lemmas
   need it: `parse_lines` itself is the column-0 instance, and it is what
   every statement outside this file uses. *)
Fixpoint parse_lines_at (off : nat) (lines : list string) (st : pstate)
  : blocks :=
  match lines with
  | [] => finish st
  | l :: rest =>
      let (bs, st') := step_at off l st in
      (bs ++ parse_lines_at off rest st')%list
  end.

Lemma parse_lines_at_zero :
  forall lines st, parse_lines_at 0 lines st = parse_lines lines st.
Proof.
  induction lines as [|l lines IH]; intros st; [reflexivity|].
  cbn [parse_lines_at parse_lines]. rewrite step_at_zero.
  destruct (step l st) as [bs st'] eqn:E. rewrite IH. reflexivity.
Qed.

(** Running the fold `k` columns over, from a state shifted to match,
    gives the same blocks: the shift lives only in the state, and `finish`
    does not read columns. *)
Lemma parse_lines_at_shift :
  forall k off lines st,
    parse_lines_at (k + off) lines (pad_state k st) = parse_lines_at off lines st.
Proof.
  induction lines as [|l lines IH]; intros st.
  { cbn [parse_lines_at]. apply pad_state_finish. }
  cbn [parse_lines_at]. rewrite step_at_shift.
  destruct (step_at off l st) as [bs st'] eqn:E. cbn [fst snd].
  rewrite IH. reflexivity.
Qed.

Lemma parse_lines_shift :
  forall k lines st,
    parse_lines_at k lines (pad_state k st) = parse_lines lines st.
Proof.
  intros k lines st.
  rewrite <- (parse_lines_at_zero lines st).
  rewrite <- (parse_lines_at_shift k 0 lines st), Nat.add_0_r.
  reflexivity.
Qed.

(* A canonical quote prefix eats exactly two columns. *)
Lemma consumed_quote_prefix :
  forall l, consumed ("> " ++ l) l = 2.
Proof.
  intros l. unfold consumed. rewrite length_append. cbn [String.length]. lia.
Qed.


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
                (PQuote done (pad_state 2 inner))
    = mk (BlockQuote (rev done ++ parse_lines lines inner)%list)
      :: parse_lines tail (PPara []).
Proof.
  induction lines as [|l lines IH]; intros tail done inner.
  - cbn [map app].
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_close _ KBlank _ _ _ _
                  (classify_blank EmptyString eq_refl) eq_refl eq_refl eq_refl)).
    rewrite pad_state_finish. reflexivity.
  - cbn [map app].
    destruct (step l inner) as [bs inner'] eqn:Es.
    assert (Esh : step_at (consumed ("> " ++ l) l) l (pad_state 2 inner)
                  = (bs, pad_state 2 inner')).
    { rewrite consumed_quote_prefix.
      rewrite <- (Nat.add_0_r 2) at 1. rewrite step_at_shift.
      rewrite step_at_zero, Es. reflexivity. }
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _ (classify_canonical_quote l) Esh)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

(* ...and the same when the input simply ends. *)
Lemma parse_lines_quote_cont_eof :
  forall lines done inner,
    parse_lines (map (fun l => ("> " ++ l)%string) lines)
                (PQuote done (pad_state 2 inner))
    = [mk (BlockQuote (rev done ++ parse_lines lines inner)%list)].
Proof.
  induction lines as [|l lines IH]; intros done inner.
  - cbn [map parse_lines finish]. rewrite pad_state_finish. reflexivity.
  - cbn [map].
    destruct (step l inner) as [bs inner'] eqn:Es.
    assert (Esh : step_at (consumed ("> " ++ l) l) l (pad_state 2 inner)
                  = (bs, pad_state 2 inner')).
    { rewrite consumed_quote_prefix.
      rewrite <- (Nat.add_0_r 2) at 1. rewrite step_at_shift.
      rewrite step_at_zero, Es. reflexivity. }
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _ (classify_canonical_quote l) Esh)).
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
  cbn [app]. rewrite consumed_quote_prefix.
  rewrite parse_lines_quote_cont, rev_involutive.
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
  cbn [app]. rewrite consumed_quote_prefix.
  rewrite parse_lines_quote_cont_eof, rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.

(* The same four lemmas, seen through an all-whitespace pad in front of
   every "> " — verbatim copies of the proofs above with
   classify_canonical_quote_pad in place of classify_canonical_quote.
   This is what lets a quote nested inside a list item ignore the
   item's own indent entirely: the pad never reaches `rest`, so the
   recursion into the quote's contents is byte-identical to the
   unpadded case.  A nested list is not byte-identical -- its recorded
   column moves with the pad -- which is why the list side is stated as
   a shift (`run_lines_pad_shift`) rather than an equality. *)
Lemma consumed_quote_prefix_pad :
  forall pad l, consumed (pad ++ "> " ++ l) l = String.length pad + 2.
Proof.
  intros pad l. unfold consumed. rewrite !length_append.
  cbn [String.length]. lia.
Qed.

Lemma parse_lines_quote_cont_pad :
  forall pad, is_blank pad = true ->
  forall sep, classify sep = KBlank ->
  forall lines tail done inner,
    parse_lines (map (fun l => pad ++ "> " ++ l)%string lines ++ sep :: tail)%list
                (PQuote done (pad_state (String.length pad + 2) inner))
    = mk (BlockQuote (rev done ++ parse_lines lines inner)%list)
      :: parse_lines tail (PPara []).
Proof.
  intros pad Hpad sep Hsep. induction lines as [|l lines IH]; intros tail done inner.
  - cbn [map app].
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_close _ KBlank _ _ _ _ Hsep eq_refl eq_refl eq_refl)).
    rewrite pad_state_finish. reflexivity.
  - cbn [map app].
    destruct (step l inner) as [bs inner'] eqn:Es.
    assert (Esh : step_at (consumed (pad ++ "> " ++ l) l) l
                    (pad_state (String.length pad + 2) inner)
                  = (bs, pad_state (String.length pad + 2) inner')).
    { rewrite consumed_quote_prefix_pad.
      rewrite <- (Nat.add_0_r (String.length pad + 2)) at 1.
      rewrite step_at_shift, step_at_zero, Es. reflexivity. }
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _
                  (classify_canonical_quote_pad pad l Hpad) Esh)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

Lemma parse_lines_quote_cont_eof_pad :
  forall pad, is_blank pad = true ->
  forall lines done inner,
    parse_lines (map (fun l => pad ++ "> " ++ l)%string lines)
                (PQuote done (pad_state (String.length pad + 2) inner))
    = [mk (BlockQuote (rev done ++ parse_lines lines inner)%list)].
Proof.
  intros pad Hpad. induction lines as [|l lines IH]; intros done inner.
  - cbn [map parse_lines finish]. rewrite pad_state_finish. reflexivity.
  - cbn [map].
    destruct (step l inner) as [bs inner'] eqn:Es.
    assert (Esh : step_at (consumed (pad ++ "> " ++ l) l) l
                    (pad_state (String.length pad + 2) inner)
                  = (bs, pad_state (String.length pad + 2) inner')).
    { rewrite consumed_quote_prefix_pad.
      rewrite <- (Nat.add_0_r (String.length pad + 2)) at 1.
      rewrite step_at_shift, step_at_zero, Es. reflexivity. }
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _
                  (classify_canonical_quote_pad pad l Hpad) Esh)).
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
  cbn [app]. rewrite consumed_quote_prefix_pad.
  rewrite (parse_lines_quote_cont_pad pad Hpad sep Hsep), rev_involutive.
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
  cbn [app]. rewrite consumed_quote_prefix_pad.
  rewrite (parse_lines_quote_cont_eof_pad pad Hpad), rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.
(*
Running lines without finishing
-------------------------------
*)

(** Run a finite line prefix without applying [finish].  List proofs need
    the residual inner state at an item boundary; [parse_lines] deliberately
    hides it by finishing at end of input. *)
Fixpoint run_lines (lines : list string) (st : pstate) : blocks * pstate :=
  match lines with
  | [] => ([], st)
  | l :: rest =>
      let '(bs, st') := step l st in
      let '(more, st'') := run_lines rest st' in
      ((bs ++ more)%list, st'')
  end.

Lemma run_lines_app :
  forall xs ys st,
    run_lines (xs ++ ys)%list st =
      let '(bs, st') := run_lines xs st in
      let '(more, st'') := run_lines ys st' in
      ((bs ++ more)%list, st'').
Proof.
  induction xs as [|x xs IH]; intros ys st.
  - cbn [app run_lines]. destruct (run_lines ys st). reflexivity.
  -
  cbn [run_lines app]. destruct (step x st) as [head st1].
  rewrite (IH ys st1).
  destruct (run_lines xs st1) as [middle st2].
  destruct (run_lines ys st2) as [tail st3].
  rewrite app_assoc. reflexivity.
Qed.

Lemma run_lines_continue :
  forall xs ys st head middle tail final,
    run_lines xs st = (head, middle) ->
    run_lines ys middle = (tail, final) ->
    run_lines (xs ++ ys)%list st = ((head ++ tail)%list, final).
Proof.
  intros xs ys st head middle tail final Hxs Hys.
  rewrite run_lines_app, Hxs, Hys. reflexivity.
Qed.

Lemma parse_lines_run :
  forall lines st bs st',
    run_lines lines st = (bs, st') ->
    parse_lines lines st = (bs ++ finish st')%list.
Proof.
  induction lines as [|l lines IH]; intros st bs st' Hrun.
  - cbn [run_lines] in Hrun. inversion Hrun. reflexivity.
  - cbn [run_lines] in Hrun.
    destruct (step l st) as [head st1] eqn:Hstep.
    destruct (run_lines lines st1) as [rest st2] eqn:Hrest.
    inversion Hrun; subst bs st'.
    rewrite (parse_lines_step _ _ _ _ _ Hstep), (IH _ _ _ Hrest).
    rewrite app_assoc. reflexivity.
Qed.

Lemma parse_lines_app_run :
  forall xs ys st,
    parse_lines (xs ++ ys)%list st =
      let '(bs, st') := run_lines xs st in
      (bs ++ parse_lines ys st')%list.
Proof.
  induction xs as [|x xs IH]; intros ys st.
  - cbn [run_lines]. reflexivity.
  - cbn [app parse_lines].
    destruct (step x st) as [head st1] eqn:Hstep.
    rewrite (IH ys st1).
    cbn [run_lines]. rewrite Hstep.
    destruct (run_lines xs st1) as [rest st2].
    rewrite app_assoc. reflexivity.
Qed.

Lemma app_cons_app :
  forall {A : Type} (xs : list A) x ys tail,
    ((xs ++ (x :: ys)) ++ tail)%list =
    (xs ++ (x :: (ys ++ tail)))%list.
Proof.
  intros A xs x ys tail. induction xs as [|a xs IH];
    [reflexivity|cbn; rewrite IH; reflexivity].
Qed.

(*
Projecting a run to the list state
----------------------------------

`run_lines` on an open list carries a full `pstate`; only the outer
`list_state` matters for the tight/loose verdict.  `scan_list_content` is
that projection, defined directly on lines so it can be computed and
rewritten without unfolding the parser.  `run_lines_list_cont` is the
bridge: as long as the lines are all continuations, running them agrees
with scanning them.
*)

(** The tight/loose state changes made while an already-open canonical
    list consumes continuation lines. *)
Fixpoint scan_list_content (ls : list_state) (lines : list string) : list_state :=
  match lines with
  | [] => ls
  | l :: rest =>
      let ls' :=
        match classify l with
        | KBlank => list_blank ls
        | k => list_content ls k
        end in
      scan_list_content ls' rest
  end.

Lemma run_lines_list_cont :
  forall lines ls done inner bs inner',
    ls_indent ls = 0 ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) lines) inner =
      (bs, inner') ->
    run_lines (map (fun l => (bullet_cont ++ l)%string) lines)
      (PList ls done inner)
    = ([], PList (scan_list_content ls lines) (rev bs ++ done)%list inner').
Proof.
  induction lines as [|l lines IH]; intros ls done inner bs inner' Hind Hrun.
  - cbn [map run_lines] in Hrun |- *. inversion Hrun; subst. reflexivity.
  - cbn [map run_lines] in Hrun |- *.
    destruct (step (bullet_cont ++ l) inner) as [head inner1] eqn:Hstep.
    destruct (run_lines (map (fun l0 => bullet_cont ++ l0) lines) inner1)
      as [rest inner2] eqn:Hrest.
    inversion Hrun; subst bs inner'.
    destruct (classify l) as [| |f|q|lvl txt|m item|] eqn:Hclass.
    + rewrite (step_list_blank (bullet_cont ++ l) ls done inner head inner1).
      2: { rewrite classify_bullet_cont. exact Hclass. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass.
      rewrite (IH (list_blank ls) (rev head ++ done)%list inner1 rest inner2).
      * rewrite rev_app_distr, app_assoc. reflexivity.
      * cbn [list_blank]. exact Hind.
      * exact Hrest.
    + rewrite (step_list_indented (bullet_cont ++ l) KThematic ls done inner head inner1).
      2: { rewrite classify_bullet_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_bullet_cont. reflexivity. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass.
      rewrite (IH (list_content ls KThematic) (rev head ++ done)%list
                   inner1 rest inner2).
      * rewrite rev_app_distr, app_assoc. reflexivity.
      * cbn [list_content]. exact Hind.
      * exact Hrest.
    + rewrite (step_list_indented (bullet_cont ++ l) (KFence f) ls done inner head inner1).
      2: { rewrite classify_bullet_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_bullet_cont. reflexivity. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass.
      rewrite (IH (list_content ls (KFence f)) (rev head ++ done)%list
                   inner1 rest inner2) by (cbn [list_content]; assumption).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented (bullet_cont ++ l) (KQuote q) ls done inner head inner1).
      2: { rewrite classify_bullet_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_bullet_cont. reflexivity. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass.
      rewrite (IH (list_content ls (KQuote q)) (rev head ++ done)%list
                   inner1 rest inner2) by (cbn [list_content]; assumption).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented (bullet_cont ++ l) (KHeading lvl txt)
                 ls done inner head inner1).
      2: { rewrite classify_bullet_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_bullet_cont. reflexivity. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass.
      rewrite (IH (list_content ls (KHeading lvl txt)) (rev head ++ done)%list
                   inner1 rest inner2) by (cbn [list_content]; assumption).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented (bullet_cont ++ l) (KList m item)
                 ls done inner head inner1).
      2: { rewrite classify_bullet_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_bullet_cont. reflexivity. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass.
      rewrite (IH (list_content ls (KList m item)) (rev head ++ done)%list
                   inner1 rest inner2) by (cbn [list_content]; assumption).
      rewrite rev_app_distr, app_assoc. reflexivity.
    + rewrite (step_list_indented (bullet_cont ++ l) KText ls done inner head inner1).
      2: { rewrite classify_bullet_cont. exact Hclass. }
      2: discriminate.
      2: { rewrite Hind, indent_of_bullet_cont. reflexivity. }
      2: exact Hstep.
      cbn [scan_list_content]. rewrite Hclass.
      rewrite (IH (list_content ls KText) (rev head ++ done)%list
                   inner1 rest inner2) by (cbn [list_content]; assumption).
      rewrite rev_app_distr, app_assoc. reflexivity.
Qed.

(*
The scan's state algebra
------------------------
*)

Lemma scan_list_content_nonblank :
  forall lines ind marker loose items,
    forallb nonblank lines = true ->
    scan_list_content (LSt ind marker loose false items) lines
    = LSt ind marker loose false items.
Proof.
  induction lines as [|l lines IH]; intros ind marker loose items H;
    [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hl Hrest].
  cbn [scan_list_content].
  destruct (classify l) as [| |f|q|lvl txt|m rest|] eqn:Hclass.
  - apply classify_kblank_blank in Hclass. unfold nonblank in Hl.
    rewrite Hclass in Hl. discriminate.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
  - unfold list_content. apply IH. exact Hrest.
  - unfold list_content. rewrite Bool.orb_false_r. apply IH. exact Hrest.
Qed.

Lemma scan_list_content_loose :
  forall lines ind marker blanks items,
    ls_loose (scan_list_content (LSt ind marker true blanks items) lines) = true.
Proof.
  induction lines as [|l lines IH]; intros ind marker blanks items;
    [reflexivity|].
  cbn [scan_list_content]. destruct (classify l); apply IH.
Qed.

Lemma scan_list_content_app :
  forall xs ys ls,
    scan_list_content ls (xs ++ ys)%list =
    scan_list_content (scan_list_content ls xs) ys.
Proof.
  induction xs as [|x xs IH]; intros ys ls; [reflexivity|].
  cbn [app]. destruct (classify x) eqn:Hclass;
    cbn [scan_list_content]; apply IH.
Qed.

Lemma scan_list_content_fields :
  forall lines ls,
    ls_indent (scan_list_content ls lines) = ls_indent ls /\
    ls_marker (scan_list_content ls lines) = ls_marker ls /\
    ls_items (scan_list_content ls lines) = ls_items ls.
Proof.
  intros lines ls. split.
  - revert ls. induction lines as [|l lines IH]; intros ls; [reflexivity|].
    cbn [scan_list_content]. destruct (classify l);
      rewrite IH; destruct ls; reflexivity.
  - split.
    + revert ls. induction lines as [|l lines IH]; intros ls; [reflexivity|].
      cbn [scan_list_content]. destruct (classify l);
        rewrite IH; destruct ls; reflexivity.
    + revert ls. induction lines as [|l lines IH]; intros ls; [reflexivity|].
      cbn [scan_list_content]. destruct (classify l);
        rewrite IH; destruct ls; reflexivity.
Qed.

Lemma scan_list_content_loose_ext :
  forall lines ind marker loose blanks done,
    ls_loose (scan_list_content (LSt ind marker loose blanks done) lines) =
    ls_loose (scan_list_content (LSt 0 "-"%char loose blanks []) lines).
Proof.
  induction lines as [|l lines IH]; intros ind marker loose blanks done;
    [reflexivity|].
  cbn [scan_list_content]. destruct (classify l);
    cbn [list_blank list_content]; apply IH.
Qed.

Lemma scan_list_content_blanks_last :
  forall lines ls,
    lines <> [] -> nonblank (last lines EmptyString) = true ->
    ls_blanks (scan_list_content ls lines) = false.
Proof.
  induction lines as [|l lines IH]; intros ls Hne Hlast; [congruence|].
  destruct lines as [|l2 lines'].
  - cbn [last scan_list_content] in Hlast |- *.
    destruct (classify l) as [| |f|q|lvl txt|m item|] eqn:Hclass;
      cbn [list_blank list_content].
    all: try (apply classify_kblank_blank in Hclass; unfold nonblank in Hlast;
              rewrite Hclass in Hlast; discriminate).
    all: destruct ls; reflexivity.
  - cbn [last] in Hlast.
    change (ls_blanks
      (scan_list_content
        (match classify l with
         | KBlank => list_blank ls
         | k => list_content ls k
         end) (l2 :: lines')) = false).
    apply IH; [discriminate|exact Hlast].
Qed.

Lemma scan_list_content_after_blank :
  forall b rest ind marker items,
    classify b <> KBlank ->
    (forall m item, classify b <> KList m item) ->
    ls_loose
      (scan_list_content (list_blank (LSt ind marker false false items))
         (b :: rest)) = true.
Proof.
  intros b rest ind marker items Hblank Hlist.
  cbn [scan_list_content].
  destruct (classify b) as [| |f|q|lvl txt|m item|] eqn:Hclass.
  - exfalso. apply Hblank. reflexivity.
  - apply scan_list_content_loose.
  - apply scan_list_content_loose.
  - apply scan_list_content_loose.
  - apply scan_list_content_loose.
  - exfalso. apply (Hlist m item). reflexivity.
  - apply scan_list_content_loose.
Qed.

(*
Item and list layout
--------------------

Where a list's lines come from.  These are layout primitives rather than
renderer policy, and the uniformity theorems below are stated in terms of
them, so they live here and `Render.v` reuses them.
*)

(* A list item's lines: the marker (`bullet_open`, from Line.v) on the
   first line, two spaces of plain indent (`bullet_cont`) on every line
   after — not repeated per line like quote_line, since bullet_cont is
   whitespace and Line.classify_ws_prefix carries every recognizer
   through it for free. *)
Definition indent_lines (first_prefix rest_prefix : string) (ls : list string)
  : list string :=
  match ls with
  | [] => []
  | l :: rest => (first_prefix ++ l) :: map (fun x => rest_prefix ++ x) rest
  end.

(* Items separated by a blank line when the list is loose, concatenated
   directly when tight — the rendering choice `cb_ok`'s spacing condition
   has to match back up with. *)
Fixpoint list_lines (sp : list_spacing) (lss : list (list string))
  : list string :=
  match lss with
  | [] => []
  | [ls] => ls
  | ls :: rest =>
      (ls ++ (match sp with Loose => [EmptyString] | Tight => [] end)
       ++ list_lines sp rest)%list
  end.

(*
List-item uniformity
--------------------

The list analogue of `quote_uniformity`: an item's contents parse
exactly as they would at top level.  Two differences from the quote
case, and both are real rather than artefacts of the proof.

A quote repeats its prefix on every line, so the parser re-derives the
descent line by line.  An item's continuation is plain whitespace, so
the descent is a *column shift* instead: `step_pad_shift` is that
statement for one line, `run_lines_pad_shift` for a run.  The shift is
what makes nesting free -- a list opened inside an item records a column
two further right, and nothing else changes.

The tight/loose bit is the one thing that is *not* uniform, and
`lines_loose` is where it lives.  It is a scan of the lines, not a
function of the parsed tree: a blank line loosens the enclosing list
unless the next non-blank line opens a list.  A renderer-side predicate
that reads the block tree cannot express this, because the tree does not
record where the blanks sit relative to the markers.
*)

(* Padding is a shift of the state, not a no-op.  Stating it as a shift
   rather than as an equality is what makes it hold for an item whose
   content opens a list, where the pad genuinely moves a recorded
   column. *)
Lemma pad_safe_pad_state :
  forall k st, pad_safe (pad_state k st) = pad_safe st.
Proof.
  intros k st. induction st as [| | |done inner IH|ls done inner IH];
    cbn [pad_state pad_safe]; try reflexivity. exact IH.
Qed.

Lemma step_pad_shift :
  forall p l st,
    is_blank p = true -> pad_safe st = true ->
    step (p ++ l) (pad_state (String.length p) st)
    = (fst (step l st), pad_state (String.length p) (snd (step l st))).
Proof.
  intros p l st Hp Hsafe.
  rewrite (step_pad p l (pad_state (String.length p) st) Hp)
    by (rewrite pad_safe_pad_state; exact Hsafe).
  rewrite <- (Nat.add_0_r (String.length p)) at 1.
  rewrite step_at_shift, step_at_zero. reflexivity.
Qed.

(* `pad_safe` along a whole run.  This is the theorem's only side
   condition beyond the marker line, and it says exactly "no fence is
   open directly inside the item" -- fence content is verbatim, so a pad
   in front of it is not a shift. *)
Fixpoint run_pad_safe (lines : list string) (st : pstate) : bool :=
  match lines with
  | [] => pad_safe st
  | l :: rest => (pad_safe st && run_pad_safe rest (snd (step l st)))%bool
  end.

Lemma run_lines_pad_shift :
  forall p lines st,
    is_blank p = true ->
    run_pad_safe lines st = true ->
    run_lines (map (fun l => (p ++ l)%string) lines) (pad_state (String.length p) st)
    = (fst (run_lines lines st), pad_state (String.length p) (snd (run_lines lines st))).
Proof.
  intros p lines. induction lines as [|l rest IH]; intros st Hp Hsafe.
  - reflexivity.
  - cbn [map run_lines] in *.
    apply andb_prop in Hsafe as [Hnow Hlater].
    rewrite (step_pad_shift p l st Hp Hnow).
    destruct (step l st) as [bs st'] eqn:Es. cbn [fst snd] in *.
    rewrite (IH st' Hp Hlater).
    destruct (run_lines rest st') as [more st''] eqn:Er. reflexivity.
Qed.

(* And from the idle state the shift is *invisible*: `pad_state` moves
   columns, `finish` reads none, and the emitted blocks are untouched.  So
   a blank pad in front of every line of a run changes nothing at all,
   whatever the run opens -- a nested list included.  `run_pad_safe` is
   the whole side condition. *)
Lemma run_lines_pad_invisible :
  forall p L,
    is_blank p = true ->
    run_pad_safe L (PPara []) = true ->
    run_lines (map (fun l => (p ++ l)%string) L) (PPara [])
    = (fst (run_lines L (PPara [])),
       pad_state (String.length p) (snd (run_lines L (PPara [])))).
Proof.
  intros p L Hp Hsafe. exact (run_lines_pad_shift p L (PPara []) Hp Hsafe).
Qed.

Lemma parse_lines_pad_invisible :
  forall p L,
    is_blank p = true ->
    run_pad_safe L (PPara []) = true ->
    parse_lines (map (fun l => (p ++ l)%string) L) (PPara [])
    = parse_lines L (PPara []).
Proof.
  intros p L Hp Hsafe.
  rewrite (parse_lines_run _ _ _ _ (run_lines_pad_invisible p L Hp Hsafe)).
  rewrite pad_state_finish.
  symmetry. apply parse_lines_run, surjective_pairing.
Qed.

Lemma consumed_bullet_open : forall l, consumed (bullet_open ++ l) l = 2.
Proof.
  intros l. unfold consumed, bullet_open. rewrite length_append.
  cbn [String.length]. lia.
Qed.

(* The marker line, with the item's residue parsed at column 2. *)
Lemma step_item_open :
  forall l0,
    is_thematic (bullet_open ++ l0) = false ->
    step (bullet_open ++ l0) (PPara [])
    = ([], PList (LSt 0 "-"%char false false [])
            (rev (fst (step l0 (PPara []))))
            (pad_state 2 (snd (step l0 (PPara []))))).
Proof.
  intros l0 Hth.
  destruct (step l0 (PPara [])) as [bs inner] eqn:Es. cbn [fst snd].
  rewrite (step_list_open _ _ _ _ _ (classify_bullet_open l0 Hth) Es).
  rewrite indent_of_bullet_open, consumed_bullet_open. reflexivity.
Qed.

(** The tight/loose verdict, read off the lines.  A blank arms the flag;
    a line that opens a list spends it without loosening (djot.js's
    `+list` exemption); anything else spends it and loosens. *)
Fixpoint lines_loose (loose gap : bool) (ls : list string) : bool :=
  match ls with
  | [] => loose
  | l :: rest =>
      match classify l with
      | KBlank => lines_loose loose true rest
      | KList _ _ => lines_loose loose false rest
      | _ => lines_loose (loose || gap)%bool false rest
      end
  end.

(* A nonblank first line contributes nothing: it cannot arm the flag, and
   with nothing armed it cannot spend one either.  So the verdict for an
   item's lines is the verdict for its continuation lines, which is the
   form `list_uniformity` states and the renderer consumes. *)
Lemma lines_loose_cons_nonblank :
  forall a rest,
    classify a <> KBlank ->
    lines_loose false false (a :: rest) = lines_loose false false rest.
Proof.
  intros a rest H. cbn [lines_loose].
  destruct (classify a) eqn:E; try reflexivity. congruence.
Qed.

Lemma scan_loose_eq :
  forall lines ls,
    ls_loose (scan_list_content ls lines)
    = lines_loose (ls_loose ls) (ls_blanks ls) lines.
Proof.
  induction lines as [|l rest IH]; intros ls; [reflexivity|].
  cbn [scan_list_content lines_loose].
  destruct (classify l) eqn:E; rewrite IH; reflexivity.
Qed.

Lemma scan_items_eq :
  forall lines ls, ls_items (scan_list_content ls lines) = ls_items ls.
Proof.
  induction lines as [|l rest IH]; intros ls; [reflexivity|].
  cbn [scan_list_content]. destruct (classify l) eqn:E; rewrite IH; reflexivity.
Qed.

(* The scan's state in closed form, once no blank is left armed.  The
   canonical setting always ends an item on a nonblank line, so this is
   the form every use wants. *)
Lemma scan_shape :
  forall lines ls,
    ls_blanks (scan_list_content ls lines) = false ->
    scan_list_content ls lines
    = LSt (ls_indent ls) (ls_marker ls)
          (lines_loose (ls_loose ls) (ls_blanks ls) lines) false (ls_items ls).
Proof.
  intros lines ls Hb.
  pose proof (scan_list_content_fields lines ls) as [Hi [Hm Hit]].
  pose proof (scan_loose_eq lines ls) as Hlo.
  destruct (scan_list_content ls lines) as [i m lo b its].
  cbn in Hi, Hm, Hit, Hb, Hlo. subst. reflexivity.
Qed.

(* One item's lines, run from idle: the marker opens the list and the
   continuation lines land in it, shifted two columns. *)
Lemma run_item_open :
  forall l0 rest,
    is_thematic (bullet_open ++ l0) = false ->
    run_pad_safe rest (snd (step l0 (PPara []))) = true ->
    ls_blanks (scan_list_content (LSt 0 "-"%char false false []) rest) = false ->
    run_lines (indent_lines bullet_open bullet_cont (l0 :: rest)) (PPara [])
    = ([], PList (LSt 0 "-"%char (lines_loose false false rest) false [])
            (rev (fst (run_lines (l0 :: rest) (PPara []))))
            (pad_state 2 (snd (run_lines (l0 :: rest) (PPara []))))).
Proof.
  intros l0 rest Hth Hsafe Hb.
  cbn [indent_lines run_lines].
  rewrite (step_item_open l0 Hth).
  pose proof (run_lines_pad_shift bullet_cont rest (snd (step l0 (PPara [])))
                eq_refl Hsafe) as Hrun.
  change (String.length bullet_cont) with 2 in Hrun.
  rewrite (run_lines_list_cont rest (LSt 0 "-"%char false false [])
             (rev (fst (step l0 (PPara [])))) _ _ _ eq_refl Hrun).
  rewrite (scan_shape rest _ Hb).
  cbn [ls_indent ls_marker ls_loose ls_blanks ls_items].
  cbn [run_lines].
  destruct (step l0 (PPara [])) as [b i] eqn:Es. cbn [fst snd].
  destruct (run_lines rest i) as [more i'] eqn:Er. cbn [fst snd app].
  rewrite rev_app_distr. reflexivity.
Qed.

(* The same, for an item that is not the first: the marker closes the
   item in progress instead of opening the list. *)
Lemma run_item_sibling :
  forall l0 rest ls done inner,
    ls_indent ls = 0 ->
    ls_marker ls = "-"%char ->
    is_thematic (bullet_open ++ l0) = false ->
    run_pad_safe rest (snd (step l0 (PPara []))) = true ->
    run_lines (indent_lines bullet_open bullet_cont (l0 :: rest)) (PList ls done inner)
    = ([], PList (scan_list_content
                    (list_next ls (rev done ++ finish inner)%list l0) rest)
            (rev (fst (run_lines (l0 :: rest) (PPara []))))
            (pad_state 2 (snd (run_lines (l0 :: rest) (PPara []))))).
Proof.
  intros l0 rest ls done inner Hind Hmark Hth Hsafe.
  cbn [indent_lines run_lines].
  destruct (step l0 (PPara [])) as [b i] eqn:Es.
  rewrite (step_list_sibling _ _ _ _ _ _ _ _
             (classify_bullet_open l0 Hth)
             (ltac:(rewrite Hmark; apply Ascii.eqb_refl))
             (ltac:(rewrite Hind, indent_of_bullet_open; reflexivity))
             Es).
  rewrite consumed_bullet_open.
  pose proof (run_lines_pad_shift bullet_cont rest i eq_refl) as Hrun.
  cbn [snd] in Hsafe. specialize (Hrun Hsafe).
  change (String.length bullet_cont) with 2 in Hrun.
  assert (Hi0 : ls_indent (list_next ls (rev done ++ finish inner)%list l0) = 0).
  { unfold list_next. destruct (is_blank l0); exact Hind. }
  rewrite (run_lines_list_cont rest (list_next ls (rev done ++ finish inner)%list l0)
             (rev b) (pad_state 2 i) _ _ Hi0 Hrun).
  destruct (run_lines rest i) as [more i'] eqn:Er. cbn [fst snd app].
  rewrite rev_app_distr. reflexivity.
Qed.

(* `lines_loose` only ever accumulates with `||`, so the incoming verdict
   factors out.  This is what lets an item's contribution be read off its
   own lines, independent of what the items before it decided. *)
Lemma lines_loose_or :
  forall L lo g, lines_loose lo g L = (lo || lines_loose false g L)%bool.
Proof.
  induction L as [|l rest IH]; intros lo g.
  - cbn [lines_loose]. rewrite orb_false_r. reflexivity.
  - cbn [lines_loose]. destruct (classify l); try apply IH.
    all: cbn [orb]; rewrite (IH (lo || g)%bool false), (IH g false);
         destruct lo, g; reflexivity.
Qed.

(* A blank line closes what `finish` would have closed, and emits it.
   The exception is a list, which a blank does not close -- there the
   equation holds one level down instead, which is the induction.  A
   fence is the one state where it fails, and `pad_safe` excludes it. *)
Lemma step_blank_finish :
  forall l st, classify l = KBlank -> pad_safe st = true ->
    (fst (step l st) ++ finish (snd (step l st)))%list = finish st.
Proof.
  intros l st Hl. induction st as [cur|lvl cur|f acc|done inner IH|ls done inner IH];
    intros Hsafe.
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hl eq_refl). cbn [open_kind fst snd finish app].
      reflexivity.
    + rewrite (step_para_flush l c cur' Hl). reflexivity.
  - rewrite (step_heading_close l lvl cur Hl). reflexivity.
  - discriminate Hsafe.
  - rewrite (step_quote_close l KBlank done inner _ _ Hl eq_refl eq_refl
               (surjective_pairing _)).
    cbn [fst snd open_kind finish app]. reflexivity.
  - cbn [pad_safe] in Hsafe.
    rewrite (step_list_blank l ls done inner _ _ Hl (surjective_pairing _)).
    cbn [fst snd finish app list_blank ls_loose ls_items].
    rewrite rev_app_distr, rev_involutive, <- app_assoc, (IH Hsafe).
    reflexivity.
Qed.

(* A blank line leaves no state a later text line could continue lazily.
   `step_list_close` needs this to route the line that closes a list. *)
Lemma step_blank_lazy_false :
  forall l st, classify l = KBlank -> lazy_ok (snd (step l st)) = false.
Proof.
  intros l st Hblank. induction st as
    [cur|lvl cur|f acc|done inner IH|ls done inner IH].
  - destruct cur as [|c cur'].
    + rewrite (step_idle l KBlank Hblank eq_refl). reflexivity.
    + rewrite (step_para_flush l c cur' Hblank). reflexivity.
  - unfold step. cbn [step_fuel]. rewrite Hblank. reflexivity.
  - destruct (fence_close f l) eqn:Hclose.
    + rewrite (step_fence_close l f acc Hclose). reflexivity.
    + rewrite (step_fence_content l f acc Hclose). reflexivity.
  - rewrite (step_quote_close l KBlank done inner [] (PPara [])
      Hblank eq_refl eq_refl eq_refl). reflexivity.
  - destruct (step l inner) as [bs inner'] eqn:Hstep.
    rewrite (step_list_blank l ls done inner bs inner' Hblank Hstep).
    cbn [snd lazy_ok]. exact IH.
Qed.

Lemma run_pad_safe_final :
  forall L st, run_pad_safe L st = true -> pad_safe (snd (run_lines L st)) = true.
Proof.
  induction L as [|l rest IH]; intros st H; [exact H|].
  cbn [run_pad_safe] in H. apply andb_prop in H as [_ Hlater].
  cbn [run_lines]. destruct (step l st) as [bs st'] eqn:Es.
  cbn [snd] in Hlater.
  specialize (IH st' Hlater). destruct (run_lines rest st') as [more st''] eqn:Er.
  cbn [snd] in IH |- *. exact IH.
Qed.

(* The list's lines after its first item: each remaining item contributes
   the inter-item separator and then its own indented lines. *)
Definition item_sep (sp : list_spacing) : list string :=
  match sp with Loose => [EmptyString] | Tight => [] end.

Fixpoint list_tail_lines (sp : list_spacing) (itemss : list (list string)) : list string :=
  match itemss with
  | [] => []
  | L :: rest => (item_sep sp ++ indent_lines bullet_open bullet_cont L
                  ++ list_tail_lines sp rest)%list
  end.

Lemma list_lines_cons2 :
  forall sp x xs, xs <> [] ->
    list_lines sp (x :: xs) = (x ++ item_sep sp ++ list_lines sp xs)%list.
Proof. intros sp x xs H. destruct xs; [congruence|reflexivity]. Qed.

Lemma list_lines_cons :
  forall sp L rest,
    list_lines sp (map (indent_lines bullet_open bullet_cont) (L :: rest))
    = (indent_lines bullet_open bullet_cont L ++ list_tail_lines sp rest)%list.
Proof.
  intros sp L rest. revert L. induction rest as [|y r IH]; intros L.
  - cbn [map list_lines list_tail_lines]. rewrite app_nil_r. reflexivity.
  - assert (Hne : map (indent_lines bullet_open bullet_cont) (y :: r) <> []).
    { cbn [map]. intros HH. discriminate HH. }
    change (map (indent_lines bullet_open bullet_cont) (L :: y :: r))
      with (indent_lines bullet_open bullet_cont L
            :: map (indent_lines bullet_open bullet_cont) (y :: r)).
    rewrite (list_lines_cons2 sp _ _ Hne), (IH y).
    cbn [list_tail_lines]. rewrite !app_assoc. reflexivity.
Qed.

(*
Uniformity for the whole list
-----------------------------

One statement over a list of items, and it is what removes the mutual
dependency between the roundtrip's block layer and its list layer: it
mentions no `cblock` and no acceptance predicate, only line lists, so
nothing about the canonical form has to be known to state or prove it.
One proof, every construct -- including a nested list, which is why it
subsumes the per-depth list reasoning.

The spacing is the only part that is not a plain map.  It is Loose when
some item's own lines force it, or when the rendering separates items by
a blank at all -- which needs two items, since a one-item list emits no
separator.
*)

(* What an item's lines must satisfy: the marker line does not form a
   thematic break, the item does not start blank, no fence is left open
   inside it, and it does not end blank. *)
Definition item_ok (L : list string) : bool :=
  match L with
  | [] => false
  | l0 :: more =>
      (negb (is_thematic (bullet_open ++ l0))
       && nonblank l0
       && run_pad_safe more (snd (step l0 (PPara [])))
       && match more with [] => true | _ => nonblank (last more EmptyString) end)%bool
  end.

(* The verdict contributed by the items after the first.  Each of them is
   preceded by a separator, so on a loose rendering each one loosens. *)
Definition list_loose_of (sp : list_spacing) (itemss : list (list string)) : bool :=
  (existsb (fun L => lines_loose false false L) itemss
   || match sp with
      | Loose => negb (Nat.eqb (List.length itemss) 0)
      | Tight => false
      end)%bool.

(* `post` and `out` are what follows the list in the input and in the
   output: the lemmas below say nothing about how the list ends, so one
   induction serves both endings (end of input, and a blank plus a line
   that closes the list).  Instantiated at the two `list_uniformity`
   corollaries. *)
Lemma parse_item_and_tail :
  forall sp l0 more rest post out ls done inner,
    ls_indent ls = 0 -> ls_marker ls = "-"%char ->
    item_ok (l0 :: more) = true ->
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> ls_marker ls2 = "-"%char -> ls_blanks ls2 = false ->
       pad_safe inner2 = true ->
       parse_lines (list_tail_lines sp rest ++ post)%list (PList ls2 done2 inner2)
       = mk (BulletList (if (ls_loose ls2 || list_loose_of sp rest)%bool then Loose else Tight)
                (rev (ls_items ls2) ++ (rev done2 ++ finish inner2)%list
                 :: map (fun L => parse_lines L (PPara [])) rest)) :: out) ->
    parse_lines (indent_lines bullet_open bullet_cont (l0 :: more)
                 ++ (list_tail_lines sp rest ++ post))%list (PList ls done inner)
    = mk (BulletList
             (if ((ls_loose ls || ls_blanks ls)
                  || lines_loose false false (l0 :: more)
                  || list_loose_of sp rest)%bool then Loose else Tight)
             (rev (ls_items ls) ++ (rev done ++ finish inner)%list
              :: parse_lines (l0 :: more) (PPara [])
              :: map (fun L => parse_lines L (PPara [])) rest)) :: out.
Proof.
  intros sp l0 more rest post out ls done inner Hind Hmark Hok IH.
  cbn [item_ok] in Hok.
  apply andb_prop in Hok as [Hok Hlast].
  apply andb_prop in Hok as [Hok Hsafe].
  apply andb_prop in Hok as [Hth Hnb].
  apply negb_true_iff in Hth.
  assert (Hnb' : is_blank l0 = false).
  { unfold nonblank in Hnb. apply negb_true_iff in Hnb. exact Hnb. }
  assert (Hcl : classify l0 <> KBlank).
  { intros E. apply classify_kblank_blank in E. rewrite E in Hnb'. discriminate. }
  rewrite parse_lines_app_run.
  rewrite (run_item_sibling l0 more ls done inner Hind Hmark Hth Hsafe).
  cbn [fst snd app].
  set (item := (rev done ++ finish inner)%list).
  set (ls1 := scan_list_content (list_next ls item l0) more).
  set (R := run_lines (l0 :: more) (PPara [])).
  pose proof (scan_list_content_fields more (list_next ls item l0)) as [Hf1 [Hf2 Hf3]].
  assert (Hitems : ls_items ls1 = item :: ls_items ls).
  { unfold ls1. rewrite Hf3. unfold list_next. rewrite Hnb'. reflexivity. }
  assert (Hind1 : ls_indent ls1 = 0).
  { unfold ls1. rewrite Hf1. unfold list_next. destruct (is_blank l0); exact Hind. }
  assert (Hmark1 : ls_marker ls1 = "-"%char).
  { unfold ls1. rewrite Hf2. unfold list_next. destruct (is_blank l0); exact Hmark. }
  assert (Hblanks1 : ls_blanks ls1 = false).
  { unfold ls1. destruct more as [|m ms].
    - cbn [scan_list_content]. unfold list_next. rewrite Hnb'. reflexivity.
    - apply (scan_list_content_blanks_last (m :: ms) _ ltac:(discriminate) Hlast). }
  assert (Hpad1 : pad_safe (pad_state 2 (snd R)) = true).
  { rewrite pad_safe_pad_state. unfold R. apply run_pad_safe_final.
    cbn [run_pad_safe pad_safe]. exact Hsafe. }
  assert (Hloose1 : ls_loose ls1
                    = ((ls_loose ls || ls_blanks ls)
                       || lines_loose false false (l0 :: more))%bool).
  { unfold ls1. rewrite scan_loose_eq. unfold list_next. rewrite Hnb'.
    cbn [ls_loose ls_blanks].
    rewrite lines_loose_or, (lines_loose_cons_nonblank l0 more Hcl). reflexivity. }
  assert (Hdone1 : (rev (rev (fst R)) ++ finish (pad_state 2 (snd R)))%list
                   = parse_lines (l0 :: more) (PPara [])).
  { rewrite rev_involutive, pad_state_finish. unfold R.
    symmetry. apply parse_lines_run, surjective_pairing. }
  rewrite (IH ls1 (rev (fst R)) (pad_state 2 (snd R)) Hind1 Hmark1 Hblanks1 Hpad1).
  rewrite Hitems, Hloose1, Hdone1.
  cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

(* `Hclose` is the whole of what the ending contributes: from any list
   state the parser has reached, `post` emits that list and then whatever
   `out` is.  Both endings satisfy it -- `parse_lines_nil` for end of
   input, `parse_list_close` for a closing line. *)
Lemma parse_list_tail :
  forall sp itemss post out ls done inner,
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> pad_safe inner2 = true ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    ls_indent ls = 0 -> ls_marker ls = "-"%char -> ls_blanks ls = false ->
    pad_safe inner = true ->
    forallb item_ok itemss = true ->
    parse_lines (list_tail_lines sp itemss ++ post)%list (PList ls done inner)
    = mk (BulletList (if (ls_loose ls || list_loose_of sp itemss)%bool then Loose else Tight)
             (rev (ls_items ls) ++ (rev done ++ finish inner)%list
              :: map (fun L => parse_lines L (PPara [])) itemss)) :: out.
Proof.
  intros sp itemss. induction itemss as [|L rest IH];
    intros post out ls done inner Hclose Hind Hmark Hblanks Hpad Hok.
  - cbn [list_tail_lines app map]. rewrite (Hclose ls done inner Hind Hpad).
    cbn [finish rev app].
    unfold list_loose_of. cbn [existsb List.length Nat.eqb negb].
    destruct sp; rewrite ?orb_false_r; reflexivity.
  - destruct L as [|l0 more]; [cbn [forallb item_ok] in Hok; discriminate|].
    cbn [forallb] in Hok. apply andb_prop in Hok as [HL Hrest].
    cbn [list_tail_lines]. rewrite <- !app_assoc. destruct sp.
    + cbn [item_sep app].
      rewrite (parse_item_and_tail Tight l0 more rest post out ls done inner
                 Hind Hmark HL
                 (fun a b c H1 H2 H3 H4 => IH post out a b c Hclose H1 H2 H3 H4 Hrest)).
      rewrite Hblanks. unfold list_loose_of. cbn [existsb List.length orb].
      rewrite ?orb_false_r.
      destruct (ls_loose ls), (lines_loose false false (l0 :: more)),
               (existsb (fun L => lines_loose false false L) rest); reflexivity.
    + change (item_sep Loose ++ (indent_lines bullet_open bullet_cont (l0 :: more)
                                 ++ (list_tail_lines Loose rest ++ post)))%list
        with (EmptyString :: (indent_lines bullet_open bullet_cont (l0 :: more)
                              ++ (list_tail_lines Loose rest ++ post)))%list.
      rewrite (parse_lines_step _ _ _ _ _
                 (step_list_blank EmptyString ls done inner _ _
                    (classify_blank EmptyString eq_refl) (surjective_pairing _))).
      cbn [app].
      rewrite (parse_item_and_tail Loose l0 more rest post out (list_blank ls)
                 (rev (fst (step EmptyString inner)) ++ done)%list
                 (snd (step EmptyString inner))
                 Hind Hmark HL
                 (fun a b c H1 H2 H3 H4 => IH post out a b c Hclose H1 H2 H3 H4 Hrest)).
      cbn [list_blank ls_loose ls_blanks ls_items].
      rewrite rev_app_distr, rev_involutive, <- app_assoc.
      rewrite (step_blank_finish EmptyString inner (classify_blank EmptyString eq_refl) Hpad).
      unfold list_loose_of. cbn [existsb List.length Nat.eqb negb].
      destruct (ls_loose ls), (lines_loose false false (l0 :: more)),
               (existsb (fun L => lines_loose false false L) rest); reflexivity.
Qed.

(* What closes a list: not the blank line -- that only records a gap --
   but the line after it, once that line is not blank, not a sibling
   marker, and not indented into the item.  The list is emitted whole and
   the parser restarts on that line from idle. *)
Lemma parse_list_close :
  forall ls done inner next tail,
    pad_safe inner = true ->
    classify next <> KBlank ->
    (forall m item, classify next <> KList m item) ->
    Nat.ltb (ls_indent ls) (indent_of next) = false ->
    parse_lines (EmptyString :: next :: tail) (PList ls done inner)
    = (finish (PList ls done inner) ++ parse_lines (next :: tail) (PPara []))%list.
Proof.
  intros ls done inner next tail Hpad Hnb Hnl Hind.
  destruct (step EmptyString inner) as [bs inner'] eqn:Hb.
  rewrite (parse_lines_step _ _ _ _ _
             (step_list_blank EmptyString ls done inner bs inner'
                (classify_blank EmptyString eq_refl) Hb)).
  cbn [app].
  assert (Hfin : finish (PList (list_blank ls) (rev bs ++ done)%list inner')
                 = finish (PList ls done inner)).
  { pose proof (step_blank_finish EmptyString (PList ls done inner)
                  (classify_blank EmptyString eq_refl) Hpad) as H.
    rewrite (step_list_blank EmptyString ls done inner bs inner'
               (classify_blank EmptyString eq_refl) Hb) in H.
    cbn [fst snd app] in H. exact H. }
  assert (Hlazy : lazy_ok inner' = false).
  { pose proof (step_blank_lazy_false EmptyString inner
                  (classify_blank EmptyString eq_refl)) as H.
    rewrite Hb in H. cbn [snd] in H. exact H. }
  assert (Hind' : Nat.ltb (ls_indent (list_blank ls)) (indent_of next) = false)
    by exact Hind.
  (* the four kinds that open directly; the quote and list kinds do not *)
  assert (Hdirect : forall k,
            classify next = k -> direct_open k = true -> k <> KBlank ->
            is_lazy k inner' = false ->
            parse_lines (next :: tail)
              (PList (list_blank ls) (rev bs ++ done)%list inner')
            = (finish (PList ls done inner)
               ++ parse_lines (next :: tail) (PPara []))%list).
  { intros k Hclass Hk Hkb Hkl.
    rewrite (parse_lines_step _ _ _ _ _
               (step_list_close next k (list_blank ls) (rev bs ++ done)%list
                  inner' _ _ Hclass Hk Hkb Hind' Hkl (surjective_pairing _))).
    rewrite (parse_lines_step _ _ _ _ _
               (eq_trans (step_idle next k Hclass Hk) (surjective_pairing _))).
    rewrite Hfin, <- app_assoc. reflexivity. }
  destruct (classify next) as [| |f|q|lvl txt|m listrest|] eqn:Hclass.
  - congruence.
  - apply (Hdirect KThematic eq_refl eq_refl ltac:(discriminate) eq_refl).
  - apply (Hdirect (KFence f) eq_refl eq_refl ltac:(discriminate) eq_refl).
  - rewrite (parse_lines_step _ _ _ _ _
               (step_list_quote_close next q (list_blank ls) (rev bs ++ done)%list
                  inner' _ _ Hclass Hind' (surjective_pairing _))).
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_open next q _ _ Hclass (surjective_pairing _))).
    rewrite Hfin. reflexivity.
  - apply (Hdirect (KHeading lvl txt) eq_refl eq_refl ltac:(discriminate) eq_refl).
  - exfalso. apply (Hnl m listrest). reflexivity.
  - apply (Hdirect KText eq_refl eq_refl ltac:(discriminate) Hlazy).
Qed.

(** The list's spacing, read off its items' lines.  Loose when an item
    forces it, or when the rendering puts a blank between items -- which
    a one-item list never does, so a `Loose` single item renders and
    parses back as `Tight`. *)
Definition list_spacing_of (sp : list_spacing) (itemss : list (list string)) : list_spacing :=
  if (existsb (fun L => lines_loose false false L) itemss
      || match sp with
         | Loose => negb (Nat.eqb (List.length itemss) 1)
         | Tight => false
         end)%bool
  then Loose else Tight.

(** Uniformity for a bullet list: every item's contents parse exactly as
    they would at top level, and the list's spacing is a scan of those
    same lines.  Stated over line lists, so it says nothing about the
    canonical form and needs nothing from it.

    The general form leaves the ending open (see `parse_list_tail`); the
    two corollaries below are the endings that occur. *)
Theorem list_uniformity_gen :
  forall sp itemss post out,
    (forall ls2 done2 inner2,
       ls_indent ls2 = 0 -> pad_safe inner2 = true ->
       parse_lines post (PList ls2 done2 inner2)
       = (finish (PList ls2 done2 inner2) ++ out)%list) ->
    itemss <> [] ->
    forallb item_ok itemss = true ->
    parse_lines (list_lines sp (map (indent_lines bullet_open bullet_cont) itemss)
                 ++ post)%list (PPara [])
    = mk (BulletList (list_spacing_of sp itemss)
             (map (fun L => parse_lines L (PPara [])) itemss)) :: out.
Proof.
  intros sp itemss post out Hclose Hne Hok.
  destruct itemss as [|L tail]; [congruence|].
  destruct L as [|l0 more]; [cbn [forallb item_ok] in Hok; discriminate|].
  cbn [forallb] in Hok. apply andb_prop in Hok as [HL Htail].
  pose proof HL as HL'. cbn [item_ok] in HL'.
  apply andb_prop in HL' as [HL' Hlast].
  apply andb_prop in HL' as [HL' Hsafe].
  apply andb_prop in HL' as [Hth Hnb].
  apply negb_true_iff in Hth.
  assert (Hnb' : is_blank l0 = false).
  { unfold nonblank in Hnb. apply negb_true_iff in Hnb. exact Hnb. }
  assert (Hcl : classify l0 <> KBlank).
  { intros E. apply classify_kblank_blank in E. rewrite E in Hnb'. discriminate. }
  assert (Hb : ls_blanks (scan_list_content (LSt 0 "-"%char false false []) more) = false).
  { destruct more as [|m ms]; [reflexivity|].
    apply (scan_list_content_blanks_last (m :: ms) _ ltac:(discriminate) Hlast). }
  rewrite list_lines_cons, <- app_assoc, parse_lines_app_run.
  rewrite (run_item_open l0 more Hth Hsafe Hb). cbn [fst snd app].
  assert (Hpad1 : pad_safe (pad_state 2 (snd (run_lines (l0 :: more) (PPara [])))) = true).
  { rewrite pad_safe_pad_state. apply run_pad_safe_final.
    cbn [run_pad_safe pad_safe]. exact Hsafe. }
  rewrite (parse_list_tail sp tail post out
             (LSt 0 "-"%char (lines_loose false false more) false [])
             (rev (fst (run_lines (l0 :: more) (PPara []))))
             (pad_state 2 (snd (run_lines (l0 :: more) (PPara []))))
             Hclose eq_refl eq_refl eq_refl Hpad1 Htail).
  cbn [ls_loose ls_items rev app].
  rewrite rev_involutive, pad_state_finish.
  rewrite <- (parse_lines_run (l0 :: more) (PPara []) _ _ (surjective_pairing _)).
  unfold list_spacing_of, list_loose_of.
  cbn [existsb List.length map].
  rewrite (lines_loose_cons_nonblank l0 more Hcl).
  destruct sp; cbn [Nat.eqb negb orb];
    destruct (lines_loose false false more),
             (existsb (fun L => lines_loose false false L) tail),
             tail; reflexivity.
Qed.

(** The list ends the input. *)
Theorem list_uniformity :
  forall sp itemss,
    itemss <> [] ->
    forallb item_ok itemss = true ->
    parse_lines (list_lines sp (map (indent_lines bullet_open bullet_cont) itemss))
                (PPara [])
    = [mk (BulletList (list_spacing_of sp itemss)
             (map (fun L => parse_lines L (PPara [])) itemss))].
Proof.
  intros sp itemss Hne Hok.
  rewrite <- (app_nil_r (list_lines sp (map (indent_lines bullet_open bullet_cont) itemss))).
  apply list_uniformity_gen; [| exact Hne | exact Hok].
  intros ls2 done2 inner2 _ _. rewrite parse_lines_nil, app_nil_r. reflexivity.
Qed.

(** A blank line and then a line that closes the list: the list is
    emitted and everything after it parses from idle. *)
Theorem list_uniformity_tail :
  forall sp itemss next tail,
    itemss <> [] ->
    forallb item_ok itemss = true ->
    classify next <> KBlank ->
    (forall m item, classify next <> KList m item) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map (indent_lines bullet_open bullet_cont) itemss)
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = mk (BulletList (list_spacing_of sp itemss)
             (map (fun L => parse_lines L (PPara [])) itemss))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros sp itemss next tail Hne Hok Hnb Hnl Hindent.
  apply list_uniformity_gen; [| exact Hne | exact Hok].
  intros ls2 done2 inner2 Hind2 Hpad2.
  apply parse_list_close; try assumption.
  rewrite Hind2, Hindent. reflexivity.
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
