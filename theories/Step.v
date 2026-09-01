(* ai-disclosure: autonomous *)

(** * Block parsing as an incremental fold

   Block parsing is a fold over classified lines with an explicit state.

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

   The equation lemmas are the interface the wf and roundtrip proofs
   use; those for the fold live in `Uniformity.v`, the per-branch ones
   for `step` at the bottom of this file.  Keep both in sync with the
   definition. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast Attributes Marker Inline.
Import ListNotations.

Local Open Scope string_scope.

(** ** Block settings

What the block layer is configurable in.  Today that is seven questions:
may a list marker close an open paragraph rather than extend it, may an
underline turn that paragraph into a heading, are pipe tables enabled, may an
open ATX heading consume another source line, are fenced divs enabled, are task
markers semantic, and do `=format` fences produce raw blocks? Djot answers no
to the first two and yes to the remaining five.

Its inline counterpart is `Inline.dconfig`, which is a genuine table --
a row per delimiter -- and carries a side condition that admissible
tables have to satisfy.  The first two decisions' single overlap is checked
separately by `Invariants.block_prefix_ok`; keeping the class computational
avoids threading a proof through the parser.
*)
Class bconfig : Type := BConfig {
  (* May a list marker close an open paragraph?  Asked of the marker's
     own fields, so the answer can depend on the numeral and on nothing
     else. *)
  bmarker_interrupts : list lstyle -> string -> option task_marker -> string -> bool;
  (* May a run of `n` copies of `c`, alone on a line, close an open
     paragraph and turn it into a heading?  `Some k` means a heading of
     level `S k`, so a setting cannot ask for a level-0 heading and
     `wf_block`'s `1 <= lvl` needs no side condition to hold. *)
  bunderline : ascii -> nat -> option nat;
  (* Does a classified pipe row open a djot table?  When false the complete
     source line is ordinary paragraph text. *)
  btables : bool;
  (* May an open ATX heading consume a same-level heading line or a lazy text
     line?  Djot says yes; the Markdown-facing profile uses one source line
     per heading. *)
  bheading_continues : bool
  ; (* Are fenced div containers enabled?  When false their complete opener
       spelling is ordinary paragraph text. *)
  bdivs : bool;
  (* Are task markers semantic task-list items?  When false they remain
     ordinary bullet items whose content starts with the preserved box. *)
  btasks : bool
  ; (* Does an info string beginning with `=` make a raw block?  When false
       the same fence is an ordinary code block whose language retains `=`. *)
  braw_blocks : bool
  ; (* Is a `:` marker's list a definition list?  When false the same lines
       are an ordinary bullet list whose items keep their colon markers, so
       the term/definition split is what goes away and nothing else. *)
  bdeflists : bool
  ; (* Does a `{...}` line open a block attribute spec?  When false the
       complete spelling is ordinary paragraph text, and a spec spanning
       several lines is the paragraph those lines make. *)
  battrs : bool
  ; (* Does a `[^label]:` line open a footnote definition?  Half of one
       capability: the other half is `dconfig`'s `dc_footnotes`, and
       `Profile.with_footnotes` is what moves the two together. *)
  bfootnotes : bool
}.

(*
The settings themselves
-----------------------

Named separately from the records that hold them, so that a
configuration reads as a choice per question rather than as a tuple.
*)

(* djot's answers. *)
Definition no_interrupt (_ : list lstyle) (_ : string)
  (_ : option task_marker) (_ : string) : bool := false.
Definition no_underline (_ : ascii) (_ : nat) : option nat := None.

(* A marker interrupts when it cannot be the tail of ordinary prose: a
   bullet, whose core is empty, or the numeral `1`.  Excluding every
   other numeral is what keeps `The civil war ended in` / `1865. And
   this should not start a list.` one paragraph -- djot's own regression
   test for the rule this setting relaxes, and the only corpus case an
   unrestricted answer gets wrong. *)
Definition prose_safe_markers (_ : list lstyle) (core : string)
  (_ : option task_marker) (_ : string) : bool :=
  match core with
  | EmptyString => true
  | _ => String.eqb core "1"
  end.

(* Setext underlines: `=` at any length, `-` at two or more.  The length
   condition on `-` is not a style choice -- a lone `-` is a bullet
   marker, so admitting it would make one line answer to two settings at
   once, and which won would depend on the order `step` tests them in. *)
Definition setext_underline (c : ascii) (n : nat) : option nat :=
  if Ascii.eqb c "=" then Some 0
  else if Ascii.eqb c "-" then (if Nat.leb 2 n then Some 1 else None)
  else None.

#[export] Instance djot_bconfig : bconfig :=
  BConfig no_interrupt no_underline true true true true true true true
    true.

(* Field-local block knobs.  Each preserves the other decisions, which is what
   lets independently justified settings compose without rebuilding a record
   by hand. *)
Definition with_marker_interrupts
  (f : list lstyle -> string -> option task_marker -> string -> bool)
  (K : bconfig) : bconfig :=
  BConfig f (@bunderline K) (@btables K) (@bheading_continues K) (@bdivs K)
    (@btasks K) (@braw_blocks K) (@bdeflists K) (@battrs K)
    (@bfootnotes K).

Definition with_underline
  (f : ascii -> nat -> option nat) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) f (@btables K) (@bheading_continues K)
    (@bdivs K) (@btasks K) (@braw_blocks K) (@bdeflists K) (@battrs K)
    (@bfootnotes K).

Definition with_tables (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) enabled
    (@bheading_continues K) (@bdivs K) (@btasks K) (@braw_blocks K)
    (@bdeflists K) (@battrs K) (@bfootnotes K).

Definition with_heading_continuation (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K) enabled
    (@bdivs K) (@btasks K) (@braw_blocks K) (@bdeflists K) (@battrs K)
    (@bfootnotes K).

Definition with_divs (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) enabled (@btasks K) (@braw_blocks K)
    (@bdeflists K) (@battrs K) (@bfootnotes K).

Definition with_tasks (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) (@bdivs K) enabled (@braw_blocks K)
    (@bdeflists K) (@battrs K) (@bfootnotes K).

Definition with_raw_blocks (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) (@bdivs K) (@btasks K) enabled (@bdeflists K)
    (@battrs K) (@bfootnotes K).

Definition with_deflists (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) (@bdivs K) (@btasks K) (@braw_blocks K) enabled
    (@battrs K) (@bfootnotes K).

Definition with_block_attrs (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) (@bdivs K) (@btasks K) (@braw_blocks K)
    (@bdeflists K) enabled (@bfootnotes K).

(* Exported, but the profile-level `with_footnotes` is what a caller
   should reach for: a reference the document cannot define, or a
   definition nothing can reference, is not a setting anyone wants. *)
Definition with_block_footnotes (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) (@bdivs K) (@btasks K) (@braw_blocks K)
    (@bdeflists K) (@battrs K) enabled.

(* Other settings, deliberately not `Instance`s: they are named where wanted
   (for example, in `check/Sublist.v`) so inference here always means Djot's.

   A marker interrupts when it cannot be the tail of ordinary prose: a
   bullet, whose core is empty, or the numeral `1`.  Excluding every
   other numeral is what keeps `The civil war ended in` / `1865. And
   this should not start a list.` one paragraph -- djot's own regression
   test for the rule this knob relaxes, and the only corpus case the
   unrestricted knob gets wrong. *)
Definition sublist_bconfig : bconfig :=
  with_marker_interrupts prose_safe_markers djot_bconfig.
Definition setext_bconfig : bconfig :=
  with_underline setext_underline djot_bconfig.

(* The block half of the Markdown-facing profile.  Apply the field-local
   knobs rather than spelling a record so adding another independent block
   setting has one composition point. Core CommonMark has no tables. *)
Definition markdown_bconfig : bconfig :=
  with_block_attrs false
   (with_deflists false
    (with_raw_blocks false
     (with_tasks false
      (with_divs false
       (with_heading_continuation false
         (with_tables false
           (with_underline setext_underline
             (with_marker_interrupts prose_safe_markers djot_bconfig)))))))).

(* Classification remains profile-independent.  This projection is the
   construct-creation gate: disabling tasks changes only a recognized task
   marker into the bullet marker and literal item prefix it came from. *)
Definition configured_list_styles `{bconfig}
  (sty : list lstyle) (chk : option task_marker) : list lstyle :=
  if btasks then sty else
  match sty, chk with
  | [STask c], Some _ => [SBullet c]
  | _, _ => sty
  end.

Definition configured_list_check `{bconfig}
  (chk : option task_marker) : task_status :=
  if btasks then
    match chk with Some m => tm_status m | None => Incomplete end
  else Incomplete.

Definition configured_list_rest `{bconfig}
  (chk : option task_marker) (rest : string) : string :=
  if btasks then rest else
  match chk with
  | Some m => task_marker_source m ++ rest
  | None => rest
  end.

Lemma configured_list_rest_length `{bconfig} :
  forall l sty core chk rest,
    classify l = KList sty core chk rest ->
    String.length (configured_list_rest chk rest) < String.length l.
Proof.
  intros l sty core chk rest E. unfold configured_list_rest.
  destruct btasks; [exact (classify_list_length _ _ _ _ _ E)|].
  exact (classify_list_literal_length _ _ _ _ _ E).
Qed.

(* Which line kinds close an open paragraph instead of extending it.
   The setting's *type* is what says only a list marker may: every other
   kind answers `false` definitionally, so a lemma about a text line
   pays nothing and needs no class law to say so. *)
Definition binterrupt `{bconfig} (k : line_kind) : bool :=
  match k with
  | KList sty core chk rest =>
      bmarker_interrupts (configured_list_styles sty chk) core
        (if btasks then chk else None) (configured_list_rest chk rest)
  | _ => false
  end.

(* The level an underline gives an open paragraph, if it gives it one. *)
Definition bunderline_of `{bconfig} (l : string) : option nat :=
  match underline_of l with
  | Some (c, n) => bunderline c n
  | None => None
  end.

Lemma bunderline_of_blank `{bconfig} :
  forall l, is_blank l = true -> bunderline_of l = None.
Proof.
  intros l Hb. unfold bunderline_of. rewrite (underline_of_blank l Hb).
  reflexivity.
Qed.

Lemma bunderline_of_ws_prefix `{bconfig} :
  forall p l, is_blank p = true -> bunderline_of (p ++ l) = bunderline_of l.
Proof.
  intros p l Hp. unfold bunderline_of.
  rewrite (underline_of_ws_prefix p l Hp). reflexivity.
Qed.

(* Whether a line takes an open paragraph away from itself, either way.
   This is the one query the paragraph branch of `step` and the
   canonical `para_ok` both ask, so a third setting that ends a
   paragraph extends this and nothing else. *)
Definition bcuts `{bconfig} (l : string) : bool :=
  match bunderline_of l with
  | Some _ => true
  | None => binterrupt (classify l)
  end.

(* The delimiter table this file is read at.  Implicit, so nothing below
   mentions it: what it buys is that the statements quantify over the
   family rather than over djot's spelling. *)
Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(* Paragraph assembly is `Inline.para_inlines`. *)

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
  | String "="%char fmt =>
      if braw_blocks then mk (RawBlock fmt text)
      else mk (CodeBlock (String "="%char fmt) text)
  | info => mk (CodeBlock info text)
  end.

(*
Table assembly
==============

A row line contributes a `trow` and nothing else (`Line.table_row`);
head/align assignment happens here, over the rows a table has
collected, because a separator marks the row *before* it.  djot.js does
the same at `-row` (parse.ts:987-1014): a separator sets the table's
aligns for every following row and, if the table already has a row,
turns that row into a header at the aligns it just read.  So the target
is the *last* row built, which two consecutive separators both claim.
*)

(* A cell's alignment is its column's, positionally, defaulting past the
   end of the separator: a row wider than the separator gets
   `AlignDefault` for the excess (`tables.test:60`). *)
Fixpoint cells_of (ct : cell_type) (aligns : list align) (cs : list string)
  : list cell :=
  match cs with
  | [] => []
  | c :: cs' =>
      match aligns with
      | [] => Cell ct AlignDefault (parse_inline_line c) :: cells_of ct [] cs'
      | a :: als => Cell ct a (parse_inline_line c) :: cells_of ct als cs'
      end
  end.

(* The retroactive half: a row already built, re-read as a header at the
   separator's aligns.  Its inlines are kept rather than reparsed --
   nothing about a cell's content depends on which kind of cell it is. *)
Fixpoint head_of (aligns : list align) (r : list cell) : list cell :=
  match r with
  | [] => []
  | Cell _ _ ils :: r' =>
      match aligns with
      | [] => Cell HeadCell AlignDefault ils :: head_of [] r'
      | a :: als => Cell HeadCell a ils :: head_of als r'
      end
  end.

(* `acc` is the rows built so far, reversed, so its head is the row a
   separator promotes. *)
Fixpoint table_fold (rows : list trow) (aligns : list align)
  (acc : list (list cell)) : list (list cell) :=
  match rows with
  | [] => rev acc
  | TSep als :: rest =>
      table_fold rest als
        (match acc with [] => [] | r :: acc' => head_of als r :: acc' end)
  | TCells cs :: rest =>
      table_fold rest aligns (cells_of BodyCell aligns cs :: acc)
  end.

(* What a table has seen after its rows.  `TOpen` is still taking rows;
   `TAfterBlank` has seen a blank, which ends the rows but not the table,
   because a caption may still follow across any number of blanks; and
   `TCaption` is accumulating a caption's lines, reversed, exactly as a
   paragraph accumulator does.

   The blank is what makes the third state necessary rather than
   optional.  djot.js closes the table at the blank and merges the
   caption into it afterwards, reaching backward past a container that
   has already been reified (parse.ts:1048-1069).  Nothing here can reach
   backward -- `step` emits blocks upward -- so the table waits instead,
   and the two are the same function.  What waiting must not change is
   list tightness: `blank_absorbed` stays `false` for a table, so the
   blank arms the enclosing list exactly as it does today, which is what
   djot.js's own `blankline` event does. *)
Inductive tcap : Type :=
  | TOpen
  | TAfterBlank
  | TCaption (lines : list string).

(* The caption's lines, for the state invariant: they are a paragraph
   accumulator and carry its condition. *)
Definition cap_lines (c : tcap) : list string :=
  match c with TCaption ls => ls | _ => [] end.

(* An empty caption is no caption: `^ ` with nothing after it opens one
   with no content, and djot.js renders that as no caption at all, so
   `Some []` would be a second spelling of `None` -- which is what
   `wf_block` rules out. *)
Definition caption_of (c : tcap) : option inlines :=
  match c with
  | TOpen | TAfterBlank => None
  | TCaption [] => None
  | TCaption ls => Some (para_inlines (rev ls))
  end.

(* A table of separators alone has no rows at all, which is a table djot
   renders as `<table>\n</table>` (`tables.test:97`). *)
Definition table_block (rows : list trow) (c : tcap) : node block :=
  mk (Table (caption_of c) (table_fold rows [] [])).

(*
The line fold
=============
*)

(* A list, mid-parse.  `ls_indent` is the column its markers sit at:
   continuation is "indented past the marker", djot.js's `this.indent >
   container.extra.indent`.  Note what that rule does *not* mention —
   the marker's width.  A list records no column but this one, and the
   parser never consults how wide a marker was.

   `ls_styles` is the candidate style set, which siblings narrow by
   intersection (`narrow`); an empty intersection ends the list.  Each
   candidate is paired with the start number the *first* item's marker
   yields under it, because that decoding is style-dependent: `i.` is 1
   read as roman and 9 read as alpha, and which one it is may not be
   settled until a later sibling narrows the set.  djot.js keeps the two
   apart — `extra.styles` and `firstMarker`, combined at close by
   `getListStart` (parse.ts:823) — but pairing them at open says the
   same thing without carrying the marker text, and makes narrowing a
   plain filter that cannot disturb the number.

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
  ; ls_styles : list (lstyle * nat)
  ; ls_loose : bool
  ; ls_blanks : bool
  ; ls_items : list blocks      (* finished items, reversed *)
  (* The checkbox of the item still open, and of the ones already
     closed -- parallel to `done`/`inner` and to `ls_items`, and pushed
     with them in `list_next`, so the two lists pair up by construction.
     A list whose style is not a task style carries `Incomplete`
     everywhere and nothing reads it, which is djot.js's `checkbox: null`
     on every list-item container.  Kept beside `ls_items` rather than
     inside it because `ls_items`'s element type is what twenty proofs in
     `ListUniformity.v` manipulate. *)
  ; ls_check : task_status
  ; ls_checks : list task_status }.

(* The fold's state: a container stack.  Every accumulator holds its
   items in *reverse* order, hence the `rev` at each use site. *)
Inductive pstate : Type :=
  | PPara (cur : list string)              (* [] = no open block *)
  | PHeading (level : nat) (cur : list string)
  (* An open code fence: the closer it wants, the *absolute* column its
     opening backticks sit at, and the content lines it has taken.  The
     column is what makes the content independent of how deep the fence
     is nested: djot.js removes exactly `tip.indent` characters of
     leading whitespace from each line (block.ts:1081-1086), so a fence
     opened at column 2 inside a list item stores `code`, not `  code`.
     Like every other column in this state it is absolute, `off +
     indent_of l` -- see `open_attr`. *)
  | PFence (f : fence) (ind : nat) (acc : list string)
  | PQuote (done : blocks) (inner : pstate)
  (* An open fenced div: the fence length it must be closed by, its
     class, and the contents so far.  Unlike a quote it removes no
     prefix and shifts no column — its whole continuation rule is the
     `div_close` test, which is why it needs none of the pad layer. *)
  | PDiv (len : nat) (cls : string) (done : blocks) (inner : pstate)
  (* done/inner are the *current item*'s state, exactly as for a quote;
     ls_items holds the items already closed. *)
  | PList (ls : list_state) (done : blocks) (inner : pstate)
  (* An open block attribute spec.  `pend` is what earlier consecutive
     specs already contributed, `ind` the opener's indentation — a
     continuation line has to be indented past it — `ap` the character
     machine, and `slices` the lines eaten so far, reversed.  The slices
     are kept because a spec that turns out not to parse becomes an
     ordinary paragraph of exactly those lines (djot.js block.ts:585-596),
     which is the only reason this state is not just an `attr`. *)
  | PAttr (pend : attr) (ind : nat) (ap : aparser) (slices : list string)
  (* An open reference definition: the column its bracket sits at, its
     label, and the destination so far.  Like `PAttr`'s the column is
     absolute (`off + indent_of l`), because a continuation line is one
     indented past it and the two ways of reaching a nested line have to
     record the same number (`step_fuel_shift`, `step_fuel_pad`).  Unlike
     `PAttr` this state keeps no source lines: a definition that stops
     being continued is complete, never retracted. *)
  | PRef (ind : nat) (lbl : string) (val : string)
  (* A footnote definition is a block container.  `done` and `inner`
     have the same source-order convention as quotes and divs; `ind` is
     the opener's absolute column and governs later continuation lines. *)
  | PFoot (ind : nat) (lbl : string) (done : blocks) (inner : pstate)
  (* An open table: the row lines it has taken, reversed.  It records no
     column, unlike every other container that spans lines: a row's
     content is what is left of the line after the container prefixes,
     and nothing in it is measured against the column the first bar sat
     at.  So this is the state that costs `step_fuel_shift` and
     `step_fuel_pad` nothing. *)
  | PTable (rows : list trow) (cap : tcap)
  (* Attributes looking for the block they decorate.  djot.js keeps them
     in a document-wide `blockAttributes` and attaches them when the next
     container *opens* (parse.ts:183); here a container is reified only
     when it closes, so they ride along until it emits.  `inner` is idle
     exactly while they are still unclaimed, which is what makes "a blank
     line drops them" a test on `inner` rather than a separate state. *)
  | PPend (pend : attr) (inner : pstate).

(* Container nesting depth.  Half of the parser's termination measure:
   a quote descent shortens the line, but a list descent hands the line
   to the inner container unchanged and shortens *this* instead. *)
Fixpoint pstate_depth (st : pstate) : nat :=
  match st with
  | PPara _ | PHeading _ _ | PFence _ _ _ => 0
  | PQuote _ inner => S (pstate_depth inner)
  | PDiv _ _ _ inner => S (pstate_depth inner)
  | PList _ _ inner => S (pstate_depth inner)
  (* PAttr resolves to `PPend _ (PPara [])`, depth 1, on the same line, so
     it has to sit above that. *)
  | PAttr _ _ _ _ => 2
  (* PRef reprocesses the line that ends it against `PPara []`, depth 0.
     PTable ends the same way. *)
  | PRef _ _ _ | PTable _ _ => 1
  | PFoot _ _ _ inner => S (pstate_depth inner)
  | PPend _ inner => S (pstate_depth inner)
  end.

(* Is nothing open here?  `PPara []` is the idle state, and the only one:
   every other constructor has a block or a container in flight. *)
Definition is_idle (st : pstate) : bool :=
  match st with PPara [] => true | _ => false end.

(* End of input (or of an enclosing container): close everything still
   open, outermost result first. *)
(* A heading's text lines become its inlines exactly as a paragraph's do
   — same assembly, different wrapper. *)
Definition heading_block (lvl : nat) (cur : list string) : node block :=
  mk (Heading lvl (para_inlines (rev cur))).

(* A div's class becomes a `class` attribute on the node, as in djot.js
   (block.ts:670-672); a classless div carries no attributes at all, so
   the canonical case stays `mk`-wrapped and proofs compute through it. *)
Definition div_block (cls : string) (bs : blocks) : node block :=
  if String.eqb cls EmptyString
  then mk (Div bs)
  else Node NoPos [("class", cls)] (Div bs).

(* The block a list closes to, read off the candidate set its state
   carries.  Stated on the *set* rather than on a marker because the set
   is what `list_block` matches on, and because siblings narrow it: a
   list whose first marker is ambiguous closes to a block that marker
   alone does not determine.

   It lives here rather than beside the markers because of its one
   configured arm: the colon needs `bdeflists`, and the section variable
   is what keeps that argument implicit at its twenty-odd call sites in
   the uniformity chain. *)
Definition styles_list (S : list (lstyle * nat)) (sp : list_spacing)
                       (items : list blocks) : node block :=
  match S with
  | (SOrd n d, start) :: _ => mk (OrderedList (OLAttrs n d start) sp items)
  (* The colon is the definition-list style, and this is the only place
     it differs from a bullet: djot.js's `-list` picks the node from the
     same style set (parse.ts:824), and `def_items` is the split its
     `-list_item` runs.  Spelled as a test on the character rather than
     as a pattern so that a proof holding an unknown bullet can case on
     it in one step.

     With definition lists off the split is what goes away: the items are
     the same items, their markers are still colons, and the list is the
     bullet list any other marker would have made. *)
  | (SBullet c, _) :: _ =>
      if (Ascii.eqb c ":" && bdeflists)%bool
      then mk (DefinitionList sp (def_items items))
      else mk (BulletList sp items)
  (* The state-free form cannot construct a task list because statuses are
     per item.  [styles_list_checked] below is the uniformity result used for
     that style; this fallback keeps the older projection total. *)
  | _ => mk (BulletList sp items)
  end.

(* The state-aware form used by list uniformity.  Non-task styles ignore the
   parallel status list; task styles pair it with the item blocks exactly as
   [list_block] does at close. *)
Definition styles_list_checked (S : list (lstyle * nat)) (sp : list_spacing)
    (checks : list task_status) (items : list blocks) : node block :=
  match S with
  | (STask _, _) :: _ => mk (TaskList sp (task_items checks items))
  | _ => styles_list S sp items
  end.

(* The same at a marker whose set no sibling narrows.  Bullets give a
   `BulletList` definitionally, so instantiating the uniformity chain at
   `bullet` still reads as it did; an ordered marker gives the
   `OrderedList` its style and start. *)
Definition marker_list (m : marker) (sp : list_spacing) (items : list blocks)
  : node block := styles_list (mk_styles m) sp items.

Definition marker_list_checked (m : marker) (sp : list_spacing)
    (checks : list task_status) (items : list blocks) : node block :=
  styles_list_checked (mk_styles m) sp checks items.

(* The colon's own instance, which is the whole of the capability: with
   definition lists on it is the split, and the generic uniformity chain
   reaches `ck_block LKDef` through this one rewrite. *)
Lemma marker_list_checked_colon :
  forall sp checks items,
    bdeflists = true ->
    marker_list_checked colon sp checks items
    = mk (DefinitionList sp (def_items items)).
Proof.
  intros sp checks items H.
  unfold marker_list_checked, styles_list_checked, styles_list, colon,
    mk_styles, with_starts, mk_sty.
  cbn [map fst snd]. rewrite H. reflexivity.
Qed.

(* The list a `PList` closes to.  djot.js takes the first surviving
   candidate -- "take first if ambiguous", parse.ts:817 -- which is why
   `styles_of_core` lists the roman reading before the alpha one.  The
   empty case is unreachable: `open_list` is only reached from a `KList`,
   whose style set `list_marker` has already found nonempty, and
   `narrow` replaces the set only when the result is nonempty. *)
Definition list_block (ls : list_state) (last : blocks) : node block :=
  styles_list_checked (ls_styles ls)
    (if ls_loose ls then Loose else Tight)
    (rev (ls_check ls :: ls_checks ls))
    (rev (last :: ls_items ls)).

(* The block a reference definition closes to.  It carries no HTML of its
   own — `Html.v` renders it as nothing, as djot.js does, which keeps it a
   block only for the roundtrip's sake — and `Document.v` reads the pair
   off it into the document's reference map. *)
Definition ref_block (lbl val : string) : node block := mk (RefDef lbl val).

Definition foot_block (lbl : string) (bs : blocks) : node block :=
  mk (FootnoteDef lbl bs).

(* A continuation line's contribution: one whitespace-free run, whitespace
   stripped, and nothing else on the line (djot.js block.ts:308-313).  A
   blank line is excluded by `nonempty_str`, which is what closes an open
   definition at a paragraph break. *)
Definition ref_cont (l : string) : option string :=
  let t := drop_leading_ws l in
  if (nonempty_str t && no_ws t)%bool then Some t else None.

(* A blank line is never a continuation: it has no run to contribute.
   This is what closes an open definition at a paragraph break, and what
   keeps `PRef` inside `pad_safe` where `PAttr` is not. *)
Lemma ref_cont_blank : forall l, is_blank l = true -> ref_cont l = None.
Proof.
  intros l H. unfold ref_cont. rewrite (drop_leading_ws_blank l H). reflexivity.
Qed.

Lemma ref_cont_no_ws : forall l t, ref_cont l = Some t -> no_ws t = true.
Proof.
  intros l t H. unfold ref_cont in H.
  destruct (nonempty_str (drop_leading_ws l) && no_ws (drop_leading_ws l))%bool
    eqn:E; [|discriminate].
  injection H as <-. apply andb_true_iff in E as [_ E]. exact E.
Qed.

Fixpoint finish (st : pstate) : blocks :=
  match st with
  | PPara [] => []
  | PPara cur => [mk (Para (para_inlines (rev cur)))]
  | PHeading lvl cur => [heading_block lvl cur]
  | PFence f _ acc => [fence_block f (rev acc)]
  | PTable rows cap => [table_block (rev rows) cap]
  | PQuote done inner => [mk (BlockQuote (rev done ++ finish inner)%list)]
  | PDiv _ cls done inner => [div_block cls (rev done ++ finish inner)%list]
  | PList ls done inner =>
      [list_block ls (rev done ++ finish inner)%list]
  (* A spec still wanting continuation lines never was one: its lines are
     a paragraph.  A finished spec with no block after it contributes
     nothing, which is `{#id}` alone in a document. *)
  | PAttr _ _ ap slices =>
      if ap_done ap then []
      else match slices with
           | [] => []
           | _ => [mk (Para (para_inlines (rev slices)))]
           end
  | PRef _ lbl val => [ref_block lbl val]
  | PFoot _ lbl done inner =>
      [foot_block lbl (rev done ++ finish inner)%list]
  | PPend pend inner => decorate_head pend (finish inner)
  end.

(* `list_block`'s match, resolved for a bullet.  The uniformity chain
   works over a canonical rendering, where the style set is a bullet
   singleton, and this is the one place that set is looked at. *)
(* Stated on the candidate *set* the state carries, not on a marker: a
   list whose first marker is ambiguous closes to a block that marker
   alone does not name, because siblings narrow the set.  The marker form
   below is the instance where nothing narrows. *)
Lemma list_block_styles :
  forall S ls last,
    ls_styles ls = S ->
    list_block ls last
    = styles_list_checked S (if ls_loose ls then Loose else Tight)
        (rev (ls_check ls :: ls_checks ls)) (rev (last :: ls_items ls)).
Proof.
  intros S ls last H. unfold list_block. rewrite H. reflexivity.
Qed.

Lemma list_block_marker :
  forall m ls last,
    ls_styles ls = mk_styles m ->
    list_block ls last
    = marker_list_checked m (if ls_loose ls then Loose else Tight)
        (rev (ls_check ls :: ls_checks ls)) (rev (last :: ls_items ls)).
Proof.
  intros m ls last H. unfold marker_list_checked.
  rewrite (list_block_styles (mk_styles m) ls last H).
  reflexivity.
Qed.

Lemma finish_list_styles :
  forall S ls done inner,
    ls_styles ls = S ->
    finish (PList ls done inner)
    = [styles_list_checked S (if ls_loose ls then Loose else Tight)
         (rev (ls_check ls :: ls_checks ls))
         (rev ((rev done ++ finish inner)%list :: ls_items ls))].
Proof.
  intros S ls done inner H. cbn [finish].
  rewrite (list_block_styles S ls _ H). reflexivity.
Qed.

Lemma finish_list_marker :
  forall m ls done inner,
    ls_styles ls = mk_styles m ->
    finish (PList ls done inner)
    = [marker_list_checked m (if ls_loose ls then Loose else Tight)
         (rev (ls_check ls :: ls_checks ls))
         (rev ((rev done ++ finish inner)%list :: ls_items ls))].
Proof.
  intros m ls done inner H. unfold marker_list_checked.
  apply (finish_list_styles _ _ _ _ H).
Qed.

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
  | PFence _ _ _ => false
  | PQuote _ inner => lazy_ok inner
  | PDiv _ _ _ inner => lazy_ok inner
  | PList _ _ inner => lazy_ok inner
  | PAttr _ _ _ _ => false     (* a spec is not a paragraph, however it ends *)
  | PRef _ _ _ => false        (* nor is a reference definition *)
  | PTable _ _ => false        (* nor is a table: a lazy line ends it *)
  | PFoot _ _ _ inner => lazy_ok inner
  | PPend _ inner => lazy_ok inner
  end.

(* djot.js's `this.tip()`: the innermost open container.  Nothing can be
   nested inside a code block, so "the tip is a code block" is exactly
   "a fence is open anywhere down the spine".  `fenced_div`'s `continue`
   consults it before testing for its own closer (block.ts:635-638,
   issue #109), so a `:::` line that is code stays code. *)
Fixpoint in_fence (st : pstate) : bool :=
  match st with
  | PFence _ _ _ => true
  | PQuote _ inner | PDiv _ _ _ inner | PList _ _ inner
  | PFoot _ _ _ inner | PPend _ inner => in_fence inner
  | PPara _ | PHeading _ _ | PAttr _ _ _ _ | PRef _ _ _
  | PTable _ _ => false
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
  | PFence f ind acc => PFence f ind acc   (* excluded by lazy_ok *)
  | PQuote done inner => PQuote done (feed_lazy l inner)
  | PDiv len cls done inner => PDiv len cls done (feed_lazy l inner)
  | PList ls done inner => PList ls done (feed_lazy l inner)
  | PFoot ind lbl done inner => PFoot ind lbl done (feed_lazy l inner)
  | PAttr _ _ _ _ | PRef _ _ _ | PTable _ _ => st   (* excluded by lazy_ok *)
  | PPend pend inner => PPend pend (feed_lazy l inner)
  end.

(* A heading's text, pushed onto its accumulator.  `# ` with nothing
   after it opens a heading with no text rather than a blank line of it,
   which is what keeps the accumulator's nonblank invariant. *)
Definition push_text (rest : string) (cur : list string) : list string :=
  if is_blank rest then cur else drop_leading_ws rest :: cur.

(* What a line opens, for every kind but KQuote — a quote has to parse
   the line it encloses, which is the parser's one recursion, so it stays
   inside `step_fuel`.  The split is deliberate: every equation lemma
   downstream is stated over `open_kind`, which is exactly why fuel
   appears in no lemma statement anywhere in the development. *)
Definition open_kind `{bconfig} (l : string) (k : line_kind) : blocks * pstate :=
  match k with
  | KBlank => ([], PPara [])
  | KThematic => ([mk ThematicBreak], PPara [])
  | KFence _ => ([], PPara [])        (* unreachable: see open_fence *)
  | KHeading lvl rest => ([], PHeading lvl (push_text rest []))
  | KDiv len cls =>
      if bdivs then ([], PDiv len cls [] (PPara []))
      else ([], PPara [drop_leading_ws l])
  | KText => ([], PPara [drop_leading_ws l])
  | KQuote _ => ([], PPara [])        (* unreachable: see open_quote *)
  | KList _ _ _ _ => ([], PPara [])     (* unreachable: see open_list *)
  | KAttr _ => ([], PPara [])         (* unreachable: see open_attr *)
  | KFoot _ _ => ([], PPara [])       (* unreachable: see open_foot *)
  | KRef _ _ => ([], PPara [])        (* unreachable: see open_ref *)
  (* A table needs no column and no descent, so unlike every other
     container it opens here rather than in a wrapper of its own.  A profile
     that disables tables keeps the complete row spelling as paragraph text. *)
  | KRow r =>
      if btables then ([], PTable [r] TOpen)
      else ([], PPara [drop_leading_ws l])
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

(* The result of a line handed down through pending block attributes.
   Nothing emitted means the block they are waiting for is still open, so
   they wait; the first block emitted is that block, and they attach to
   it and are gone. *)
Definition pend_result (pend : attr) (r : blocks * pstate) : blocks * pstate :=
  let (bs, st') := r in
  match bs with
  | [] => ([], PPend pend st')
  | _ => (decorate_head pend bs, st')
  end.

(* A quote prefix opens a fresh quote around whatever its enclosed line
   parsed to. *)
Definition open_quote (descended : blocks * pstate) : blocks * pstate :=
  let (bs, inner) := descended in ([], PQuote (rev bs) inner).

(* An attribute spec opens its container at the column its brace sits
   at.  Like a list's `ls_indent` this is an *absolute* column, `off +
   indent_of l`, not a line-local one: continuation lines are tested
   against it, and the two ways of reaching a nested line — moving the
   offset, or padding the line — have to record the same number
   (`step_fuel_shift`, `step_fuel_pad`).  That is also why it is not part
   of `open_kind`, which never sees the offset. *)
(* With block attributes off the spec never opens, so `PAttr` is
   unreachable and the line is the paragraph text its own spelling makes.
   The pending attribute is dropped with it, which is sound because
   nothing can be pending: the only source of one is a `PAttr` that
   closed. *)
Definition open_attr (pend : attr) (ind : nat) (ap : aparser) (l : string)
  : blocks * pstate :=
  if battrs then ([], PAttr pend ind ap [drop_leading_ws l])
  else ([], PPara [drop_leading_ws l]).

(* Neither setting closes anything, which is what the two step equations
   below need in order to be stated without a case split. *)
Lemma open_attr_fst :
  forall pend ind ap l, fst (open_attr pend ind ap l) = [].
Proof. intros. unfold open_attr. destruct battrs; reflexivity. Qed.

(* And so closing into a spec emits exactly what the closed state does. *)
Lemma close_reopen_attr :
  forall st pend ind ap l,
    close_reopen st (open_attr pend ind ap l)
    = (finish st, snd (open_attr pend ind ap l)).
Proof.
  intros. unfold close_reopen, open_attr. destruct battrs; cbn [snd];
    rewrite app_nil_r; reflexivity.
Qed.

(* A code fence opens at the column its border sits at, and for the same
   reason as `open_attr` is not part of `open_kind`: the column is
   absolute and `open_kind` never sees the offset.  Nothing is *tested*
   against this one -- a closer at any indentation closes -- but every
   content line is measured from it. *)
Definition open_fence (ind : nat) (f : fence) : blocks * pstate :=
  ([], PFence f ind []).

(* A reference definition opens at the column its bracket sits at, and for
   the same reason as `open_attr` is not part of `open_kind`: the column is
   absolute and `open_kind` never sees the offset. *)
Definition open_ref (ind : nat) (lbl val : string) : blocks * pstate :=
  ([], PRef ind lbl val).

(* With footnotes off the definition never opens, so `PFoot` is
   unreachable and the complete `[^label]:` line is paragraph text.  The
   descent is computed either way and discarded here, which costs nothing
   and keeps the four call sites identical. *)
Definition open_foot (l : string) (ind : nat) (lbl : string)
  (descended : blocks * pstate) : blocks * pstate :=
  if bfootnotes
  then let (bs, inner) := descended in ([], PFoot ind lbl (rev bs) inner)
  else ([], PPara [drop_leading_ws l]).

Lemma open_foot_fst :
  forall l ind lbl d, fst (open_foot l ind lbl d) = [].
Proof. intros. unfold open_foot. destruct bfootnotes; [destruct d|]; reflexivity. Qed.

Lemma close_reopen_foot :
  forall st l ind lbl d,
    close_reopen st (open_foot l ind lbl d)
    = (finish st, snd (open_foot l ind lbl d)).
Proof.
  intros. unfold close_reopen, open_foot.
  destruct bfootnotes; [destruct d|]; cbn [snd]; rewrite app_nil_r; reflexivity.
Qed.

(* A list marker opens a fresh list, whose first item holds whatever the
   rest of the line parsed to.  A new list is tight until something makes
   it loose, and starts with every style its marker admits. *)
(* A non-task marker's item is `Incomplete`, which nothing reads: see
   `ls_check`. *)
Definition chk_status (chk : option task_marker) : task_status :=
  match chk with Some m => tm_status m | None => Incomplete end.

Definition open_list (ind : nat) (sty : list (lstyle * nat))
  (chk : task_status) (descended : blocks * pstate) : blocks * pstate :=
  let (bs, inner) := descended in
  ([], PList (LSt ind sty false false [] chk []) (rev bs) inner).

(*
Tight/loose bookkeeping
-----------------------

Three events move the flags, mirroring djot.js's annot tests. *)

(* A blank line inside the list arms the flag. *)
Definition list_blank (ls : list_state) : list_state :=
  LSt (ls_indent ls) (ls_styles ls) (ls_loose ls) true (ls_items ls)
      (ls_check ls) (ls_checks ls).

(* A sibling's candidate set, intersected into this list's.  Separate
   from `list_next` so that the tight/loose lemmas, which say nothing
   about styles, keep quantifying over an arbitrary `list_state`. *)
Definition list_narrow (ls : list_state) (ns : list (lstyle * nat))
  : list_state :=
  LSt (ls_indent ls) ns (ls_loose ls) (ls_blanks ls) (ls_items ls)
      (ls_check ls) (ls_checks ls).

(* Narrowing to what is already there changes nothing.  This is what
   makes the uniformity chain blind to styles: a canonical rendering
   repeats one marker, so every sibling re-offers the style the list
   already has. *)
Lemma list_narrow_id : forall ls, list_narrow ls (ls_styles ls) = ls.
Proof. intros ls. destruct ls. reflexivity. Qed.

(* Does a blank line arriving here come to rest inside something the item
   still has open?  djot.js's tight/loose machinery only ever inspects the
   top container and the one below it (parse.ts:1199-1203), which are the
   item and the list exactly when the item's content is a leaf; anything
   deeper hides the list, so the blank never reaches it.

   The containers' `continue`s run before the blankline handler
   (block.ts:634 before parse.ts:1197), so what matters is the stack
   *after* this line: a div, a code block, a nested list and an unfinished
   attribute spec all survive a blank and absorb it, while a blockquote
   has already closed and lets it through.  A heading and a reference
   definition close too, and `PPend` is not on the stack at all -- djot.js
   keeps pending block attributes in a document-wide variable.

   Tabulating survival that way is what lets this be a predicate on the
   state *before* the descent even though the rule is about the stack
   after: `step` is deterministic and a blank's effect on the top
   constructor depends on nothing else.  Reading it off `inner` rather
   than `inner'` is why every pad lemma below stays one line. *)
Fixpoint blank_absorbed (st : pstate) : bool :=
  match st with
  | PFence _ _ _ | PDiv _ _ _ _ | PList _ _ _ | PAttr _ _ _ _
  | PFoot _ _ _ _ => true
  | PPend _ inner => blank_absorbed inner
  | _ => false
  end.

(* Does this line come to rest as a container closer, leaving nothing at
   the tip?  djot.js tests `isBlank` *after* the container `continue`s
   have eaten the line (block.ts:1051), so a `:::` that closes a div
   fires the same `blankline` event an empty line does -- and the
   enclosing list is armed by a line that is not blank at all.

   A fence closer does not, and the difference is which side of that test
   consumes it: a code block eats its closer inside its own `continue`,
   before `isBlank` runs.  Verified against the oracle both ways
   (`.project/oracle-disagreements.md`, "a div's closing line").

   Read off the state *before* the descent, like `blank_absorbed` and for
   the same reason: `step` is deterministic, so whether the line closes
   the div is a fact about the state it arrives at.  Only the immediate
   inner is inspected -- a `PList` between here and the div is the list
   that gets armed instead, exactly as it is for a blank. *)
Fixpoint div_closer (l : string) (st : pstate) : bool :=
  match st with
  | PDiv len _ _ inner => (negb (in_fence inner) && div_close len l)%bool
  | PPend _ inner => div_closer l inner
  | _ => false
  end.

(* Content within the current item.  A line that opens a nested list is
   a `+list` event, which djot.js excludes from loosening; anything else
   loosens the list if a blank line is armed.  Either way the flag is
   spent. *)
Definition list_content (ls : list_state) (k : line_kind) : list_state :=
  let loose :=
    match k with
    | KList _ _ _ _ => ls_loose ls
    | _ => (ls_loose ls || ls_blanks ls)%bool
    end in
  LSt (ls_indent ls) (ls_styles ls) loose false (ls_items ls)
      (ls_check ls) (ls_checks ls).

(* A sibling marker closes the current item and opens the next.  The
   boundary itself neither loosens nor spends the flag (djot.js keeps
   `blanklines` across `+list_item`); the content that follows on the
   same line does, which is what makes `- a`, blank, `- b` loose. *)
Definition list_next (ls : list_state) (item : blocks) (chk : task_status)
  (rest : string) : list_state :=
  let items := item :: ls_items ls in
  let checks := ls_check ls :: ls_checks ls in
  if is_blank rest
  then LSt (ls_indent ls) (ls_styles ls) (ls_loose ls) (ls_blanks ls) items
           chk checks
  else
    let loose :=
      match classify rest with
      | KList _ _ _ _ => ls_loose ls
      | _ => (ls_loose ls || ls_blanks ls)%bool
      end in
    LSt (ls_indent ls) (ls_styles ls) loose false items chk checks.

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

(* Kinds `open_kind` handles: everything but those that open a container
   by parsing part of the line again, or that record a column. *)
Definition direct_open (k : line_kind) : bool :=
  match k with
  | KQuote _ | KList _ _ _ _ | KAttr _ | KFoot _ _ | KRef _ _ | KFence _ => false
  | _ => true
  end.

(* What a line opens, when it opens something.  `open_kind` answers for
   every kind that needs neither a column nor a second look at the line;
   the six that do are the six `direct_open` excludes, and they are
   collected here so that the answer is given once rather than at each
   state that can be interrupted.

   `descend` is the parse of a container prefix's residue, which is
   `step_fuel`'s one recursion.  Taking it as an argument rather than
   making the two mutually recursive is what keeps the fuel out of this
   definition, and therefore out of every lemma stated over it.

   `ind` is the opener's *absolute* column, `off + indent_of l` at every
   call site.  A line-local column would make `step_fuel_shift` false --
   see the block-attribute entry in
   .project/project-engineering-lessons.md. *)
Definition open_line (descend : string -> blocks * pstate)
  (ind : nat) (l : string) (k : line_kind) : blocks * pstate :=
  match k with
  | KQuote rest => open_quote (descend rest)
  | KList sty core chk rest =>
      open_list ind
        (with_starts (configured_list_styles sty chk) core)
        (configured_list_check chk)
        (descend (configured_list_rest chk rest))
  | KAttr ap => open_attr [] ind ap l
  | KFoot lbl rest => open_foot l ind lbl (descend rest)
  | KRef lbl v => open_ref ind lbl v
  | KFence f => open_fence ind f
  | k => open_kind l k
  end.

(* `open_line` is a case split on `direct_open` and nothing else, which
   is what lets a lemma about a kind it does not name stay stated over
   `open_kind`. *)
Lemma open_line_direct :
  forall descend ind l k,
    direct_open k = true -> open_line descend ind l k = open_kind l k.
Proof. intros descend ind l k H. destruct k; (reflexivity || discriminate). Qed.

Fixpoint step_fuel (n : nat) (off : nat) (l : string) (st : pstate) {struct n}
  : blocks * pstate :=
  match n with
  | O => ([], st)                     (* unreachable from step *)
  | S n' =>
      (* The one recursion: a container prefix's residue, parsed from
         idle at the offset the prefix ate.  Named once because
         `open_line` is its only consumer and three of that definition's
         branches want it. *)
      let descend := fun rest =>
        step_fuel n' (off + consumed l rest) rest (PPara []) in
      match st with
      | PFence f ind acc =>
          (* Verbatim: only the close test, and the closing line is
             consumed rather than reprocessed — the one state that is
             not "continue or close-and-reopen".  Verbatim up to the
             fence's own column, that is: the line keeps whatever it is
             indented *past* the opener and nothing before it. *)
          if fence_close f l
          then ([fence_block f (rev acc)], PPara [])
          else ([], PFence f ind (drop_ws_upto (ind - off) l :: acc))
      | PPara [] =>
          (* Idle: nothing to close, so the line just opens its block. *)
          open_line descend (off + indent_of l) l (classify l)
      | PPara (c :: cur') =>
          (* The underline test runs before the classifier, because the
             kinds an underline wears are kinds that mean something else:
             `===` is `KText` and `---` is `KThematic`, and both of those
             would otherwise continue the paragraph.  It is only asked of
             an *open* paragraph, so a line that opens one is classified
             as it always was. *)
          match bunderline_of l with
          | Some lvl => ([heading_block (S lvl) (c :: cur')], PPara [])
          | None =>
          match classify l with
          | KBlank => close_reopen (PPara (c :: cur')) (open_kind l KBlank)
          | k =>
              if binterrupt k
              then close_reopen (PPara (c :: cur'))
                     (open_line descend (off + indent_of l) l k)
              else ([], PPara (drop_leading_ws l :: c :: cur'))
          end
          end
      | PHeading lvl cur =>
          (* Unlike a paragraph, a heading *is* interruptible: only a
             matching-level marker or a lazy text line continues it. *)
          match classify l with
          | KHeading lvl' rest =>
              if bheading_continues
              then if Nat.eqb lvl' lvl
                   then ([], PHeading lvl (push_text rest cur))
                   else close_reopen (PHeading lvl cur)
                          (open_kind l (KHeading lvl' rest))
              else close_reopen (PHeading lvl cur)
                     (open_kind l (KHeading lvl' rest))
          | KText =>
              if bheading_continues
              then ([], PHeading lvl (drop_leading_ws l :: cur))
              else close_reopen (PHeading lvl cur) (open_kind l KText)
          | k =>
              close_reopen (PHeading lvl cur)
                (open_line descend (off + indent_of l) l k)
          end
      | PQuote done inner =>
          match classify l with
          | KQuote rest =>
              (* continue: descend into the quote already open, keeping
                 what it has closed so far *)
              let (bs, inner') := step_fuel n' (off + consumed l rest) rest inner in
              ([], PQuote (rev bs ++ done)%list inner')
          | k =>
              if is_lazy k inner
              then ([], PQuote done (feed_lazy l inner))
              else close_reopen (PQuote done inner)
                     (open_line descend (off + indent_of l) l k)
          end
      | PDiv len cls done inner =>
          (* The close test runs before the line reaches anything nested
             inside, because djot.js runs container `continue`s
             outermost-first (block.ts:634) and `div_close` strips
             leading whitespace.  That is why an indented `:::` inside a
             list inside a div closes the *div*, and why
             `div_uniformity`'s side condition has to reach every line of
             the contents rather than only the outermost ones.

             The closing line is consumed rather than reprocessed, as a
             code fence's is: djot.js advances `this.pos` past the fence
             before closing (block.ts:645).  Otherwise the line descends
             unchanged, at the same offset — a div eats no prefix.

             `in_fence` is checked first: inside an open code block a
             `:::` line is content, not a closer. *)
          if (negb (in_fence inner) && div_close len l)%bool
          then ([div_block cls (rev done ++ finish inner)%list], PPara [])
          else
            let (bs, inner') := step_fuel n' off l inner in
            ([], PDiv len cls (rev bs ++ done)%list inner')
      | PList ls done inner =>
          match classify l with
          | KBlank =>
              (* a blank arms the loose flag but closes nothing: it goes
                 to the item's contents, where it ends any open
                 paragraph.  It arms *this* list only when nothing the
                 item has open absorbs it first, which `blank_absorbed`
                 reads off the state before the descent.  The recursion
                 then arms exactly the innermost list that can see it. *)
              let (bs, inner') := step_fuel n' off l inner in
              let ls' := if blank_absorbed inner then ls else list_blank ls in
              ([], PList ls' (rev bs ++ done)%list inner')
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
                let ls' :=
                  if div_closer l inner then list_blank ls else list_content ls k in
                ([], PList ls' (rev bs ++ done)%list inner')
              else
                match k with
                | KList sty core chk rest =>
                    match narrow (ls_styles ls) (configured_list_styles sty chk) with
                    | [] =>
                        (* no style survives: a different list *)
                        close_reopen (PList ls done inner)
                          (open_line descend (off + indent_of l) l
                             (KList sty core chk rest))
                    | ns =>
                        (* a sibling item: narrow the style set, close the
                           current item, open the next around the rest of
                           the line *)
                        let item := (rev done ++ finish inner)%list in
                        let (bs, inner') :=
                          step_fuel n'
                            (off + consumed l (configured_list_rest chk rest))
                            (configured_list_rest chk rest) (PPara []) in
                        ([], PList (list_next (list_narrow ls ns) item
                               (configured_list_check chk)
                               (configured_list_rest chk rest))
                               (rev bs) inner')
                    end
                | _ =>
                    if is_lazy k inner
                    then ([], PList ls done (feed_lazy l inner))
                    else close_reopen (PList ls done inner)
                           (open_line descend
                              (off + indent_of l) l k)
                end
          end
      | PAttr pend ind ap slices =>
          (* djot.js runs this container's `continue` before anything
             else (block.ts:566).  A finished spec refuses every line and
             closes; an unfinished one takes the line only if it is
             indented past the opener; and a spec that fails, at either
             point, becomes a paragraph of the lines it ate.  In all three
             cases the line is reprocessed against what the container
             became, which is the close-and-reopen rule with the reopening
             computed rather than supplied.

             The failing *indented* line is part of that paragraph — its
             slice is pushed before the feed (block.ts:569-572) — and the
             non-indented line is not, but both are then handed to
             `PPara slices`, which appends the one and closes on the
             other.  One equation covers both.

             A *blank* continuation line is fed to the machine but not
             recorded.  djot.js records it, so a spec that spans a blank
             line and then fails reproduces that blank inside its
             paragraph — and a paragraph containing a blank line is
             exactly what `Wf.wf_block` rules out, because it does not
             round-trip: parsing that rendering back splits the paragraph
             in two.  The divergence is confined to specs that both span
             a blank line and fail. *)
          if ap_done ap
          then step_fuel n' off l (PPend (attr_merge (ap_attrs ap) pend) (PPara []))
          else if Nat.ltb ind (off + indent_of l)
          then
            let ap' := attr_feed l ap in
            if ap_failed ap'
            then step_fuel n' off l (PPara slices)
            else ([], PAttr pend ind ap' (push_text l slices))
          else step_fuel n' off l (PPara slices)
      | PRef ind lbl val =>
          (* A line indented past the bracket and carrying one
             whitespace-free run extends the destination; anything else
             ends the definition and is reprocessed at this level.  There
             is no failure case — the definition is already complete when
             the state is entered — so unlike `PAttr` nothing is
             retracted. *)
          match (if Nat.ltb ind (off + indent_of l) then ref_cont l else None) with
          | Some t => ([], PRef ind lbl (val ++ t))
          | None =>
              let (bs, st') := step_fuel n' off l (PPara []) in
              ((ref_block lbl val :: bs)%list, st')
          end
      | PTable rows cap =>
          (* Four rules, and which apply depends on what the table has
             seen.  A caption opener is read here rather than by
             `classify`, which is what confines the construct to a table
             (see `Line.caption_open`).  A line that looks like a row but
             fails to scan (an unclosed verbatim) is a `KText` line by
             then, so it arrives already carrying djot.js's answer. *)
          match cap with
          | TCaption ls =>
              (* The caption owns every nonblank line, row lines
                 included, and a blank ends it. *)
              if is_blank l
              then ((table_block (rev rows) cap :: nil)%list, PPara [])
              else ([], PTable rows (TCaption (drop_leading_ws l :: ls)))
          | _ =>
              match caption_open l with
              | Some rest => ([], PTable rows (TCaption (push_text rest [])))
              | None =>
                  if is_blank l
                  then
                    (* The rows are over, but the table is not: a caption
                       may still follow, across any number of blanks. *)
                    ([], PTable rows TAfterBlank)
                  else
                    match classify l, cap with
                    (* A blank between two rows starts a second table,
                       which is why `TAfterBlank` is a state and not a
                       flag on the blank itself. *)
                    | KRow r, TOpen => ([], PTable (r :: rows) TOpen)
                    | _, _ =>
                        let (bs, st') := step_fuel n' off l (PPara []) in
                        ((table_block (rev rows) cap :: bs)%list, st')
                    end
              end
          end
      | PFoot ind lbl done inner =>
          if is_blank l
          then let (bs, inner') := step_fuel n' off l inner in
               ([], PFoot ind lbl (rev bs ++ done)%list inner')
          else if Nat.ltb ind (off + indent_of l)
          then let (bs, inner') := step_fuel n' off l inner in
               ([], PFoot ind lbl (rev bs ++ done)%list inner')
          else
            let (bs, st') := step_fuel n' off l (PPara []) in
            ((foot_block lbl (rev done ++ finish inner)%list :: bs)%list, st')
      | PPend pend inner =>
          (* Two lines are the pending attributes' own business, and only
             while nothing has claimed them yet: a blank line drops them
             (parse.ts:1231), and another spec merges into them.  Every
             other line goes down to `inner` and gets decorated by
             whatever it closes. *)
          match classify l with
          | KBlank =>
              if is_idle inner then ([], PPara [])
              else pend_result pend (step_fuel n' off l inner)
          | KAttr ap =>
              if is_idle inner
              then open_attr pend (off + indent_of l) ap l
              else pend_result pend (step_fuel n' off l inner)
          | _ => pend_result pend (step_fuel n' off l inner)
          end
      end
  end.

(* The transition proper.  Each descent either shortens the line (a
   quote prefix, a list marker) or drops a container from the state (a
   list item's contents), so line length plus nesting depth strictly
   decreases and this much fuel is always enough — `step_fuel_enough`
   retires it, and it appears in no lemma statement anywhere (only in
   the tactics that unfold `step`). *)
Definition step (l : string) (st : pstate) : blocks * pstate :=
  step_fuel (S (String.length l + pstate_depth st)) 0 l st.

(** Fold the transition over the lines, then close the stack.
   Structurally recursive on `lines`, so it always terminates and proofs
   can step it one line at a time. *)
Fixpoint parse_lines (lines : list string) (st : pstate) : blocks :=
  match lines with
  | [] => finish st
  | l :: rest =>
      let (bs, st') := step l st in
      (bs ++ parse_lines rest st')%list
  end.

(** Entry point of the block parser: split the source into lines and fold from
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
  cbn [step_fuel open_line].
  destruct st as [cur|hlvl hcur|f fnd acc|done inner|dlen dcls ddone dinner|ls done inner|apend aind aap aslices|rind rlbl rval|find flbl fdone finner|trows tcap|ppend pinner].
  - (* idle, or an open paragraph *)
    cbn [pstate_depth] in Hn |- *.
    destruct cur as [|c cur'].
    + destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; try reflexivity.
      * pose proof (classify_quote_length _ _ E) as Hlt.
        cbn [open_line pstate_depth]; rewrite ?Nat.add_0_r.
        rewrite (IH n' _ rest (PPara [])) by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l) _ rest (PPara [])) by (cbn [pstate_depth]; lia).
        reflexivity.
      * pose proof (configured_list_rest_length _ _ _ _ _ E) as Hlt.
        cbn [open_line pstate_depth]; rewrite ?Nat.add_0_r.
        rewrite (IH n' _ (configured_list_rest chk mr) (PPara []))
          by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l) _ (configured_list_rest chk mr) (PPara []))
          by (cbn [pstate_depth]; lia).
        reflexivity.
      * pose proof (classify_foot_length _ _ _ E) as Hlt.
        cbn [open_line pstate_depth]; rewrite ?Nat.add_0_r.
        rewrite (IH n' _ frest (PPara [])) by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l) _ frest (PPara []))
          by (cbn [pstate_depth]; lia).
        reflexivity.
    + destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E;
        try reflexivity.
      destruct (binterrupt (KList m mc chk mr)) eqn:Ei; [|reflexivity].
      pose proof (configured_list_rest_length _ _ _ _ _ E) as Hlt.
      cbn [open_line pstate_depth]; rewrite ?Nat.add_0_r.
      rewrite (IH n' _ (configured_list_rest chk mr) (PPara []))
        by (cbn [pstate_depth]; lia).
      rewrite (IH (String.length l) _ (configured_list_rest chk mr) (PPara []))
        by (cbn [pstate_depth]; lia).
      reflexivity.
  - (* an open heading: the quote and list branches recurse *)
    cbn [pstate_depth] in Hn |- *.
    destruct bheading_continues eqn:Hheading.
    2: {
      destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; try reflexivity.
      - pose proof (classify_quote_length _ _ E) as Hlt.
        cbn [open_line pstate_depth]; rewrite ?Nat.add_0_r.
        rewrite (IH n' _ rest (PPara [])) by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l) _ rest (PPara []))
          by (cbn [pstate_depth]; lia).
        reflexivity.
      - pose proof (configured_list_rest_length _ _ _ _ _ E) as Hlt.
        cbn [open_line pstate_depth]; rewrite ?Nat.add_0_r.
        rewrite (IH n' _ (configured_list_rest chk mr) (PPara []))
          by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l) _ (configured_list_rest chk mr) (PPara []))
          by (cbn [pstate_depth]; lia).
        reflexivity.
      - pose proof (classify_foot_length _ _ _ E) as Hlt.
        cbn [open_line pstate_depth]; rewrite ?Nat.add_0_r.
        rewrite (IH n' _ frest (PPara [])) by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l) _ frest (PPara []))
          by (cbn [pstate_depth]; lia).
        reflexivity. }
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; try reflexivity.
    + pose proof (classify_quote_length _ _ E) as Hlt.
      cbn [open_line pstate_depth]; rewrite ?Nat.add_0_r.
      rewrite (IH n' _ rest (PPara [])) by (cbn [pstate_depth]; lia).
      rewrite (IH (String.length l) _ rest (PPara [])) by (cbn [pstate_depth]; lia).
      reflexivity.
    + pose proof (configured_list_rest_length _ _ _ _ _ E) as Hlt.
      cbn [open_line pstate_depth]; rewrite ?Nat.add_0_r.
      rewrite (IH n' _ (configured_list_rest chk mr) (PPara []))
        by (cbn [pstate_depth]; lia).
      rewrite (IH (String.length l) _ (configured_list_rest chk mr) (PPara []))
        by (cbn [pstate_depth]; lia).
      reflexivity.
    + pose proof (classify_foot_length _ _ _ E) as Hlt.
      cbn [open_line pstate_depth]; rewrite ?Nat.add_0_r.
      rewrite (IH n' _ frest (PPara [])) by (cbn [pstate_depth]; lia).
      rewrite (IH (String.length l) _ frest (PPara []))
        by (cbn [pstate_depth]; lia).
      reflexivity.
  - destruct (fence_close f l); reflexivity.
  - (* inside a quote: continuing descends with the same inner state *)
    cbn [pstate_depth] in Hn |- *.
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; try reflexivity.
    + pose proof (classify_quote_length _ _ E) as Hlt.
      rewrite (IH n' _ rest inner) by lia.
      rewrite (IH (String.length l + S (pstate_depth inner)) _ rest inner) by lia.
      reflexivity.
    + pose proof (configured_list_rest_length _ _ _ _ _ E) as Hlt.
      rewrite (IH n' _ (configured_list_rest chk mr) (PPara []))
        by (cbn [pstate_depth]; lia).
      rewrite (IH (String.length l + S (pstate_depth inner)) _
                 (configured_list_rest chk mr) (PPara []))
        by (cbn [pstate_depth]; lia).
      reflexivity.
    + pose proof (classify_foot_length _ _ _ E) as Hlt.
      rewrite (IH n' _ frest (PPara [])) by (cbn [pstate_depth]; lia).
      rewrite (IH (String.length l + S (pstate_depth inner)) _ frest (PPara []))
        by (cbn [pstate_depth]; lia).
      reflexivity.
  - (* inside a div: the close test decides, and the descent keeps the
       line but drops a level, exactly as a list item's contents do *)
    cbn [pstate_depth] in Hn |- *.
    destruct (negb (in_fence dinner) && div_close dlen l)%bool; [reflexivity|].
    rewrite (IH n' _ l dinner) by lia.
    rewrite (IH (String.length l + S (pstate_depth dinner)) _ l dinner) by lia.
    reflexivity.
  - (* inside a list: an item's contents keep the line and drop a level *)
    cbn [pstate_depth] in Hn |- *.
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E.
    9: { (* an unindented footnote closes the list and opens outside it *)
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - rewrite (IH n' _ l inner) by lia.
        rewrite (IH (String.length l + S (pstate_depth inner)) _ l inner) by lia.
        reflexivity.
      - pose proof (classify_foot_length _ _ _ E) as Hlt.
        rewrite (IH n' _ frest (PPara [])) by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l + S (pstate_depth inner)) _ frest (PPara []))
          by (cbn [pstate_depth]; lia).
        reflexivity. }
    7: { (* a bullet marker: a sibling item, or a list of another style *)
      pose proof (configured_list_rest_length _ _ _ _ _ E) as Hlt.
      destruct (Nat.ltb (ls_indent ls) (off + indent_of l)).
      - rewrite (IH n' _ l inner) by lia.
        rewrite (IH (String.length l + S (pstate_depth inner)) _ l inner) by lia.
        reflexivity.
      - destruct (narrow (ls_styles ls) (configured_list_styles m chk));
          rewrite (IH n' _ (configured_list_rest chk mr) (PPara []))
            by (cbn [pstate_depth]; lia);
          rewrite (IH (String.length l + S (pstate_depth inner)) _
                     (configured_list_rest chk mr) (PPara []))
            by (cbn [pstate_depth]; lia);
          reflexivity. }
    1: { (* a blank line goes to the item's contents *)
      rewrite (IH n' _ l inner) by lia.
      rewrite (IH (String.length l + S (pstate_depth inner)) _ l inner) by lia.
      reflexivity. }
    4: { (* an unindented quote closes the list and opens outside it *)
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
  - (* an open attribute spec: every branch but "take the line" hands the
       line on, and each target is shallower than PAttr's depth of 2 *)
    cbn [pstate_depth] in Hn |- *.
    set (q := PPend (attr_merge (ap_attrs aap) apend) (PPara [])).
    assert (Hq : pstate_depth q = 1) by reflexivity.
    destruct (ap_done aap).
    + rewrite (IH n' _ l q) by lia.
      rewrite (IH (String.length l + 2) _ l q) by lia.
      reflexivity.
    + destruct (Nat.ltb aind (off + indent_of l));
        [destruct (ap_failed (attr_feed l aap)); [|reflexivity]|];
        rewrite (IH n' _ l (PPara aslices)) by (cbn [pstate_depth]; lia);
        rewrite (IH (String.length l + 2) _ l (PPara aslices))
          by (cbn [pstate_depth]; lia);
        reflexivity.
  - (* an open reference definition: a continuation line recurses into
       nothing, and the line that ends it is reprocessed from idle *)
    cbn [pstate_depth] in Hn |- *.
    destruct (if Nat.ltb rind (off + indent_of l) then ref_cont l else None);
      [reflexivity|].
    rewrite (IH n' _ l (PPara [])) by (cbn [pstate_depth]; lia).
    rewrite (IH (String.length l + 1) _ l (PPara [])) by (cbn [pstate_depth]; lia).
    reflexivity.
  - (* an open footnote: blank and indented lines descend into its
       contents; a line outside the container closes it and is reprocessed *)
    cbn [pstate_depth] in Hn |- *.
    destruct (is_blank l).
    + rewrite (IH n' _ l finner) by lia.
      rewrite (IH (String.length l + S (pstate_depth finner)) _ l finner) by lia.
      reflexivity.
    + destruct (Nat.ltb find (off + indent_of l)).
      * rewrite (IH n' _ l finner) by lia.
        rewrite (IH (String.length l + S (pstate_depth finner)) _ l finner) by lia.
        reflexivity.
      * rewrite (IH n' _ l (PPara [])) by (cbn [pstate_depth]; lia).
        rewrite (IH (String.length l + S (pstate_depth finner)) _ l (PPara []))
          by (cbn [pstate_depth]; lia).
        reflexivity.
  - (* an open table: a row line recurses into nothing, and the line
       that ends it is reprocessed from idle *)
    cbn [pstate_depth] in Hn |- *.
    destruct (classify l) eqn:E; try reflexivity;
      rewrite (IH n' _ l (PPara [])) by (cbn [pstate_depth]; lia);
      rewrite (IH (String.length l + 1) _ l (PPara []))
        by (cbn [pstate_depth]; lia);
      reflexivity.
  - (* pending attributes: a blank line and a further spec are theirs
       while nothing has claimed them, and every other line descends *)
    cbn [pstate_depth] in Hn |- *.
    destruct (classify l) eqn:E;
      try (destruct (is_idle pinner); [reflexivity|]);
      rewrite (IH n' _ l pinner) by lia;
      rewrite (IH (String.length l + S (pstate_depth pinner)) _ l pinner) by lia;
      reflexivity.
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
indentation.  An open fence is included: it records the column its border
sits at, that column moves with the offset, and a content line is measured
against the difference -- which the shift leaves alone.  Fences are still a
problem for `step_fuel_pad` below, which pads the line itself rather than
moving the offset: there the two sides carry the *same* state, so a fence
opened `k` columns to the left of where the padded line starts strips `k`
columns too few. *)

(* The shift, on the state: every recorded column moves by n. *)
Fixpoint pad_state (n : nat) (st : pstate) : pstate :=
  match st with
  | PFence f ind acc => PFence f (n + ind) acc
  | PQuote done inner => PQuote done (pad_state n inner)
  | PDiv len cls done inner => PDiv len cls done (pad_state n inner)
  | PList ls done inner =>
      PList (LSt (n + ls_indent ls) (ls_styles ls) (ls_loose ls)
                 (ls_blanks ls) (ls_items ls) (ls_check ls) (ls_checks ls))
            done (pad_state n inner)
  | PAttr pend ind ap slices => PAttr pend (n + ind) ap slices
  | PRef ind lbl val => PRef (n + ind) lbl val
  | PFoot ind lbl done inner =>
      PFoot (n + ind) lbl done (pad_state n inner)
  | PPend pend inner => PPend pend (pad_state n inner)
  | _ => st
  end.

Lemma ltb_add_mono_l :
  forall n a b, Nat.ltb (n + a) (n + b) = Nat.ltb a b.
Proof.
  intros n a b. destruct (Nat.ltb a b) eqn:E.
  - apply Nat.ltb_lt. apply Nat.ltb_lt in E. lia.
  - apply Nat.ltb_ge. apply Nat.ltb_ge in E. lia.
Qed.

Lemma pad_state_in_fence :
  forall n st, in_fence (pad_state n st) = in_fence st.
Proof.
  intros n st.
  induction st as [| | |done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|rind rlbl rval|find flbl fdone finner IH|trows tcap|ppend pinner IH];
    cbn [pad_state in_fence]; try reflexivity; exact IH.
Qed.

Lemma pad_state_depth :
  forall n st, pstate_depth (pad_state n st) = pstate_depth st.
Proof.
  intros n st. induction st as [| | |done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|rind rlbl rval|find flbl fdone finner IH|trows tcap|ppend pinner IH];
    try reflexivity; cbn [pad_state pstate_depth]; rewrite IH; reflexivity.
Qed.

(* finish reads a list's spacing and items, never its column. *)
Lemma pad_state_finish :
  forall n st, finish (pad_state n st) = finish st.
Proof.
  intros n st. induction st as [| | |done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|rind rlbl rval|find flbl fdone finner IH|trows tcap|ppend pinner IH];
    try reflexivity; cbn [pad_state finish]; rewrite IH; reflexivity.
Qed.

Lemma pad_state_lazy_ok :
  forall n st, lazy_ok (pad_state n st) = lazy_ok st.
Proof.
  intros n st. induction st as [cur| | |done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|rind rlbl rval|find flbl fdone finner IH|trows tcap|ppend pinner IH];
    try reflexivity; cbn [pad_state lazy_ok]; exact IH.
Qed.

Lemma pad_state_feed_lazy :
  forall n l st, feed_lazy l (pad_state n st) = pad_state n (feed_lazy l st).
Proof.
  intros n l st.
  induction st as [cur|lvl cur| |done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|rind rlbl rval|find flbl fdone finner IH|trows tcap|ppend pinner IH];
    cbn [pad_state feed_lazy]; try reflexivity; rewrite IH; reflexivity.
Qed.

(* The three flag updates preserve ls_indent, so each commutes with the
   shift. *)
Lemma pad_list_blank :
  forall n ls,
    list_blank (LSt (n + ls_indent ls) (ls_styles ls) (ls_loose ls)
                    (ls_blanks ls) (ls_items ls) (ls_check ls) (ls_checks ls))
    = LSt (n + ls_indent (list_blank ls)) (ls_styles (list_blank ls))
          (ls_loose (list_blank ls)) (ls_blanks (list_blank ls))
          (ls_items (list_blank ls)) (ls_check (list_blank ls)) (ls_checks (list_blank ls)).
Proof. intros n ls. destruct ls. reflexivity. Qed.

(* Padding never changes which constructor is on top, so the blank's
   "is a list open here" test is pad-invariant. *)
Lemma pad_state_is_idle :
  forall n st, is_idle (pad_state n st) = is_idle st.
Proof. intros n st. destruct st; reflexivity. Qed.

(* A blank prefix is invisible to the closer test, since `div_close`
   drops leading whitespace before counting colons. *)
Lemma div_closer_ws_prefix :
  forall p l st, is_blank p = true -> div_closer (p ++ l) st = div_closer l st.
Proof.
  intros p l st Hp.
  induction st as [cur|lvl cur| |done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|rind rlbl rval|find flbl fdone finner IH|trows tcap|ppend pinner IH];
    cbn [div_closer]; try reflexivity.
  - rewrite (div_close_ws_prefix p dlen l Hp). reflexivity.
  - exact IH.
Qed.

Lemma pad_state_div_closer :
  forall n l st, div_closer l (pad_state n st) = div_closer l st.
Proof.
  intros n l st.
  induction st as [cur|lvl cur| |done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|rind rlbl rval|find flbl fdone finner IH|trows tcap|ppend pinner IH];
    cbn [pad_state div_closer]; try reflexivity.
  - rewrite pad_state_in_fence. reflexivity.
  - exact IH.
Qed.

Lemma pad_state_blank_absorbed :
  forall n st, blank_absorbed (pad_state n st) = blank_absorbed st.
Proof.
  intros n st.
  induction st as [| | |done inner IH|dlen dcls ddone dinner IH|ls done inner IH
                  |apend aind aap aslices|rind rlbl rval
                  |find flbl fdone finner IH|trows tcap|ppend pinner IH];
    try reflexivity; cbn [pad_state blank_absorbed]; exact IH.
Qed.


Lemma pad_list_content :
  forall n ls k,
    list_content (LSt (n + ls_indent ls) (ls_styles ls) (ls_loose ls)
                      (ls_blanks ls) (ls_items ls) (ls_check ls) (ls_checks ls)) k
    = LSt (n + ls_indent (list_content ls k)) (ls_styles (list_content ls k))
          (ls_loose (list_content ls k)) (ls_blanks (list_content ls k))
          (ls_items (list_content ls k)) (ls_check (list_content ls k)) (ls_checks (list_content ls k)).
Proof. intros n ls k. destruct ls; destruct k; reflexivity. Qed.

Lemma pad_list_narrow :
  forall n ls ns,
    list_narrow (LSt (n + ls_indent ls) (ls_styles ls) (ls_loose ls)
                     (ls_blanks ls) (ls_items ls) (ls_check ls) (ls_checks ls)) ns
    = LSt (n + ls_indent (list_narrow ls ns)) (ls_styles (list_narrow ls ns))
          (ls_loose (list_narrow ls ns)) (ls_blanks (list_narrow ls ns))
          (ls_items (list_narrow ls ns)) (ls_check (list_narrow ls ns)) (ls_checks (list_narrow ls ns)).
Proof. intros n ls ns. destruct ls. reflexivity. Qed.

Lemma pad_list_next :
  forall n ls item chk rest,
    list_next (LSt (n + ls_indent ls) (ls_styles ls) (ls_loose ls)
                   (ls_blanks ls) (ls_items ls) (ls_check ls) (ls_checks ls))
              item chk rest
    = LSt (n + ls_indent (list_next ls item chk rest))
          (ls_styles (list_next ls item chk rest))
          (ls_loose (list_next ls item chk rest))
          (ls_blanks (list_next ls item chk rest))
          (ls_items (list_next ls item chk rest))
          (ls_check (list_next ls item chk rest))
          (ls_checks (list_next ls item chk rest)).
Proof.
  intros n ls item chk rest. unfold list_next.
  destruct ls; destruct (is_blank rest); reflexivity.
Qed.

(* The two shapes `pad_state` leaves behind, as `close_reopen` sees them. *)
Lemma finish_pad_list :
  forall n ls done inner,
    finish (PList (LSt (n + ls_indent ls) (ls_styles ls) (ls_loose ls)
                       (ls_blanks ls) (ls_items ls) (ls_check ls) (ls_checks ls)) done (pad_state n inner))
    = finish (PList ls done inner).
Proof.
  intros n ls done inner. cbn [finish].
  rewrite (pad_state_finish n inner). destruct ls. reflexivity.
Qed.

Lemma finish_pad_div :
  forall n len cls done inner,
    finish (PDiv len cls done (pad_state n inner))
    = finish (PDiv len cls done inner).
Proof.
  intros n len cls done inner. cbn [finish].
  rewrite (pad_state_finish n inner). reflexivity.
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
  destruct st as [cur|hlvl hcur|f fnd acc|done inner|dlen dcls ddone dinner|ls done inner|apend aind aap aslices|rind rlbl rval|find flbl fdone finner|trows tcap|ppend pinner].
  (* idle, or an open paragraph *)
  { cbn [pad_state step_fuel open_line].
    destruct cur as [|c cur'].
    { destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy];
        try reflexivity;
        try (cbn [open_fence fst snd pad_state]; rewrite Nat.add_assoc;
             reflexivity).
      { cbn [open_kind fst snd pad_state]. destruct bdivs; reflexivity. }
      { rewrite <- Nat.add_assoc.
        pose proof (IH k (off + consumed l rest) rest (PPara [])) as H;
          cbn [pad_state] in H; rewrite H.
        destruct (step_fuel n (off + consumed l rest) rest (PPara []))
          as [bs inner'] eqn:Ed.
        cbn [open_quote fst snd pad_state]. reflexivity. }
      { rewrite <- !Nat.add_assoc.
        pose proof (IH k (off + consumed l (configured_list_rest chk mr))
                      (configured_list_rest chk mr) (PPara [])) as H;
          cbn [pad_state] in H; rewrite H.
        destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara []))
          as [bs inner'] eqn:Ed.
        cbn [open_list fst snd pad_state]. reflexivity. }
      { unfold open_attr. destruct (@battrs K); cbn [fst snd pad_state];
        rewrite ?Nat.add_assoc; reflexivity. }
      { rewrite <- !Nat.add_assoc.
        pose proof (IH k (off + consumed l frest) frest (PPara [])) as H;
          cbn [pad_state] in H; rewrite H.
        destruct (step_fuel n (off + consumed l frest) frest (PPara []))
          as [bs inner'] eqn:Ed.
        unfold open_foot. destruct (@bfootnotes K);
          cbn [fst snd pad_state]; reflexivity. }
      { cbn [open_ref fst snd pad_state]. rewrite Nat.add_assoc. reflexivity. }
      { cbn [open_kind]. destruct (@btables K); reflexivity. } }
    { destruct (bunderline_of l) as [ulvl|] eqn:Eu;
        [cbn [fst snd pad_state]; reflexivity|].
      destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy];
        try reflexivity.
      destruct (binterrupt (KList m mc chk mr)) eqn:Ei; [|reflexivity].
      rewrite <- !Nat.add_assoc.
      pose proof (IH k (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara [])) as H;
        cbn [pad_state] in H; rewrite H.
      destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                  (configured_list_rest chk mr) (PPara []))
        as [bs inner'] eqn:Ed.
      cbn [close_reopen open_list fst snd pad_state]. reflexivity. } }
  (* heading *)
  { cbn [pad_state step_fuel open_line].
    destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
    { reflexivity. }
    { reflexivity. }
    { (* fence: opens at the column its border sits at *)
      cbn [close_reopen open_fence fst snd pad_state].
      rewrite Nat.add_assoc. reflexivity. }
    { cbn [close_reopen open_kind fst snd pad_state].
      destruct bdivs; reflexivity. }    (* div: opens, records no column *)
    { rewrite <- Nat.add_assoc.
      pose proof (IH k (off + consumed l rest) rest (PPara [])) as H;
        cbn [pad_state] in H; rewrite H.
      destruct (step_fuel n (off + consumed l rest) rest (PPara []))
        as [bs inner'] eqn:Ed.
      cbn [close_reopen open_quote fst snd pad_state]. reflexivity. }
    { destruct bheading_continues; [destruct (klvl =? hlvl)%nat|]; reflexivity. }
    { rewrite <- !Nat.add_assoc.
      pose proof (IH k (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara [])) as H;
        cbn [pad_state] in H; rewrite H.
      destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                  (configured_list_rest chk mr) (PPara []))
        as [bs inner'] eqn:Ed.
      cbn [close_reopen open_list fst snd pad_state]. reflexivity. }
    { unfold open_attr. destruct (@battrs K);
        cbn [close_reopen fst snd pad_state];
        rewrite ?Nat.add_assoc; reflexivity. }
    { rewrite <- !Nat.add_assoc.
      pose proof (IH k (off + consumed l frest) frest (PPara [])) as H;
        cbn [pad_state] in H; rewrite H.
      destruct (step_fuel n (off + consumed l frest) frest (PPara []))
        as [bs inner'] eqn:Ed.
      unfold open_foot. destruct (@bfootnotes K);
        cbn [close_reopen fst snd pad_state]; reflexivity. }
    { cbn [close_reopen open_ref fst snd pad_state].
      rewrite Nat.add_assoc. reflexivity. }
    { cbn [close_reopen open_kind fst snd pad_state].
      destruct (@btables K); reflexivity. }
    { destruct bheading_continues; reflexivity. } }
  (* fence: the column moves with the offset, and the content lines are
     measured against the difference, which the shift leaves alone *)
  { cbn [pad_state step_fuel open_line]. destruct (fence_close f l); [reflexivity|].
    replace (k + fnd - (k + off)) with (fnd - off) by lia. reflexivity. }
  (* quote *)
  { cbn [pad_state step_fuel open_line].
    destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
    { cbn [is_lazy close_reopen open_kind fst snd pad_state];
      destruct (@bdivs K); cbn [close_reopen fst snd pad_state];
      rewrite finish_pad_quote; reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      rewrite finish_pad_quote. reflexivity. }
    { (* fence: opens at the column its border sits at *)
      cbn [close_reopen open_fence fst snd pad_state].
      rewrite finish_pad_quote, Nat.add_assoc. reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state];
      destruct (@bdivs K); cbn [close_reopen fst snd pad_state];
      rewrite finish_pad_quote; reflexivity. }
    { rewrite <- Nat.add_assoc.
      rewrite (IH k (off + consumed l rest) rest inner).
      destruct (step_fuel n (off + consumed l rest) rest inner)
        as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      rewrite finish_pad_quote. reflexivity. }
    { rewrite <- !Nat.add_assoc.
      pose proof (IH k (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara [])) as H;
        cbn [pad_state] in H; rewrite H.
      destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                  (configured_list_rest chk mr) (PPara []))
        as [bs inner'] eqn:Ed.
      cbn [close_reopen open_list fst snd pad_state].
      rewrite finish_pad_quote. reflexivity. }
    { unfold open_attr. destruct (@battrs K);
        cbn [close_reopen fst snd pad_state];
        rewrite ?Nat.add_assoc, finish_pad_quote; reflexivity. }
    { rewrite <- !Nat.add_assoc.
      pose proof (IH k (off + consumed l frest) frest (PPara [])) as H;
        cbn [pad_state] in H; rewrite H.
      destruct (step_fuel n (off + consumed l frest) frest (PPara []))
        as [bs inner'] eqn:Ed.
      unfold open_foot. destruct (@bfootnotes K);
        cbn [close_reopen fst snd pad_state]; rewrite finish_pad_quote; reflexivity. }
    { cbn [close_reopen open_ref fst snd pad_state].
      rewrite Nat.add_assoc, finish_pad_quote. reflexivity. }
    { (* row: not lazy, and it opens a state with no column *)
      cbn [is_lazy close_reopen open_kind fst snd pad_state].
      destruct (@btables K); cbn [close_reopen fst snd pad_state];
        rewrite finish_pad_quote; reflexivity. }
    { cbn [is_lazy]. rewrite pad_state_lazy_ok.
      destruct (lazy_ok inner) eqn:El.
      { cbn [pad_state]. rewrite pad_state_feed_lazy. reflexivity. }
      { cbn [close_reopen open_kind fst snd pad_state].
        rewrite finish_pad_quote. reflexivity. } } }
  (* div: the close test reads the line, never the offset, and the
     descent passes both through untouched *)
  { cbn [pad_state step_fuel open_line]. rewrite (pad_state_in_fence k dinner).
    destruct (negb (in_fence dinner) && div_close dlen l)%bool.
    { cbn [fst snd pad_state]. rewrite (pad_state_finish k dinner). reflexivity. }
    { rewrite (IH k off l dinner).
      destruct (step_fuel n off l dinner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. reflexivity. } }
  (* list: every recorded column lives here *)
  { cbn [pad_state step_fuel open_line].
    destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_state_blank_absorbed.
      destruct (blank_absorbed inner); [reflexivity|].
      rewrite pad_list_blank. reflexivity. }
    all: cbn [ls_indent]; rewrite <- Nat.add_assoc, ltb_add_mono_l.
    all: destruct (Nat.ltb (ls_indent ls) (off + indent_of l)) eqn:Elt.
    (* thematic *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_state_div_closer.
      destruct (div_closer l inner);
        [rewrite pad_list_blank | rewrite pad_list_content]; reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      rewrite finish_pad_list. reflexivity. }
    (* fence *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_state_div_closer.
      destruct (div_closer l inner);
        [rewrite pad_list_blank | rewrite pad_list_content]; reflexivity. }
    { cbn [close_reopen open_fence fst snd pad_state].
      rewrite finish_pad_list, Nat.add_assoc. reflexivity. }
    (* div *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_state_div_closer.
      destruct (div_closer l inner);
        [rewrite pad_list_blank | rewrite pad_list_content]; reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      destruct (@bdivs K); cbn [close_reopen fst snd pad_state];
      rewrite finish_pad_list; reflexivity. }
    (* quote *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_state_div_closer.
      destruct (div_closer l inner);
        [rewrite pad_list_blank | rewrite pad_list_content]; reflexivity. }
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
      cbn [fst snd pad_state]. rewrite pad_state_div_closer.
      destruct (div_closer l inner);
        [rewrite pad_list_blank | rewrite pad_list_content]; reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      rewrite finish_pad_list. reflexivity. }
    (* list marker *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_state_div_closer.
      destruct (div_closer l inner);
        [rewrite pad_list_blank | rewrite pad_list_content]; reflexivity. }
    { cbn [ls_styles].
      destruct (narrow (ls_styles ls) (configured_list_styles m chk))
        as [|s0 ss] eqn:Em.
      { rewrite <- !Nat.add_assoc.
        pose proof (IH k (off + consumed l (configured_list_rest chk mr))
                      (configured_list_rest chk mr) (PPara [])) as H;
          cbn [pad_state] in H; rewrite H.
        destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara []))
          as [bs inner'] eqn:Ed.
        cbn [close_reopen open_list fst snd pad_state].
        rewrite finish_pad_list. reflexivity. }
      { rewrite <- Nat.add_assoc, (pad_state_finish k inner).
        pose proof (IH k (off + consumed l (configured_list_rest chk mr))
                      (configured_list_rest chk mr) (PPara [])) as H;
          cbn [pad_state] in H; rewrite H.
        destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                    (configured_list_rest chk mr) (PPara []))
          as [bs inner'] eqn:Ed.
        cbn [fst snd pad_state].
        rewrite pad_list_narrow, pad_list_next. reflexivity. } }
    (* attribute spec *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_state_div_closer.
      destruct (div_closer l inner);
        [rewrite pad_list_blank | rewrite pad_list_content]; reflexivity. }
    { unfold open_attr. destruct (@battrs K);
        cbn [close_reopen fst snd pad_state];
        rewrite ?Nat.add_assoc, finish_pad_list; reflexivity. }
    (* footnote definition *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_state_div_closer.
      destruct (div_closer l inner);
        [rewrite pad_list_blank | rewrite pad_list_content]; reflexivity. }
    { rewrite <- !Nat.add_assoc.
      pose proof (IH k (off + consumed l frest) frest (PPara [])) as H;
        cbn [pad_state] in H; rewrite H.
      destruct (step_fuel n (off + consumed l frest) frest (PPara []))
        as [bs inner'] eqn:Ed.
      unfold open_foot. destruct (@bfootnotes K);
        cbn [close_reopen fst snd pad_state]; rewrite finish_pad_list; reflexivity. }
    (* reference definition *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_state_div_closer.
      destruct (div_closer l inner);
        [rewrite pad_list_blank | rewrite pad_list_content]; reflexivity. }
    { cbn [close_reopen open_ref fst snd pad_state].
      rewrite Nat.add_assoc, finish_pad_list. reflexivity. }
    (* table row *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_state_div_closer.
      destruct (div_closer l inner);
        [rewrite pad_list_blank | rewrite pad_list_content]; reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      destruct (@btables K); cbn [close_reopen fst snd pad_state];
        rewrite finish_pad_list; reflexivity. }
    (* text *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_state_div_closer.
      destruct (div_closer l inner);
        [rewrite pad_list_blank | rewrite pad_list_content]; reflexivity. }
    { cbn [is_lazy]. rewrite pad_state_lazy_ok.
      destruct (lazy_ok inner) eqn:El.
      { cbn [pad_state]. rewrite pad_state_feed_lazy. reflexivity. }
      { cbn [close_reopen open_kind fst snd pad_state].
        rewrite finish_pad_list. reflexivity. } } }
  (* attribute spec: it records no column, and neither does anything it
     turns into *)
  { cbn [pad_state step_fuel open_line].
    destruct (ap_done aap).
    { pose proof (IH k off l (PPend (attr_merge (ap_attrs aap) apend) (PPara [])))
        as H; cbn [pad_state] in H; rewrite H; reflexivity. }
    { rewrite <- Nat.add_assoc, ltb_add_mono_l.
      destruct (Nat.ltb aind (off + indent_of l)).
      { destruct (ap_failed (attr_feed l aap)); [|reflexivity].
        pose proof (IH k off l (PPara aslices)) as H;
          cbn [pad_state] in H; rewrite H; reflexivity. }
      { pose proof (IH k off l (PPara aslices)) as H;
          cbn [pad_state] in H; rewrite H; reflexivity. } } }
  (* reference definition: its column shifts with the run, and the line
     that ends it is reprocessed from idle *)
  { cbn [pad_state step_fuel open_line]. rewrite <- Nat.add_assoc, ltb_add_mono_l.
    destruct (if Nat.ltb rind (off + indent_of l) then ref_cont l else None);
      [reflexivity|].
    pose proof (IH k off l (PPara [])) as H; cbn [pad_state] in H; rewrite H.
    destruct (step_fuel n off l (PPara [])) as [bs st'] eqn:Ed.
    cbn [fst snd pad_state]. reflexivity. }
  (* footnote definition: its opener column shifts, while its contents
     follow the same shifted run recursively *)
  { cbn [pad_state step_fuel open_line].
    destruct (is_blank l).
    { rewrite (IH k off l finner).
      destruct (step_fuel n off l finner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. reflexivity. }
    { rewrite <- Nat.add_assoc, ltb_add_mono_l.
      destruct (Nat.ltb find (off + indent_of l)).
      { rewrite (IH k off l finner).
        destruct (step_fuel n off l finner) as [bs inner'] eqn:Ed.
        cbn [fst snd pad_state]. reflexivity. }
      { pose proof (IH k off l (PPara [])) as H;
          cbn [pad_state] in H; rewrite H.
        destruct (step_fuel n off l (PPara [])) as [bs st'] eqn:Ed.
        cbn [fst snd pad_state]. rewrite (pad_state_finish k finner). reflexivity. } } }
  (* table: it records no column, and the line that ends it is
     reprocessed from idle *)
  { cbn [pad_state step_fuel open_line].
    destruct tcap as [| |ls].
    { destruct (caption_open l) as [rest|]; [reflexivity|].
      destruct (is_blank l); [reflexivity|].
      destruct (classify l) eqn:E; cbn [open_line is_lazy]; try reflexivity;
        (pose proof (IH k off l (PPara [])) as H;
         cbn [pad_state] in H; rewrite H;
         destruct (step_fuel n off l (PPara [])) as [bs st'] eqn:Ed;
         cbn [fst snd pad_state]; reflexivity). }
    { destruct (caption_open l) as [rest|]; [reflexivity|].
      destruct (is_blank l); [reflexivity|].
      destruct (classify l) eqn:E; cbn [open_line is_lazy];
        (pose proof (IH k off l (PPara [])) as H;
         cbn [pad_state] in H; rewrite H;
         destruct (step_fuel n off l (PPara [])) as [bs st'] eqn:Ed;
         cbn [fst snd pad_state]; reflexivity). }
    { destruct (is_blank l); reflexivity. } }
  (* pending attributes: transparent to the shift, since they carry no
     column and the block they decorate carries its own *)
  { cbn [pad_state step_fuel open_line]. rewrite (pad_state_is_idle k pinner).
    destruct (classify l) eqn:E; cbn [open_line is_lazy];
      try (destruct (is_idle pinner);
           [unfold open_attr; destruct (@battrs K); cbn [fst snd pad_state];
             rewrite ?Nat.add_assoc; reflexivity|]);
      rewrite (IH k off l pinner);
      destruct (step_fuel n off l pinner) as [bs st'] eqn:Ed;
      cbn [pend_result fst snd pad_state];
      destruct bs; reflexivity. }
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

Lemma step_fence_close :
  forall l f ind acc, fence_close f l = true ->
  step l (PFence f ind acc) = ([fence_block f (rev acc)], PPara []).
Proof. intros l f ind acc H. unfold step. cbn [step_fuel open_line]. rewrite H. reflexivity. Qed.

(* The content line keeps what it is indented past the fence's own
   column.  `step` runs at offset 0, so that column is the whole of the
   subtraction here; inside a container `step_fuel` sees the offset the
   prefixes ate and takes the difference. *)
Lemma step_fence_content :
  forall l f ind acc, fence_close f l = false ->
  step l (PFence f ind acc) = ([], PFence f ind (drop_ws_upto ind l :: acc)).
Proof.
  intros l f ind acc H. unfold step. cbn [step_fuel open_line]. rewrite H, Nat.sub_0_r.
  reflexivity.
Qed.

(* At an idle state every non-quote kind opens its block. *)
Lemma step_idle :
  forall l k, classify l = k -> direct_open k = true ->
  step l (PPara []) = open_kind l k.
Proof.
  intros l k H Hk. unfold step. cbn [step_fuel]. rewrite H.
  apply open_line_direct, Hk.
Qed.

(* An open paragraph is flushed by a blank line and by nothing else. *)
Lemma step_para_flush :
  forall l c cur', classify l = KBlank ->
  step l (PPara (c :: cur')) =
  ([mk (Para (para_inlines (rev (c :: cur'))))], PPara []).
Proof.
  intros l c cur' H. unfold step. cbn [step_fuel open_line].
  rewrite (bunderline_of_blank l (classify_kblank_blank l H)), H. reflexivity.
Qed.

(* Any other line continues it -- unless a setting says the line ends a
   paragraph, which is the whole of what `bcuts` answers. *)
Lemma step_para_cont :
  forall l c cur', classify l <> KBlank -> bcuts l = false ->
  step l (PPara (c :: cur')) = ([], PPara (drop_leading_ws l :: c :: cur')).
Proof.
  intros l c cur' H Hc. unfold step. cbn [step_fuel open_line].
  unfold bcuts in Hc. destruct (bunderline_of l); [discriminate|].
  destruct (classify l) eqn:E; try (congruence || reflexivity).
  rewrite Hc. reflexivity.
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
  intros l rest bs inner H Hr. unfold step at 1. cbn [step_fuel open_line]. rewrite H. cbn [open_line].
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
  cbn [step_fuel open_line pstate_depth]. rewrite H.
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
  intros l done inner H Hl. unfold step. cbn [step_fuel open_line]. rewrite H.
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
  intros l k done inner bs st' H Hk Hlz Ho. unfold step. cbn [step_fuel open_line].
  rewrite H.
  destruct k; try discriminate; rewrite Hlz; rewrite Ho; reflexivity.
Qed.

(*
An open div
-----------

Two equations, not seven: a div does not classify the line at all.  The
close test decides, and everything else descends unchanged.  This is the
whole of the div's continuation rule, and it is why the container needs
no share of the pad layer. *)

Lemma step_div_close :
  forall l len cls done inner,
    in_fence inner = false -> div_close len l = true ->
    step l (PDiv len cls done inner)
    = ([div_block cls (rev done ++ finish inner)%list], PPara []).
Proof.
  intros l len cls done inner Hf H. unfold step. cbn [step_fuel open_line].
  rewrite Hf, H. reflexivity.
Qed.

Lemma step_div_cont :
  forall l len cls done inner bs inner',
    (negb (in_fence inner) && div_close len l)%bool = false ->
    step l inner = (bs, inner') ->
    step l (PDiv len cls done inner)
    = ([], PDiv len cls (rev bs ++ done)%list inner').
Proof.
  intros l len cls done inner bs inner' H Hr. unfold step at 1.
  cbn [step_fuel open_line pstate_depth]. rewrite H.
  rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
  rewrite Hr. reflexivity.
Qed.

(* A blank line never closes a div, whichever way the tip test goes. *)
Lemma div_stays_open_blank :
  forall l inner len,
    is_blank l = true ->
    (negb (in_fence inner) && div_close len l)%bool = false.
Proof.
  intros l inner len H. rewrite (div_close_blank len l H).
  apply Bool.andb_false_r.
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
  forall l sty core chk rest bs inner,
    classify l = KList sty core chk rest ->
    step (configured_list_rest chk rest) (PPara []) = (bs, inner) ->
    step l (PPara []) =
      ([], PList (LSt (indent_of l)
                      (with_starts (configured_list_styles sty chk) core)
                      false false [] (configured_list_check chk) [])
             (rev bs)
             (pad_state (consumed l (configured_list_rest chk rest)) inner)).
Proof.
  intros l sty core chk rest bs inner H Hr. unfold step at 1. cbn [step_fuel open_line].
  rewrite H. cbn [open_line].
  change (step_fuel ?n (0 + consumed l (configured_list_rest chk rest))
            (configured_list_rest chk rest) (PPara []))
    with (step_fuel n (consumed l (configured_list_rest chk rest))
            (configured_list_rest chk rest) (PPara [])).
  rewrite (step_fuel_enough_off _ (consumed l (configured_list_rest chk rest))
             (configured_list_rest chk rest) (PPara []))
    by (cbn [pstate_depth];
        pose proof (configured_list_rest_length _ _ _ _ _ H); lia).
  change (step_fuel
            (S (String.length (configured_list_rest chk rest)
                + pstate_depth (PPara [])))
            (consumed l (configured_list_rest chk rest))
            (configured_list_rest chk rest) (PPara []))
    with (step_at (consumed l (configured_list_rest chk rest))
            (configured_list_rest chk rest) (PPara [])).
  rewrite step_at_idle, Hr. reflexivity.
Qed.

(* The blank arms this list only when the item has nothing open to absorb
   it first; `blank_absorbed inner` is the test. *)
Lemma step_list_blank :
  forall l ls done inner bs inner',
    classify l = KBlank ->
    step l inner = (bs, inner') ->
    step l (PList ls done inner) =
    ([], PList (if blank_absorbed inner then ls else list_blank ls)
               (rev bs ++ done)%list inner').
Proof.
  intros l ls done inner bs inner' H Hr. unfold step at 1.
  cbn [step_fuel open_line pstate_depth]. rewrite H.
  rewrite step_fuel_enough by (cbn [pstate_depth]; lia).
  rewrite Hr. reflexivity.
Qed.

(* The conclusion carries the closer test rather than excluding it by
   hypothesis: the one line this rule has to get right is a div's closer,
   so a `div_closer l inner = false` precondition would have to be
   discharged precisely where it is false. *)
Lemma step_list_indented :
  forall l k ls done inner bs inner',
    classify l = k -> k <> KBlank ->
    Nat.ltb (ls_indent ls) (indent_of l) = true ->
    step l inner = (bs, inner') ->
    step l (PList ls done inner) =
    ([], PList (if div_closer l inner then list_blank ls else list_content ls k)
           (rev bs ++ done)%list inner').
Proof.
  intros l k ls done inner bs inner' H Hk Hind Hr. unfold step at 1.
  cbn [step_fuel open_line pstate_depth]. rewrite H, !Nat.add_0_l.
  destruct k eqn:Ek; try congruence;
    rewrite Hind;
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia);
    rewrite Hr; reflexivity.
Qed.

Lemma step_list_sibling :
  forall l sty core chk rest ls done inner bs inner' s0 ss,
    classify l = KList sty core chk rest ->
    narrow (ls_styles ls) (configured_list_styles sty chk) = s0 :: ss ->
    Nat.ltb (ls_indent ls) (indent_of l) = false ->
    step (configured_list_rest chk rest) (PPara []) = (bs, inner') ->
    step l (PList ls done inner) =
    ([], PList (list_next (list_narrow ls (s0 :: ss))
                  (rev done ++ finish inner)%list (configured_list_check chk)
                  (configured_list_rest chk rest))
           (rev bs)
           (pad_state (consumed l (configured_list_rest chk rest)) inner')).
Proof.
  intros l sty core chk rest ls done inner bs inner' s0 ss H Hm Hind Hr.
  unfold step at 1.
  cbn [step_fuel open_line pstate_depth]. rewrite H, !Nat.add_0_l, Hind, Hm.
  change (step_fuel ?n (0 + consumed l (configured_list_rest chk rest))
            (configured_list_rest chk rest) (PPara []))
    with (step_fuel n (consumed l (configured_list_rest chk rest))
            (configured_list_rest chk rest) (PPara [])).
  rewrite (step_fuel_enough_off _ (consumed l (configured_list_rest chk rest))
             (configured_list_rest chk rest) (PPara []))
    by (cbn [pstate_depth];
        pose proof (configured_list_rest_length _ _ _ _ _ H); lia).
  change (step_fuel
            (S (String.length (configured_list_rest chk rest)
                + pstate_depth (PPara [])))
            (consumed l (configured_list_rest chk rest))
            (configured_list_rest chk rest) (PPara []))
    with (step_at (consumed l (configured_list_rest chk rest))
            (configured_list_rest chk rest) (PPara [])).
  rewrite step_at_idle, Hr. reflexivity.
Qed.

Lemma step_list_diffstyle :
  forall l sty core chk rest ls done inner bs inner',
    classify l = KList sty core chk rest ->
    narrow (ls_styles ls) (configured_list_styles sty chk) = [] ->
    Nat.ltb (ls_indent ls) (indent_of l) = false ->
    step (configured_list_rest chk rest) (PPara []) = (bs, inner') ->
    step l (PList ls done inner) =
    (finish (PList ls done inner),
     PList (LSt (indent_of l)
                (with_starts (configured_list_styles sty chk) core)
                false false [] (configured_list_check chk) []) (rev bs)
       (pad_state (consumed l (configured_list_rest chk rest)) inner')).
Proof.
  intros l sty core chk rest ls done inner bs inner' H Hm Hind Hr.
  unfold step at 1.
  cbn [step_fuel open_line pstate_depth]. rewrite H, !Nat.add_0_l, Hind, Hm.
  change (step_fuel ?n (0 + consumed l (configured_list_rest chk rest))
            (configured_list_rest chk rest) (PPara []))
    with (step_fuel n (consumed l (configured_list_rest chk rest))
            (configured_list_rest chk rest) (PPara [])).
  rewrite (step_fuel_enough_off _ (consumed l (configured_list_rest chk rest))
             (configured_list_rest chk rest) (PPara []))
    by (cbn [pstate_depth];
        pose proof (configured_list_rest_length _ _ _ _ _ H); lia).
  change (step_fuel
            (S (String.length (configured_list_rest chk rest)
                + pstate_depth (PPara [])))
            (consumed l (configured_list_rest chk rest))
            (configured_list_rest chk rest) (PPara []))
    with (step_at (consumed l (configured_list_rest chk rest))
            (configured_list_rest chk rest) (PPara [])).
  rewrite step_at_idle, Hr. reflexivity.
Qed.

(* An attribute spec is not `direct_open` — it records a column, so it
   opens through `open_attr` rather than `open_kind` — which is why it
   needs its own pair of equations, exactly as a quote does. *)
(* Stated through `open_attr` rather than through `PAttr`, because the
   spec opens only where the capability is on and the two consumers below
   need the equation at either setting. *)
Lemma step_attr_open :
  forall l ap, classify l = KAttr ap ->
  step l (PPara []) = open_attr [] (indent_of l) ap l.
Proof. intros l ap H. unfold step. cbn [step_fuel open_line]. rewrite H. reflexivity. Qed.

Lemma step_list_attr_close :
  forall l ap ls done inner,
    classify l = KAttr ap ->
    Nat.ltb (ls_indent ls) (indent_of l) = false ->
    step l (PList ls done inner)
    = (finish (PList ls done inner), snd (open_attr [] (indent_of l) ap l)).
Proof.
  intros l ap ls done inner H Hind. unfold step. cbn [step_fuel open_line pstate_depth].
  rewrite H, !Nat.add_0_l, Hind.
  unfold close_reopen, open_attr. destruct (@battrs K); cbn [fst snd];
    rewrite app_nil_r; reflexivity.
Qed.

(* A footnote definition consumes its opener and then parses the residue
   as the first body line, just like a quote parses its stripped line. *)
Lemma step_foot_open :
  forall l lbl rest bs inner,
    classify l = KFoot lbl rest ->
    step rest (PPara []) = (bs, inner) ->
    step l (PPara []) =
      open_foot l (indent_of l) lbl (bs, pad_state (consumed l rest) inner).
Proof.
  intros l lbl rest bs inner H Hr. unfold step at 1. cbn [step_fuel open_line].
  rewrite H. cbn [open_line].
  change (step_fuel ?n (0 + consumed l rest) rest (PPara []))
    with (step_fuel n (consumed l rest) rest (PPara [])).
  rewrite (step_fuel_enough_off _ (consumed l rest) rest (PPara []))
    by (cbn [pstate_depth]; pose proof (classify_foot_length _ _ _ H); lia).
  change (step_fuel (S (String.length rest + pstate_depth (PPara [])))
            (consumed l rest) rest (PPara []))
    with (step_at (consumed l rest) rest (PPara [])).
  rewrite step_at_idle, Hr. reflexivity.
Qed.

Lemma step_list_foot_close :
  forall l lbl rest ls done inner bs inner',
    classify l = KFoot lbl rest ->
    Nat.ltb (ls_indent ls) (indent_of l) = false ->
    step rest (PPara []) = (bs, inner') ->
    step l (PList ls done inner) =
      (finish (PList ls done inner),
       snd (open_foot l (indent_of l) lbl
              (bs, pad_state (consumed l rest) inner'))).
Proof.
  intros l lbl rest ls done inner bs inner' H Hind Hr.
  unfold step at 1. cbn [step_fuel open_line pstate_depth].
  rewrite H, !Nat.add_0_l, Hind.
  change (step_fuel ?n (0 + consumed l rest) rest (PPara []))
    with (step_fuel n (consumed l rest) rest (PPara [])).
  rewrite (step_fuel_enough_off _ (consumed l rest) rest (PPara []))
    by (cbn [pstate_depth]; pose proof (classify_foot_length _ _ _ H); lia).
  change (step_fuel (S (String.length rest + pstate_depth (PPara [])))
            (consumed l rest) rest (PPara []))
    with (step_at (consumed l rest) rest (PPara [])).
  rewrite step_at_idle, Hr. rewrite close_reopen_foot. reflexivity.
Qed.

(* And a reference definition is not `direct_open` either, for the same
   reason and with the same pair of equations. *)
Lemma step_ref_open :
  forall l lbl v, classify l = KRef lbl v ->
  step l (PPara []) = ([], PRef (indent_of l) lbl v).
Proof. intros l lbl v H. unfold step. cbn [step_fuel open_line]. rewrite H. reflexivity. Qed.

(* A code fence is not `direct_open` either, and for the same reason: it
   records the column its border sits at, so it opens through
   `open_fence`. *)
Lemma step_fence_open :
  forall l f, classify l = KFence f ->
  step l (PPara []) = ([], PFence f (indent_of l) []).
Proof. intros l f H. unfold step. cbn [step_fuel open_line]. rewrite H. reflexivity. Qed.

(* A blank line closes an open definition, emitting it, and leaves the
   idle state: `ref_cont` refuses a blank line at any column. *)
Lemma step_ref_blank :
  forall l ind lbl v, classify l = KBlank ->
  step l (PRef ind lbl v) = ([ref_block lbl v], PPara []).
Proof.
  intros l ind lbl v H. unfold step. cbn [step_fuel open_line].
  rewrite (ref_cont_blank l (classify_kblank_blank l H)),
          step_fuel_enough by (cbn [pstate_depth]; lia).
  rewrite (step_idle l KBlank H eq_refl).
  destruct (Nat.ltb ind (0 + indent_of l)); reflexivity.
Qed.

(*
Table transitions
-----------------

A table records no column, so all four rules read off the line alone --
`step_fuel`'s offset appears in none of them.  The close rule needs no
`step_fuel_enough` either: a table is one level deep, so the fuel left
for the reprocessed line is exactly `step`'s own.
*)

Lemma step_row_open :
  forall l r, btables = true -> classify l = KRow r ->
    step l (PPara []) = ([], PTable [r] TOpen).
Proof.
  intros l r Htables H.
  rewrite (step_idle l (KRow r) H eq_refl).
  cbn [open_kind]. rewrite Htables. reflexivity.
Qed.

Lemma step_row_disabled :
  forall l r, btables = false -> classify l = KRow r ->
    step l (PPara []) = ([], PPara [drop_leading_ws l]).
Proof.
  intros l r Htables H.
  rewrite (step_idle l (KRow r) H eq_refl).
  cbn [open_kind]. rewrite Htables. reflexivity.
Qed.

Lemma step_table_row :
  forall l rows r,
    caption_open l = None -> is_blank l = false -> classify l = KRow r ->
    step l (PTable rows TOpen) = ([], PTable (r :: rows) TOpen).
Proof.
  intros l rows r Hc Hb H. unfold step. cbn [step_fuel open_line].
  rewrite Hc, Hb, H. reflexivity.
Qed.

Lemma step_table_blank :
  forall l rows, is_blank l = true ->
  step l (PTable rows TOpen) = ([], PTable rows TAfterBlank).
Proof.
  intros l rows H. unfold step. cbn [step_fuel open_line].
  rewrite (caption_open_blank l H), H. reflexivity.
Qed.

Lemma step_table_close :
  forall l rows bs st',
    caption_open l = None -> is_blank l = false ->
    step l (PPara []) = (bs, st') ->
    step l (PTable rows TAfterBlank)
    = (table_block (rev rows) TAfterBlank :: bs, st')%list.
Proof.
  intros l rows bs st' Hc Hb Hs. unfold step at 1. cbn [step_fuel open_line pstate_depth].
  rewrite Hc, Hb.
  replace (String.length l + 1) with (S (String.length l + 0)) by lia.
  change (step_fuel (S (String.length l + 0)) 0 l (PPara []))
    with (step l (PPara [])).
  rewrite Hs. destruct (classify l); reflexivity.
Qed.

Lemma step_list_ref_close :
  forall l lbl v ls done inner,
    classify l = KRef lbl v ->
    Nat.ltb (ls_indent ls) (indent_of l) = false ->
    step l (PList ls done inner)
    = (finish (PList ls done inner), PRef (indent_of l) lbl v).
Proof.
  intros l lbl v ls done inner H Hind. unfold step. cbn [step_fuel open_line pstate_depth].
  rewrite H, !Nat.add_0_l, Hind.
  cbn [close_reopen open_ref]. rewrite app_nil_r. reflexivity.
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
  unfold step at 1. cbn [step_fuel open_line pstate_depth].
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

(* A code fence at or left of the marker closes the list and opens at its
   own column, the same way `step_list_quote_close` does for a quote. *)
Lemma step_list_fence_close :
  forall l f ls done inner,
    classify l = KFence f ->
    Nat.ltb (ls_indent ls) (indent_of l) = false ->
    step l (PList ls done inner) =
      (finish (PList ls done inner), PFence f (indent_of l) []).
Proof.
  intros l f ls done inner H Hind. unfold step. cbn [step_fuel open_line].
  rewrite H, !Nat.add_0_l, Hind. cbn [close_reopen open_fence].
  rewrite app_nil_r. reflexivity.
Qed.

Lemma step_list_lazy :
  forall l ls done inner,
    classify l = KText -> Nat.ltb (ls_indent ls) (indent_of l) = false ->
    lazy_ok inner = true ->
    step l (PList ls done inner) = ([], PList ls done (feed_lazy l inner)).
Proof.
  intros l ls done inner H Hind Hl. unfold step. cbn [step_fuel open_line].
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
  intros l k ls done inner bs st' H Hk Hnb Hind Hlz Ho. unfold step. cbn [step_fuel open_line].
  rewrite H, !Nat.add_0_l.
  destruct k;
    [congruence | idtac | discriminate | idtac | discriminate | idtac
    | discriminate | discriminate | discriminate | discriminate | idtac
    | idtac];
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

An open fence pays for it with a side condition rather than an
exclusion.  It strips its own column from every content line, and the two
sides here carry the *same* state, so the padded side strips from a line
that is `String.length p` characters longer while subtracting the same
column: the two agree exactly when the fence sits at or right of where the
padded line starts.  `fence_cols_ok` is that condition, and `pad_safe` is
what is left once the fence no longer needs excluding.  Both stop at
`PQuote`, because a quote prefix absorbs the pad before handing down its
residue. *)

(* Every fence open in this state sits at column `off` or further right.
   `step_fuel_pad` asks it of `String.length p + off`, and the two ways of
   supplying it are the two ways the lemma is used: at the top level `off`
   is 0 and `pad_state` has moved every column by `String.length p`
   (`fence_cols_ok_pad_state`), or there is no fence and it is vacuous. *)
Fixpoint fence_cols_ok (off : nat) (st : pstate) : bool :=
  match st with
  | PFence _ ind _ => Nat.leb off ind
  | PList _ _ inner | PDiv _ _ _ inner | PFoot _ _ _ inner | PPend _ inner =>
      fence_cols_ok off inner
  | _ => true
  end.

(* Column zero is left of everything, which is what makes the condition
   free at `step`. *)
Lemma fence_cols_ok_0 : forall st, fence_cols_ok 0 st = true.
Proof.
  induction st as [| | | |dlen dcls ddone dinner IH|ls done inner IH| | |find flbl fdone finner IH|trows tcap|ppend pinner IH];
    cbn [fence_cols_ok]; try reflexivity; assumption.
Qed.

Lemma fence_cols_ok_pad_state :
  forall k off st, fence_cols_ok (k + off) (pad_state k st) = fence_cols_ok off st.
Proof.
  intros k off st.
  induction st as [| |f ind acc| |dlen dcls ddone dinner IH|ls done inner IH| | |find flbl fdone finner IH|trows tcap|ppend pinner IH];
    cbn [pad_state fence_cols_ok]; try reflexivity; try assumption.
  destruct (Nat.leb off ind) eqn:E.
  - apply Nat.leb_le. apply Nat.leb_le in E. lia.
  - apply Nat.leb_gt. apply Nat.leb_gt in E. lia.
Qed.

(* A lazy line's pad is dropped wherever the line comes to rest -- the
   reason feed_lazy strips leading whitespace at all. *)
Lemma feed_lazy_ws_prefix :
  forall p l st,
    is_blank p = true -> feed_lazy (p ++ l) st = feed_lazy l st.
Proof.
  intros p l st Hp.
  induction st as [cur|lvl cur| |done inner IH|dlen dcls ddone dinner IH|ls done inner IH|apend aind aap aslices|rind rlbl rval|find flbl fdone finner IH|trows tcap|ppend pinner IH];
    cbn [feed_lazy];
    try (rewrite (drop_leading_ws_ws_prefix p l Hp); reflexivity);
    try (rewrite IH; reflexivity).
  all: reflexivity.
Qed.

Fixpoint pad_safe (st : pstate) : bool :=
  match st with
  (* PList and PDiv both hand the line down unchanged, so a pad reaches
     whatever they contain; PQuote strips its prefix, so it never does. *)
  | PList _ _ inner => pad_safe inner
  | PDiv _ _ _ inner => pad_safe inner
  | PFoot _ _ _ inner => pad_safe inner
  | PPend _ inner => pad_safe inner
  (* PAttr is the whole of the exclusion now, and it is not
     `step_fuel_pad` that wants it: a pad is invisible to a spec, but a
     *blank* line inside an open one is a continuation line rather than a
     close, so `step_blank_finish` fails.  Nothing a canonical rendering
     emits opens a spec. *)
  | PAttr _ _ _ _ => false
  | _ => true
  end.

(* The other half of what `pad_safe` used to be, and the reason the two
   were worth separating: "a blank line closes whatever this state has
   open".  A spec fails it because a blank inside one is a continuation
   line, and a fence because a blank inside one is content.  Where
   `pad_safe` is asked of *every* line of a run, this is asked only of the
   state a run ends in -- so an item may contain a code block and still
   satisfy it, which is exactly the case the fence exclusion used to
   cost.  It is strictly stronger than `pad_safe`, but nothing needs to
   say so: `run_safe` carries both, each where it is wanted. *)
Fixpoint blank_safe (st : pstate) : bool :=
  match st with
  | PFence _ _ _ => false
  | PAttr _ _ _ _ => false
  | PList _ _ inner | PDiv _ _ _ inner | PFoot _ _ _ inner | PPend _ inner =>
      blank_safe inner
  | _ => true
  end.

Lemma fence_cols_ok_pad :
  forall k st, fence_cols_ok k (pad_state k st) = true.
Proof.
  intros k st. rewrite <- (Nat.add_0_r k) at 1.
  rewrite fence_cols_ok_pad_state. apply fence_cols_ok_0.
Qed.

Lemma step_fuel_pad :
  forall n p off l st,
    is_blank p = true ->
    pad_safe st = true ->
    fence_cols_ok (String.length p + off) st = true ->
    step_fuel n off (p ++ l) st = step_fuel n (String.length p + off) l st.
Proof.
  induction n as [|n IH]; intros p off l st Hp Hsafe Hcol; [reflexivity|].
  (* natural subtraction truncates, so this needs the residue to be no
     longer than the line -- which classify always gives *)
  assert (Hc : forall rest, String.length rest <= String.length l ->
                 consumed (p ++ l) rest = String.length p + consumed l rest).
  { intros rest Hle. unfold consumed. rewrite length_append. lia. }
  destruct st as [cur|hlvl hcur|f fnd acc|done inner|dlen dcls ddone dinner|ls done inner|apend aind aap aslices|rind rlbl rval|find flbl fdone finner|trows tcap|ppend pinner].
  { cbn [step_fuel open_line]. rewrite (classify_ws_prefix p l Hp).
    destruct cur as [|c cur'].
    { destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy];
        try reflexivity.
      { (* fence: opens at the column its border sits at *)
        unfold open_fence. rewrite (indent_of_ws_prefix p l Hp), Nat.add_assoc,
          (Nat.add_comm off (String.length p)). reflexivity. }
      { cbn [open_kind]. rewrite (drop_leading_ws_ws_prefix p l Hp).
        destruct (@bdivs K); reflexivity. }
      { rewrite (Hc rest ltac:(pose proof (classify_quote_length _ _ E); lia)),
                Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
      { rewrite (Hc (configured_list_rest chk mr)
                   ltac:(pose proof (configured_list_rest_length _ _ _ _ _ E); lia)),
                (indent_of_ws_prefix p l Hp), !Nat.add_assoc, (Nat.add_comm off (String.length p)).
        reflexivity. }
      { unfold open_attr. rewrite (indent_of_ws_prefix p l Hp),
          (drop_leading_ws_ws_prefix p l Hp), Nat.add_assoc,
          (Nat.add_comm off (String.length p)). reflexivity. }
      { unfold open_foot.
        rewrite (Hc frest ltac:(pose proof (classify_foot_length _ _ _ E); lia)),
                (indent_of_ws_prefix p l Hp), ?(drop_leading_ws_ws_prefix p l Hp),
                !Nat.add_assoc, (Nat.add_comm off (String.length p)).
        reflexivity. }
      { unfold open_ref. rewrite (indent_of_ws_prefix p l Hp), Nat.add_assoc,
          (Nat.add_comm off (String.length p)). reflexivity. }
      { cbn [open_kind]. rewrite (drop_leading_ws_ws_prefix p l Hp).
        reflexivity. }
      { cbn [open_kind]. rewrite (drop_leading_ws_ws_prefix p l Hp).
        reflexivity. } }
    { rewrite (bunderline_of_ws_prefix p l Hp).
      destruct (bunderline_of l) as [ulvl|] eqn:Eu; [reflexivity|].
      destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy];
        try (cbn [open_kind close_reopen];
           rewrite (drop_leading_ws_ws_prefix p l Hp); reflexivity);
        try reflexivity.
      destruct (binterrupt (KList m mc chk mr)) eqn:Ei;
        [|rewrite (drop_leading_ws_ws_prefix p l Hp); reflexivity].
      rewrite (Hc (configured_list_rest chk mr)
                 ltac:(pose proof (configured_list_rest_length _ _ _ _ _ E); lia)),
              (indent_of_ws_prefix p l Hp), !Nat.add_assoc,
              (Nat.add_comm off (String.length p)).
      reflexivity. } }
  { cbn [step_fuel open_line]. rewrite (classify_ws_prefix p l Hp).
    destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy];
      try reflexivity.
    { (* fence: opens at the column its border sits at *)
      cbn [close_reopen]; unfold open_fence.
      rewrite (indent_of_ws_prefix p l Hp), Nat.add_assoc,
        (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [close_reopen open_kind].
      rewrite (drop_leading_ws_ws_prefix p l Hp).
      destruct (@bdivs K); reflexivity. }
    { rewrite (Hc rest ltac:(pose proof (classify_quote_length _ _ E); lia)),
              Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { rewrite (Hc (configured_list_rest chk mr)
                 ltac:(pose proof (configured_list_rest_length _ _ _ _ _ E); lia)),
              (indent_of_ws_prefix p l Hp), !Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [close_reopen]; unfold open_attr. rewrite (indent_of_ws_prefix p l Hp),
        (drop_leading_ws_ws_prefix p l Hp), Nat.add_assoc,
        (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [close_reopen]; unfold open_foot.
      rewrite (Hc frest ltac:(pose proof (classify_foot_length _ _ _ E); lia)),
              (indent_of_ws_prefix p l Hp), ?(drop_leading_ws_ws_prefix p l Hp),
              !Nat.add_assoc, (Nat.add_comm off (String.length p)).
      reflexivity. }
    { cbn [close_reopen]; unfold open_ref. rewrite (indent_of_ws_prefix p l Hp),
        Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [open_kind]. rewrite (drop_leading_ws_ws_prefix p l Hp).
        reflexivity. }
    { cbn [open_kind]. rewrite (drop_leading_ws_ws_prefix p l Hp).
      reflexivity. } }
  (* inside a fence: the close test reads through the pad, and the
     content line strips the pad along with the columns the fence's own
     column asks for -- which is what `fence_cols_ok` leaves room for *)
  { cbn [step_fuel open_line]. rewrite (fence_close_ws_prefix f p l Hp).
    destruct (fence_close f l); [reflexivity|].
    cbn [fence_cols_ok] in Hcol. apply Nat.leb_le in Hcol.
    replace (fnd - off)
      with (String.length p + (fnd - (String.length p + off))) by lia.
    rewrite (drop_ws_upto_ws_prefix p _ l Hp). reflexivity. }
  { cbn [step_fuel open_line]. rewrite (classify_ws_prefix p l Hp).
    destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy];
      try reflexivity.
    { (* fence: opens at the column its border sits at *)
      cbn [close_reopen]; unfold open_fence.
      rewrite (indent_of_ws_prefix p l Hp), Nat.add_assoc,
        (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [close_reopen open_kind].
      rewrite (drop_leading_ws_ws_prefix p l Hp).
      destruct (@bdivs K); reflexivity. }
    { rewrite (Hc rest ltac:(pose proof (classify_quote_length _ _ E); lia)),
              Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { rewrite (Hc (configured_list_rest chk mr)
                 ltac:(pose proof (configured_list_rest_length _ _ _ _ _ E); lia)),
              (indent_of_ws_prefix p l Hp), !Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [close_reopen]; unfold open_attr. rewrite (indent_of_ws_prefix p l Hp),
        (drop_leading_ws_ws_prefix p l Hp), Nat.add_assoc,
        (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [close_reopen]; unfold open_foot.
      rewrite (Hc frest ltac:(pose proof (classify_foot_length _ _ _ E); lia)),
              (indent_of_ws_prefix p l Hp), ?(drop_leading_ws_ws_prefix p l Hp),
              !Nat.add_assoc, (Nat.add_comm off (String.length p)).
      reflexivity. }
    { cbn [close_reopen]; unfold open_ref. rewrite (indent_of_ws_prefix p l Hp),
        Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [is_lazy close_reopen open_kind].
      rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity. }
    { cbn [is_lazy]. destruct (lazy_ok inner);
        [rewrite (feed_lazy_ws_prefix p l _ Hp)|
         cbn [close_reopen open_kind];
         rewrite (drop_leading_ws_ws_prefix p l Hp)]; reflexivity. } }
  (* div: the pad is invisible to the close test and passes through *)
  { cbn [pad_safe] in Hsafe; cbn [fence_cols_ok] in Hcol. cbn [step_fuel open_line].
    rewrite (div_close_ws_prefix p dlen l Hp).
    destruct (negb (in_fence dinner) && div_close dlen l)%bool; [reflexivity|].
    rewrite (IH p off l dinner Hp Hsafe Hcol). reflexivity. }
  { cbn [pad_safe] in Hsafe; cbn [fence_cols_ok] in Hcol. cbn [step_fuel open_line].
    rewrite (classify_ws_prefix p l Hp).
    destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
    { rewrite (IH p off l inner Hp Hsafe Hcol). reflexivity. }
    all: rewrite (indent_of_ws_prefix p l Hp), Nat.add_assoc,
                 (Nat.add_comm off (String.length p)).
    all: destruct (Nat.ltb (ls_indent ls) (String.length p + off + indent_of l))
           eqn:Elt;
         try (rewrite (div_closer_ws_prefix p l inner Hp),
                      (IH p off l inner Hp Hsafe Hcol); reflexivity).
    { reflexivity. }
    { reflexivity. }
    { cbn [is_lazy open_kind close_reopen].
      rewrite (drop_leading_ws_ws_prefix p l Hp).
      destruct (@bdivs K); reflexivity. }
    { rewrite (Hc rest ltac:(pose proof (classify_quote_length _ _ E); lia)),
              Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { reflexivity. }
    { destruct (narrow (ls_styles ls) (configured_list_styles m chk));
        rewrite (Hc (configured_list_rest chk mr)
                   ltac:(pose proof (configured_list_rest_length _ _ _ _ _ E); lia)),
                !Nat.add_assoc, (Nat.add_comm off (String.length p));
        reflexivity. }
    { cbn [close_reopen]; unfold open_attr.
      rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity. }
    { unfold open_foot.
      rewrite (Hc frest ltac:(pose proof (classify_foot_length _ _ _ E); lia)),
              ?(drop_leading_ws_ws_prefix p l Hp),
              Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { reflexivity. }
    { cbn [is_lazy close_reopen open_kind].
      rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity. }
    { cbn [is_lazy]. destruct (lazy_ok inner);
        [rewrite (feed_lazy_ws_prefix p l _ Hp)|
         cbn [close_reopen open_kind];
         rewrite (drop_leading_ws_ws_prefix p l Hp)]; reflexivity. } }
  { discriminate Hsafe. }
  (* reference definition: the pad moves the opener's column, and the
     continuation test reads the line through drop_leading_ws *)
  { cbn [step_fuel open_line]. unfold ref_cont.
    rewrite (indent_of_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp),
      Nat.add_assoc, (Nat.add_comm off (String.length p)).
    destruct (Nat.ltb rind (String.length p + off + indent_of l));
      [destruct (nonempty_str (drop_leading_ws l) && no_ws (drop_leading_ws l))%bool;
       [reflexivity|]|];
      rewrite (IH p off l (PPara []) Hp eq_refl eq_refl); reflexivity. }
  (* footnote definition: padding shifts its opener and is passed through
     recursively to whichever state owns the current body line *)
  { cbn [pad_safe] in Hsafe; cbn [fence_cols_ok] in Hcol. cbn [step_fuel open_line].
    rewrite (is_blank_ws_prefix p l Hp).
    destruct (is_blank l).
    { rewrite (IH p off l finner Hp Hsafe Hcol). reflexivity. }
    { rewrite (indent_of_ws_prefix p l Hp), Nat.add_assoc,
              (Nat.add_comm off (String.length p)).
      destruct (Nat.ltb find (String.length p + off + indent_of l)).
      { rewrite (IH p off l finner Hp Hsafe Hcol). reflexivity. }
      { rewrite (IH p off l (PPara []) Hp eq_refl eq_refl). reflexivity. } } }
  (* table: the pad is invisible to the row scanner and to the caption
     opener alike, and the line that ends the table is reprocessed from
     idle *)
  { cbn [step_fuel open_line]. rewrite (caption_open_ws_prefix p l Hp),
      (is_blank_ws_prefix p l Hp), (classify_ws_prefix p l Hp),
      (drop_leading_ws_ws_prefix p l Hp).
    destruct tcap as [| |ls].
    { destruct (caption_open l); [reflexivity|].
      destruct (is_blank l); [reflexivity|].
      destruct (classify l) eqn:E; cbn [open_line is_lazy]; try reflexivity;
        rewrite (IH p off l (PPara []) Hp eq_refl eq_refl); reflexivity. }
    { destruct (caption_open l); [reflexivity|].
      destruct (is_blank l); [reflexivity|].
      destruct (classify l) eqn:E; cbn [open_line is_lazy];
        rewrite (IH p off l (PPara []) Hp eq_refl eq_refl); reflexivity. }
    { destruct (is_blank l); reflexivity. } }
  (* pending attributes: transparent *)
  { cbn [pad_safe] in Hsafe; cbn [fence_cols_ok] in Hcol. cbn [step_fuel open_line].
    rewrite (classify_ws_prefix p l Hp).
    destruct (classify l) eqn:E; cbn [open_line is_lazy];
      try (destruct (is_idle pinner);
           [unfold open_attr; rewrite (indent_of_ws_prefix p l Hp),
              (drop_leading_ws_ws_prefix p l Hp), Nat.add_assoc,
              (Nat.add_comm off (String.length p)); reflexivity|]);
      rewrite (IH p off l pinner Hp Hsafe Hcol); reflexivity. }
Qed.

(** A blank prefix in front of a line is exactly a shift of its starting
    column. *)
Lemma step_pad :
  forall p l st,
    is_blank p = true -> pad_safe st = true ->
    fence_cols_ok (String.length p) st = true ->
    step (p ++ l) st = step_at (String.length p) l st.
Proof.
  intros p l st Hp Hsafe Hcol. unfold step, step_at.
  rewrite (step_fuel_pad _ p 0 l st Hp Hsafe
             ltac:(rewrite Nat.add_0_r; exact Hcol)), Nat.add_0_r.
  apply step_fuel_enough_off. rewrite length_append. lia.
Qed.

End WithTable.
