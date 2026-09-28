(* ai-disclosure: autonomous *)

(** * Block parsing as an incremental fold

   Block parsing is a fold over classified lines with an explicit state, a
   container stack growing inward: a paragraph accumulator (empty is
   idle), a fence collecting verbatim lines, or a container holding the
   blocks it has closed so far and the state of its contents.  A
   container strips its prefix and `step` re-enters on the enclosed line,
   so a container's contents run the same transition as the top level;
   nesting and uniformity both come from that.

   `step` is the per-line transition and `finish` closes the stack at end
   of input; `parse_lines` is the fold.  The fold's equation lemmas live
   in `Uniformity.v`, the per-branch ones for `step` at the end of this
   file. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast Attributes Marker Inline.
Import ListNotations.

Local Open Scope string_scope.

(** ** Block settings

What the block layer is configurable in, one question per field.  Its
inline counterpart is `InlineTable.dconfig`, a table with a side condition
admissible tables satisfy.  The one overlap between the first two
settings is checked separately by `Invariants.block_prefix_ok`, which
keeps the class computational rather than threading a proof through the
parser.
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
  ; (* Does a colon on a text line pair a label with the block that
       follows?  The one setting that is *non-conservative*: every
       spelling it recognizes is already a valid djot paragraph, so
       turning it on changes documents that parse today.  That is why it
       is off in `djot_bconfig` where every other block setting is on.
       See `.project/keyed-blocks.md`. *)
  bkeyed : bool;
  (* Does a newly opened quote recognize an Obsidian-style callout header? *)
  bcallouts : bool
}.

(* The source line currently being folded.  It is an observation only:
   no parsing decision may inspect it.  The ordinary parser uses line 0;
   the located driver installs a fresh local instance for every line. *)
Class LineIx : Type := LineIxAt { lix : nat }.

#[export] Instance semantic_line_ix : LineIx := LineIxAt 0.

(*
The settings themselves
-----------------------

Named separately from the records that hold them, so that a
configuration reads as a choice per question rather than as a tuple.
*)

(* djot's answers. *)
Local Definition no_interrupt (_ : list lstyle) (_ : string)
  (_ : option task_marker) (_ : string) : bool := false.
Local Definition no_underline (_ : ascii) (_ : nat) : option nat := None.

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
Local Definition setext_underline (c : ascii) (n : nat) : option nat :=
  if Ascii.eqb c "=" then Some 0
  else if Ascii.eqb c "-" then (if Nat.leb 2 n then Some 1 else None)
  else None.

#[export] Instance djot_bconfig : bconfig :=
  BConfig no_interrupt no_underline true true true true true true true
    true false false.

(* Field-local block knobs.  Each preserves the other decisions, which is what
   lets independently justified settings compose without rebuilding a record
   by hand. *)
Definition with_marker_interrupts
  (f : list lstyle -> string -> option task_marker -> string -> bool)
  (K : bconfig) : bconfig :=
  BConfig f (@bunderline K) (@btables K) (@bheading_continues K) (@bdivs K)
    (@btasks K) (@braw_blocks K) (@bdeflists K) (@battrs K)
    (@bfootnotes K) (@bkeyed K) (@bcallouts K).

Definition with_underline
  (f : ascii -> nat -> option nat) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) f (@btables K) (@bheading_continues K)
    (@bdivs K) (@btasks K) (@braw_blocks K) (@bdeflists K) (@battrs K)
    (@bfootnotes K) (@bkeyed K) (@bcallouts K).

Definition with_tables (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) enabled
    (@bheading_continues K) (@bdivs K) (@btasks K) (@braw_blocks K)
    (@bdeflists K) (@battrs K) (@bfootnotes K) (@bkeyed K) (@bcallouts K).

Definition with_heading_continuation (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K) enabled
    (@bdivs K) (@btasks K) (@braw_blocks K) (@bdeflists K) (@battrs K)
    (@bfootnotes K) (@bkeyed K) (@bcallouts K).

Definition with_divs (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) enabled (@btasks K) (@braw_blocks K)
    (@bdeflists K) (@battrs K) (@bfootnotes K) (@bkeyed K) (@bcallouts K).

Definition with_tasks (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) (@bdivs K) enabled (@braw_blocks K)
    (@bdeflists K) (@battrs K) (@bfootnotes K) (@bkeyed K) (@bcallouts K).

Definition with_raw_blocks (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) (@bdivs K) (@btasks K) enabled (@bdeflists K)
    (@battrs K) (@bfootnotes K) (@bkeyed K) (@bcallouts K).

Definition with_deflists (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) (@bdivs K) (@btasks K) (@braw_blocks K) enabled
    (@battrs K) (@bfootnotes K) (@bkeyed K) (@bcallouts K).

Definition with_block_attrs (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) (@bdivs K) (@btasks K) (@braw_blocks K)
    (@bdeflists K) enabled (@bfootnotes K) (@bkeyed K) (@bcallouts K).

(* Exported, but the profile-level `with_footnotes` is what a caller
   should reach for: a reference the document cannot define, or a
   definition nothing can reference, is not a setting anyone wants. *)
Definition with_block_footnotes (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) (@bdivs K) (@btasks K) (@braw_blocks K)
    (@bdeflists K) (@battrs K) enabled (@bkeyed K) (@bcallouts K).

(* Keys are a mode, not a default: see `bkeyed`. *)
Definition with_keyed (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) (@bdivs K) (@btasks K) (@braw_blocks K)
    (@bdeflists K) (@battrs K) (@bfootnotes K) enabled (@bcallouts K).

Definition with_callouts (enabled : bool) (K : bconfig) : bconfig :=
  BConfig (@bmarker_interrupts K) (@bunderline K) (@btables K)
    (@bheading_continues K) (@bdivs K) (@btasks K) (@braw_blocks K)
    (@bdeflists K) (@battrs K) (@bfootnotes K) (@bkeyed K) enabled.

(* Other settings, deliberately not `Instance`s: they are named where
   wanted (`dev/check/Sublist.v`, `dev/check/Setext.v`), so that
   inference here always means djot's. *)
Definition sublist_bconfig : bconfig :=
  with_marker_interrupts prose_safe_markers djot_bconfig.
Definition setext_bconfig : bconfig :=
  with_underline setext_underline djot_bconfig.

(* Keys on, and everything else djot's.  Named here rather than built at
   each use because it is the configuration the whole of
   `.project/keyed-blocks.md` is stated against. *)
Definition keyed_bconfig : bconfig := with_keyed true djot_bconfig.

(* The block half of the Markdown-like profile: djot plus the Markdown
   readings a Markdown writer relies on.  Setext underlines and sublists
   without a blank line are additions; an ATX heading is one line, because
   `# a` then `# b` is two headings to a Markdown reader.  Every other
   construct stays djot's. *)
Definition markdown_like_bconfig : bconfig :=
  with_heading_continuation false
    (with_underline setext_underline
      (with_marker_interrupts prose_safe_markers djot_bconfig)).

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

Local Lemma configured_list_rest_length `{bconfig} :
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

Local Lemma bunderline_of_blank `{bconfig} :
  forall l, is_blank l = true -> bunderline_of l = None.
Proof.
  intros l Hb. unfold bunderline_of. rewrite (underline_of_blank l Hb).
  reflexivity.
Qed.

Local Lemma bunderline_of_ws_prefix `{bconfig} :
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
Context {LI : LineIx}.
(* Whether the nodes this parse builds carry where they came from.
   Every statement below is uniform in it: no branch reads a position,
   so the located and the semantic parse take the same descent. *)
Context {P : PosPolicy}.

(* Every line retained beyond the transition that read it carries its source
   line index.  The text remains a suffix of the input line; its right-hand
   coordinate is therefore just [String.length (snd l)]. *)
Definition stored_line : Type := nat * string.

Definition remember_line (s : string) : stored_line := (lix, s).

Definition remember_lines (lines : list string) : list stored_line :=
  map remember_line lines.

Definition line_texts (lines : list stored_line) : list string := map snd lines.

(* What an open container records of the source it has claimed: where it
   started, and the end of the last line it took.  A `span` is the same
   pair once the container is closed; this is the mutable half, so it is
   a type of its own and `extent_span` is the projection.  Both
   coordinates are end-anchored like a stored line's, so `pad_state`
   moves neither (`step_fuel_shift`, `step_fuel_pad`). *)
Record extent : Type := Extent
  { extent_start : spot
  ; extent_stop : spot }.

(* A column on the current line, as bytes from there to the line's end.
   `column` is absolute, so a caller inside a container passes the column
   it measured the line at, never `indent_of` of a stripped residue. *)
Local Definition spot_at (l : string) (column : nat) : spot :=
  Spot lix (String.length l - column).

(* The end of the current line's content, which is where a half-open
   range that runs to the end of the line stops. *)
Local Definition line_stop : spot := Spot lix 0.

Definition line_span_from (l : string) (column : nat) : span :=
  SrcSpan (spot_at l column) line_stop.

(* A container opening at `column` of this line, having claimed it. *)
Definition open_extent (l : string) (column : nat) : extent :=
  Extent (spot_at l column) line_stop.

(* One more line claimed: the start stays, the stop moves here. *)
Definition touch_extent (e : extent) : extent :=
  Extent (extent_start e) line_stop.

Definition extent_span (e : extent) : span :=
  SrcSpan (extent_start e) (extent_stop e).

(* A stored line is a suffix of its source line with nothing trimmed at
   the end, so its content starts `String.length` bytes before the end of
   that line. *)
Local Definition stored_start (sl : stored_line) : spot :=
  Spot (fst sl) (String.length (snd sl)).

Local Definition stored_stop (sl : stored_line) : spot := Spot (fst sl) 0.

(* The range of an accumulator, which every state holds reversed: from
   the first line's content to the end of the last.  The empty list is
   not a range -- a block with no lines is never emitted -- and stands
   for itself rather than for a point in the source. *)
Definition stored_span (cur : list stored_line) : span :=
  match cur with
  | [] => SrcSpan (Spot 0 0) (Spot 0 0)
  | newest :: _ =>
      SrcSpan (stored_start (List.last cur newest)) (stored_stop newest)
  end.

(* A construct whose accumulated lines are followed by a closing line
   this line is: a setext underline. *)
Local Definition span_through_line (r : span) : span :=
  SrcSpan (span_start r) line_stop.


Lemma line_texts_remember_lines :
  forall lines, line_texts (remember_lines lines) = lines.
Proof.
  induction lines as [|l rest IH].
  - reflexivity.
  - unfold line_texts, remember_lines in *. cbn [map remember_line snd].
    rewrite IH. reflexivity.
Qed.

Lemma line_texts_rev :
  forall lines, line_texts (rev lines) = rev (line_texts lines).
Proof.
  intros lines. unfold line_texts. apply map_rev.
Qed.

Lemma remember_lines_cons :
  forall l lines,
    remember_lines (l :: lines) = remember_line l :: remember_lines lines.
Proof. reflexivity. Qed.

Lemma line_texts_rev_remember_lines :
  forall lines,
    line_texts (rev (remember_lines lines)) = rev lines.
Proof.
  intros lines. rewrite line_texts_rev, line_texts_remember_lines. reflexivity.
Qed.

Lemma line_texts_rev_remember_snoc :
  forall a lines,
    line_texts (rev (remember_lines (rev lines) ++ [remember_line a])%list)
    = (a :: lines)%list.
Proof.
  intros a lines. rewrite line_texts_rev. unfold line_texts.
  rewrite map_app. cbn [map snd remember_line].
  fold (line_texts (remember_lines (rev lines))).
  rewrite line_texts_remember_lines, rev_app_distr, rev_involutive.
  reflexivity.
Qed.

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

A row line contributes a `trow` and nothing else (`Line.table_row`).
Head/align assignment happens here, over the rows a table has collected,
because a separator marks the row before it: it sets the aligns for
every following row and, if the table already has a row, turns that row
into a header at those aligns.  So the target is the last row built,
which two consecutive separators both claim.
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

(* What a table has seen after its rows.  `TOpen` still takes rows;
   `TAfterBlank` has seen a blank, which ends the rows but not the table,
   since a caption may still follow across any number of blanks; and
   `TCaption` accumulates a caption's lines, reversed, as a paragraph
   accumulator does.

   The table waits because `step` emits blocks upward and cannot reach
   back into a table already emitted to add its caption.  Waiting does
   not change list tightness: `blank_absorbed` stays `false` for a table,
   so a blank arms the enclosing list as it would after a closed
   table. *)
Record cell_part : Type := CellPart
  { cell_range : span
  ; cell_text_start : spot }.

Definition row_part : Type := span * list cell_part.

Inductive tcap : Type :=
  | TOpen (row_parts : list row_part)
  | TAfterBlank (row_parts : list row_part)
  | TCaption (row_parts : list row_part)
      (caption_start : spot) (lines : list stored_line).

(* The caption's lines, for the state invariant: they are a paragraph
   accumulator and carry its condition. *)
Local Definition cap_lines (c : tcap) : list stored_line :=
  match c with TCaption _ _ ls => ls | _ => [] end.

(* An empty caption is no caption: `^ ` with nothing after it has no
   content, so `Some []` would be a second spelling of `None`, which
   `wf_block` rules out.  The test is on the inlines rather than on the
   lines because a line can have content and still leave none: an
   attribute spec with nothing to attach to is gone by the time the
   caption is built. *)
Definition caption_of (c : tcap) : option inlines :=
  match c with
  | TOpen _ | TAfterBlank _ => None
  | TCaption _ _ ls =>
      let ils := para_inlines_at 0 (rev ls) in
      if nonempty ils then Some ils else None
  end.

Local Definition cap_row_parts (c : tcap) : list row_part :=
  match c with
  | TOpen rs | TAfterBlank rs | TCaption rs _ _ => rs
  end.

Definition table_parts (c : tcap) : parts :=
  let caption :=
    match c, caption_of c with
    | TCaption _ start ls, Some _ =>
        Some (SrcSpan start (stored_stop (hd (0, EmptyString) ls)))
    | _, _ => None
    end in
  Ast.PTable caption
    (map (fun r => (fst r, map cell_range (snd r)))
       (rev (cap_row_parts c))).

Local Fixpoint cells_of_located (ct : cell_type) (aligns : list align)
  (cs : list string) (parts : list cell_part) : list cell :=
  match cs with
  | [] => []
  | c :: cs' =>
      let al := match aligns with [] => AlignDefault | a :: _ => a end in
      let als := match aligns with [] => [] | _ :: als => als end in
      let ils := match parts with
                 | [] => parse_inline_line c
                 | part :: _ =>
                     parse_inline_line_located
                       (spot_line (cell_text_start part))
                       (spot_rem (cell_text_start part)) c
                 end in
      let rest := match parts with [] => [] | _ :: ps => ps end in
      Cell ct al ils :: cells_of_located ct als cs' rest
  end.

(* Separator lines change alignment but do not consume a row part.
   [table_fold] still makes every structural decision; this fold only
   chooses the located scan for the same cell strings. *)
Local Fixpoint table_fold_located (rows : list trow) (parts : list row_part)
  (aligns : list align) (acc : list (list cell)) : list (list cell) :=
  match rows with
  | [] => rev acc
  | TSep als :: rest =>
      table_fold_located rest parts als
        (match acc with [] => [] | r :: acc' => head_of als r :: acc' end)
  | TCells cs :: rest =>
      let cell_parts := match parts with [] => [] | (_, ps) :: _ => ps end in
      let rest_parts := match parts with [] => [] | _ :: ps => ps end in
      table_fold_located rest rest_parts aligns
        (cells_of_located BodyCell aligns cs cell_parts :: acc)
  end.

(* A table of separators alone has no rows at all, which is a table djot
   renders as `<table>\n</table>` (`tables.test:97`). *)
Definition table_block (rows : list trow) (c : tcap) : node block :=
  mk (Table (caption_of c)
        (if pos_records
         then table_fold_located rows (rev (cap_row_parts c)) [] []
         else table_fold rows [] [])).

(* One row's authored parts.  The row classifier and this projection
   share [row_cells_trace]; the trace's coordinates are relative to its
   opening bar, which is end-anchored here after container prefixes have
   been removed.  Separator lines make alignment, not AST rows. *)
Definition table_row_part (l : string) (r : trow)
  : option row_part :=
  match r, row_body l with
  | TCells _, Some body =>
      match row_cells_trace (row_inner body) O O false EmptyString [] 1 0 with
      | Some cells =>
          let width := String.length (drop_leading_ws l) in
          let cell_part_of := fun x =>
            let '(_, a, b, text_start) := x in
            CellPart (SrcSpan (Spot lix (width - a))
                              (Spot lix (width - b)))
                     (Spot lix (width - text_start)) in
          Some (SrcSpan (Spot lix width)
                        (Spot lix (width - S (String.length body))),
                map cell_part_of cells)
      | None => None
      end
  | _, _ => None
  end.

Local Lemma table_row_part_ws_prefix : forall p l r,
  is_blank p = true -> table_row_part (p ++ l) r = table_row_part l r.
Proof.
  intros p l r Hp. unfold table_row_part, row_body.
  rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity.
Qed.

(*
The line fold
=============
*)

(* A list, mid-parse.  `ls_indent` is the column its markers sit at: a
   continuation line is one indented past it.  The rule does not mention
   the marker's width, and the parser never consults it.

   `ls_styles` is the candidate style set, which siblings narrow by
   intersection (`narrow`); an empty intersection ends the list.  Each
   candidate is paired with the start number the first item's marker
   yields under it, because the decoding depends on the style: `i.` is 1
   read as roman and 9 read as alpha, and which it is may not be settled
   until a later sibling narrows the set.  Pairing them at open makes
   narrowing a plain filter that cannot disturb the number.

   Tight/loose is decided on the line sequence rather than on the
   finished tree: a blank line arms `ls_blanks`, and the next sibling
   marker, or the next content line that does not open a nested list,
   makes the list loose.  So `- a`, blank, `  - b` stays tight although a
   blank separates the item's two children, as the syntax reference's
   `- two` / blank / `  - sub` example requires.  The list is emitted only
   when it closes, so nothing is revised retroactively. *)
Record list_state : Type := LSt
  { ls_indent : nat
  ; ls_extent : extent               (* the list's own source range *)
  ; ls_item_extent : extent          (* the item still open *)
  ; ls_item_extents : list extent    (* finished items, reversed *)
  ; ls_styles : list (lstyle * nat)
  ; ls_loose : bool
  ; ls_blanks : bool
  ; ls_items : list blocks      (* finished items, reversed *)
  (* The checkbox of the item still open, and of those already closed:
     parallel to `done`/`inner` and to `ls_items`, and pushed with them in
     `list_next`, so the two pair up by construction.  A non-task list
     carries `Incomplete` everywhere and nothing reads it.  Kept beside
     `ls_items` rather than inside it, so that `ls_items`'s element type
     stays the one `ListUniformity.v` works with. *)
  ; ls_check : task_status
  ; ls_checks : list task_status }.

(* The fold's state: a container stack.  Every accumulator holds its
   items in *reverse* order, hence the `rev` at each use site. *)
Inductive pstate : Type :=
  | PPara (cur : list stored_line)              (* [] = no open block *)
  (* An open heading.  `range` starts at the `#`, which is part of the
     construct and is not in `cur`: a stored line is the text after the
     marker, so the accumulator alone cannot say where the heading
     began. *)
  | PHeading (level : nat) (range : extent) (cur : list stored_line)
  (* An open code fence: the closer it wants, the absolute column its
     opening backticks sit at (`off + indent_of l`, as for `open_attr`),
     and the content lines it has taken.  Each content line loses up to
     that many columns of leading whitespace, so a fence opened at column
     2 inside a list item stores `code`, not `  code`.

     `range` is the source it has claimed and `open_line_span` its
     opening line, which tells a fence with a closing line from one the
     input ended inside. *)
  | PFence (f : fence) (ind : nat) (range : extent)
      (open_line_span : span) (acc : list stored_line)
  | PQuote (range : extent)
      (header : option (string * option callout_fold * stored_line))
      (done : blocks) (inner : pstate)
  (* An open fenced div: the fence length it must be closed by, its
     class, and the contents so far.  Unlike a quote it removes no
     prefix and shifts no column -- its whole continuation rule is the
     `div_close` test, which is why it needs none of the pad layer.
     `range` and `open_line_span` are the fence's, as for `PFence`. *)
  | PDiv (len : nat) (cls : string) (range : extent)
      (open_line_span : span) (done : blocks) (inner : pstate)
  (* done/inner are the *current item*'s state, exactly as for a quote;
     ls_items holds the items already closed. *)
  | PList (ls : list_state) (done : blocks) (inner : pstate)
  (* An open block attribute spec.  `pend` is what earlier consecutive
     specs already contributed, `ind` the opener's indentation (a
     continuation line has to be indented past it), `ap` the character
     machine, and `slices` the lines eaten so far, reversed.  The slices
     are kept because a spec that turns out not to parse becomes an
     ordinary paragraph of exactly those lines, which is the only reason
     this state is not just an `attr`.  `specs` holds the ranges of the
     settled specs `pend` came from, in source order, and `range` the one
     still open, which joins them when it settles: one `RAttrSpec` entry
     each on the block they decorate. *)
  | PAttr (pend : attr) (specs : list span) (range : extent)
      (ind : nat) (ap : aparser) (slices : list stored_line)
  (* A paragraph the block attribute recovery built.  `cur` is its lines,
     reversed, exactly as `PPara` holds them; `k` counts the lines from
     the front that the failed spec had eaten, which are read with
     attribute recognition off.  It records no column, so `pad_state`
     leaves it alone, and it is never built with `k = 0` or with an empty
     `cur`: the recovery always hands over at least the line the spec
     opened on. *)
  | PParaOff (k : nat) (cur : list stored_line)
  (* An open reference definition: the column its bracket sits at, its
     label, and the destination so far.  Like `PAttr`'s the column is
     absolute (`off + indent_of l`), because a continuation line is one
     indented past it and the two ways of reaching a nested line have to
     record the same number (`step_fuel_shift`, `step_fuel_pad`).  Unlike
     `PAttr` this state keeps no source lines: a definition that stops
     being continued is complete, never retracted. *)
  | PRef (range : extent) (ind : nat) (lbl : string) (val : string)
  (* A footnote definition is a block container.  `done` and `inner`
     have the same source-order convention as quotes and divs; `ind` is
     the opener's absolute column and governs later continuation lines. *)
  | PFoot (range : extent) (ind : nat) (lbl : string)
      (done : blocks) (inner : pstate)
  (* An open table: its source range and the row lines it has taken,
     reversed.  Unlike every other container that spans lines it records
     no column: a row's content is what is left of the line after the
     container prefixes, and nothing in it is measured against the column
     the first bar sat at. *)
  | PTable (range : extent) (rows : list trow) (cap : tcap)
  (* Attributes looking for the block they decorate.  A container is
     built only when it closes, so they ride along until it emits.
     `inner` is idle exactly while they are unclaimed, which makes "a
     blank line drops them" a test on `inner` rather than a separate
     state.  `specs` is the same set as source ranges. *)
  | PPend (pend : attr) (specs : list span) (inner : pstate)
  (* An open key: the label's source, the key line as written, and the
     state its block is being built in.  Like `PDiv` it eats no prefix
     and shifts no column, so it records none.  Its continuation rule is
     `PPend`'s rather than `PDiv`'s: a div closes when a line says so, a
     key closes when the state under it emits a block, which is
     `key_result` below.

     The line is kept because retraction reproduces it byte for byte:
     a key that gets no block becomes the paragraph it would have been
     with the setting off, and nothing is reassembled
     (`.project/keyed-blocks.md` 3.5, 6). *)
  | PKey (range : extent) (lbl : string) (src : string) (inner : pstate).

End WithTable.
Module StateErase.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.
Context {LI : LineIx}.
Context {P : PosPolicy}.

(* The coordinate half of erasure.  A line index is the only thing in a
   spot that the ambient instance would have written differently -- the
   right-hand coordinate is `String.length`, which no instance sees --
   so forgetting the provenance a state accumulated is setting every
   line index to the one `semantic_line_ix` writes. *)
Local Definition of_spot (s : spot) : spot := Spot 0 (spot_rem s).

Local Definition of_span (r : span) : span :=
  SrcSpan (of_spot (span_start r)) (of_spot (span_stop r)).

Local Definition of_extent (e : extent) : extent :=
  Extent (of_spot (extent_start e)) (of_spot (extent_stop e)).

Local Definition of_line (sl : stored_line) : stored_line := (0, snd sl).

Local Definition of_lines (ls : list stored_line) : list stored_line :=
  map of_line ls.

(* And every reader of a stored line reads past the index. *)
Local Lemma of_lines_texts : forall ls, line_texts (of_lines ls) = line_texts ls.
Proof.
  induction ls as [|x ls IH]; [reflexivity|].
  unfold line_texts, of_lines in *; cbn [map]. rewrite IH. reflexivity.
Qed.

Local Lemma of_lines_rev : forall ls, of_lines (rev ls) = rev (of_lines ls).
Proof. intros ls. apply map_rev. Qed.

Local Lemma of_lines_texts_rev : forall ls,
  line_texts (rev (of_lines ls)) = line_texts (rev ls).
Proof. intros ls. rewrite <- of_lines_rev. apply of_lines_texts. Qed.

Local Lemma of_lines_length : forall ls,
  List.length (of_lines ls) = List.length ls.
Proof. intros ls. apply length_map. Qed.

(* Forget the provenance an incremental state has accumulated: the
   positions on the blocks it retains, and the line indices of every
   coordinate it recorded.  Both are observational -- no transition
   branches on either -- so this is the state half of the refinement
   relation, and its fixed point is the state the ambient instance
   reaches on the same input. *)
Local Definition of_cap (c : tcap) : tcap :=
  match c with
  | TOpen _ => TOpen []
  | TAfterBlank _ => TAfterBlank []
  | TCaption _ start lines => TCaption [] (of_spot start) (of_lines lines)
  end.

(* A paragraph's inlines, erased, are the ones the ambient instance
   builds from the same texts: `InlineLocated.para_inlines_at_erase` with the
   line indices the located state recorded thrown away. *)
Local Lemma of_para_inlines_at : forall off ls,
  Erase.of_inlines (@para_inlines_at T located_pos off ls) =
  @para_inlines_at T semantic_pos off (of_lines ls).
Proof.
  intros off ls. rewrite (@para_inlines_at_erase T located_pos),
    (@para_inlines_at_semantic T).
  unfold line_texts in *. rewrite of_lines_texts. reflexivity.
Qed.

Local Lemma inlines_nonempty : forall (xs : inlines),
  nonempty (Erase.of_inlines xs) = nonempty xs.
Proof. intros [|x xs]; reflexivity. Qed.

Local Lemma of_cells_of_located : forall ct aligns cs parts,
  Erase.row (cells_of_located ct aligns cs parts) = cells_of ct aligns cs.
Proof.
  intros ct aligns cs. revert aligns.
  induction cs as [|c cs IH]; intros aligns parts; [reflexivity|].
  destruct aligns as [|al als], parts as [|part parts];
    cbn [cells_of_located cells_of Erase.row map Erase.of_cell];
    rewrite ?erase_parse_inline_line_located,
            ?erase_parse_inline_line, IH; reflexivity.
Qed.

Local Lemma of_head_of : forall als r,
  Erase.row (head_of als r) = head_of als (Erase.row r).
Proof.
  intros als r. revert als.
  induction r as [|[ct al ils] r IH]; intros als; [reflexivity|].
  destruct als; cbn [head_of Erase.row map Erase.of_cell];
    rewrite IH; reflexivity.
Qed.

Local Lemma of_table_fold_located : forall rows parts aligns acc,
  map Erase.row (table_fold_located rows parts aligns acc) =
  table_fold rows aligns (map Erase.row acc).
Proof.
  induction rows as [|r rows IH]; intros parts aligns acc.
  - cbn [table_fold_located table_fold]. apply map_rev.
  - destruct r as [als|cs].
    + cbn [table_fold_located table_fold].
      destruct acc as [|row acc]; cbn [map].
      * apply IH.
      * rewrite <- of_head_of. apply IH.
    + destruct parts as [|[range cellparts] parts];
        cbn [table_fold_located table_fold]; rewrite IH;
        cbn [map]; rewrite of_cells_of_located; reflexivity.
Qed.

Local Definition of_list_state (ls : list_state) : list_state :=
  LSt (ls_indent ls) (of_extent (ls_extent ls))
    (of_extent (ls_item_extent ls))
    (map of_extent (ls_item_extents ls))
    (ls_styles ls) (ls_loose ls) (ls_blanks ls)
    (map Erase.of_blocks (ls_items ls)) (ls_check ls) (ls_checks ls).

Local Fixpoint state (st : pstate) : pstate :=
  match st with
  | PPara cur => PPara (of_lines cur)
  | PHeading lvl range cur =>
      PHeading lvl (of_extent range) (of_lines cur)
  | PFence f ind range opener acc =>
      PFence f ind (of_extent range) (of_span opener) (of_lines acc)
  | PQuote range header done inner =>
      PQuote (of_extent range)
        (option_map (fun '(kind, fold, title) => (kind, fold, of_line title)) header)
        (Erase.of_blocks done) (state inner)
  | PDiv len cls range opener done inner =>
      PDiv len cls (of_extent range) (of_span opener)
        (Erase.of_blocks done) (state inner)
  | PList ls done inner =>
      PList (of_list_state ls) (Erase.of_blocks done) (state inner)
  | PAttr pend specs range ind ap slices =>
      PAttr pend (map of_span specs) (of_extent range) ind ap
        (of_lines slices)
  | PParaOff k cur => PParaOff k (of_lines cur)
  | PRef range ind lbl val => PRef (of_extent range) ind lbl val
  | PFoot range ind lbl done inner =>
      PFoot (of_extent range) ind lbl (Erase.of_blocks done)
        (state inner)
  | PTable range rows cap =>
      PTable (of_extent range) rows (of_cap cap)
  | PPend pend specs inner =>
      PPend pend (map of_span specs) (state inner)
  | PKey range lbl src inner =>
      PKey (of_extent range) lbl src (state inner)
  end.

Local Definition result (r : blocks * pstate) : blocks * pstate :=
  (Erase.of_blocks (fst r), state (snd r)).

End WithTable.
End StateErase.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.
Context {LI : LineIx}.
Context {P : PosPolicy}.

(* Container nesting depth.  Half of the parser's termination measure:
   a quote descent shortens the line, but a list descent hands the line
   to the inner container unchanged and shortens *this* instead. *)
Fixpoint pstate_depth (st : pstate) : nat :=
  match st with
  | PPara _ | PParaOff _ _ | PHeading _ _ _ | PFence _ _ _ _ _ => 0
  | PQuote _ _ _ inner => S (pstate_depth inner)
  | PDiv _ _ _ _ _ inner => S (pstate_depth inner)
  | PList _ _ inner => S (pstate_depth inner)
  (* PAttr resolves to `PPend _ (PPara [])`, depth 1, on the same line, so
     it has to sit above that. *)
  | PAttr _ _ _ _ _ _ => 2
  (* PRef reprocesses the line that ends it against `PPara []`, depth 0.
     PTable ends the same way. *)
  | PRef _ _ _ _ | PTable _ _ _ => 1
  | PFoot _ _ _ _ inner => S (pstate_depth inner)
  | PPend _ _ inner => S (pstate_depth inner)
  | PKey _ _ _ inner => S (pstate_depth inner)
  end.

(* Is nothing open here?  `PPara []` is the idle state, and the only one:
   every other constructor has a block or a container in flight. *)
Definition is_idle (st : pstate) : bool :=
  match st with PPara [] => true | _ => false end.

(* End of input (or of an enclosing container): close everything still
   open, outermost result first. *)
(* A heading's text lines become its inlines exactly as a paragraph's
   do. *)
Definition heading_block (lvl : nat) (cur : list stored_line) : node block :=
  mk (Heading lvl (para_inlines_at 0 (rev cur))).

(* The same, for a paragraph whose first `k` lines came from a failed
   block attribute spec.  Only an underline reaches it, so only a
   configuration with both `bunderline_of` and `battrs` on can, and the
   lines keep the reading they had as a paragraph. *)
Definition heading_block_off (k lvl : nat) (cur : list stored_line) : node block :=
  mk (Heading lvl (para_inlines_at k (rev cur))).

(* The title stays a source suffix until this point.  Its trimmed value
   uses the original suffix length to locate each inline correctly. *)
Definition callout_title `{PosPolicy} (sl : stored_line) : inlines :=
  let '(line, source) := sl in
  let title := strip_trailing_ws source in
  if pos_records
  then parse_inline_line_located line (String.length source) title
  else parse_inline_line title.

Definition quote_block `{PosPolicy}
  (header : option (string * option callout_fold * stored_line))
  (bs : blocks) : block :=
  match header with
  | None => BlockQuote bs
  | Some (kind, fold, source) =>
      Ext_callout kind fold (callout_title source) bs
  end.

(* The lines a failed block attribute spec ate, handed to the paragraph
   that inherits them.  All of them are frozen, so the count is their
   length, plus `extra`, which is 1 in the one case where the line that
   failed the spec is frozen too without being in `slices`: an indented
   continuation line is frozen before it is fed, and reaches the
   paragraph by being reprocessed against this state.

   Over-counting is harmless.  A line that does not join the paragraph
   leaves `k` above the length, and `iscan_lines_off` then reads every
   line it has with attributes off, which is what the shorter paragraph
   wanted anyway. *)
Definition para_recover (extra : nat) (slices : list stored_line) : pstate :=
  PParaOff (extra + List.length slices) slices.

(* The same lines when there is no next line: the document, or the
   container, ended with the spec still open. *)
Definition finish_para_recover (slices : list stored_line) : blocks :=
  match slices with
  | [] => []
  | _ => [set_pos (prov_at (stored_span slices))
            (mk (Para (para_inlines_at (List.length slices)
                         (rev slices))))]
  end.

(* A div's class becomes a `class` attribute on the node; a classless div
   carries no attributes at all, so the canonical case stays `mk`-wrapped
   and proofs compute through it. *)
Definition div_block (cls : string) (bs : blocks) : node block :=
  if String.eqb cls EmptyString
  then mk (Div bs)
  else Node NoPos [("class", cls)] (Div bs).

(* The block a list closes to, read off the candidate set its state
   carries.  Stated on the set rather than on a marker because siblings
   narrow it: a list whose first marker is ambiguous closes to a block
   that marker alone does not determine.  Defined here rather than beside
   the markers because the colon's arm reads `bdeflists`, which this
   section keeps implicit. *)
Definition styles_list (S : list (lstyle * nat)) (sp : list_spacing)
                       (items : list blocks) : node block :=
  match S with
  | (SOrd n d, start) :: _ => mk (OrderedList (OLAttrs n d start) sp items)
  (* The colon is the definition-list style, and this is the only place
     it differs from a bullet.  Spelled as a test on the character rather
     than as a pattern, so that a proof holding an unknown bullet can case
     on it in one step.  With definition lists off the split goes away:
     the items and their colon markers stay, and the list is the bullet
     list any other marker would make. *)
  | (SBullet c, _) :: _ =>
      if (Ascii.eqb c ":" && bdeflists)%bool
      then mk (DefinitionList sp (def_items items))
      else mk (BulletList sp items)
  (* The state-free form cannot build a task list, since statuses are per
     item: `styles_list_checked` below handles that style, and this arm
     keeps the function total. *)
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

(* The same at a marker whose set no sibling narrows.  A bullet gives a
   `BulletList` definitionally; an ordered marker gives the `OrderedList`
   of its style and start. *)
Local Definition marker_list (m : marker) (sp : list_spacing) (items : list blocks)
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

(* The spans of a list's items, in source order, parallel to the items
   themselves: the one still open is the last. *)
Local Definition list_item_spans (ls : list_state) : parts :=
  PItems (map extent_span (rev (ls_item_extent ls :: ls_item_extents ls))).

(* [def_split] takes the first paragraph as the term.  The blocks it
   leaves are the definition.  Read the same split for provenance, so
   invisible blocks before the term and an absent term follow exactly
   the semantic definition-list assembly. *)
Local Fixpoint def_term_span (bs : blocks) : option span :=
  match bs with
  | [] => None
  | n :: rest =>
      match node_contents n with
      | Para _ => option_map node_span (node_provenance n)
      | x => if invisible_block x then def_term_span rest else None
      end
  end.

Local Definition blocks_span (bs : blocks) (fallback : spot) : span :=
  match bs with
  | [] => SrcSpan fallback fallback
  | first :: _ =>
      match node_provenance first,
            node_provenance (List.last bs first) with
      | Some p, Some q =>
          SrcSpan (span_start (node_span p)) (span_stop (node_span q))
      | _, _ => SrcSpan fallback fallback
      end
  end.

Local Fixpoint def_item_spans (ranges : list span) (items : list blocks)
  : list (span * span * span) :=
  match ranges, items with
  | item :: ranges', bs :: items' =>
      let term := match def_term_span bs with
                  | Some r => r
                  | None => SrcSpan (span_start item) (span_start item)
                  end in
      let definition := blocks_span (snd (def_item bs)) (span_stop term) in
      (item, term, definition) :: def_item_spans ranges' items'
  | _, _ => []
  end.

Local Definition list_parts (ls : list_state) (last : blocks) : parts :=
  let ranges := map extent_span
                    (rev (ls_item_extent ls :: ls_item_extents ls)) in
  match ls_styles ls with
  | (SBullet c, _) :: _ =>
      if (Ascii.eqb c ":" && bdeflists)%bool
      then PDefItems (def_item_spans ranges (rev (last :: ls_items ls)))
      else PItems ranges
  | _ => PItems ranges
  end.

(* The list a `PList` closes to: the first surviving candidate, which is
   why `styles_of_core` lists the roman reading before the alpha one.
   The empty case is unreachable: `open_list` is only reached from a
   `KList`, whose style set `list_marker` has already found nonempty, and
   `narrow` replaces the set only when the result is nonempty. *)
Definition list_block (ls : list_state) (last : blocks) : node block :=
  styles_list_checked (ls_styles ls)
    (if ls_loose ls then Loose else Tight)
    (rev (ls_check ls :: ls_checks ls))
    (rev (last :: ls_items ls)).

Local Lemma list_block_erase : forall ls last,
  Erase.of_blocks [list_block ls last] =
  [list_block (StateErase.of_list_state ls) (Erase.of_blocks last)].
Proof.
  intros ls last.
  destruct ls as [li le lie lies styles loose blanks items check checks].
  unfold list_block, styles_list_checked.
  cbn [ls_styles ls_loose ls_check ls_checks ls_items StateErase.of_list_state].
  destruct styles as [|[sty start] styles].
  - cbn [styles_list Erase.of_blocks Erase.of_block mk].
    fold Erase.of_blocks. fold (map Erase.of_blocks (rev (last :: items))).
    rewrite map_rev. reflexivity.
  - destruct sty.
    + cbn [styles_list Erase.of_blocks Erase.of_block mk].
      destruct (Ascii.eqb c
          (Ascii.Ascii false true false true true true false false)
          && bdeflists)%bool;
        cbn [Erase.of_blocks Erase.of_block mk].
      * fold Erase.of_blocks. rewrite Erase.def_items_erase, map_rev. reflexivity.
      * fold Erase.of_blocks. fold (map Erase.of_blocks (rev (last :: items))).
        rewrite map_rev. reflexivity.
    + cbn [styles_list Erase.of_blocks Erase.of_block mk]. fold Erase.of_blocks.
      rewrite Erase.task_items_erase, map_rev. reflexivity.
    + cbn [styles_list Erase.of_blocks Erase.of_block mk]. fold Erase.of_blocks.
      fold (map Erase.of_blocks (rev (last :: items))).
      rewrite map_rev. reflexivity.
Qed.

(* The block a reference definition closes to.  It renders to no HTML and
   is a block for the roundtrip's sake; `Document.v` reads the pair off it
   into the document's reference map. *)
Definition ref_block (lbl val : string) : node block := mk (RefDef lbl val).

Definition foot_block (lbl : string) (bs : blocks) : node block :=
  mk (FootnoteDef lbl bs).

(* What an open key becomes once the state under it has been closed.  A
   key claims the first block that comes out and nothing after it, so no
   block at all is a key that never got one, and that retracts to the
   paragraph its own line would have been with the setting off
   (`.project/keyed-blocks.md` sections 4 and 6).

   The label's inlines are built here rather than at classification, as a
   paragraph's are built when it closes: the scan that found the split
   kept a byte offset and nothing else.  `start` is where the key line
   began, which is where its label begins. *)
Definition key_label (start : spot) (lbl : string) : inlines :=
  if pos_records
  then parse_inline_line_located (spot_line start) (spot_rem start)
         (strip_trailing_ws lbl)
  else para_inlines [lbl].

Definition key_close (start : spot) (lbl src : string) (bs : blocks) : blocks :=
  match bs with
  | [] => [mk (Para (para_inlines [src]))]
  | b :: rest => (mk (Ext_keyed (key_label start lbl) b) :: rest)%list
  end.

(* A continuation line's contribution: one whitespace-free run,
   whitespace stripped, and nothing else on the line.  A blank line is
   excluded by `nonempty_str`, which is what closes an open definition at
   a paragraph break. *)
Definition ref_cont (l : string) : option string :=
  let t := drop_leading_ws l in
  if (nonempty_str t && no_ws t)%bool then Some t else None.

(* A blank line is never a continuation: it has no run to contribute.
   This is what closes an open definition at a paragraph break, and what
   keeps `PRef` inside `pad_safe` where `PAttr` is not. *)
Local Lemma ref_cont_blank : forall l, is_blank l = true -> ref_cont l = None.
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
  | PPara cur =>
      [set_pos (prov_at (stored_span cur))
         (mk (Para (para_inlines_at 0 (rev cur))))]
  | PParaOff k cur =>
      [set_pos (prov_at (stored_span cur))
         (mk (Para (para_inlines_at k (rev cur))))]
  | PHeading lvl range cur =>
      [set_pos (prov_at (extent_span range)) (heading_block lvl cur)]
  | PFence f _ range opener acc =>
      [set_pos (prov_with (extent_span range) [(ROpenFence, opener)])
         (fence_block f (line_texts (rev acc)))]
  | PTable range rows cap =>
      [set_pos (Provenance (extent_span range) [] (table_parts cap))
         (table_block (rev rows) cap)]
  | PQuote range header done inner =>
      let bs := (rev done ++ finish inner)%list in
      [set_pos (prov_at (extent_span range))
         (mk (quote_block header bs))]
  | PDiv _ cls range opener done inner =>
      [set_pos (prov_with (extent_span range) [(ROpenFence, opener)])
         (div_block cls (rev done ++ finish inner)%list)]
  | PList ls done inner =>
      (* Bound once: a list nested in the item would otherwise be
         finished twice, and a line of `n` markers `2^n` times. *)
      let last := (rev done ++ finish inner)%list in
      [set_pos (Provenance (extent_span (ls_extent ls)) []
                  (list_parts ls last))
         (list_block ls last)]
  (* A spec still wanting continuation lines never was one: its lines are
     a paragraph.  A finished spec with no block after it contributes
     nothing, which is `{#id}` alone in a document.  An earlier spec's
     attributes were waiting on the block this one turned out to be, so
     the recovered paragraph is what they attach to. *)
  | PAttr pend specs _ _ ap slices =>
      if ap_done ap then []
      else add_roles_head (attr_roles specs)
             (decorate_head pend (finish_para_recover slices))
  | PRef range _ lbl val =>
      [set_pos (prov_at (extent_span range)) (ref_block lbl val)]
  | PFoot range _ lbl done inner =>
      [set_pos (prov_at (extent_span range))
         (foot_block lbl (rev done ++ finish inner)%list)]
  | PPend pend specs inner =>
      add_roles_head (attr_roles specs) (decorate_head pend (finish inner))
  | PKey range lbl src inner =>
      pos_head (prov_at (extent_span range))
        (key_close (extent_start range) lbl src (finish inner))
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

Local Lemma list_block_marker :
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

Local Lemma finish_list_styles :
  forall S ls done inner,
    ls_styles ls = S ->
    finish (PList ls done inner)
    = [set_pos (Provenance (extent_span (ls_extent ls)) []
                  (list_parts ls (rev done ++ finish inner)%list))
         (styles_list_checked S (if ls_loose ls then Loose else Tight)
            (rev (ls_check ls :: ls_checks ls))
            (rev ((rev done ++ finish inner)%list :: ls_items ls)))].
Proof.
  intros S ls done inner H. cbn [finish].
  rewrite (list_block_styles S ls _ H). reflexivity.
Qed.

Local Lemma finish_list_marker :
  forall m ls done inner,
    ls_styles ls = mk_styles m ->
    finish (PList ls done inner)
    = [set_pos (Provenance (extent_span (ls_extent ls)) []
                  (list_parts ls (rev done ++ finish inner)%list))
         (marker_list_checked m (if ls_loose ls then Loose else Tight)
            (rev (ls_check ls :: ls_checks ls))
            (rev ((rev done ++ finish inner)%list :: ls_items ls)))].
Proof.
  intros m ls done inner H. unfold marker_list_checked.
  apply (finish_list_styles _ _ _ _ H).
Qed.

(* Lazy continuation.  A nonblank, otherwise featureless line that is
   missing its container prefixes still continues the innermost open
   inline container (a paragraph or a heading) and nothing else, which is
   why fence content is excluded.  An empty PPara is the idle state, not
   an open block; a PHeading is always open, even with no text yet. *)
Fixpoint lazy_ok (st : pstate) : bool :=
  match st with
  | PPara [] => false
  | PPara (_ :: _) => true
  | PParaOff _ _ => true       (* a recovered paragraph is still one *)
  (* where headings are one line, a lazy line has nothing to continue *)
  | PHeading _ _ _ => bheading_continues
  | PFence _ _ _ _ _ => false
  | PQuote _ _ _ inner => lazy_ok inner
  | PDiv _ _ _ _ _ inner => lazy_ok inner
  | PList _ _ inner => lazy_ok inner
  | PAttr _ _ _ _ _ _ => false (* a spec is not a paragraph, however it ends *)
  | PRef _ _ _ _ => false      (* nor is a reference definition *)
  | PTable _ _ _ => false      (* nor is a table: a lazy line ends it *)
  | PFoot _ _ _ _ inner => lazy_ok inner
  | PPend _ _ inner => lazy_ok inner
  (* A lazy line continues whatever paragraph the key has open, and
     continues nothing when the key is still waiting for its block. *)
  | PKey _ _ _ inner => lazy_ok inner
  end.

(* Whether the innermost open container is a code block, i.e. a fence is
   open anywhere down the spine (nothing nests inside a code block).  An
   open div consults this before testing for its own closer, so a `:::`
   line that is code stays code. *)
Fixpoint in_fence (st : pstate) : bool :=
  match st with
  | PFence _ _ _ _ _ => true
  (* A key is see-through here, or a `:::` line inside a code block
     inside a key would close an enclosing div. *)
  | PQuote _ _ _ inner | PDiv _ _ _ _ _ inner | PList _ _ inner
  | PFoot _ _ _ _ inner | PPend _ _ inner | PKey _ _ _ inner => in_fence inner
  | PPara _ | PParaOff _ _ | PHeading _ _ _ | PAttr _ _ _ _ _ _
  | PRef _ _ _ _ | PTable _ _ _ => false
  end.

Definition is_lazy (k : line_kind) (inner : pstate) : bool :=
  match k with KText => lazy_ok inner | _ => false end.

(* Content within the current item.  A line that opens a nested list does
   not loosen; anything else loosens the list if a blank line is armed.
   Either way the flag is spent. *)
Definition list_content (ls : list_state) (k : line_kind) : list_state :=
  let loose :=
    match k with
    | KList _ _ _ _ => ls_loose ls
    | _ => (ls_loose ls || ls_blanks ls)%bool
    end in
  LSt (ls_indent ls) (touch_extent (ls_extent ls))
      (touch_extent (ls_item_extent ls)) (ls_item_extents ls)
      (ls_styles ls) loose false (ls_items ls) (ls_check ls) (ls_checks ls).

(* Append a lazy line to the innermost paragraph.  Its leading whitespace
   goes, as on a non-lazy continuation line: a lazy line is a
   continuation line that omits container prefixes.  Canonical renderings
   never produce one, so no roundtrip proof observes this; it keeps the
   state's content independent of ambient indentation. *)
Fixpoint feed_lazy (l : string) (st : pstate) : pstate :=
  match st with
  | PPara cur => PPara (remember_line (drop_leading_ws l) :: cur)
  | PParaOff k cur => PParaOff k (remember_line (drop_leading_ws l) :: cur)
  | PHeading lvl range cur =>
      PHeading lvl (touch_extent range) (remember_line (drop_leading_ws l) :: cur)
  | PFence f ind range opener acc =>
      PFence f ind range opener acc   (* excluded by lazy_ok *)
  | PQuote range header done inner =>
      PQuote (touch_extent range) header done (feed_lazy l inner)
  | PDiv len cls range opener done inner =>
      PDiv len cls (touch_extent range) opener done (feed_lazy l inner)
  (* Content of the current item, as a line indented into it would be. *)
  | PList ls done inner => PList (list_content ls KText) done (feed_lazy l inner)
  | PFoot range ind lbl done inner =>
      PFoot (touch_extent range) ind lbl done (feed_lazy l inner)
  | PAttr _ _ _ _ _ _ | PRef _ _ _ _ | PTable _ _ _ => st
  | PPend pend specs inner => PPend pend specs (feed_lazy l inner)
  | PKey range lbl src inner =>
      PKey (touch_extent range) lbl src (feed_lazy l inner)
  end.

(* A heading's text, pushed onto its accumulator.  `# ` with nothing
   after it opens a heading with no text rather than a blank line of it,
   which is what keeps the accumulator's nonblank invariant. *)
Definition push_text (rest : string) (cur : list stored_line)
  : list stored_line :=
  if is_blank rest then cur else remember_line (drop_leading_ws rest) :: cur.

(* A text line's opening, taken on the line already normalized.  Passing
   the normalized line rather than the raw one is what makes the whole
   arm blind to a leading pad: `step_fuel_pad` needs a padded line and a
   shifted offset to be the same descent, and every proof site already
   rewrites `drop_leading_ws (p ++ l)` to `drop_leading_ws l`.

   The value is inline content and never block syntax (3.3), so it opens
   a paragraph directly and the key needs neither a column nor a
   descent; that is what keeps this inside `open_kind` and out of the six
   kinds `direct_open` excludes.  `push_text` supplies the line-final
   form, where the value is empty and the block comes from the lines
   below. *)
Definition open_text `{bconfig} (t : string) : blocks * pstate :=
  match (if bkeyed then key_split t else None) with
  | Some (lbl, v) =>
      ([], PKey (open_extent t 0) lbl t (PPara (push_text v [])))
  | None => ([], PPara [remember_line t])
  end.

(* Does this line open a paragraph rather than a key?  With the setting
   off every line does, so this conjunct costs a djot document nothing;
   with it on it is what a canonical rendering has to keep true of a
   paragraph's *first* line, since 3.5 says continuation lines are never
   tested.  That is section 8's rendering obligation, and it is wider
   than the label: `Para "Note: this matters"` renders as itself and
   reparses as a key. *)
Definition keyless `{bconfig} (l : string) : bool :=
  match (if bkeyed then key_split l else None) with
  | Some _ => false
  | None => true
  end.

Lemma open_text_keyless :
  forall l,
    keyless l = true ->
    open_text (drop_leading_ws l)
    = ([], PPara [remember_line (drop_leading_ws l)]).
Proof.
  intros l H. unfold keyless in H. unfold open_text.
  rewrite key_split_drop_leading_ws.
  destruct (if bkeyed then key_split l else None) as [[lbl v]|];
    [discriminate|reflexivity].
Qed.

(* And a pad is invisible to it, which is what `step_fuel_pad`'s users
   need wherever the condition travels. *)
Local Lemma keyless_ws_prefix :
  forall p l, is_blank p = true -> keyless (p ++ l) = keyless l.
Proof.
  intros p l Hp. unfold keyless. rewrite (key_split_ws_prefix p l Hp).
  reflexivity.
Qed.

(* What a line opens, for every kind but KQuote: a quote parses the line
   it encloses, which is the parser's one recursion, so it stays inside
   `step_fuel`.  Every equation lemma downstream is stated over
   `open_kind`, which keeps fuel out of every lemma statement. *)
Definition open_kind `{bconfig} (l : string) (k : line_kind) : blocks * pstate :=
  match k with
  | KBlank => ([], PPara [])
  | KThematic =>
      ([posnode (prov_at (line_span_from l (indent_of l))) ThematicBreak],
       PPara [])
  | KFence _ => ([], PPara [])        (* unreachable: see open_fence *)
  | KHeading lvl rest =>
      ([], PHeading lvl (open_extent l (indent_of l)) (push_text rest []))
  | KDiv len cls =>
      if bdivs
      then ([], PDiv len cls (open_extent l (indent_of l))
                   (line_span_from l (indent_of l)) [] (PPara []))
      else ([], PPara [remember_line (drop_leading_ws l)])
  (* The one place a key can open.  3.5: a line is tested for a split
     exactly when it would otherwise open a paragraph, which is this arm
     and no other -- an open paragraph's continuation lines never reach
     here, and the fallback arms below belong to constructs a setting has
     switched off rather than to text. *)
  | KText => open_text (drop_leading_ws l)
  | KQuote _ => ([], PPara [])        (* unreachable: see open_quote *)
  | KList _ _ _ _ => ([], PPara [])     (* unreachable: see open_list *)
  | KAttr _ => ([], PPara [])         (* unreachable: see open_attr *)
  | KFoot _ _ => ([], PPara [])       (* unreachable: see open_foot *)
  | KRef _ _ => ([], PPara [])        (* unreachable: see open_ref *)
  (* A table needs no column and no descent, so unlike every other
     container it opens here rather than in a wrapper of its own.  A profile
     that disables tables keeps the complete row spelling as paragraph text. *)
  | KRow r =>
      if btables
      then ([], PTable (open_extent l (indent_of l)) [r]
                  (TOpen (if pos_records then
                            match table_row_part l r with
                            | Some p => [p]
                            | None => []
                            end else [])))
      else ([], PPara [remember_line (drop_leading_ws l)])
  end.

(* The other half of the per-line rule: this line does not continue the
   open container, so the container's blocks close and the line is
   reprocessed at the enclosing level.  Every state answers a line one of
   these two ways, continue or close-and-reopen, and `finish` closes the
   stack at end of input; a new container supplies only its continuation
   rule.

   Both wrappers take the opening already computed rather than computing
   it, so neither joins the recursion, and `step`'s fuel decrements once
   per nesting level. *)
Definition close_reopen (st : pstate) (opened : blocks * pstate)
  : blocks * pstate :=
  let (bs, st') := opened in ((finish st ++ bs)%list, st').

(* The result of a line handed down through pending block attributes.
   Nothing emitted means the block they are waiting for is still open, so
   they wait; the first block emitted is that block, and they attach to
   it and are gone. *)
Definition pend_result (pend : attr) (specs : list span)
  (r : blocks * pstate) : blocks * pstate :=
  let (bs, st') := r in
  match bs with
  | [] => ([], PPend pend specs st')
  | _ => (add_roles_head (attr_roles specs) (decorate_head pend bs), st')
  end.

(* Pending attributes change what a line emits, never what it leaves
   open: they either attach to an emitted block or move into a `PPend`,
   which `lazy_ok` reads through. *)
Local Lemma lazy_ok_pend_result :
  forall pend specs r,
    lazy_ok (snd (pend_result pend specs r)) = lazy_ok (snd r).
Proof. intros pend specs [bs st]. destruct bs; reflexivity. Qed.

(* The result of a line handed down through an open key.  `PPend`'s
   shape and for `PPend`'s reason: nothing emitted means the block the
   key is waiting for is still open, and the first block emitted is that
   block.  What differs is only what the key does with it, and that a
   key with nothing emitted is retracted rather than dropped. *)
Definition key_result (range : extent) (lbl src : string) (r : blocks * pstate)
  : blocks * pstate :=
  let (bs, st') := r in
  match bs with
  | [] => ([], PKey range lbl src st')
  | _ => (pos_head (prov_at (extent_span range))
            (key_close (extent_start range) lbl src bs), st')
  end.

(* A quote prefix opens a fresh quote around whatever its enclosed line
   parsed to. *)
Definition open_quote (l : string) (descended : blocks * pstate)
  : blocks * pstate :=
  let (bs, inner) := descended in
  ([], PQuote (open_extent l (indent_of l)) None (rev bs) inner).

(** The callout header a quote opener's content carries, when callouts are
   on. *)
Definition quote_header (rest : string)
  : option (string * option callout_fold * string) :=
  if bcallouts then callout_header rest else None.

Definition open_callout (l kind : string) (fold : option callout_fold)
  (title : string) : blocks * pstate :=
  ([], PQuote (open_extent l (indent_of l))
    (Some (kind, fold, remember_line title)) [] (PPara [])).

(* An attribute spec opens its container at the column its brace sits
   at.  Like a list's `ls_indent` this is an absolute column, `off +
   indent_of l`, not a line-local one: continuation lines are tested
   against it, and the two ways of reaching a nested line (moving the
   offset, or padding the line) have to record the same number
   (`step_fuel_shift`, `step_fuel_pad`).  That is also why it is not part
   of `open_kind`, which never sees the offset. *)
(* With block attributes off the spec never opens, so `PAttr` is
   unreachable and the line is the paragraph text its own spelling makes.
   The pending attribute is dropped with it, which is sound because
   nothing can be pending: the only source of one is a `PAttr` that
   closed. *)
Definition open_attr (pend : attr) (specs : list span)
  (ind : nat) (ap : aparser) (l : string)
  : blocks * pstate :=
  if battrs
  then ([], PAttr pend specs (open_extent l (indent_of l)) ind ap
              [remember_line (drop_leading_ws l)])
  else ([], PPara [remember_line (drop_leading_ws l)]).

(* Neither setting closes anything, which is what the two step equations
   below need in order to be stated without a case split. *)
Lemma open_attr_fst :
  forall pend specs ind ap l, fst (open_attr pend specs ind ap l) = [].
Proof. intros. unfold open_attr. destruct battrs; reflexivity. Qed.

(* And so closing into a spec emits exactly what the closed state does. *)
Lemma close_reopen_attr :
  forall st pend specs ind ap l,
    close_reopen st (open_attr pend specs ind ap l)
    = (finish st, snd (open_attr pend specs ind ap l)).
Proof.
  intros. unfold close_reopen, open_attr. destruct battrs; cbn [snd];
    rewrite app_nil_r; reflexivity.
Qed.

(* A code fence opens at the column its border sits at, and for the same
   reason as `open_attr` is not part of `open_kind`: the column is
   absolute and `open_kind` never sees the offset.  Nothing is *tested*
   against this one -- a closer at any indentation closes -- but every
   content line is measured from it. *)
Definition open_fence (l : string) (ind : nat) (f : fence) : blocks * pstate :=
  let col := indent_of l in
  ([], PFence f ind (open_extent l col) (line_span_from l col) []).

(* A reference definition opens at the column its bracket sits at, and for
   the same reason as `open_attr` is not part of `open_kind`: the column is
   absolute and `open_kind` never sees the offset. *)
Definition open_ref (l : string) (ind : nat) (lbl val : string)
  : blocks * pstate :=
  ([], PRef (open_extent l (indent_of l)) ind lbl val).

(* With footnotes off the definition never opens, so `PFoot` is
   unreachable and the complete `[^label]:` line is paragraph text.  The
   descent is computed either way and discarded here, which costs nothing
   and keeps the four call sites identical. *)
Definition open_foot (l : string) (ind : nat) (lbl : string)
  (descended : blocks * pstate) : blocks * pstate :=
  if bfootnotes
  then let (bs, inner) := descended in
       ([], PFoot (open_extent l (indent_of l)) ind lbl (rev bs) inner)
  else ([], PPara [remember_line (drop_leading_ws l)]).

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
Local Definition chk_status (chk : option task_marker) : task_status :=
  match chk with Some m => tm_status m | None => Incomplete end.

(* A list just opened on line `l`: one item, nothing closed yet, and both
   extents starting at the marker. *)
Definition list_opened (l : string) (ind : nat) (sty : list (lstyle * nat))
  (chk : task_status) : list_state :=
  let range := open_extent l (indent_of l) in
  LSt ind range range [] sty false false [] chk [].

Definition open_list (l : string) (ind : nat) (sty : list (lstyle * nat))
  (chk : task_status) (descended : blocks * pstate) : blocks * pstate :=
  let (bs, inner) := descended in
  ([], PList (list_opened l ind sty chk) (rev bs) inner).

(*
Tight/loose bookkeeping
-----------------------

Three events move the flags. *)

(* A blank line inside the list arms the flag. *)
Definition list_blank (ls : list_state) : list_state :=
  LSt (ls_indent ls) (ls_extent ls) (ls_item_extent ls)
      (ls_item_extents ls) (ls_styles ls) (ls_loose ls) true (ls_items ls)
      (ls_check ls) (ls_checks ls).

(* A sibling's candidate set, intersected into this list's.  Separate
   from `list_next` so that the tight/loose lemmas, which say nothing
   about styles, keep quantifying over an arbitrary `list_state`. *)
Definition list_narrow (ls : list_state) (ns : list (lstyle * nat))
  : list_state :=
  LSt (ls_indent ls) (ls_extent ls) (ls_item_extent ls)
      (ls_item_extents ls) ns (ls_loose ls) (ls_blanks ls) (ls_items ls)
      (ls_check ls) (ls_checks ls).

(* Narrowing to what is already there changes nothing.  This is what
   makes the uniformity chain blind to styles: a canonical rendering
   repeats one marker, so every sibling re-offers the style the list
   already has. *)
Lemma list_narrow_id : forall ls, list_narrow ls (ls_styles ls) = ls.
Proof. intros ls. destruct ls. reflexivity. Qed.

(* Does a blank line arriving here come to rest inside something the item
   still has open?  A div, a code block, a nested list and an unfinished
   attribute spec survive a blank and absorb it.  A block quote, a
   heading and a reference definition close and let it through, and
   pending attributes are not a container.

   The rule is about the container stack after the line, but `step` is
   deterministic and a blank's effect on the top constructor depends on
   nothing else, so it is a predicate on the state before the descent.
   Reading it off `inner` rather than `inner'` keeps every pad lemma
   below one line. *)
(*
Claiming a block out of column
------------------------------

Section 5 of `.project/keyed-blocks.md`.  While a key's block is open
the enclosing containers stop asking about column and the line goes
straight down to the key.  The override lasts exactly as long as the
block, so the block has to announce its own end on a line of its own; a
paragraph, list, table or quote ends by being interrupted, and the
interrupting line is the one the container outside needed to see, so
there would be nothing for the override to last until (5.2).

The test reads the arriving line and not only the state, and that is
forced rather than convenient: on `- foo:` the key is still *waiting*
when the fence line arrives, so a test that asks whether a key holds an
open block answers no, the list closes, and nothing happens.  The block
can only be open once the line has been taken, which is what the test
decides.
*)

Definition announces_end (st : pstate) : bool :=
  match st with
  | PFence _ _ _ _ _ | PDiv _ _ _ _ _ _ => true
  | _ => false
  end.

Definition claimable (k : line_kind) : bool :=
  match k with
  | KThematic | KFence _ | KDiv _ _ => true
  | _ => false
  end.

Fixpoint key_claims (l : string) (st : pstate) : bool :=
  match st with
  (* `is_idle` is the key's own retraction test (6.1), which is what
     makes a blank end the override: the same condition that says the
     key may still claim says a blank retracts it. *)
  | PKey _ _ _ inner =>
      if is_idle inner then claimable (classify l) else announces_end inner
  (* Not a quote: 5.1 keeps the `>` prefix, so a line the override hands
     down could not enter one anyway.  These are the states `blank_safe`
     reads through, which is what ties the two together. *)
  | PList _ _ inner | PDiv _ _ _ _ _ inner
  | PFoot _ _ _ _ inner | PPend _ _ inner => key_claims l inner
  | _ => false
  end.

(* Whether a list hands this line to the current item: ordinarily the
   column test, and whatever the column when a key below claims it. *)
Definition list_takes (ls : list_state) (off : nat) (l : string)
  (inner : pstate) : bool :=
  (key_claims l inner || Nat.ltb (ls_indent ls) (off + indent_of l))%bool.

Fixpoint blank_absorbed (st : pstate) : bool :=
  match st with
  | PFence _ _ _ _ _ | PDiv _ _ _ _ _ _ | PList _ _ _
  | PAttr _ _ _ _ _ _ | PFoot _ _ _ _ _ => true
  (* A key absorbs nothing of its own: with its block still unopened a
     blank retracts it, which closes rather than continues, so an
     enclosing list is armed exactly as `- foo:` / blank / `- bar`
     needs (6.1). *)
  | PPend _ _ inner | PKey _ _ _ inner => blank_absorbed inner
  | _ => false
  end.

(* A sibling marker closes the current item and opens the next.  A blank
   armed since the item's last content line is a blank between items, so
   the marker spends it into looseness, whatever follows the marker on
   its line. *)
Definition list_next (ls : list_state) (item : blocks) (chk : task_status)
  (l : string) : list_state :=
  LSt (ls_indent ls) (touch_extent (ls_extent ls)) (open_extent l (indent_of l))
      (ls_item_extent ls :: ls_item_extents ls) (ls_styles ls)
      (ls_loose ls || ls_blanks ls)%bool false (item :: ls_items ls)
      chk (ls_check ls :: ls_checks ls).

(* The per-line transition, on fuel.  The only recursion is into a
   stripped quote prefix, and `classify_quote_length` says that line is
   strictly shorter, so the line's own length is always enough fuel.
   `step` below fixes it there, and `step_fuel_enough` retires it, so no
   downstream statement mentions fuel. *)
(* Columns a container prefix ate before handing down its residue.  The
   parser measures indentation in the original line's coordinates, so a
   nested marker's column survives the descent -- see the nested-list
   entry in .project/djotjs-divergences.md. *)
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
  | KQuote rest =>
      match quote_header rest with
      | Some (kind, fold, title) => open_callout l kind fold title
      | None => open_quote l (descend rest)
      end
  | KList sty core chk rest =>
      open_list l ind
        (with_starts (configured_list_styles sty chk) core)
        (configured_list_check chk)
        (descend (configured_list_rest chk rest))
  | KAttr ap => open_attr [] [] ind ap l
  | KFoot lbl rest => open_foot l ind lbl (descend rest)
  | KRef lbl v => open_ref l ind lbl v
  | KFence f => open_fence l ind f
  | k => open_kind l k
  end.

(* `open_line` is a case split on `direct_open` and nothing else, which
   is what lets a lemma about a kind it does not name stay stated over
   `open_kind`. *)
Local Lemma open_line_direct :
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
      | PFence f ind range opener acc =>
          (* Verbatim: only the close test, and the closing line is
             consumed rather than reprocessed, the one state that is not
             "continue or close-and-reopen".  A content line keeps
             whatever it is indented past the opener, and nothing before
             it. *)
          if fence_close f l
          then ([set_pos
                   (prov_with (extent_span (touch_extent range))
                      [(ROpenFence, opener);
                       (RCloseFence, line_span_from l (indent_of l))])
                   (fence_block f (line_texts (rev acc)))], PPara [])
          else ([], PFence f ind (touch_extent range) opener
                      (remember_line (drop_ws_upto (ind - off) l) :: acc))
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
          | Some lvl =>
              ([set_pos
                  (prov_at (span_through_line (stored_span (c :: cur'))))
                  (heading_block (S lvl) (c :: cur'))], PPara [])
          | None =>
          match classify l with
          | KBlank => close_reopen (PPara (c :: cur')) (open_kind l KBlank)
          | k =>
              if binterrupt k
              then close_reopen (PPara (c :: cur'))
                     (open_line descend (off + indent_of l) l k)
              else ([], PPara (remember_line (drop_leading_ws l) :: c :: cur'))
          end
          end
      | PParaOff koff cur =>
          (* The recovery's paragraph takes lines exactly as `PPara` does.
             The count rides along untouched, because it counts from the
             front and lines arrive at the back.  There is no idle case:
             `PParaOff` is never built with an empty `cur`. *)
          match bunderline_of l with
          | Some lvl =>
              ([set_pos (prov_at (span_through_line (stored_span cur)))
                  (heading_block_off koff (S lvl) cur)], PPara [])
          | None =>
          match classify l with
          | KBlank => close_reopen (PParaOff koff cur) (open_kind l KBlank)
          | k =>
              if binterrupt k
              then close_reopen (PParaOff koff cur)
                     (open_line descend (off + indent_of l) l k)
              else ([], PParaOff koff
                          (remember_line (drop_leading_ws l) :: cur))
          end
          end
      | PHeading lvl range cur =>
          (* Unlike a paragraph, a heading *is* interruptible: only a
             matching-level marker or a lazy text line continues it. *)
          match classify l with
          | KHeading lvl' rest =>
              if bheading_continues
              then if Nat.eqb lvl' lvl
                   then ([], PHeading lvl (touch_extent range)
                               (push_text rest cur))
                   else close_reopen (PHeading lvl range cur)
                          (open_kind l (KHeading lvl' rest))
              else close_reopen (PHeading lvl range cur)
                     (open_kind l (KHeading lvl' rest))
          | KText =>
              if bheading_continues
              then ([], PHeading lvl (touch_extent range)
                          (remember_line (drop_leading_ws l) :: cur))
              else close_reopen (PHeading lvl range cur) (open_kind l KText)
          | k =>
              close_reopen (PHeading lvl range cur)
                (open_line descend (off + indent_of l) l k)
          end
      | PQuote range header done inner =>
          match classify l with
          | KQuote rest =>
              (* continue: descend into the quote already open, keeping
                 what it has closed so far *)
              let (bs, inner') := step_fuel n' (off + consumed l rest) rest inner in
              ([], PQuote (touch_extent range) header (rev bs ++ done)%list inner')
          | k =>
              if is_lazy k inner
              then ([], PQuote (touch_extent range) header done (feed_lazy l inner))
              else close_reopen (PQuote range header done inner)
                     (open_line descend (off + indent_of l) l k)
          end
      | PDiv len cls range opener done inner =>
          (* The close test runs before the line reaches anything nested
             inside, and `div_close` strips leading whitespace, so an
             indented `:::` inside a list inside a div closes the div.
             Hence `div_uniformity`'s side condition reaches every line of
             the contents, not only the outermost ones.

             The closing line is consumed rather than reprocessed, as a
             code fence's is.  Otherwise the line descends unchanged at
             the same offset: a div eats no prefix.

             `in_fence` is checked first: inside an open code block a
             `:::` line is content, not a closer. *)
          if (negb (in_fence inner) && div_close len l)%bool
          then ([set_pos
                   (prov_with (extent_span (touch_extent range))
                      [(ROpenFence, opener);
                       (RCloseFence, line_span_from l (indent_of l))])
                   (div_block cls (rev done ++ finish inner)%list)], PPara [])
          else
            let (bs, inner') := step_fuel n' off l inner in
            ([], PDiv len cls (touch_extent range) opener
                    (rev bs ++ done)%list inner')
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
              if list_takes ls off l inner
              then
                (* indented past the marker: contents of the current
                   item.  The line is passed down unchanged: every
                   recognizer already skips leading whitespace, so block
                   structure is right; what the extra indent still costs
                   is inline and verbatim text, the same open indentation
                   gap quotes and headings have. *)
                let (bs, inner') := step_fuel n' off l inner in
                ([], PList (list_content ls k) (rev bs ++ done)%list inner')
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
                               (configured_list_check chk) l)
                               (rev bs) inner')
                    end
                | _ =>
                    if is_lazy k inner
                    then ([], PList (list_content ls k) done (feed_lazy l inner))
                    else close_reopen (PList ls done inner)
                           (open_line descend
                              (off + indent_of l) l k)
                end
          end
      | PAttr pend specs range ind ap slices =>
          (* A finished spec refuses every line and closes; an unfinished
             one takes the line only if it is indented past the opener;
             and a spec that fails, at either point, becomes a paragraph
             of the lines it ate.  In all three cases the line is
             reprocessed against what the container became.

             The failing indented line is part of that paragraph (it is
             frozen before it is fed) and a non-indented one is not, but
             both are handed to the recovered paragraph, which appends the
             one and closes on the other.  One equation covers both.  An
             earlier spec's attributes travel with the recovery, and
             `pend_result` attaches them to the paragraph when it closes.

             A blank line splits on the same indentation test.  Indented
             past the opener it is a continuation, fed to the machine but
             not recorded.  djot.js records it, so a spec that spans a
             blank and then fails gives a paragraph containing a blank
             line, which does not round-trip (`Wf.wf_block`); the
             divergence is confined to specs that both span a blank line
             and fail.  Not indented past it, the blank fails the spec and
             the recovery runs on that line: the recovered paragraph stays
             open and takes the blank without recording it, so `{%` /
             blank / `c` is one paragraph of two lines, and only a second
             blank closes it. *)
          if ap_done ap
          then step_fuel n' off l
                 (PPend (Attr.merge (ap_attrs ap) pend)
                    (specs ++ [extent_span range])%list (PPara []))
          else if Nat.ltb ind (off + indent_of l)
          then
            let ap' := attr_feed l ap in
            if ap_failed ap'
            then pend_result pend specs
                   (step_fuel n' off l (para_recover 1 slices))
            else ([], PAttr pend specs (touch_extent range) ind ap'
                        (push_text l slices))
          else if is_blank l
          then ([], PPend pend specs (para_recover 0 slices))
          else pend_result pend specs
                 (step_fuel n' off l (para_recover 0 slices))
      | PRef range ind lbl val =>
          (* A line indented past the bracket and carrying one
             whitespace-free run extends the destination; anything else
             ends the definition and is reprocessed at this level.  There
             is no failure case, since the definition is already complete
             when the state is entered, so unlike `PAttr` nothing is
             retracted. *)
          match (if Nat.ltb ind (off + indent_of l) then ref_cont l else None) with
          | Some t => ([], PRef (touch_extent range) ind lbl (val ++ t))
          | None =>
              let (bs, st') := step_fuel n' off l (PPara []) in
              ((set_pos (prov_at (extent_span range)) (ref_block lbl val)
                  :: bs)%list, st')
          end
      | PTable range rows cap =>
          (* Four rules, and which apply depends on what the table has
             seen.  A caption opener is read here rather than by
             `classify`, which confines the construct to a table (see
             `Line.caption_open`).  A line that looks like a row but fails
             to scan (an unclosed verbatim) is a `KText` line by then. *)
          match cap with
          | TCaption parts start ls =>
              (* The caption owns every nonblank line, row lines
                 included, and a blank ends it. *)
              if is_blank l
              then ((set_pos (Provenance (extent_span range) [] (table_parts cap))
                       (table_block (rev rows) cap) :: nil)%list, PPara [])
              else ([], PTable (touch_extent range) rows
                          (TCaption parts start
                            (remember_line (drop_leading_ws l) :: ls)))
          | _ =>
              match caption_open l with
              | Some rest =>
                  ([], PTable (touch_extent range) rows
                          (TCaption (cap_row_parts cap)
                            (spot_at l (indent_of l)) (push_text rest [])))
              | None =>
                  if is_blank l
                  then
                    (* The rows are over, but the table is not: a caption
                       may still follow, across any number of blanks. *)
                    ([], PTable range rows (TAfterBlank (cap_row_parts cap)))
                  else
                    match classify l, cap with
                    (* A blank between two rows starts a second table,
                       which is why `TAfterBlank` is a state and not a
                       flag on the blank itself. *)
                    | KRow r, TOpen parts =>
                        ([], PTable (touch_extent range) (r :: rows)
                          (TOpen (if pos_records then
                                   match table_row_part l r with
                                   | Some p => p :: parts
                                   | None => parts
                                   end else parts)))
                    | _, _ =>
                        let (bs, st') := step_fuel n' off l (PPara []) in
                        ((set_pos (Provenance (extent_span range) [] (table_parts cap))
                            (table_block (rev rows) cap) :: bs)%list, st')
                    end
              end
          end
      | PFoot range ind lbl done inner =>
          if is_blank l
          then let (bs, inner') := step_fuel n' off l inner in
               ([], PFoot (touch_extent range) ind lbl
                        (rev bs ++ done)%list inner')
          else if Nat.ltb ind (off + indent_of l)
          then let (bs, inner') := step_fuel n' off l inner in
               ([], PFoot (touch_extent range) ind lbl
                        (rev bs ++ done)%list inner')
          else if is_lazy (classify l) inner
          then ([], PFoot (touch_extent range) ind lbl done (feed_lazy l inner))
          else
            let (bs, st') := step_fuel n' off l (PPara []) in
            ((set_pos (prov_at (extent_span range))
                (foot_block lbl (rev done ++ finish inner)%list)
                :: bs)%list, st')
      | PPend pend specs inner =>
          (* Two lines are the pending attributes' own business, and only
             while nothing has claimed them yet: a blank line drops them,
             and another spec merges into them.  Every other line goes
             down to `inner` and gets decorated by whatever it closes. *)
          match classify l with
          | KBlank =>
              if is_idle inner then ([], PPara [])
              else pend_result pend specs (step_fuel n' off l inner)
          | KAttr ap =>
              if is_idle inner
              then open_attr pend specs (off + indent_of l) ap l
              else pend_result pend specs (step_fuel n' off l inner)
          | _ => pend_result pend specs (step_fuel n' off l inner)
          end
      | PKey range lbl src inner =>
          (* One line is the key's own business.  A blank arriving while
             nothing is open under it ends the key with no block, which
             is retraction (6.1); the test is `is_idle` and nothing else,
             because a blank reaches here only when nothing under the key
             claimed it first, and every container that survives a blank
             claims it.

             Every other line goes down and is answered by
             `key_result`. *)
          if (is_blank l && is_idle inner)%bool
          then ([posnode (prov_at (extent_span range))
                   (Para (para_inlines [src]))], PPara [])
          else key_result (touch_extent range) lbl src
                 (step_fuel n' off l inner)
      end
  end.

(* The transition proper.  Each descent either shortens the line (a
   quote prefix, a list marker) or drops a container from the state (a
   list item's contents), so line length plus nesting depth strictly
   decreases and this much fuel is always enough.  `step_fuel_enough`
   retires it, and it appears in no lemma statement. *)
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

Local Lemma step_fuel_stable :
  forall bound n off l st,
    n <= bound -> S (String.length l + pstate_depth st) <= n ->
    step_fuel n off l st
    = step_fuel (S (String.length l + pstate_depth st)) off l st.
Proof.
  induction bound as [|bound IH]; intros n off l st Hb Hn; [lia|].
  destruct n as [|n']; [lia|].
  cbn [step_fuel open_line].
  destruct st as [cur|hlvl hrng hcur|f fnd crng cop acc|qrng qhead done inner|dlen dcls drng dop ddone dinner|ls done inner|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner|trng trows tcap|ppend pspecs pinner|krng klbl ksrc kinner].
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
      destruct (list_takes ls off l inner).
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
      destruct (list_takes ls off l inner).
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
      destruct (list_takes ls off l inner).
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
    all: destruct (list_takes ls off l inner);
         [ rewrite (IH n' _ l inner) by lia;
           rewrite (IH (String.length l + S (pstate_depth inner)) _ l inner) by lia;
           reflexivity
         | reflexivity ].
  - (* an open attribute spec: every branch but "take the line" hands the
       line on, and each target is shallower than PAttr's depth of 2 *)
    cbn [pstate_depth] in Hn |- *.
    set (q := PPend (Attr.merge (ap_attrs aap) apend) (aspecs ++ [extent_span arng])%list (PPara [])).
    assert (Hq : pstate_depth q = 1) by reflexivity.
    destruct (ap_done aap).
    + rewrite (IH n' _ l q) by lia.
      rewrite (IH (String.length l + 2) _ l q) by lia.
      reflexivity.
    + assert (Hd : forall e, pstate_depth (para_recover e aslices) = 0)
        by reflexivity.
      destruct (Nat.ltb aind (off + indent_of l));
        [destruct (ap_failed (attr_feed l aap)); [|reflexivity]|];
        [ set (e := 1) | set (e := 0) ];
        rewrite (IH n' _ l (para_recover e aslices)) by (rewrite ?Hd; lia);
        rewrite (IH (String.length l + 2) _ l (para_recover e aslices))
          by (rewrite ?Hd; lia);
        reflexivity.
  - (* the recovery's paragraph: the branches an open paragraph has, and
       only the list one recurses *)
    cbn [pstate_depth] in Hn |- *.
    destruct (classify l) as [| |g|dl dc|rest|kl kr|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E;
      try reflexivity.
    destruct (binterrupt (KList m mc chk mr)) eqn:Ei; [|reflexivity].
    pose proof (configured_list_rest_length _ _ _ _ _ E) as Hlt.
    cbn [open_line pstate_depth]; rewrite ?Nat.add_0_r.
    rewrite (IH n' _ (configured_list_rest chk mr) (PPara []))
      by (cbn [pstate_depth]; lia).
    rewrite (IH (String.length l) _ (configured_list_rest chk mr) (PPara []))
      by (cbn [pstate_depth]; lia).
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
  - (* an open key: a blank arriving at an idle inner retracts it and
       recurses into nothing; every other line descends *)
    cbn [pstate_depth] in Hn |- *.
    destruct (is_blank l && is_idle kinner)%bool; [reflexivity|].
    rewrite (IH n' _ l kinner) by lia.
    rewrite (IH (String.length l + S (pstate_depth kinner)) _ l kinner) by lia.
    reflexivity.
Qed.

Lemma step_fuel_enough :
  forall n l st,
    S (String.length l + pstate_depth st) <= n -> step_fuel n 0 l st = step l st.
Proof. intros n l st H. apply (step_fuel_stable n); lia. Qed.

(* The same, at an arbitrary offset: descents need it, since only the
   outermost call runs at offset 0. *)
Local Lemma step_fuel_enough_off :
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

(* The shift, on a list: its indent is the only column it records.  Its
   extents are measured from the end of the line and do not move. *)
Local Definition ls_pad (n : nat) (ls : list_state) : list_state :=
  LSt (n + ls_indent ls) (ls_extent ls) (ls_item_extent ls)
      (ls_item_extents ls) (ls_styles ls) (ls_loose ls) (ls_blanks ls)
      (ls_items ls) (ls_check ls) (ls_checks ls).

(* The shift, on the state: every recorded column moves by n. *)
Fixpoint pad_state (n : nat) (st : pstate) : pstate :=
  match st with
  | PFence f ind range opener acc => PFence f (n + ind) range opener acc
  | PQuote range header done inner =>
      PQuote range header done (pad_state n inner)
  | PDiv len cls range opener done inner =>
      PDiv len cls range opener done (pad_state n inner)
  | PList ls done inner => PList (ls_pad n ls) done (pad_state n inner)
  | PAttr pend specs range ind ap slices =>
      PAttr pend specs range (n + ind) ap slices
  | PRef range ind lbl val => PRef range (n + ind) lbl val
  | PFoot range ind lbl done inner =>
      PFoot range (n + ind) lbl done (pad_state n inner)
  | PPend pend specs inner => PPend pend specs (pad_state n inner)
  | PKey range lbl src inner => PKey range lbl src (pad_state n inner)
  | _ => st
  end.

(* The recovery's paragraph records no column, so padding leaves it
   alone.  `pad_state`'s catch-all says this; the lemma exists so the
   shift proof can rewrite without unfolding `para_recover`. *)
Local Lemma pad_state_para_recover :
  forall n e sl, pad_state n (para_recover e sl) = para_recover e sl.
Proof. reflexivity. Qed.

Local Lemma ltb_add_mono_l :
  forall n a b, Nat.ltb (n + a) (n + b) = Nat.ltb a b.
Proof.
  intros n a b. destruct (Nat.ltb a b) eqn:E.
  - apply Nat.ltb_lt. apply Nat.ltb_lt in E. lia.
  - apply Nat.ltb_ge. apply Nat.ltb_ge in E. lia.
Qed.

Local Lemma pad_state_in_fence :
  forall n st, in_fence (pad_state n st) = in_fence st.
Proof.
  intros n st.
  induction st as [| | |qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    cbn [pad_state in_fence]; try reflexivity; exact IH.
Qed.

Local Lemma pad_state_depth :
  forall n st, pstate_depth (pad_state n st) = pstate_depth st.
Proof.
  intros n st. induction st as [| | |qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    try reflexivity; cbn [pad_state pstate_depth]; rewrite IH; reflexivity.
Qed.

(* finish reads a list's spacing and items, never its column. *)
Lemma pad_state_finish :
  forall n st, finish (pad_state n st) = finish st.
Proof.
  intros n st. induction st as [| | |qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    try reflexivity; cbn [pad_state finish]; rewrite IH; reflexivity.
Qed.

Local Lemma pad_state_lazy_ok :
  forall n st, lazy_ok (pad_state n st) = lazy_ok st.
Proof.
  intros n st. induction st as [cur| | |qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    try reflexivity; cbn [pad_state lazy_ok]; exact IH.
Qed.

Local Lemma pad_state_feed_lazy :
  forall n l st, feed_lazy l (pad_state n st) = pad_state n (feed_lazy l st).
Proof.
  intros n l st.
  induction st as [cur|lvl cur| |qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    cbn [pad_state feed_lazy]; try reflexivity; rewrite IH; reflexivity.
Qed.

(* The three flag updates preserve ls_indent, so each commutes with the
   shift. *)
Local Lemma pad_list_blank :
  forall n ls,
    list_blank (ls_pad n ls)
    = ls_pad n (list_blank ls).
Proof. intros n ls. destruct ls. reflexivity. Qed.

(* Padding never changes which constructor is on top, so the blank's
   "is a list open here" test is pad-invariant. *)
Lemma pad_state_is_idle :
  forall n st, is_idle (pad_state n st) = is_idle st.
Proof. intros n st. destruct st; reflexivity. Qed.

Lemma pad_state_blank_absorbed :
  forall n st, blank_absorbed (pad_state n st) = blank_absorbed st.
Proof.
  intros n st.
  induction st as [| | |qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH
                  |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
                  |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    try reflexivity; cbn [pad_state blank_absorbed]; exact IH.
Qed.


(* A pad shifts columns and moves no line, and `key_claims` reads a line
   and a shape but no column, so the override survives `step_fuel_shift`
   and `step_fuel_pad` on its own account. *)
Lemma pad_state_announces_end :
  forall n st, announces_end (pad_state n st) = announces_end st.
Proof. intros n st. destruct st; reflexivity. Qed.

Local Lemma pad_state_key_claims :
  forall n l st, key_claims l (pad_state n st) = key_claims l st.
Proof.
  intros n l st.
  induction st as [| | |qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH
                  |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
                  |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    try reflexivity; cbn [pad_state key_claims]; try exact IH.
  rewrite pad_state_is_idle, pad_state_announces_end. reflexivity.
Qed.

(* A pad is invisible to the override for the same reason it is
   invisible to the classifier: the line's kind is what the test reads. *)
Local Lemma key_claims_ws_prefix :
  forall p l st, is_blank p = true ->
    key_claims (p ++ l) st = key_claims l st.
Proof.
  intros p l st Hp.
  induction st as [| | |qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH
                  |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
                  |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    try reflexivity; cbn [key_claims]; try exact IH.
  rewrite (classify_ws_prefix p l Hp). reflexivity.
Qed.

Local Lemma pad_state_list_takes :
  forall n ls off l inner,
    list_takes (ls_pad n ls)
               (n + off) l (pad_state n inner)
    = list_takes ls off l inner.
Proof.
  intros n ls off l inner. unfold list_takes.
  rewrite pad_state_key_claims. cbn [ls_pad ls_indent].
  rewrite <- Nat.add_assoc, ltb_add_mono_l. reflexivity.
Qed.

Local Lemma pad_list_content :
  forall n ls k,
    list_content (ls_pad n ls) k
    = ls_pad n (list_content ls k).
Proof. intros n ls k. destruct ls; destruct k; reflexivity. Qed.

Local Lemma pad_list_narrow :
  forall n ls ns,
    list_narrow (ls_pad n ls) ns
    = ls_pad n (list_narrow ls ns).
Proof. intros n ls ns. destruct ls. reflexivity. Qed.

Local Lemma pad_list_next :
  forall n ls item chk l,
    list_next (ls_pad n ls) item chk l = ls_pad n (list_next ls item chk l).
Proof. intros n ls item chk l. destruct ls. reflexivity. Qed.

(* The two shapes `pad_state` leaves behind, as `close_reopen` sees them. *)
Local Lemma finish_pad_list :
  forall n ls done inner,
    finish (PList (ls_pad n ls) done (pad_state n inner))
    = finish (PList ls done inner).
Proof.
  intros n ls done inner. cbn [finish].
  rewrite (pad_state_finish n inner). destruct ls. reflexivity.
Qed.

Local Lemma finish_pad_div :
  forall n len cls range opener done inner,
    finish (PDiv len cls range opener done (pad_state n inner))
    = finish (PDiv len cls range opener done inner).
Proof.
  intros n len cls range opener done inner. cbn [finish].
  rewrite (pad_state_finish n inner). reflexivity.
Qed.

Local Lemma finish_pad_quote :
  forall n range header done inner,
    finish (PQuote range header done (pad_state n inner))
    = finish (PQuote range header done inner).
Proof.
  intros n range header done inner. cbn [finish].
  rewrite (pad_state_finish n inner).
  reflexivity.
Qed.

(* `open_kind`'s text arm is a case split (a line that opens a paragraph
   may open a key instead), and the shift and pad proofs meet it wherever
   a line opens one.  Neither branch records a column, so both close the
   same way. *)
Ltac key_open_cases :=
  cbn [open_kind]; unfold open_text;
  match goal with
  | [ |- context [ if ?b then key_split ?l else None ] ] =>
      destruct (if b then key_split l else None) as [[? ?]|]
  end.

(** Moving the whole run `k` columns to the right moves every recorded
    column by `k` and changes nothing else -- not the blocks, not the
    tight/loose flags, not which branch any line takes. *)
Lemma step_fuel_shift :
  forall n k off l st,
    step_fuel n (k + off) l (pad_state k st)
    = (fst (step_fuel n off l st), pad_state k (snd (step_fuel n off l st))).
Proof.
  induction n as [|n IH]; intros k off l st; [reflexivity|].
  destruct st as [cur|hlvl hrng hcur|f fnd crng cop acc|qrng qhead done inner|dlen dcls drng dop ddone dinner|ls done inner|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner|trng trows tcap|ppend pspecs pinner|krng klbl ksrc kinner].
  (* idle, or an open paragraph *)
  { cbn [pad_state step_fuel open_line].
    destruct cur as [|c cur'].
    { destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy];
        try reflexivity; try (key_open_cases; reflexivity);
        try (cbn [open_fence fst snd pad_state]; rewrite Nat.add_assoc;
             reflexivity).
      { cbn [open_kind fst snd pad_state]. destruct bdivs; reflexivity. }
      { rewrite <- Nat.add_assoc.
        pose proof (IH k (off + consumed l rest) rest (PPara [])) as H;
          cbn [pad_state] in H; rewrite H.
        destruct (step_fuel n (off + consumed l rest) rest (PPara []))
          as [bs inner'] eqn:Ed.
        destruct (quote_header rest)
          as [[[kind fold] title]|];
          cbn [open_callout open_quote fst snd pad_state]; reflexivity. }
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
        try reflexivity; try (key_open_cases; reflexivity).
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
      destruct (quote_header rest)
        as [[[kind fold] title]|];
        cbn [close_reopen open_callout open_quote fst snd pad_state];
        reflexivity. }
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
    { destruct bheading_continues;
        [reflexivity|key_open_cases; reflexivity]. } }
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
      { key_open_cases;
        cbn [close_reopen open_kind fst snd pad_state];
        rewrite finish_pad_quote; reflexivity. } } }
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
    all: rewrite pad_state_list_takes.
    all: destruct (list_takes ls off l inner) eqn:Elt.
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
    { cbn [close_reopen open_fence fst snd pad_state].
      rewrite finish_pad_list, Nat.add_assoc. reflexivity. }
    (* div *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      destruct (@bdivs K); cbn [close_reopen fst snd pad_state];
      rewrite finish_pad_list; reflexivity. }
    (* quote *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
    { rewrite <- Nat.add_assoc.
      pose proof (IH k (off + consumed l rest) rest (PPara [])) as H;
        cbn [pad_state] in H; rewrite H.
      destruct (step_fuel n (off + consumed l rest) rest (PPara []))
        as [bs inner'] eqn:Ed.
      destruct (quote_header rest)
        as [[[kind fold] title]|];
        cbn [close_reopen open_callout open_quote fst snd pad_state];
        rewrite finish_pad_list; reflexivity. }
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
    { change (ls_styles (ls_pad k ls)) with (ls_styles ls).
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
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
    { unfold open_attr. destruct (@battrs K);
        cbn [close_reopen fst snd pad_state];
        rewrite ?Nat.add_assoc, finish_pad_list; reflexivity. }
    (* footnote definition *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
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
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
    { cbn [close_reopen open_ref fst snd pad_state].
      rewrite Nat.add_assoc, finish_pad_list. reflexivity. }
    (* table row *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
    { cbn [is_lazy close_reopen open_kind fst snd pad_state].
      destruct (@btables K); cbn [close_reopen fst snd pad_state];
        rewrite finish_pad_list; reflexivity. }
    (* text *)
    { rewrite (IH k off l inner).
      destruct (step_fuel n off l inner) as [bs inner'] eqn:Ed.
      cbn [fst snd pad_state]. rewrite pad_list_content. reflexivity. }
    { cbn [is_lazy]. rewrite pad_state_lazy_ok.
      destruct (lazy_ok inner) eqn:El.
      { cbn [pad_state]. rewrite pad_state_feed_lazy. reflexivity. }
      { key_open_cases;
        cbn [close_reopen open_kind fst snd pad_state];
        rewrite finish_pad_list; reflexivity. } } }
  (* attribute spec: it records no column, and neither does anything it
     turns into *)
  { cbn [pad_state step_fuel open_line].
    destruct (ap_done aap).
    { pose proof (IH k off l (PPend (Attr.merge (ap_attrs aap) apend) (aspecs ++ [extent_span arng])%list (PPara [])))
        as H; cbn [pad_state] in H; rewrite H; reflexivity. }
    { rewrite <- Nat.add_assoc, ltb_add_mono_l.
      destruct (Nat.ltb aind (off + indent_of l)).
      { destruct (ap_failed (attr_feed l aap)); [|reflexivity].
        pose proof (IH k off l (para_recover 1 aslices)) as H;
          rewrite pad_state_para_recover in H; rewrite H;
          destruct (step_fuel n off l (para_recover 1 aslices)) as [bs st'] eqn:Ed;
          cbn [pend_result fst snd pad_state]; destruct bs; reflexivity. }
      { destruct (is_blank l);
          [cbn [fst snd pad_state]; rewrite pad_state_para_recover; reflexivity|].
        pose proof (IH k off l (para_recover 0 aslices)) as H;
          rewrite pad_state_para_recover in H; rewrite H;
          destruct (step_fuel n off l (para_recover 0 aslices)) as [bs st'] eqn:Ed;
          cbn [pend_result fst snd pad_state]; destruct bs; reflexivity. } } }
  (* the recovery's paragraph: it records no column either, and takes the
     line exactly as an open paragraph does *)
  { cbn [pad_state step_fuel open_line].
    destruct (bunderline_of l) as [ulvl|] eqn:Eu;
      [cbn [fst snd pad_state]; reflexivity|].
    destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy];
      try reflexivity; try (key_open_cases; reflexivity).
    destruct (binterrupt (KList m mc chk mr)) eqn:Ei; [|reflexivity].
    rewrite <- !Nat.add_assoc.
    pose proof (IH k (off + consumed l (configured_list_rest chk mr))
                  (configured_list_rest chk mr) (PPara [])) as H;
      cbn [pad_state] in H; rewrite H.
    destruct (step_fuel n (off + consumed l (configured_list_rest chk mr))
                (configured_list_rest chk mr) (PPara []))
      as [bs inner'] eqn:Ed.
    cbn [close_reopen open_list fst snd pad_state]. reflexivity. }
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
      { unfold is_lazy. rewrite pad_state_lazy_ok.
        destruct (match classify l with KText => lazy_ok finner | _ => false end).
        { cbn [fst snd pad_state]. rewrite pad_state_feed_lazy. reflexivity. }
        pose proof (IH k off l (PPara [])) as H;
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
  (* an open key: it records no column either, and both the retraction
     and the descent are blind to the offset *)
  { cbn [pad_state step_fuel open_line]. rewrite (pad_state_is_idle k kinner).
    destruct (is_blank l && is_idle kinner)%bool; [reflexivity|].
    rewrite (IH k off l kinner).
    destruct (step_fuel n off l kinner) as [bs st'] eqn:Ed.
    cbn [key_result fst snd pad_state]. destruct bs; reflexivity. }
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
Local Lemma step_at_idle :
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
  forall l f ind range opener acc, fence_close f l = true ->
  step l (PFence f ind range opener acc)
  = ([set_pos
        (prov_with (extent_span (touch_extent range))
           [(ROpenFence, opener);
            (RCloseFence, line_span_from l (indent_of l))])
        (fence_block f (line_texts (rev acc)))], PPara []).
Proof. intros l f ind range opener acc H. unfold step. cbn [step_fuel open_line]. rewrite H. reflexivity. Qed.

(* The content line keeps what it is indented past the fence's own
   column.  `step` runs at offset 0, so that column is the whole of the
   subtraction here; inside a container `step_fuel` sees the offset the
   prefixes ate and takes the difference. *)
Lemma step_fence_content :
  forall l f ind range opener acc, fence_close f l = false ->
  step l (PFence f ind range opener acc)
  = ([], PFence f ind (touch_extent range) opener
           (remember_line (drop_ws_upto ind l) :: acc)).
Proof.
  intros l f ind range opener acc H. unfold step. cbn [step_fuel open_line]. rewrite H, Nat.sub_0_r.
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
  ([set_pos (prov_at (stored_span (c :: cur')))
      (mk (Para (para_inlines_at 0 (rev (c :: cur')))))], PPara []).
Proof.
  intros l c cur' H. unfold step. cbn [step_fuel open_line].
  rewrite (bunderline_of_blank l (classify_kblank_blank l H)), H. reflexivity.
Qed.

(* The same for the recovery's paragraph, which flushes with its own
   count. *)
Lemma step_para_off_flush :
  forall l k cur, classify l = KBlank ->
  step l (PParaOff k cur) =
  ([set_pos (prov_at (stored_span cur))
      (mk (Para (para_inlines_at k (rev cur))))], PPara []).
Proof.
  intros l k cur H. unfold step. cbn [step_fuel open_line].
  rewrite (bunderline_of_blank l (classify_kblank_blank l H)), H. reflexivity.
Qed.

(* Any other line continues it -- unless a setting says the line ends a
   paragraph, which is the whole of what `bcuts` answers. *)
Lemma step_para_cont :
  forall l c cur', classify l <> KBlank -> bcuts l = false ->
  step l (PPara (c :: cur'))
  = ([], PPara (remember_line (drop_leading_ws l) :: c :: cur')).
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
    (quote_header rest) = None ->
    step rest (PPara []) = (bs, inner) ->
    step l (PPara [])
    = ([], PQuote (open_extent l (indent_of l)) None (rev bs)
             (pad_state (consumed l rest) inner)).
Proof.
  intros l rest bs inner H Hheader Hr. unfold step at 1.
  cbn [step_fuel open_line]. rewrite H. cbn [open_line]. rewrite Hheader.
  change (step_fuel ?n (0 + consumed l rest) rest (PPara []))
    with (step_fuel n (consumed l rest) rest (PPara [])).
  rewrite (step_fuel_enough_off _ (consumed l rest) rest (PPara []))
    by (cbn [pstate_depth]; pose proof (classify_quote_length _ _ H); lia).
  change (step_fuel (S (String.length rest + pstate_depth (PPara [])))
            (consumed l rest) rest (PPara []))
    with (step_at (consumed l rest) rest (PPara [])).
  rewrite step_at_idle, Hr. reflexivity.
Qed.

Lemma step_callout_open :
  forall l rest kind fold title,
    classify l = KQuote rest ->
    (quote_header rest) =
      Some (kind, fold, title) ->
    step l (PPara []) =
      ([], PQuote (open_extent l (indent_of l))
        (Some (kind, fold, remember_line title)) [] (PPara [])).
Proof.
  intros l rest kind fold title H Hheader.
  unfold step. cbn [step_fuel open_line]. rewrite H.
  cbn [open_line]. rewrite Hheader. reflexivity.
Qed.

Lemma step_quote_open_no_blocks :
  forall l rest, classify l = KQuote rest -> fst (step l (PPara [])) = [].
Proof.
  intros l rest H. unfold step. cbn [step_fuel open_line].
  rewrite H. cbn [open_line].
  destruct (quote_header rest)
    as [[[kind fold] title]|]; cbn [open_callout open_quote fst];
    try reflexivity.
  destruct (step_fuel (String.length l + pstate_depth (PPara []))
    (0 + consumed l rest) rest (PPara []));
    cbn [open_quote fst]; reflexivity.
Qed.

Lemma step_quote_cont :
  forall l rest range header done inner bs inner',
    classify l = KQuote rest ->
    step_at (consumed l rest) rest inner = (bs, inner') ->
    step l (PQuote range header done inner)
    = ([], PQuote (touch_extent range) header (rev bs ++ done)%list inner').
Proof.
  intros l rest range header done inner bs inner' H Hr. unfold step at 1.
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
Local Lemma step_quote_lazy :
  forall l range header done inner,
    classify l = KText -> lazy_ok inner = true ->
    step l (PQuote range header done inner)
    = ([], PQuote (touch_extent range) header done (feed_lazy l inner)).
Proof.
  intros l range header done inner H Hl.
  unfold step. cbn [step_fuel open_line]. rewrite H.
  cbn [is_lazy]. rewrite Hl. reflexivity.
Qed.

(* Anything else closes the quote, and the line is then reprocessed
   outside it, by the same `open_kind` the idle state uses. *)
Lemma step_quote_close :
  forall l k range header done inner bs st',
    classify l = k -> direct_open k = true -> is_lazy k inner = false ->
    open_kind l k = (bs, st') ->
    step l (PQuote range header done inner) =
    (finish (PQuote range header done inner) ++ bs, st')%list.
Proof.
  intros l k range header done inner bs st' H Hk Hlz Ho.
  unfold step. cbn [step_fuel open_line].
  rewrite H.
  destruct k; try discriminate; rewrite Hlz; rewrite Ho; reflexivity.
Qed.

(* The same for every kind but a quote line: the line closes the quote
   and then does what it does at idle. *)
Lemma step_quote_close_any :
  forall l range header done inner,
    (forall r, classify l <> KQuote r) ->
    is_lazy (classify l) inner = false ->
    step l (PQuote range header done inner) =
    ((finish (PQuote range header done inner) ++ fst (step l (PPara [])))%list,
     snd (step l (PPara []))).
Proof.
  intros l range header done inner Hq Hlz.
  unfold step. cbn [step_fuel pstate_depth]. rewrite Nat.add_0_r.
  destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|]
    eqn:E; cbn [is_lazy] in Hlz |- *; try rewrite Hlz.
  all: try (exfalso; eapply Hq; reflexivity).
  all: unfold close_reopen.
  all: try (rewrite !open_line_direct by reflexivity;
            destruct (open_kind l _); reflexivity).
  all: cbn [open_line]; rewrite ?Nat.add_0_l.
  all: try (match goal with |- context [open_fence ?a ?b ?c] =>
              destruct (open_fence a b c); reflexivity end).
  all: try (match goal with |- context [open_attr ?a ?b ?c ?d ?e] =>
              destruct (open_attr a b c d e); reflexivity end).
  all: try (match goal with |- context [open_ref ?a ?b ?c ?d] =>
              destruct (open_ref a b c d); reflexivity end).
  (* the two that descend: the residue is shorter than the line, so the
     quote's fuel and the idle state's are both enough *)
  - pose proof (configured_list_rest_length _ _ _ _ _ E) as Hlen.
    rewrite (step_fuel_enough_off (String.length l + S (pstate_depth inner)))
      by (cbn [pstate_depth]; lia).
    rewrite (step_fuel_enough_off (String.length l)) by (cbn [pstate_depth]; lia).
    match goal with |- context [open_list ?a ?b ?c ?d ?e] =>
      destruct (open_list a b c d e); reflexivity end.
  - pose proof (classify_foot_length _ _ _ E) as Hlen.
    rewrite (step_fuel_enough_off (String.length l + S (pstate_depth inner)))
      by (cbn [pstate_depth]; lia).
    rewrite (step_fuel_enough_off (String.length l)) by (cbn [pstate_depth]; lia).
    match goal with |- context [open_foot ?a ?b ?c ?d] =>
      destruct (open_foot a b c d); reflexivity end.
Qed.

(*
An open div
-----------

Two equations, not seven: a div does not classify the line at all.  The
close test decides, and everything else descends unchanged.  This is the
whole of the div's continuation rule, and it is why the container needs
no share of the pad layer. *)

Lemma step_div_close :
  forall l len cls range opener done inner,
    in_fence inner = false -> div_close len l = true ->
    step l (PDiv len cls range opener done inner)
    = ([set_pos
          (prov_with (extent_span (touch_extent range))
             [(ROpenFence, opener);
              (RCloseFence, line_span_from l (indent_of l))])
          (div_block cls (rev done ++ finish inner)%list)], PPara []).
Proof.
  intros l len cls range opener done inner Hf H. unfold step. cbn [step_fuel open_line].
  rewrite Hf, H. reflexivity.
Qed.

Lemma step_div_cont :
  forall l len cls range opener done inner bs inner',
    (negb (in_fence inner) && div_close len l)%bool = false ->
    step l inner = (bs, inner') ->
    step l (PDiv len cls range opener done inner)
    = ([], PDiv len cls (touch_extent range) opener
             (rev bs ++ done)%list inner').
Proof.
  intros l len cls range opener done inner bs inner' H Hr. unfold step at 1.
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
indent: it can never close the list itself, only a later non-blank,
non-indented, non-matching-marker line can.  Everything else checks
indent first: indented past the marker it is item content; otherwise a
matching marker is a sibling, a different marker opens a new list, and
anything else is lazy continuation or a close, as for a quote. *)

Lemma step_list_open :
  forall l sty core chk rest bs inner,
    classify l = KList sty core chk rest ->
    step (configured_list_rest chk rest) (PPara []) = (bs, inner) ->
    step l (PPara []) =
      ([], PList (list_opened l (indent_of l)
                      (with_starts (configured_list_styles sty chk) core)
                      (configured_list_check chk))
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

(* The descend side keeps its column hypothesis: the override only
   weakens the test, so a line already indented past the marker is taken
   whatever any key below is doing. *)
Local Lemma list_takes_of_ltb :
  forall ls off l inner,
    Nat.ltb (ls_indent ls) (off + indent_of l) = true ->
    list_takes ls off l inner = true.
Proof.
  intros ls off l inner H. unfold list_takes. rewrite H. apply orb_true_r.
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
  cbn [step_fuel open_line pstate_depth]. rewrite H, !Nat.add_0_l.
  pose proof (list_takes_of_ltb ls 0 l inner
                (eq_trans (f_equal _ (Nat.add_0_l _)) Hind)) as Ht.
  destruct k eqn:Ek; try congruence;
    rewrite Ht;
    rewrite step_fuel_enough by (cbn [pstate_depth]; lia);
    rewrite Hr; reflexivity.
Qed.

Lemma step_list_sibling :
  forall l sty core chk rest ls done inner bs inner' s0 ss,
    classify l = KList sty core chk rest ->
    narrow (ls_styles ls) (configured_list_styles sty chk) = s0 :: ss ->
    list_takes ls 0 l inner = false ->
    step (configured_list_rest chk rest) (PPara []) = (bs, inner') ->
    step l (PList ls done inner) =
    ([], PList (list_next (list_narrow ls (s0 :: ss))
                  (rev done ++ finish inner)%list (configured_list_check chk) l)
           (rev bs)
           (pad_state (consumed l (configured_list_rest chk rest)) inner')).
Proof.
  intros l sty core chk rest ls done inner bs inner' s0 ss H Hm Hind Hr.
  unfold step at 1.
  cbn [step_fuel open_line pstate_depth]. rewrite H, ?Nat.add_0_l, Hind, Hm.
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

Local Lemma step_list_diffstyle :
  forall l sty core chk rest ls done inner bs inner',
    classify l = KList sty core chk rest ->
    narrow (ls_styles ls) (configured_list_styles sty chk) = [] ->
    list_takes ls 0 l inner = false ->
    step (configured_list_rest chk rest) (PPara []) = (bs, inner') ->
    step l (PList ls done inner) =
    (finish (PList ls done inner),
     PList (list_opened l (indent_of l)
                (with_starts (configured_list_styles sty chk) core)
                (configured_list_check chk)) (rev bs)
       (pad_state (consumed l (configured_list_rest chk rest)) inner')).
Proof.
  intros l sty core chk rest ls done inner bs inner' H Hm Hind Hr.
  unfold step at 1.
  cbn [step_fuel open_line pstate_depth]. rewrite H, ?Nat.add_0_l, Hind, Hm.
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

(* An attribute spec records a column, so it opens through `open_attr`
   rather than `open_kind` and needs its own pair of equations, as a
   quote does. *)
(* Stated through `open_attr` rather than through `PAttr`, because the
   spec opens only where the capability is on and the two consumers below
   need the equation at either setting. *)
Lemma step_attr_open :
  forall l ap, classify l = KAttr ap ->
  step l (PPara []) = open_attr [] [] (indent_of l) ap l.
Proof. intros l ap H. unfold step. cbn [step_fuel open_line]. rewrite H. reflexivity. Qed.

Lemma step_list_attr_close :
  forall l ap ls done inner,
    classify l = KAttr ap ->
    list_takes ls 0 l inner = false ->
    step l (PList ls done inner)
    = (finish (PList ls done inner), snd (open_attr [] [] (indent_of l) ap l)).
Proof.
  intros l ap ls done inner H Hind. unfold step. cbn [step_fuel open_line pstate_depth].
  rewrite H, ?Nat.add_0_l, Hind.
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
    list_takes ls 0 l inner = false ->
    step rest (PPara []) = (bs, inner') ->
    step l (PList ls done inner) =
      (finish (PList ls done inner),
       snd (open_foot l (indent_of l) lbl
              (bs, pad_state (consumed l rest) inner'))).
Proof.
  intros l lbl rest ls done inner bs inner' H Hind Hr.
  unfold step at 1. cbn [step_fuel open_line pstate_depth].
  rewrite H, ?Nat.add_0_l, Hind.
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
  step l (PPara [])
  = ([], PRef (open_extent l (indent_of l)) (indent_of l) lbl v).
Proof. intros l lbl v H. unfold step. cbn [step_fuel open_line]. rewrite H. reflexivity. Qed.

(* A code fence is not `direct_open` either, and for the same reason: it
   records the column its border sits at, so it opens through
   `open_fence`. *)
Lemma step_fence_open :
  forall l f, classify l = KFence f ->
  step l (PPara [])
  = ([], PFence f (indent_of l) (open_extent l (indent_of l))
           (line_span_from l (indent_of l)) []).
Proof. intros l f H. unfold step. cbn [step_fuel open_line]. rewrite H. reflexivity. Qed.

(* A blank line closes an open definition, emitting it, and leaves the
   idle state: `ref_cont` refuses a blank line at any column. *)
Lemma step_ref_blank :
  forall l range ind lbl v, classify l = KBlank ->
  step l (PRef range ind lbl v)
  = ([set_pos (prov_at (extent_span range)) (ref_block lbl v)], PPara []).
Proof.
  intros l range ind lbl v H. unfold step. cbn [step_fuel open_line].
  rewrite (ref_cont_blank l (classify_kblank_blank l H)),
          step_fuel_enough by (cbn [pstate_depth]; lia).
  rewrite (step_idle l KBlank H eq_refl).
  destruct (Nat.ltb ind (0 + indent_of l)); reflexivity.
Qed.

(* Stated rather than reduced: proofs that rewrite with it keep `finish`
   a constant, where `cbn [finish]` leaves a term that no longer matches
   an induction hypothesis. *)
Lemma finish_key :
  forall range lbl src inner,
    finish (PKey range lbl src inner)
    = pos_head (prov_at (extent_span range))
        (key_close (extent_start range) lbl src (finish inner)).
Proof. reflexivity. Qed.

(*
Key transitions
---------------

Two rules and nothing else.  A key records no column, so neither reads
the offset.
*)

(* A blank arriving while nothing is open under the key ends it with no
   block, which is retraction: the key line becomes the paragraph it
   would have been with the setting off (keyed-blocks 6). *)
Lemma step_key_retract :
  forall l range lbl src, is_blank l = true ->
  step l (PKey range lbl src (PPara []))
  = ([posnode (prov_at (extent_span range)) (Para (para_inlines [src]))],
     PPara []).
Proof.
  intros l range lbl src H. unfold step. cbn [step_fuel open_line is_idle].
  rewrite H. reflexivity.
Qed.

(* Every other line goes down to the block being built, and `key_result`
   answers with what comes back. *)
Lemma step_key_pass :
  forall l range lbl src inner,
    (is_blank l && is_idle inner)%bool = false ->
    step l (PKey range lbl src inner)
    = key_result (touch_extent range) lbl src (step l inner).
Proof.
  intros l range lbl src inner H. unfold step at 1.
  cbn [step_fuel pstate_depth]. rewrite H.
  rewrite step_fuel_enough by (cbn [pstate_depth]; lia). reflexivity.
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
    step l (PPara []) =
      ([], PTable (open_extent l (indent_of l)) [r]
             (TOpen (if pos_records then
                       match table_row_part l r with
                       | Some p => [p] | None => [] end else []))).
Proof.
  intros l r Htables H.
  rewrite (step_idle l (KRow r) H eq_refl).
  cbn [open_kind]. rewrite Htables. reflexivity.
Qed.

Local Lemma step_row_disabled :
  forall l r, btables = false -> classify l = KRow r ->
    step l (PPara [])
    = ([], PPara [remember_line (drop_leading_ws l)]).
Proof.
  intros l r Htables H.
  rewrite (step_idle l (KRow r) H eq_refl).
  cbn [open_kind]. rewrite Htables. reflexivity.
Qed.

Lemma step_table_row :
  forall l range rows parts r,
    caption_open l = None -> is_blank l = false -> classify l = KRow r ->
    step l (PTable range rows (TOpen parts))
    = ([], PTable (touch_extent range) (r :: rows)
            (TOpen (if pos_records then
                     match table_row_part l r with
                     | Some p => p :: parts | None => parts end
                   else parts))).
Proof.
  intros l range rows parts r Hc Hb H. unfold step. cbn [step_fuel open_line].
  rewrite Hc, Hb, H. reflexivity.
Qed.

Lemma step_table_blank :
  forall l range rows parts, is_blank l = true ->
  step l (PTable range rows (TOpen parts)) =
    ([], PTable range rows (TAfterBlank parts)).
Proof.
  intros l range rows parts H. unfold step. cbn [step_fuel open_line].
  rewrite (caption_open_blank l H), H. reflexivity.
Qed.

Lemma step_table_close :
  forall l range rows parts bs st',
    caption_open l = None -> is_blank l = false ->
    step l (PPara []) = (bs, st') ->
    step l (PTable range rows (TAfterBlank parts))
    = (set_pos (Provenance (extent_span range) []
                  (table_parts (TAfterBlank parts)))
         (table_block (rev rows) (TAfterBlank parts))
       :: bs, st')%list.
Proof.
  intros l range rows parts bs st' Hc Hb Hs. unfold step at 1. cbn [step_fuel open_line pstate_depth].
  rewrite Hc, Hb.
  replace (String.length l + 1) with (S (String.length l + 0)) by lia.
  change (step_fuel (S (String.length l + 0)) 0 l (PPara []))
    with (step l (PPara [])).
  rewrite Hs. destruct (classify l); reflexivity.
Qed.

Lemma step_list_ref_close :
  forall l lbl v ls done inner,
    classify l = KRef lbl v ->
    list_takes ls 0 l inner = false ->
    step l (PList ls done inner)
    = (finish (PList ls done inner),
       PRef (open_extent l (indent_of l)) (indent_of l) lbl v).
Proof.
  intros l lbl v ls done inner H Hind. unfold step. cbn [step_fuel open_line pstate_depth].
  rewrite H, ?Nat.add_0_l, Hind.
  cbn [close_reopen open_ref]. rewrite app_nil_r. reflexivity.
Qed.

Lemma step_list_quote_close :
  forall l rest ls done inner bs inner',
    classify l = KQuote rest ->
    (quote_header rest) = None ->
    list_takes ls 0 l inner = false ->
    step rest (PPara []) = (bs, inner') ->
    step l (PList ls done inner) =
      (finish (PList ls done inner),
       PQuote (open_extent l (indent_of l)) None (rev bs)
         (pad_state (consumed l rest) inner')).
Proof.
  intros l rest ls done inner bs inner' H Hheader Hind Hr.
  unfold step at 1. cbn [step_fuel open_line pstate_depth].
  rewrite H, ?Nat.add_0_l, Hind.
  change (step_fuel ?n (0 + consumed l rest) rest (PPara []))
    with (step_fuel n (consumed l rest) rest (PPara [])).
  rewrite (step_fuel_enough_off _ (consumed l rest) rest (PPara []))
    by (cbn [pstate_depth]; pose proof (classify_quote_length _ _ H); lia).
  change (step_fuel (S (String.length rest + pstate_depth (PPara [])))
            (consumed l rest) rest (PPara []))
    with (step_at (consumed l rest) rest (PPara [])).
  rewrite step_at_idle, Hr. cbn [close_reopen]. rewrite Hheader.
  cbn [open_quote].
  reflexivity.
Qed.

Lemma step_list_quote_close_any :
  forall l rest ls done inner,
    classify l = KQuote rest ->
    list_takes ls 0 l inner = false ->
    step l (PList ls done inner) =
      (finish (PList ls done inner), snd (step l (PPara []))).
Proof.
  intros l rest ls done inner H Hind.
  destruct (quote_header rest)
    as [[[kind fold] title]|] eqn:E.
  - unfold step. cbn [step_fuel open_line pstate_depth].
    rewrite H, ?Nat.add_0_l, Hind, E.
    unfold close_reopen. cbn [is_lazy open_line open_callout fst snd].
    rewrite E.
    reflexivity.
  - destruct (step rest (PPara [])) as [bs inner'] eqn:Er.
    rewrite (step_list_quote_close _ _ _ _ _ _ _ H E Hind Er).
    rewrite (step_quote_open _ _ _ _ H E Er). reflexivity.
Qed.

(* A code fence at or left of the marker closes the list and opens at its
   own column, the same way `step_list_quote_close` does for a quote. *)
Lemma step_list_fence_close :
  forall l f ls done inner,
    classify l = KFence f ->
    list_takes ls 0 l inner = false ->
    step l (PList ls done inner) =
      (finish (PList ls done inner),
       PFence f (indent_of l) (open_extent l (indent_of l))
         (line_span_from l (indent_of l)) []).
Proof.
  intros l f ls done inner H Hind. unfold step. cbn [step_fuel open_line].
  rewrite H, ?Nat.add_0_l, Hind. cbn [close_reopen open_fence].
  rewrite app_nil_r. reflexivity.
Qed.

Lemma step_list_close :
  forall l k ls done inner bs st',
    classify l = k -> direct_open k = true -> k <> KBlank ->
    list_takes ls 0 l inner = false ->
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
padded line starts.  `fence_cols_ok` is that condition, and `pad_safe`
excludes only an open attribute spec.  Both stop at
`PQuote`, because a quote prefix absorbs the pad before handing down its
residue. *)

(* Every fence open in this state sits at column `off` or further right.
   `step_fuel_pad` asks it of `String.length p + off`, and the two ways of
   supplying it are the two ways the lemma is used: at the top level `off`
   is 0 and `pad_state` has moved every column by `String.length p`
   (`fence_cols_ok_pad_state`), or there is no fence and it is vacuous. *)
Fixpoint fence_cols_ok (off : nat) (st : pstate) : bool :=
  match st with
  | PFence _ ind _ _ _ => Nat.leb off ind
  | PList _ _ inner | PDiv _ _ _ _ _ inner | PFoot _ _ _ _ inner
  | PPend _ _ inner | PKey _ _ _ inner => fence_cols_ok off inner
  | _ => true
  end.

(* Column zero is left of everything, which is what makes the condition
   free at `step`. *)
Local Lemma fence_cols_ok_0 : forall st, fence_cols_ok 0 st = true.
Proof.
  induction st as [| | | |dlen dcls drng dop ddone dinner IH|ls done inner IH| | | |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    cbn [fence_cols_ok]; try reflexivity; assumption.
Qed.

Local Lemma fence_cols_ok_pad_state :
  forall k off st, fence_cols_ok (k + off) (pad_state k st) = fence_cols_ok off st.
Proof.
  intros k off st.
  induction st as [| |f ind crng cop acc| |dlen dcls drng dop ddone dinner IH|ls done inner IH| | | |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    cbn [pad_state fence_cols_ok]; try reflexivity; try assumption.
  destruct (Nat.leb off ind) eqn:E.
  - apply Nat.leb_le. apply Nat.leb_le in E. lia.
  - apply Nat.leb_gt. apply Nat.leb_gt in E. lia.
Qed.

(* The empty line reads a column only to compare it with one the state
   records, and `pad_state k` puts every such column at `k` or further
   right, past both offsets: a bare `>` and `> ` hand the line down to
   the same effect. *)
Lemma step_fuel_empty_off :
  forall n k off off' st, off <= k -> off' <= k ->
    step_fuel n off "" (pad_state k st) = step_fuel n off' "" (pad_state k st).
Proof.
  induction n as [|n IH]; intros k off off' st H H'; [reflexivity|].
  destruct st; cbn [step_fuel pad_state].
  all: replace (classify "") with KBlank by reflexivity.
  all: try replace (bunderline_of "") with (@None nat)
         by (unfold bunderline_of; destruct (@bunderline K); reflexivity).
  all: rewrite ?(IH k off off' _ H H'); try reflexivity.
  - (* a fence keeps the line, and there is nothing in it to drop *)
    destruct (fence_close f ""); [reflexivity|].
    destruct (k + ind - off), (k + ind - off'); reflexivity.
  - (* an attribute spec: neither offset reaches its column *)
    replace (indent_of "") with 0 by reflexivity.
    replace (k + ind <? off + 0)%nat with false
      by (symmetry; apply Nat.ltb_ge; lia).
    replace (k + ind <? off' + 0)%nat with false
      by (symmetry; apply Nat.ltb_ge; lia).
    destruct (ap_done ap); [|reflexivity].
    change (PPend (Attr.merge (ap_attrs ap) pend) (specs ++ [extent_span range])
              (PPara []))
      with (pad_state k (PPend (Attr.merge (ap_attrs ap) pend)
                           (specs ++ [extent_span range]) (PPara []))).
    apply IH; assumption.
  - (* a reference definition: likewise *)
    replace (indent_of "") with 0 by reflexivity.
    replace (k + ind <? off + 0)%nat with false
      by (symmetry; apply Nat.ltb_ge; lia).
    replace (k + ind <? off' + 0)%nat with false
      by (symmetry; apply Nat.ltb_ge; lia).
    change (PPara []) with (pad_state k (PPara [])).
    rewrite (IH k off off' (PPara []) H H'). reflexivity.
Qed.

(* A quote line with nothing after its `>` reads the same with or without
   the space. *)
Lemma step_quote_bare :
  forall range header done inner,
    step ">" (PQuote range header done (pad_state quote_pad inner))
    = step "> " (PQuote range header done (pad_state quote_pad inner)).
Proof.
  intros range header done inner.
  unfold step. cbn [step_fuel String.length].
  replace (classify ">") with (KQuote "") by reflexivity.
  replace (classify "> ") with (KQuote "") by reflexivity.
  replace (consumed ">" "") with 1 by reflexivity.
  replace (consumed "> " "") with 2 by reflexivity.
  rewrite (step_fuel_enough_off
             (1 + pstate_depth (PQuote range header done (pad_state quote_pad inner))))
    by (cbn [String.length pstate_depth]; lia).
  rewrite (step_fuel_enough_off
             (2 + pstate_depth (PQuote range header done (pad_state quote_pad inner))))
    by (cbn [String.length pstate_depth]; lia).
  rewrite (step_fuel_empty_off _ quote_pad (0 + 1) (0 + 2) inner
             ltac:(cbv; lia) ltac:(cbv; lia)).
  reflexivity.
Qed.

(* A lazy line's pad is dropped wherever the line comes to rest -- the
   reason feed_lazy strips leading whitespace at all. *)
Local Lemma feed_lazy_ws_prefix :
  forall p l st,
    is_blank p = true -> feed_lazy (p ++ l) st = feed_lazy l st.
Proof.
  intros p l st Hp.
  induction st as [cur|lvl cur| |qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
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
  | PDiv _ _ _ _ _ inner => pad_safe inner
  | PFoot _ _ _ _ inner => pad_safe inner
  | PPend _ _ inner => pad_safe inner
  | PKey _ _ _ inner => pad_safe inner
  (* PAttr is the whole of the exclusion, and it is not `step_fuel_pad`
     that wants it: a pad is invisible to a spec, but a blank line inside
     an open one is a continuation line rather than a close, so
     `step_blank_finish` fails.  Nothing a canonical rendering emits
     opens a spec. *)
  | PAttr _ _ _ _ _ _ => false
  | _ => true
  end.

(* "A blank line closes whatever this state has open".  A spec fails it
   because a blank inside one is a continuation line, and a fence because
   a blank inside one is content.  Where `pad_safe` is asked of *every*
   line of a run, this is asked only of the state a run ends in, which is
   why an item may contain a code block and still satisfy it.  It is
   strictly stronger than `pad_safe`, but nothing needs to say so:
   `run_safe` carries both, each where it is wanted. *)
Fixpoint blank_safe (st : pstate) : bool :=
  match st with
  | PFence _ _ _ _ _ => false
  | PAttr _ _ _ _ _ _ => false
  | PList _ _ inner | PDiv _ _ _ _ _ inner | PFoot _ _ _ _ inner => blank_safe inner
  (* A div remains open across a blank.  That is safe for the ordinary
     finish equation, but not while a key is using the div to hold an
     enclosing container open: the key still owns the next line until
     the div's closing fence. *)
  | PKey _ _ _ inner => (blank_safe inner && negb (announces_end inner))%bool
  (* A settled attribute with nothing under it yet: a blank drops it, so
     the state is closed in this predicate's own sense, but the drop
     leaves an *idle* state behind, and a key above would then still be
     waiting after a blank that section 6 says retracts it.  No run
     produces this shape -- the line that settles an attribute is also
     the line that starts the block it decorates -- so excluding it costs
     no document and makes `step_blank_inner_settled` true as stated. *)
  | PPend _ _ inner => (blank_safe inner && negb (is_idle inner))%bool
  | _ => true
  end.

(* Two ways the override is ruled out.  A line that opens no
   announced-end block cannot be claimed by a key that is still waiting,
   and the `PKey` arm of `blank_safe` excludes a key that is already
   holding one.  Together they discharge the override wherever the
   arriving line is a marker. *)
Lemma key_claims_not_claimable :
  forall l st, claimable (classify l) = false -> blank_safe st = true ->
    key_claims l st = false.
Proof.
  intros l st Hcl.
  induction st as [| | |qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH
                  |apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval
                  |frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    cbn [blank_safe key_claims]; try reflexivity; try discriminate;
    try (intro H; exact (IH H)).
  - intro H. apply andb_true_iff in H as [H _]. exact (IH H).
  - intro H. apply andb_true_iff in H as [_ Hnot].
    destruct (is_idle kinner); [exact Hcl|].
    apply negb_true_iff in Hnot. exact Hnot.
Qed.

Lemma fence_cols_ok_pad :
  forall k st, fence_cols_ok k (pad_state k st) = true.
Proof.
  intros k st. rewrite <- (Nat.add_0_r k) at 1.
  rewrite fence_cols_ok_pad_state. apply fence_cols_ok_0.
Qed.

(* The recorded spots are counted from the end of the line, so a blank
   prefix leaves every one of them where it was. *)
Local Lemma open_extent_ws_prefix :
  forall p l, is_blank p = true ->
  open_extent (p ++ l) (indent_of (p ++ l)) = open_extent l (indent_of l).
Proof.
  intros p l Hp. unfold open_extent, spot_at.
  rewrite (indent_of_ws_prefix p l Hp), length_append.
  replace (String.length p + String.length l - (String.length p + indent_of l))
    with (String.length l - indent_of l) by lia.
  reflexivity.
Qed.

Local Lemma line_span_from_ws_prefix :
  forall p l, is_blank p = true ->
  line_span_from (p ++ l) (indent_of (p ++ l)) = line_span_from l (indent_of l).
Proof.
  intros p l Hp. unfold line_span_from, spot_at.
  rewrite (indent_of_ws_prefix p l Hp), length_append.
  replace (String.length p + String.length l - (String.length p + indent_of l))
    with (String.length l - indent_of l) by lia.
  reflexivity.
Qed.

Local Lemma spot_at_ws_prefix :
  forall p l, is_blank p = true ->
    spot_at (p ++ l) (indent_of (p ++ l)) = spot_at l (indent_of l).
Proof.
  intros p l Hp. unfold spot_at.
  rewrite (indent_of_ws_prefix p l Hp), length_append.
  replace (String.length p + String.length l - (String.length p + indent_of l))
    with (String.length l - indent_of l) by lia.
  reflexivity.
Qed.

Local Lemma open_quote_ws_prefix :
  forall p l d, is_blank p = true -> open_quote (p ++ l) d = open_quote l d.
Proof.
  intros p l [bs inner] Hp. unfold open_quote.
  rewrite (open_extent_ws_prefix p l Hp). reflexivity.
Qed.

Local Lemma open_callout_ws_prefix :
  forall p l kind fold title, is_blank p = true ->
    open_callout (p ++ l) kind fold title = open_callout l kind fold title.
Proof.
  intros p l kind fold title Hp. unfold open_callout.
  rewrite (open_extent_ws_prefix p l Hp). reflexivity.
Qed.

Local Lemma open_list_ws_prefix :
  forall p l ind sty chk d, is_blank p = true ->
  open_list (p ++ l) ind sty chk d = open_list l ind sty chk d.
Proof.
  intros p l ind sty chk [bs inner] Hp. unfold open_list, list_opened.
  rewrite (open_extent_ws_prefix p l Hp). reflexivity.
Qed.

Local Lemma open_fence_ws_prefix :
  forall p l ind f, is_blank p = true ->
  open_fence (p ++ l) ind f = open_fence l ind f.
Proof.
  intros p l ind f Hp. unfold open_fence.
  rewrite (open_extent_ws_prefix p l Hp), (line_span_from_ws_prefix p l Hp).
  reflexivity.
Qed.

Local Lemma open_ref_ws_prefix :
  forall p l ind lbl v, is_blank p = true ->
  open_ref (p ++ l) ind lbl v = open_ref l ind lbl v.
Proof.
  intros p l ind lbl v Hp. unfold open_ref.
  rewrite (open_extent_ws_prefix p l Hp). reflexivity.
Qed.

Local Lemma list_next_ws_prefix :
  forall p l ls item chk, is_blank p = true ->
  list_next ls item chk (p ++ l) = list_next ls item chk l.
Proof.
  intros p l ls item chk Hp. unfold list_next.
  rewrite (open_extent_ws_prefix p l Hp). reflexivity.
Qed.

Local Lemma open_foot_ws_prefix :
  forall p l ind lbl d, is_blank p = true ->
  open_foot (p ++ l) ind lbl d = open_foot l ind lbl d.
Proof.
  intros p l ind lbl [bs inner] Hp. unfold open_foot.
  rewrite (open_extent_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp).
  reflexivity.
Qed.

Ltac ws_openers p l Hp :=
  rewrite ?(open_quote_ws_prefix p l _ Hp),
    ?(open_callout_ws_prefix p l _ _ _ Hp),
    ?(open_list_ws_prefix p l _ _ _ _ Hp),
    ?(open_fence_ws_prefix p l _ _ Hp), ?(open_ref_ws_prefix p l _ _ _ Hp),
    ?(list_next_ws_prefix p l _ _ _ Hp), ?(open_foot_ws_prefix p l _ _ _ Hp),
    ?(table_row_part_ws_prefix p l _ Hp).

Local Lemma step_fuel_pad :
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
  destruct st as [cur|hlvl hrng hcur|f fnd crng cop acc|qrng qhead done inner|dlen dcls drng dop ddone dinner|ls done inner|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner|trng trows tcap|ppend pspecs pinner|krng klbl ksrc kinner].
  { cbn [step_fuel open_line]. rewrite (classify_ws_prefix p l Hp).
    destruct cur as [|c cur'].
    { destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy]; ws_openers p l Hp;
        rewrite ?(line_span_from_ws_prefix p l Hp);
        try reflexivity; try (key_open_cases; reflexivity).
      { (* thematic break: the whole line *)
        cbn [open_kind]. rewrite (line_span_from_ws_prefix p l Hp). reflexivity. }
      { (* fence: opens at the column its border sits at *)
        unfold open_fence. rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), Nat.add_assoc,
          (Nat.add_comm off (String.length p)). reflexivity. }
      { cbn [open_kind]. rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp).
        destruct (@bdivs K); reflexivity. }
      { rewrite (Hc rest ltac:(pose proof (classify_quote_length _ _ E); lia)),
                Nat.add_assoc, (Nat.add_comm off (String.length p)).
        destruct (quote_header rest)
          as [[[kind fold] title]|];
          rewrite ?(open_callout_ws_prefix p l _ _ _ Hp); reflexivity. }
      { (* heading: opens at its marker *)
        cbn [open_kind]. rewrite (open_extent_ws_prefix p l Hp). reflexivity. }
      { rewrite (Hc (configured_list_rest chk mr)
                   ltac:(pose proof (configured_list_rest_length _ _ _ _ _ E); lia)),
                ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), !Nat.add_assoc, (Nat.add_comm off (String.length p)).
        reflexivity. }
      { unfold open_attr. rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp),
          (drop_leading_ws_ws_prefix p l Hp), Nat.add_assoc,
          (Nat.add_comm off (String.length p)). reflexivity. }
      { unfold open_foot.
        rewrite (Hc frest ltac:(pose proof (classify_foot_length _ _ _ E); lia)),
                ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), ?(drop_leading_ws_ws_prefix p l Hp),
                !Nat.add_assoc, (Nat.add_comm off (String.length p)).
        reflexivity. }
      { unfold open_ref. rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), Nat.add_assoc,
          (Nat.add_comm off (String.length p)). reflexivity. }
      { cbn [open_kind]. rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp), (table_row_part_ws_prefix p l krow Hp).
        reflexivity. }
      { cbn [open_kind]. rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp).
        reflexivity. } }
    { rewrite (bunderline_of_ws_prefix p l Hp).
      destruct (bunderline_of l) as [ulvl|] eqn:Eu; [reflexivity|].
      destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy]; ws_openers p l Hp;
        try (cbn [open_kind close_reopen];
           rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp); reflexivity);
        try reflexivity.
      destruct (binterrupt (KList m mc chk mr)) eqn:Ei;
        [|rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp); reflexivity].
      rewrite (Hc (configured_list_rest chk mr)
                 ltac:(pose proof (configured_list_rest_length _ _ _ _ _ E); lia)),
              ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), !Nat.add_assoc,
              (Nat.add_comm off (String.length p)).
      reflexivity. } }
  { cbn [step_fuel open_line]. rewrite (classify_ws_prefix p l Hp).
    destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy]; ws_openers p l Hp;
      rewrite ?(line_span_from_ws_prefix p l Hp);
      try reflexivity; try (key_open_cases; reflexivity).
    { (* thematic break: the whole line *)
      cbn [close_reopen open_kind].
      rewrite (line_span_from_ws_prefix p l Hp). reflexivity. }
    { (* fence: opens at the column its border sits at *)
      cbn [close_reopen]; unfold open_fence.
      rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), Nat.add_assoc,
        (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [close_reopen open_kind].
      rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp).
      destruct (@bdivs K); reflexivity. }
    { rewrite (Hc rest ltac:(pose proof (classify_quote_length _ _ E); lia)),
              Nat.add_assoc, (Nat.add_comm off (String.length p)).
        destruct (quote_header rest)
          as [[[kind fold] title]|];
          rewrite ?(open_callout_ws_prefix p l _ _ _ Hp); reflexivity. }
    { (* heading: opens at its marker *)
      cbn [close_reopen open_kind].
      rewrite (open_extent_ws_prefix p l Hp). reflexivity. }
    { rewrite (Hc (configured_list_rest chk mr)
                 ltac:(pose proof (configured_list_rest_length _ _ _ _ _ E); lia)),
              ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), !Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [close_reopen]; unfold open_attr. rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp),
        (drop_leading_ws_ws_prefix p l Hp), Nat.add_assoc,
        (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [close_reopen]; unfold open_foot.
      rewrite (Hc frest ltac:(pose proof (classify_foot_length _ _ _ E); lia)),
              ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), ?(drop_leading_ws_ws_prefix p l Hp),
              !Nat.add_assoc, (Nat.add_comm off (String.length p)).
      reflexivity. }
    { cbn [close_reopen]; unfold open_ref. rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp),
        Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [open_kind]. rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp), (table_row_part_ws_prefix p l krow Hp).
        reflexivity. }
    { cbn [open_kind]. rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp).
      reflexivity. } }
  (* inside a fence: the close test reads through the pad, and the
     content line strips the pad along with the columns the fence's own
     column asks for -- which is what `fence_cols_ok` leaves room for *)
  { cbn [step_fuel open_line]. rewrite (fence_close_ws_prefix f p l Hp).
    destruct (fence_close f l);
      [rewrite (line_span_from_ws_prefix p l Hp); reflexivity|].
    cbn [fence_cols_ok] in Hcol. apply Nat.leb_le in Hcol.
    replace (fnd - off)
      with (String.length p + (fnd - (String.length p + off))) by lia.
    rewrite (drop_ws_upto_ws_prefix p _ l Hp). reflexivity. }
  { cbn [step_fuel open_line]. rewrite (classify_ws_prefix p l Hp).
    destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy]; ws_openers p l Hp;
      rewrite ?(line_span_from_ws_prefix p l Hp);
      try reflexivity; try (key_open_cases; reflexivity).
    { (* thematic break: the whole line *)
      cbn [close_reopen open_kind].
      rewrite (line_span_from_ws_prefix p l Hp). reflexivity. }
    { (* fence: opens at the column its border sits at *)
      cbn [close_reopen]; unfold open_fence.
      rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), Nat.add_assoc,
        (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [close_reopen open_kind].
      rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp).
      destruct (@bdivs K); reflexivity. }
    { rewrite (Hc rest ltac:(pose proof (classify_quote_length _ _ E); lia)),
              Nat.add_assoc, (Nat.add_comm off (String.length p)).
        destruct (quote_header rest)
          as [[[kind fold] title]|];
          rewrite ?(open_callout_ws_prefix p l _ _ _ Hp); reflexivity. }
    { (* heading: opens at its marker *)
      cbn [close_reopen open_kind].
      rewrite (open_extent_ws_prefix p l Hp). reflexivity. }
    { rewrite (Hc (configured_list_rest chk mr)
                 ltac:(pose proof (configured_list_rest_length _ _ _ _ _ E); lia)),
              ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), !Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [close_reopen]; unfold open_attr. rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp),
        (drop_leading_ws_ws_prefix p l Hp), Nat.add_assoc,
        (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [close_reopen]; unfold open_foot.
      rewrite (Hc frest ltac:(pose proof (classify_foot_length _ _ _ E); lia)),
              ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), ?(drop_leading_ws_ws_prefix p l Hp),
              !Nat.add_assoc, (Nat.add_comm off (String.length p)).
      reflexivity. }
    { cbn [close_reopen]; unfold open_ref. rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp),
        Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { cbn [is_lazy close_reopen open_kind].
      rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp), (table_row_part_ws_prefix p l krow Hp). reflexivity. }
    { cbn [is_lazy]. destruct (lazy_ok inner);
        [rewrite (feed_lazy_ws_prefix p l _ Hp)|
         cbn [close_reopen open_kind];
         rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp)]; reflexivity. } }
  (* div: the pad is invisible to the close test and passes through *)
  { cbn [pad_safe] in Hsafe; cbn [fence_cols_ok] in Hcol. cbn [step_fuel open_line].
    rewrite (div_close_ws_prefix p dlen l Hp).
    destruct (negb (in_fence dinner) && div_close dlen l)%bool;
      [rewrite (line_span_from_ws_prefix p l Hp); reflexivity|].
    rewrite (IH p off l dinner Hp Hsafe Hcol). reflexivity. }
  { cbn [pad_safe] in Hsafe; cbn [fence_cols_ok] in Hcol. cbn [step_fuel open_line].
    rewrite (classify_ws_prefix p l Hp).
    destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy].
    { rewrite (IH p off l inner Hp Hsafe Hcol). reflexivity. }
    all: ws_openers p l Hp.
    all: unfold list_takes; rewrite (key_claims_ws_prefix p l inner Hp).
    all: rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), Nat.add_assoc,
                 (Nat.add_comm off (String.length p)).
    all: destruct (key_claims l inner
                   || Nat.ltb (ls_indent ls)
                        (String.length p + off + indent_of l))%bool
           eqn:Elt;
         try (rewrite (IH p off l inner Hp Hsafe Hcol); reflexivity).
    { (* thematic break: the whole line *)
      cbn [is_lazy open_kind close_reopen].
      rewrite (line_span_from_ws_prefix p l Hp). reflexivity. }
    { reflexivity. }
    { cbn [is_lazy open_kind close_reopen].
      rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp).
      destruct (@bdivs K); reflexivity. }
    { rewrite (Hc rest ltac:(pose proof (classify_quote_length _ _ E); lia)),
              Nat.add_assoc, (Nat.add_comm off (String.length p)).
        destruct (quote_header rest)
          as [[[kind fold] title]|];
          rewrite ?(open_callout_ws_prefix p l _ _ _ Hp); reflexivity. }
    { (* heading: opens at its marker *)
      cbn [is_lazy open_kind close_reopen].
      rewrite (open_extent_ws_prefix p l Hp). reflexivity. }
    { destruct (narrow (ls_styles ls) (configured_list_styles m chk));
        ws_openers p l Hp;
        rewrite (Hc (configured_list_rest chk mr)
                   ltac:(pose proof (configured_list_rest_length _ _ _ _ _ E); lia)),
                !Nat.add_assoc, (Nat.add_comm off (String.length p));
        reflexivity. }
    { cbn [close_reopen]; unfold open_attr.
      rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp). reflexivity. }
    { unfold open_foot.
      rewrite (Hc frest ltac:(pose proof (classify_foot_length _ _ _ E); lia)),
              ?(drop_leading_ws_ws_prefix p l Hp),
              Nat.add_assoc, (Nat.add_comm off (String.length p)). reflexivity. }
    { reflexivity. }
    { cbn [is_lazy close_reopen open_kind].
      rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp), (table_row_part_ws_prefix p l krow Hp). reflexivity. }
    { cbn [is_lazy]. destruct (lazy_ok inner);
        [rewrite (feed_lazy_ws_prefix p l _ Hp)|
         cbn [close_reopen open_kind];
         rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp)]; reflexivity. } }
  { discriminate Hsafe. }
  (* the recovery's paragraph: the same branches an open paragraph takes,
     and the count rides through them untouched *)
  { cbn [step_fuel open_line]. rewrite (classify_ws_prefix p l Hp).
    rewrite (bunderline_of_ws_prefix p l Hp).
    destruct (bunderline_of l) as [ulvl|] eqn:Eu; [reflexivity|].
    destruct (classify l) as [| |g|dl dc|rest|klvl krest|m mc chk mr|kap|flbl frest|rlbl rval|krow|] eqn:E; cbn [open_line is_lazy]; ws_openers p l Hp;
      try (cbn [open_kind close_reopen];
         rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp); reflexivity);
      try reflexivity.
    destruct (binterrupt (KList m mc chk mr)) eqn:Ei;
      [|rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp); reflexivity].
    rewrite (Hc (configured_list_rest chk mr)
               ltac:(pose proof (configured_list_rest_length _ _ _ _ _ E); lia)),
            ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), !Nat.add_assoc,
            (Nat.add_comm off (String.length p)).
    reflexivity. }
  (* reference definition: the pad moves the opener's column, and the
     continuation test reads the line through drop_leading_ws *)
  { cbn [step_fuel open_line]. unfold ref_cont.
    rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), (drop_leading_ws_ws_prefix p l Hp),
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
    { rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp), Nat.add_assoc,
              (Nat.add_comm off (String.length p)).
      destruct (Nat.ltb find (String.length p + off + indent_of l)).
      { rewrite (IH p off l finner Hp Hsafe Hcol). reflexivity. }
      rewrite (classify_ws_prefix p l Hp).
      destruct (is_lazy (classify l) finner);
        [rewrite (feed_lazy_ws_prefix p l _ Hp); reflexivity|].
      rewrite (IH p off l (PPara []) Hp eq_refl eq_refl). reflexivity. } }
  (* table: the pad is invisible to the row scanner and to the caption
     opener alike, and the line that ends the table is reprocessed from
     idle *)
  { cbn [step_fuel open_line]. rewrite (caption_open_ws_prefix p l Hp),
      (is_blank_ws_prefix p l Hp), (classify_ws_prefix p l Hp),
      (drop_leading_ws_ws_prefix p l Hp).
    destruct tcap as [parts|parts|parts start ls].
    { destruct (caption_open l); [rewrite (spot_at_ws_prefix p l Hp); reflexivity|].
      destruct (is_blank l); [reflexivity|].
      destruct (classify l) eqn:E; cbn [open_line is_lazy]; ws_openers p l Hp; try reflexivity;
        rewrite (IH p off l (PPara []) Hp eq_refl eq_refl); reflexivity. }
    { destruct (caption_open l); [rewrite (spot_at_ws_prefix p l Hp); reflexivity|].
      destruct (is_blank l); [reflexivity|].
      destruct (classify l) eqn:E; cbn [open_line is_lazy]; ws_openers p l Hp;
        rewrite (IH p off l (PPara []) Hp eq_refl eq_refl); reflexivity. }
    { destruct (is_blank l); reflexivity. } }
  (* pending attributes: transparent *)
  { cbn [pad_safe] in Hsafe; cbn [fence_cols_ok] in Hcol. cbn [step_fuel open_line].
    rewrite (classify_ws_prefix p l Hp).
    destruct (classify l) eqn:E; cbn [open_line is_lazy]; ws_openers p l Hp;
      try (destruct (is_idle pinner);
           [unfold open_attr; rewrite ?(open_extent_ws_prefix p l Hp), ?(line_span_from_ws_prefix p l Hp), ?(indent_of_ws_prefix p l Hp),
              (drop_leading_ws_ws_prefix p l Hp), Nat.add_assoc,
              (Nat.add_comm off (String.length p)); reflexivity|]);
      rewrite (IH p off l pinner Hp Hsafe Hcol); reflexivity. }
  (* an open key: transparent too -- the pad reaches the retraction test
     only through `is_blank`, which reads through it *)
  { cbn [pad_safe] in Hsafe; cbn [fence_cols_ok] in Hcol.
    cbn [step_fuel open_line]. rewrite (is_blank_ws_prefix p l Hp).
    destruct (is_blank l && is_idle kinner)%bool; [reflexivity|].
    rewrite (IH p off l kinner Hp Hsafe Hcol). reflexivity. }
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

(*
Lazy lines
----------

The djot syntax reference lets a paragraph line inside a block quote,
list item or footnote omit the container's prefix.  The two theorems
below say what such a line does: it continues the innermost paragraph
and closes nothing (`step_lazy`), exactly as the same line with the
prefix written out would (`step_lazy_restore`).  Both are over every
state with an open paragraph, reachable or not.
*)

(* The prefix the open containers expect in front of a line whose first
   character sits at column `col`: `> ` for a quote, and for a list item
   or a footnote enough spaces to reach one past its column. *)
Fixpoint spine_prefix (col : nat) (st : pstate) : string :=
  match st with
  | PQuote _ _ _ inner => "> " ++ spine_prefix (col + 2) inner
  | PList ls _ inner =>
      let k := S (ls_indent ls) - col in blanks k ++ spine_prefix (col + k) inner
  | PFoot _ ind _ _ inner =>
      let k := S ind - col in blanks k ++ spine_prefix (col + k) inner
  | PDiv _ _ _ _ _ inner | PPend _ _ inner | PKey _ _ _ inner =>
      spine_prefix col inner
  | _ => ""
  end.

(* A state with no container open, where a prefix ends. *)
Definition spine_leaf (st : pstate) : bool :=
  match st with
  | PQuote _ _ _ _ | PList _ _ _ | PFoot _ _ _ _ _
  | PDiv _ _ _ _ _ _ | PPend _ _ _ | PKey _ _ _ _ => false
  | _ => true
  end.

(* Every prefix the open containers accept in front of a line whose first
   character sits at column `col`, of which `spine_prefix` is one: `> `
   for a quote, after any blanks, and for a list item or a footnote any
   run of blanks that reaches past its column.  A div, pending attributes
   and a key take no prefix of their own, and the innermost block any
   indentation. *)
Inductive spine_spelling : nat -> pstate -> string -> Prop :=
  | SpLeaf : forall col st k, spine_leaf st = true -> spine_spelling col st (blanks k)
  | SpQuote : forall col j range header done inner p,
      spine_spelling (col + j + 2) inner p ->
      spine_spelling col (PQuote range header done inner) (blanks j ++ "> " ++ p)
  | SpList : forall col k ls done inner p,
      ls_indent ls < col + k ->
      spine_spelling (col + k) inner p ->
      spine_spelling col (PList ls done inner) (blanks k ++ p)
  | SpFoot : forall col k range ind lbl done inner p,
      ind < col + k ->
      spine_spelling (col + k) inner p ->
      spine_spelling col (PFoot range ind lbl done inner) (blanks k ++ p)
  | SpDiv : forall col len cls range opener done inner p,
      spine_spelling col inner p ->
      spine_spelling col (PDiv len cls range opener done inner) p
  | SpPend : forall col pend specs inner p,
      spine_spelling col inner p ->
      spine_spelling col (PPend pend specs inner) p
  | SpKey : forall col range lbl src inner p,
      spine_spelling col inner p ->
      spine_spelling col (PKey range lbl src inner) p.

Lemma spine_prefix_spelling :
  forall st col, spine_spelling col st (spine_prefix col st).
Proof.
  induction st; intros col; cbn [spine_prefix];
    first [ apply (SpLeaf col _ 0); reflexivity
          | apply (SpQuote col 0); rewrite Nat.add_0_r; apply IHst
          | apply SpList; [lia | apply IHst]
          | apply SpFoot; [lia | apply IHst]
          | apply SpDiv; apply IHst
          | apply SpPend; apply IHst
          | apply SpKey; apply IHst ].
Qed.

Local Lemma lazy_ok_pad_safe : forall st, lazy_ok st = true -> pad_safe st = true.
Proof. induction st; cbn [lazy_ok pad_safe]; intros H; auto; discriminate. Qed.

Local Lemma lazy_ok_fence_cols :
  forall c st, lazy_ok st = true -> fence_cols_ok c st = true.
Proof. intros c. induction st; cbn [lazy_ok fence_cols_ok]; intros H; auto; discriminate. Qed.



Local Lemma classify_text_quote_nonblank :
  forall x, (classify x = KText \/ exists r, classify x = KQuote r) ->
    is_blank x = false.
Proof.
  intros x H. unfold classify in H. destruct (is_blank x); [|reflexivity].
  destruct H as [H|[r H]]; discriminate.
Qed.

Local Lemma step_fuel_lazy :
  forall st n off l,
    pstate_depth st < n -> lazy_ok st = true ->
    classify l = KText -> bunderline_of l = None ->
    step_fuel n off l st = ([], feed_lazy l st).
Proof.
  intros st. induction st as [cur|hlvl hrng hcur|f fnd crng cop acc|qrng qhead done inner IH|dlen dcls drng dop ddone dinner IH|ls done inner IH|apend aspecs arng aind aap aslices|okoff ocur|rrng rind rlbl rval|frng find flbl fdone finner IH|trng trows tcap|ppend pspecs pinner IH|krng klbl ksrc kinner IH];
    intros n off l Hn Hlazy Htext Hu; (destruct n as [|n]; [lia|]);
    cbn [lazy_ok pstate_depth] in Hlazy, Hn; try discriminate;
    assert (Hnb : is_blank l = false)
      by (apply classify_text_quote_nonblank; left; exact Htext);
    cbn [step_fuel feed_lazy].
  - (* paragraph *)
    destruct cur; [discriminate|]. rewrite Hu, Htext. reflexivity.
  - (* heading *)
    rewrite Htext, Hlazy. reflexivity.
  - (* quote *)
    rewrite Htext. cbn [is_lazy]. rewrite Hlazy. reflexivity.
  - (* div *)
    rewrite (classify_text_div_close dlen l Htext), andb_false_r.
    rewrite (IH n off l ltac:(lia) Hlazy Htext Hu). reflexivity.
  - (* list: taken by the item or lazy, the flags come out the same *)
    rewrite Htext. destruct (list_takes ls off l inner).
    + rewrite (IH n off l ltac:(lia) Hlazy Htext Hu). reflexivity.
    + cbn [is_lazy]. rewrite Hlazy. reflexivity.
  - (* the recovery's paragraph *)
    rewrite Hu, Htext. reflexivity.
  - (* footnote *)
    rewrite Hnb. destruct (find <? off + indent_of l)%nat.
    + rewrite (IH n off l ltac:(lia) Hlazy Htext Hu). reflexivity.
    + rewrite Htext. cbn [is_lazy]. rewrite Hlazy. reflexivity.
  - (* pending attributes *)
    rewrite Htext, (IH n off l ltac:(lia) Hlazy Htext Hu). reflexivity.
  - (* key *)
    rewrite Hnb. cbn [andb]. rewrite (IH n off l ltac:(lia) Hlazy Htext Hu).
    reflexivity.
Qed.


Local Lemma spelling_classify :
  forall col st p l, spine_spelling col st p -> classify l = KText ->
    classify (p ++ l) = KText \/ exists r, classify (p ++ l) = KQuote r.
Proof.
  intros col st p l H Hl. induction H; cbn [append]; auto;
    rewrite ?append_assoc;
    try rewrite (classify_ws_prefix _ _ (blanks_blank _)); auto.
  right. eexists. apply classify_quote_space.
Qed.

Local Lemma spelling_div_close :
  forall len col st p l, spine_spelling col st p -> classify l = KText ->
    div_close len (p ++ l) = false.
Proof.
  intros len col st p l H Hl. induction H; cbn [append];
    rewrite ?append_assoc;
    try rewrite (div_close_ws_prefix _ _ _ (blanks_blank _)); auto.
  - apply classify_text_div_close. exact Hl.
  - apply div_close_quote_space.
Qed.

Local Lemma step_fuel_spelling :
  forall col st p, spine_spelling col st p ->
  forall n l,
    pstate_depth st < n -> lazy_ok st = true ->
    classify l = KText -> bunderline_of l = None ->
    step_fuel n col (p ++ l) st = ([], feed_lazy l st).
Proof.
  intros col st p H.
  induction H as [col st k Hleaf|col j range header done inner p Hsp IH
    |col k ls done inner p Hk Hsp IH|col k range ind lbl done inner p Hk Hsp IH
    |col len cls range opener done inner p Hsp IH|col pend specs inner p Hsp IH
    |col range lbl src inner p Hsp IH];
    intros n l Hn Hlazy Htext Hu.
  - rewrite (step_fuel_lazy st n col (blanks k ++ l) Hn Hlazy
               ltac:(rewrite (classify_ws_prefix _ _ (blanks_blank _)); exact Htext)
               ltac:(rewrite (bunderline_of_ws_prefix _ _ (blanks_blank _)); exact Hu)).
    rewrite (feed_lazy_ws_prefix _ _ _ (blanks_blank _)). reflexivity.
  - (* quote: the blanks and `> ` are consumed, and the rest descends *)
    destruct n as [|n]; [cbn [pstate_depth] in Hn; lia|].
    cbn [lazy_ok pstate_depth] in Hlazy, Hn. cbn [step_fuel feed_lazy].
    rewrite !append_assoc, (classify_ws_prefix _ _ (blanks_blank _)),
      classify_quote_space.
    replace (consumed (blanks j ++ "> " ++ p ++ l) (p ++ l)) with (j + 2)
      by (unfold consumed; rewrite length_append, blanks_length;
          cbn [String.length append]; lia).
    rewrite Nat.add_assoc, (IH n l ltac:(lia) Hlazy Htext Hu). reflexivity.
  - (* list: the blanks reach past the item's column, so it takes the line *)
    pose proof (spelling_classify _ _ _ l (SpList col k ls done inner p Hk Hsp) Htext)
      as Hc.
    destruct n as [|n]; [cbn [pstate_depth] in Hn; lia|].
    cbn [lazy_ok pstate_depth] in Hlazy, Hn. cbn [step_fuel feed_lazy].
    rewrite append_assoc in Hc |- *.
    assert (Ht : forall x, list_takes ls col (blanks k ++ x) inner = true).
    { intros x. unfold list_takes.
      rewrite (indent_of_ws_prefix _ _ (blanks_blank _)), blanks_length.
      apply orb_true_iff. right. apply Nat.ltb_lt. lia. }
    destruct Hc as [Hc|[r Hc]]; rewrite Hc, Ht;
      rewrite (step_fuel_pad n _ col _ inner (blanks_blank _)
                 (lazy_ok_pad_safe _ Hlazy) (lazy_ok_fence_cols _ _ Hlazy)),
        blanks_length;
      rewrite (Nat.add_comm k col), (IH n l ltac:(lia) Hlazy Htext Hu);
      reflexivity.
  - (* footnote: likewise *)
    pose proof (spelling_classify _ _ _ l
                  (SpFoot col k range ind lbl done inner p Hk Hsp) Htext) as Hc.
    pose proof (classify_text_quote_nonblank _ Hc) as Hnb.
    destruct n as [|n]; [cbn [pstate_depth] in Hn; lia|].
    cbn [lazy_ok pstate_depth] in Hlazy, Hn. cbn [step_fuel feed_lazy].
    rewrite append_assoc in Hnb |- *.
    rewrite Hnb, (indent_of_ws_prefix _ _ (blanks_blank _)), blanks_length.
    replace (ind <? col + (k + indent_of (p ++ l)))%nat with true
      by (symmetry; apply Nat.ltb_lt; lia).
    rewrite (step_fuel_pad n _ col _ inner (blanks_blank _)
               (lazy_ok_pad_safe _ Hlazy) (lazy_ok_fence_cols _ _ Hlazy)),
      blanks_length, (Nat.add_comm k col), (IH n l ltac:(lia) Hlazy Htext Hu).
    reflexivity.
  - (* div *)
    pose proof (fun len => spelling_div_close len _ _ _ l Hsp Htext) as Hd.
    destruct n as [|n]; [cbn [pstate_depth] in Hn; lia|].
    cbn [lazy_ok pstate_depth] in Hlazy, Hn. cbn [step_fuel feed_lazy].
    rewrite Hd, andb_false_r, (IH n l ltac:(lia) Hlazy Htext Hu). reflexivity.
  - (* pending attributes *)
    pose proof (spelling_classify _ _ _ l Hsp Htext) as Hc.
    destruct n as [|n]; [cbn [pstate_depth] in Hn; lia|].
    cbn [lazy_ok pstate_depth] in Hlazy, Hn. cbn [step_fuel feed_lazy].
    destruct Hc as [Hc|[r Hc]]; rewrite Hc;
      rewrite (IH n l ltac:(lia) Hlazy Htext Hu); reflexivity.
  - (* key *)
    pose proof (classify_text_quote_nonblank _ (spelling_classify _ _ _ l Hsp Htext))
      as Hnb.
    destruct n as [|n]; [cbn [pstate_depth] in Hn; lia|].
    cbn [lazy_ok pstate_depth] in Hlazy, Hn. cbn [step_fuel feed_lazy].
    rewrite Hnb. cbn [andb]. rewrite (IH n l ltac:(lia) Hlazy Htext Hu).
    reflexivity.
Qed.

(** A text line arriving while a paragraph is open, and not underlining
    it, continues that paragraph and closes nothing. *)
Theorem step_lazy :
  forall l st,
    lazy_ok st = true -> classify l = KText -> bunderline_of l = None ->
    step l st = ([], feed_lazy l st).
Proof.
  intros l st Hlazy Htext Hu. unfold step.
  apply step_fuel_lazy; [lia|assumption..].
Qed.

(** A lazy line parses as the same line with the open containers'
    prefixes written out, in any spelling they accept. *)
Theorem step_lazy_spelling :
  forall p l st,
    spine_spelling 0 st p ->
    lazy_ok st = true -> classify l = KText -> bunderline_of l = None ->
    step (p ++ l) st = step l st.
Proof.
  intros p l st Hp Hlazy Htext Hu. rewrite (step_lazy l st Hlazy Htext Hu).
  unfold step. apply (step_fuel_spelling 0 st p Hp); [lia|assumption..].
Qed.

(** The spelling `spine_prefix` writes is one of them. *)
Theorem step_lazy_restore :
  forall l st,
    lazy_ok st = true -> classify l = KText -> bunderline_of l = None ->
    step (spine_prefix 0 st ++ l) st = step l st.
Proof.
  intros l st. apply step_lazy_spelling, spine_prefix_spelling.
Qed.

End WithTable.

(* `para_inlines_at` asks the policy before it reads the lines, so at the
   semantic instance it *is* `para_inlines` of their texts -- by
   conversion, which `rewrite` does not see.  A proof that has reduced a
   closing arm meets the located spelling and this puts the goal back in
   the names the equational theory is stated in, as `nopos` does for the
   node wrappers. *)
Ltac sem_para :=
  repeat match goal with
  | |- context [@para_inlines_at ?TT semantic_pos 0 ?l] =>
      change (@para_inlines_at TT semantic_pos 0 l)
        with (para_inlines (line_texts l))
  | |- context [@para_inlines_at ?TT semantic_pos ?k ?l] =>
      change (@para_inlines_at TT semantic_pos k l)
        with (para_inlines_off k (line_texts l))
  end.

(* Every coordinate constructor is the ambient one, erased. *)
Local Lemma erase_spot_at : forall `{LI : LineIx} l c,
  StateErase.of_spot (@spot_at LI l c) = @spot_at semantic_line_ix l c.
Proof. reflexivity. Qed.

Local Lemma erase_line_stop : forall `{LI : LineIx},
  StateErase.of_spot (@line_stop LI) = @line_stop semantic_line_ix.
Proof. reflexivity. Qed.

Local Lemma erase_line_span_from : forall `{LI : LineIx} l c,
  StateErase.of_span (@line_span_from LI l c) = @line_span_from semantic_line_ix l c.
Proof. reflexivity. Qed.

Local Lemma erase_open_extent : forall `{LI : LineIx} l c,
  StateErase.of_extent (@open_extent LI l c) = @open_extent semantic_line_ix l c.
Proof. reflexivity. Qed.

Local Lemma erase_touch_extent : forall `{LI : LineIx} e,
  StateErase.of_extent (@touch_extent LI e) =
  @touch_extent semantic_line_ix (StateErase.of_extent e).
Proof. reflexivity. Qed.

Local Lemma erase_span_through_line : forall `{LI : LineIx} r,
  StateErase.of_span (@span_through_line LI r) =
  @span_through_line semantic_line_ix (StateErase.of_span r).
Proof. reflexivity. Qed.

Local Lemma erase_remember_line : forall `{LI : LineIx} t,
  StateErase.of_line (@remember_line LI t) = @remember_line semantic_line_ix t.
Proof. reflexivity. Qed.

Local Lemma erase_remember_lines : forall `{LI : LineIx} lines,
  StateErase.of_lines (@remember_lines LI lines) =
  @remember_lines semantic_line_ix lines.
Proof.
  intros LI lines. induction lines as [|l rest IH]; [reflexivity|].
  unfold StateErase.of_lines, remember_lines in *; cbn [map]. rewrite IH. reflexivity.
Qed.

Local Lemma erase_push_text : forall `{LI : LineIx} rest cur,
  StateErase.of_lines (@push_text LI rest cur) =
  @push_text semantic_line_ix rest (StateErase.of_lines cur).
Proof.
  intros LI rest cur. unfold push_text. destruct (is_blank rest); reflexivity.
Qed.

Local Lemma erase_para_recover : forall extra slices,
  StateErase.state (para_recover extra slices) =
  para_recover extra (StateErase.of_lines slices).
Proof.
  intros extra slices. unfold para_recover. cbn [StateErase.state].
  rewrite StateErase.of_lines_length. reflexivity.
Qed.

Local Lemma erase_list_opened : forall `{LI : LineIx} l ind sty chk,
  StateErase.of_list_state (@list_opened LI l ind sty chk) =
  @list_opened semantic_line_ix l ind sty chk.
Proof. reflexivity. Qed.

(* A fence closes to a raw or a code block, neither of which holds a
   node.  Stated over a whole list because both callers have one: the
   block a fence emits, in front of what the state below it emitted. *)
Local Lemma fence_block_erase : forall `{K : bconfig} f texts rest,
  Erase.of_blocks (@fence_block K f texts :: rest)%list =
  (@fence_block K f texts :: Erase.of_blocks rest)%list.
Proof.
  intros K f texts rest. unfold fence_block.
  destruct (f_info f) as [|c fmt]; [reflexivity|].
  destruct c as [b0 b1 b2 b3 b4 b5 b6 b7];
    destruct b0, b1, b2, b3, b4, b5, b6, b7; cbn;
    try destruct braw_blocks; reflexivity.
Qed.

(* The caption is a paragraph, so it is scanned like one and its
   erasure is that paragraph's.  Outside the section because the two
   sides sit at different policies. *)
Local Lemma erase_caption_of : forall `{T : dtable} c,
  option_map Erase.of_inlines (@caption_of T located_pos c) =
  @caption_of T semantic_pos (StateErase.of_cap c).
Proof.
  intros T [rs|rs|rs start lines]; cbn [StateErase.of_cap caption_of];
    try reflexivity.
  rewrite <- StateErase.of_lines_rev, <- (@StateErase.of_para_inlines_at T),
    StateErase.inlines_nonempty.
  destruct (nonempty (@para_inlines_at T located_pos 0 (rev lines)));
    reflexivity.
Qed.

(* Stated over a whole list because both callers have one: the table a
   caption closes, in front of what the state below it emitted. *)
Local Lemma erase_table_block : forall `{T : dtable} rows c rest,
  Erase.of_blocks (@table_block T located_pos rows c :: rest)%list =
  (@table_block T semantic_pos rows (StateErase.of_cap c) :: Erase.of_blocks rest)%list.
Proof.
  intros T rows c rest. unfold table_block.
  cbn [Erase.of_blocks Erase.of_block located_pos semantic_pos pos_records mk].
  rewrite (@StateErase.of_table_fold_located T located_pos),
    (@erase_caption_of T c). reflexivity.
Qed.

(* A located label erases to the label the semantic parse reads, wherever
   either one says the key line began. *)
Local Lemma key_label_erase : forall `{T : dtable} s s' lbl,
  Erase.of_inlines (@key_label T located_pos s lbl) = @key_label T semantic_pos s' lbl.
Proof.
  intros T s s' lbl. unfold key_label. cbn [pos_records located_pos semantic_pos].
  rewrite erase_parse_inline_line_located. symmetry. apply para_inlines_one.
Qed.

(* Closing a located state adds only provenance.  The recursive cases are
   the reason erasure is structural: blocks retained below quotes, lists,
   divs, footnotes and keys must be stripped along with the outer node. *)
Local Lemma finish_erase : forall `{T : dtable} `{K : bconfig} (st : pstate),
  Erase.of_blocks (@finish T K located_pos st) =
  @finish T K semantic_pos (StateErase.state st).
Proof.
  intros T K st. induction st;
    cbn [finish StateErase.state StateErase.of_list_state Erase.of_blocks set_pos mkpos
      located_pos semantic_pos Erase.of_block pos_records add_roles_head add_roles
      pos_head posnode];
    rewrite ?StateErase.of_lines_texts_rev, ?StateErase.of_lines_length, ?erase_table_block,
      ?Erase.blocks_app, ?Erase.blocks_rev, ?IHst;
    try reflexivity;
    (* the arms whose block holds inlines: a paragraph, a heading, and the
       recovery's paragraph, each closing once the located scan's inlines
       are erased (`StateErase.of_para_inlines_at`) *)
    try (cbn [mk Erase.of_blocks Erase.of_block heading_block];
         rewrite StateErase.of_para_inlines_at, StateErase.of_lines_rev, ?StateErase.of_lines_length;
         reflexivity).
  - destruct cur as [|first cur]; [reflexivity|].
    cbn [mk Erase.of_blocks Erase.of_block].
    rewrite StateErase.of_para_inlines_at, StateErase.of_lines_rev. reflexivity.
  - destruct (@fence_block K f (line_texts (rev acc))) as [q a b] eqn:Ef.
    pose proof (@fence_block_erase K f (line_texts (rev acc)) []) as Hf.
    rewrite Ef in Hf. cbn [Erase.of_blocks] in Hf. exact Hf.
  - destruct header as [[[kind fold] [line source]]|];
      cbn [option_map StateErase.of_line mk Erase.of_block quote_block callout_title
        located_pos semantic_pos pos_records];
      fold Erase.of_blocks;
      rewrite Erase.blocks_app, Erase.blocks_rev, IHst;
      try rewrite erase_parse_inline_line_located;
      reflexivity.
  - unfold div_block. destruct (String.eqb cls EmptyString) eqn:E;
      cbn [Erase.of_block set_pos mkpos located_pos semantic_pos mk];
      fold Erase.of_blocks;
      rewrite Erase.blocks_app, Erase.blocks_rev, IHst; reflexivity.
  - remember (@list_block K ls
      (rev done ++ @finish T K located_pos st)%list) as lb eqn:E.
    destruct lb as [p a b]. symmetry in E.
    pose proof (@list_block_erase K ls
      (rev done ++ @finish T K located_pos st)%list) as H.
    cbn [Erase.of_blocks] in H.
    replace (@list_block K ls
        (rev done ++ @finish T K located_pos st)%list)
      with (Node p a b) in H by (symmetry; exact E).
    cbn in H. rewrite H. f_equal.
    rewrite Erase.blocks_app, Erase.blocks_rev, IHst. reflexivity.
  - destruct (Attributes.ap_done ap) eqn:E; [reflexivity|].
    unfold finish_para_recover. destruct slices as [|slice slices];
      [reflexivity|].
    cbn [decorate_head Erase.of_blocks add_roles_head add_roles set_pos mkpos
      located_pos semantic_pos mk Erase.of_block].
    rewrite StateErase.of_para_inlines_at, StateErase.of_lines_rev, StateErase.of_lines_length.
    reflexivity.
  - cbn [foot_block mk Erase.of_block]. fold Erase.of_blocks.
    rewrite Erase.blocks_app, Erase.blocks_rev, IHst. reflexivity.
  - destruct (@table_block T located_pos (rev rows) cap) as [q a b] eqn:Et.
    pose proof (@erase_table_block T (rev rows) cap []) as Ht.
    rewrite Et in Ht. cbn [Erase.of_blocks] in Ht |- *. exact Ht.
  - destruct (@finish T K located_pos st) as [|[p a b] rest] eqn:E.
    + cbn in IHst. symmetry in IHst. rewrite IHst. reflexivity.
    + cbn [decorate_head add_roles_head add_roles Erase.of_blocks] in IHst |- *.
      destruct (@finish T K semantic_pos (StateErase.state st))
        as [|[q a' b'] rest'] eqn:E'; [discriminate|].
      injection IHst as Hq Ha Hb Hrest. subst q a' b' rest'.
      destruct p; reflexivity.
  - destruct (@finish T K located_pos st) as [|[p a b] rest] eqn:E.
    + cbn in IHst. symmetry in IHst.
      cbn [key_close Erase.of_blocks pos_head posnode mkpos located_pos
        semantic_pos mk Erase.of_block].
      rewrite IHst, erase_inlines_para_inlines. reflexivity.
    + cbn [Erase.of_blocks] in IHst.
      destruct (@finish T K semantic_pos (StateErase.state st))
        as [|[q a' b'] rest'] eqn:E'; [discriminate|].
      injection IHst as Hq Ha Hb Hrest. subst q a' b' rest'.
      cbn [key_close pos_head posnode mkpos located_pos semantic_pos
        Erase.of_blocks Erase.of_block mk].
      rewrite (key_label_erase _ (extent_start (StateErase.of_extent range))).
      fold Erase.of_blocks. reflexivity.
Qed.

Local Lemma list_blank_erase : forall ls,
  StateErase.of_list_state (list_blank ls) = list_blank (StateErase.of_list_state ls).
Proof. intros []; reflexivity. Qed.

Local Lemma list_narrow_erase : forall ls ns,
  StateErase.of_list_state (list_narrow ls ns) = list_narrow (StateErase.of_list_state ls) ns.
Proof. intros [] ns; reflexivity. Qed.

Local Lemma list_content_erase : forall `{LI : LineIx} ls k,
  StateErase.of_list_state (@list_content LI ls k) =
  @list_content semantic_line_ix (StateErase.of_list_state ls) k.
Proof. intros LI [] k; destruct k; reflexivity. Qed.

Local Lemma list_next_erase : forall `{LI : LineIx} ls item chk l,
  StateErase.of_list_state (@list_next LI ls item chk l) =
  @list_next semantic_line_ix (StateErase.of_list_state ls) (Erase.of_blocks item)
    chk l.
Proof. intros LI [] item chk l. reflexivity. Qed.

Local Lemma lazy_ok_erase : forall `{K : bconfig} st,
  lazy_ok (StateErase.state st) = lazy_ok st.
Proof.
  induction st; cbn [StateErase.state lazy_ok] in *; auto.
  destruct cur; reflexivity.
Qed.

Local Lemma in_fence_erase : forall st, in_fence (StateErase.state st) = in_fence st.
Proof. induction st; cbn [StateErase.state in_fence] in *; auto. Qed.

Local Lemma blank_absorbed_erase : forall st,
  blank_absorbed (StateErase.state st) = blank_absorbed st.
Proof. induction st; cbn [StateErase.state blank_absorbed] in *; auto. Qed.

Local Lemma is_idle_erase : forall st, is_idle (StateErase.state st) = is_idle st.
Proof. intros []; (reflexivity || (destruct cur; reflexivity)). Qed.

Local Lemma announces_end_erase : forall st,
  announces_end (StateErase.state st) = announces_end st.
Proof. intros []; (reflexivity || (destruct cur; reflexivity)). Qed.

Local Lemma key_claims_erase : forall `{K : bconfig} l st,
  key_claims l (StateErase.state st) = key_claims l st.
Proof.
  intros K l st. induction st; cbn [StateErase.state key_claims] in *;
    rewrite ?IHst, ?is_idle_erase, ?announces_end_erase; reflexivity.
Qed.

Local Lemma list_takes_erase : forall `{K : bconfig} ls off l st,
  list_takes (StateErase.of_list_state ls) off l (StateErase.state st) =
  list_takes ls off l st.
Proof.
  intros K ls off l st. unfold list_takes. rewrite key_claims_erase.
  destruct ls. reflexivity.
Qed.

Local Lemma feed_lazy_erase : forall `{LI : LineIx} l st,
  StateErase.state (@feed_lazy LI l st) =
  @feed_lazy semantic_line_ix l (StateErase.state st).
Proof.
  intros LI l st. induction st; cbn [feed_lazy StateErase.state];
    rewrite ?IHst; reflexivity.
Qed.

Local Lemma close_reopen_erase : forall `{T : dtable} `{K : bconfig} st r,
  StateErase.result (@close_reopen T K located_pos st r) =
  @close_reopen T K semantic_pos (StateErase.state st) (StateErase.result r).
Proof.
  intros T K st [bs st']. unfold close_reopen, StateErase.result. cbn [fst snd].
  rewrite Erase.blocks_app, finish_erase. reflexivity.
Qed.

Local Lemma pend_result_erase : forall pend specs r,
  StateErase.result (@pend_result located_pos pend specs r) =
  @pend_result semantic_pos pend (map StateErase.of_span specs) (StateErase.result r).
Proof.
  intros pend specs [bs st]. destruct bs as [|[p a b] rest]; [reflexivity|].
  cbn [pend_result StateErase.result Erase.of_blocks decorate_head add_roles_head
    add_roles pos_records located_pos semantic_pos].
  destruct p; reflexivity.
Qed.

Local Lemma key_result_erase : forall `{T : dtable} range lbl src r,
  StateErase.result (@key_result T located_pos range lbl src r) =
  @key_result T semantic_pos (StateErase.of_extent range) lbl src (StateErase.result r).
Proof.
  intros T range lbl src [bs st].
  destruct bs as [|[p a b] rest]; [reflexivity|].
  cbn [key_result StateErase.result Erase.of_blocks key_close pos_head set_pos mkpos
    located_pos semantic_pos Erase.of_block mk posnode].
  unfold StateErase.result. cbn [fst snd Erase.of_blocks Erase.of_block key_close mk].
  rewrite (key_label_erase _ (extent_start (StateErase.of_extent range))).
  fold Erase.of_blocks. reflexivity.
Qed.

Local Lemma open_line_erase : forall `{T : dtable} `{K : bconfig} `{LI : LineIx}
  dl ds ind l k,
  (forall rest, StateErase.result (dl rest) = ds rest) ->
  StateErase.result (@open_line T K LI located_pos dl ind l k) =
  @open_line T K semantic_line_ix semantic_pos ds ind l k.
Proof.
  intros T K LI dl ds ind l k H. destruct k;
    cbn [open_line open_kind StateErase.result StateErase.state StateErase.of_list_state
      posnode mkpos located_pos semantic_pos Erase.of_blocks Erase.of_block mk
      StateErase.of_lines];
    try reflexivity.
  - unfold StateErase.result; cbn [fst snd StateErase.state StateErase.of_lines].
    destruct bdivs; reflexivity.
  - destruct (quote_header rest)
      as [[[kind fold] title]|] eqn:E.
    { unfold StateErase.result, open_callout.
      cbn [fst snd StateErase.state StateErase.of_line option_map].
      rewrite erase_remember_line. reflexivity. }
    specialize (H rest). destruct (dl rest) as [bs st].
    destruct (ds rest) as [bs' st']. cbn [StateErase.result fst snd] in H.
    injection H as Hbs Hst. subst bs' st'.
    unfold StateErase.result, open_quote. cbn [StateErase.state fst snd].
    rewrite Erase.blocks_rev. reflexivity.
  - unfold StateErase.result; cbn [fst snd StateErase.state].
    rewrite erase_push_text. reflexivity.
  - specialize (H (configured_list_rest chk rest)).
    destruct (dl (configured_list_rest chk rest)) as [bs st].
    destruct (ds (configured_list_rest chk rest)) as [bs' st'].
    cbn [StateErase.result fst snd] in H. injection H as Hbs Hst. subst bs' st'.
    unfold StateErase.result, open_list. cbn [StateErase.state fst snd].
    rewrite Erase.blocks_rev, erase_list_opened. reflexivity.
  - unfold StateErase.result, open_attr; cbn [fst snd StateErase.state StateErase.of_lines].
    destruct battrs; reflexivity.
  - specialize (H rest). destruct (dl rest) as [bs st].
    destruct (ds rest) as [bs' st']. cbn [StateErase.result fst snd] in H.
    injection H as Hbs Hst. subst bs' st'.
    unfold StateErase.result, open_foot. destruct bfootnotes;
      cbn [StateErase.state fst snd StateErase.of_lines]; rewrite ?Erase.blocks_rev;
      reflexivity.
  - unfold StateErase.result; cbn [fst snd StateErase.state StateErase.of_lines].
    destruct btables; reflexivity.
  - unfold StateErase.result, open_text.
    destruct bkeyed;
      [destruct (key_split (drop_leading_ws l)) as [[lbl src]|]|];
      cbn [fst snd StateErase.state StateErase.of_lines Erase.of_blocks];
      rewrite ?erase_push_text; reflexivity.
Qed.

(* An opener emits at most one block and always a fresh state, so the
   only thing erasure has to see through is the position it writes. *)
Local Lemma open_kind_erase : forall `{T : dtable} `{LI : LineIx} `{K : bconfig} l k,
  StateErase.result (@open_kind T LI located_pos K l k) =
  @open_kind T semantic_line_ix semantic_pos K l k.
Proof.
  intros T LI K l k. destruct k;
    unfold StateErase.result, open_kind;
    cbn [fst snd StateErase.state StateErase.of_lines Erase.of_blocks Erase.of_block posnode
      mkpos located_pos semantic_pos mk];
    rewrite ?erase_push_text;
    try reflexivity.
  - destruct bdivs; reflexivity.
  - destruct btables; reflexivity.
  - unfold open_text. destruct bkeyed;
      [destruct (key_split (drop_leading_ws l)) as [[lbl src]|]|];
      cbn [fst snd StateErase.state StateErase.of_lines Erase.of_blocks];
      rewrite ?erase_push_text; reflexivity.
Qed.

(* The two shapes every close-and-reopen branch of `step_fuel` has.  They
   are stated as `apply`-ready equations rather than rewrites because the
   semantic descent is not determined by the located one syntactically. *)
Local Lemma close_reopen_kind_erase :
  forall `{T : dtable} `{K : bconfig} `{LI : LineIx} st l k,
  StateErase.result
    (@close_reopen T K located_pos st (@open_kind T LI located_pos K l k)) =
  @close_reopen T K semantic_pos (StateErase.state st)
    (@open_kind T semantic_line_ix semantic_pos K l k).
Proof.
  intros T K LI st l k.
  rewrite close_reopen_erase, open_kind_erase. reflexivity.
Qed.

Local Lemma close_reopen_line_erase :
  forall `{T : dtable} `{K : bconfig} `{LI : LineIx} st dl ds ind l k,
  (forall rest, StateErase.result (dl rest) = ds rest) ->
  StateErase.result
    (@close_reopen T K located_pos st
       (@open_line T K LI located_pos dl ind l k)) =
  @close_reopen T K semantic_pos (StateErase.state st)
    (@open_line T K semantic_line_ix semantic_pos ds ind l k).
Proof.
  intros T K LI st dl ds ind l k H.
  rewrite close_reopen_erase, (open_line_erase _ _ _ _ _ H). reflexivity.
Qed.

(* The located transition and the semantic one are the same descent.  No
   branch reads a position, so each case closes by rewriting erasure
   through the constructors the branch builds. *)
Local Lemma step_fuel_erase : forall `{T : dtable} `{K : bconfig} `{LI : LineIx}
  n off l st,
  StateErase.result (@step_fuel T K LI located_pos n off l st) =
  @step_fuel T K semantic_line_ix semantic_pos n off l (StateErase.state st).
Proof.
  intros T K LI n. induction n as [|n IH]; intros off l st; [reflexivity|].
  (* The one recursion, at the state every descent starts from. *)
  assert (Hd : forall rest,
    StateErase.result
      (@step_fuel T K LI located_pos n (off + consumed l rest) rest (PPara []))
    = @step_fuel T K semantic_line_ix semantic_pos n (off + consumed l rest)
        rest (PPara []))
    by (intros rest; apply (IH (off + consumed l rest) rest (PPara []))).
  destruct st.
  - (* PPara *)
    destruct cur as [|c cur']; cbn [step_fuel StateErase.state StateErase.of_lines map];
      [apply open_line_erase; exact Hd|];
      destruct (bunderline_of l) as [lvl|];
      [ unfold StateErase.result; cbn [fst snd StateErase.state];
        rewrite Erase.blocks_set_pos; unfold heading_block;
        cbn [Erase.of_blocks Erase.of_block mk StateErase.of_lines];
        change (StateErase.of_line c :: map StateErase.of_line cur')
          with (StateErase.of_lines (c :: cur'));
        rewrite StateErase.of_para_inlines_at, StateErase.of_lines_rev; reflexivity |];
      destruct (classify l);
      try apply close_reopen_kind_erase;
      try (destruct (binterrupt _);
           [apply close_reopen_line_erase; exact Hd
           |unfold StateErase.result; cbn [fst snd StateErase.state StateErase.of_lines map];
            rewrite erase_remember_line; reflexivity]).
  - (* PHeading *)
    cbn [step_fuel StateErase.state]; destruct (classify l);
      try (apply close_reopen_line_erase; exact Hd);
      try (destruct bheading_continues;
           [ try (destruct (Nat.eqb _ _));
             try (unfold StateErase.result;
                  cbn [fst snd StateErase.state StateErase.of_lines map];
                  rewrite ?erase_push_text, ?erase_remember_line;
                  reflexivity);
             apply close_reopen_kind_erase
           | apply close_reopen_kind_erase ]).
  - (* PFence *)
    cbn [step_fuel StateErase.state].
    destruct (fence_close f l);
      [|unfold StateErase.result; cbn [fst snd StateErase.state StateErase.of_lines map];
        rewrite erase_remember_line; reflexivity].
    unfold StateErase.result; cbn [fst snd StateErase.state].
    rewrite Erase.blocks_set_pos, StateErase.of_lines_texts_rev.
    f_equal. apply fence_block_erase.
  - (* PQuote *)
    cbn [step_fuel StateErase.state]. destruct (classify l) eqn:E; cbn [is_lazy];
      try (apply close_reopen_line_erase; exact Hd).
    + rewrite <- (IH (off + consumed l rest) rest st).
      destruct (@step_fuel T K LI located_pos n (off + consumed l rest) rest st)
        as [bs inner'].
      unfold StateErase.result; cbn [fst snd StateErase.state].
      rewrite Erase.blocks_app, Erase.blocks_rev. reflexivity.
    + rewrite lazy_ok_erase. destruct (lazy_ok st);
        [ unfold StateErase.result; cbn [fst snd StateErase.state];
          rewrite feed_lazy_erase; reflexivity
        | apply close_reopen_line_erase; exact Hd ].
  - (* PDiv *)
    cbn [step_fuel StateErase.state]. rewrite in_fence_erase.
    destruct (negb (in_fence st) && div_close len l)%bool.
    + unfold StateErase.result; cbn [fst snd StateErase.state].
      rewrite Erase.blocks_set_pos.
      unfold div_block. destruct (String.eqb cls EmptyString) eqn:E;
        cbn [Erase.of_blocks Erase.of_block mk]; fold Erase.of_blocks;
        rewrite Erase.blocks_app, Erase.blocks_rev, finish_erase; reflexivity.
    + rewrite <- (IH off l st).
      destruct (@step_fuel T K LI located_pos n off l st) as [bs inner'].
      unfold StateErase.result; cbn [fst snd StateErase.state].
      rewrite Erase.blocks_app, Erase.blocks_rev. reflexivity.
  - (* PList.  Every kind but a blank first asks whether the item takes
       the line, and that branch is the same for all of them; what is
       left afterwards is the blank, a sibling marker and a lazy line. *)
    cbn [step_fuel StateErase.state]. destruct (classify l) eqn:E.
    all: try (rewrite list_takes_erase; destruct (list_takes ls off l st)).
    all: try (rewrite <- (IH off l st);
         destruct (@step_fuel T K LI located_pos n off l st) as [bs inner'];
         unfold StateErase.result; cbn [fst snd StateErase.state];
         rewrite Erase.blocks_app, Erase.blocks_rev, list_content_erase;
         reflexivity).
    all: try (cbn [is_lazy]; apply close_reopen_line_erase; exact Hd).
    + rewrite blank_absorbed_erase. rewrite <- (IH off l st).
      destruct (@step_fuel T K LI located_pos n off l st) as [bs inner'].
      unfold StateErase.result; cbn [fst snd StateErase.state].
      rewrite Erase.blocks_app, Erase.blocks_rev.
      destruct (blank_absorbed st);
        [reflexivity|rewrite list_blank_erase; reflexivity].
    + cbn [ls_styles StateErase.of_list_state].
      destruct (narrow (ls_styles ls) (configured_list_styles sty chk))
        as [|p l0]; [apply close_reopen_line_erase; exact Hd|].
      rewrite <- (Hd (configured_list_rest chk rest)).
      destruct (@step_fuel T K LI located_pos n
        (off + consumed l (configured_list_rest chk rest))
        (configured_list_rest chk rest) (PPara [])) as [bs inner'].
      unfold StateErase.result; cbn [fst snd StateErase.state].
      rewrite Erase.blocks_rev, list_next_erase, list_narrow_erase,
        Erase.blocks_app, Erase.blocks_rev, finish_erase. reflexivity.
    + cbn [is_lazy]. rewrite lazy_ok_erase. destruct (lazy_ok st);
        [ unfold StateErase.result; cbn [fst snd StateErase.state];
          rewrite list_content_erase, feed_lazy_erase; reflexivity
        | apply close_reopen_line_erase; exact Hd ].
  - (* PAttr *)
    cbn [step_fuel StateErase.state]. destruct (ap_done ap).
    + rewrite (IH off l (PPend (Attr.merge (ap_attrs ap) pend)
        (specs ++ [extent_span range])%list (PPara []))).
      cbn [StateErase.state StateErase.of_lines map]. rewrite map_app. reflexivity.
    + destruct (Nat.ltb ind (off + indent_of l)).
      * destruct (ap_failed (attr_feed l ap)).
        -- rewrite pend_result_erase, IH, erase_para_recover. reflexivity.
        -- unfold StateErase.result; cbn [fst snd StateErase.state].
           rewrite erase_push_text. reflexivity.
      * destruct (is_blank l).
        -- unfold StateErase.result; cbn [fst snd StateErase.state].
           rewrite erase_para_recover. reflexivity.
        -- rewrite pend_result_erase, IH, erase_para_recover. reflexivity.
  - (* PParaOff *)
    cbn [step_fuel StateErase.state];
      destruct (bunderline_of l) as [lvl|];
      [ unfold StateErase.result; cbn [fst snd StateErase.state];
        rewrite Erase.blocks_set_pos; unfold heading_block_off;
        cbn [Erase.of_blocks Erase.of_block mk];
        rewrite StateErase.of_para_inlines_at, StateErase.of_lines_rev; reflexivity |];
      destruct (classify l);
      try apply close_reopen_kind_erase;
      try (destruct (binterrupt _);
           [apply close_reopen_line_erase; exact Hd
           |unfold StateErase.result; cbn [fst snd StateErase.state StateErase.of_lines map];
            rewrite erase_remember_line; reflexivity]).
  - (* PRef *)
    pose proof (IH off l (PPara [])) as Hp;
      cbn [StateErase.state StateErase.of_lines map] in Hp.
    cbn [step_fuel StateErase.state].
    destruct (if Nat.ltb ind (off + indent_of l) then ref_cont l else None);
      [reflexivity|].
    rewrite <- Hp.
    destruct (@step_fuel T K LI located_pos n off l (PPara [])) as [bs st'].
    unfold StateErase.result; cbn [fst snd]. rewrite Erase.blocks_set_pos.
    reflexivity.
  - (* PFoot *)
    cbn [step_fuel StateErase.state].
    pose proof (IH off l (PPara [])) as Hp;
      cbn [StateErase.state StateErase.of_lines map] in Hp.
    assert (Hi : StateErase.result (@step_fuel T K LI located_pos n off l st) =
      @step_fuel T K semantic_line_ix semantic_pos n off l (StateErase.state st))
      by apply IH.
    destruct (is_blank l);
      [|destruct (Nat.ltb ind (off + indent_of l))].
    + rewrite <- Hi.
      destruct (@step_fuel T K LI located_pos n off l st) as [bs inner'].
      unfold StateErase.result; cbn [fst snd StateErase.state].
      rewrite Erase.blocks_app, Erase.blocks_rev. reflexivity.
    + rewrite <- Hi.
      destruct (@step_fuel T K LI located_pos n off l st) as [bs inner'].
      unfold StateErase.result; cbn [fst snd StateErase.state].
      rewrite Erase.blocks_app, Erase.blocks_rev. reflexivity.
    + unfold is_lazy. rewrite lazy_ok_erase.
      destruct (match classify l with KText => lazy_ok st | _ => false end).
      { unfold StateErase.result; cbn [fst snd StateErase.state].
        rewrite feed_lazy_erase. reflexivity. }
      rewrite <- Hp.
      destruct (@step_fuel T K LI located_pos n off l (PPara [])) as [bs st'].
      unfold StateErase.result; cbn [fst snd]. rewrite Erase.blocks_set_pos.
      cbn [Erase.of_blocks Erase.of_block foot_block mk]. fold Erase.of_blocks.
      rewrite Erase.blocks_app, Erase.blocks_rev, finish_erase. reflexivity.
  - (* PTable *)
    cbn [step_fuel StateErase.state].
    pose proof (IH off l (PPara [])) as Hp;
      cbn [StateErase.state StateErase.of_lines map] in Hp.
    destruct cap; cbn [StateErase.of_cap];
      [ | |
        destruct (is_blank l);
        [ unfold StateErase.result; cbn [fst snd StateErase.state];
          rewrite Erase.blocks_set_pos, erase_table_block;
          cbn [StateErase.of_cap Erase.of_blocks]; reflexivity
        | unfold StateErase.result;
          cbn [fst snd StateErase.state StateErase.of_cap StateErase.of_lines map];
          reflexivity ] ].
    all: destruct (caption_open l) as [crest|];
         [ unfold StateErase.result; cbn [fst snd StateErase.state StateErase.of_cap];
           rewrite erase_push_text; reflexivity |].
    all: destruct (is_blank l); [reflexivity|].
    all: destruct (classify l);
         try (unfold StateErase.result; cbn [fst snd StateErase.state StateErase.of_cap];
              reflexivity);
         rewrite <- Hp;
         destruct (@step_fuel T K LI located_pos n off l (PPara []))
           as [bs st'];
         unfold StateErase.result; cbn [fst snd];
         rewrite Erase.blocks_set_pos; rewrite ?erase_table_block;
         cbn [StateErase.of_cap]; reflexivity.
  - (* PPend *)
    cbn [step_fuel StateErase.state]. rewrite is_idle_erase.
    destruct (classify l);
      try (rewrite pend_result_erase, IH; reflexivity).
    + destruct (is_idle st); [reflexivity|].
      rewrite pend_result_erase, IH. reflexivity.
    + destruct (is_idle st);
        [unfold StateErase.result, open_attr;
         cbn [fst snd StateErase.state StateErase.of_lines map];
         destruct battrs; reflexivity|].
      rewrite pend_result_erase, IH. reflexivity.
  - (* PKey *)
    cbn [step_fuel StateErase.state]. rewrite is_idle_erase.
    destruct (is_blank l && is_idle st)%bool;
      [unfold StateErase.result;
       cbn [fst snd Erase.of_blocks Erase.of_block posnode mkpos located_pos
         semantic_pos];
       rewrite erase_inlines_para_inlines; reflexivity|].
    rewrite key_result_erase, IH. reflexivity.
Qed.

(* The fold with the actual line index installed at each step: the
   provenance-bearing state fold the located block assembly uses. *)
Fixpoint run_lines_tagged {T : dtable} {K : bconfig} {P : PosPolicy}
  (lines : list (nat * string)) (st : pstate) : blocks * pstate :=
  match lines with
  | [] => ([], st)
  | (i, l) :: rest =>
      let (bs, st') := @step T K (LineIxAt i) P l st in
      let (more, final) := run_lines_tagged rest st' in
      ((bs ++ more)%list, final)
  end.

Local Definition finish_lines_tagged {T : dtable} {K : bconfig} {P : PosPolicy}
  (lines : list (nat * string)) (st : pstate) : blocks :=
  let (bs, final) := run_lines_tagged lines st in
  (bs ++ @finish T K P final)%list.

(* The located parse: the same fold, each line stepped at its own index
   and under the policy that keeps what the states record.  Erasing it
   gives the semantic parse (`parse_blocks_located_erase`). *)
Definition parse_blocks_located {T : dtable} {K : bconfig} (s : string)
  : blocks :=
  @finish_lines_tagged T K located_pos (split_lines_indexed s) (PPara []).

(* Each line's blocks are complete when the next line is read, so the
   fold is the ordinary one with the per-line index installed. *)
Local Lemma finish_lines_tagged_cons :
  forall `{T : dtable} `{K : bconfig} `{P : PosPolicy} i l rest st,
  @finish_lines_tagged T K P ((i, l) :: rest)%list st =
  (fst (@step T K (LineIxAt i) P l st)
   ++ @finish_lines_tagged T K P rest
        (snd (@step T K (LineIxAt i) P l st)))%list.
Proof.
  intros T K P i l rest st. unfold finish_lines_tagged.
  cbn [run_lines_tagged].
  destruct (@step T K (LineIxAt i) P l st) as [bs st']. cbn [fst snd].
  destruct (@run_lines_tagged T K P rest st') as [more final].
  rewrite <- app_assoc. reflexivity.
Qed.

Local Lemma pstate_depth_erase : forall st,
  pstate_depth (StateErase.state st) = pstate_depth st.
Proof. induction st; cbn [StateErase.state pstate_depth]; auto. Qed.

Local Lemma step_erase : forall `{T : dtable} `{K : bconfig} `{LI : LineIx} l st,
  StateErase.result (@step T K LI located_pos l st) =
  @step T K semantic_line_ix semantic_pos l (StateErase.state st).
Proof.
  intros T K LI l st. unfold step. rewrite pstate_depth_erase.
  apply step_fuel_erase.
Qed.

Local Lemma finish_lines_tagged_erase : forall `{T : dtable} `{K : bconfig} lines st,
  Erase.of_blocks (@finish_lines_tagged T K located_pos lines st) =
  @parse_lines T K semantic_line_ix semantic_pos (map snd lines)
    (StateErase.state st).
Proof.
  intros T K lines. induction lines as [|[i l] rest IH]; intros st.
  - unfold finish_lines_tagged. cbn [run_lines_tagged fst snd app].
    apply finish_erase.
  - rewrite finish_lines_tagged_cons. cbn [map snd parse_lines].
    pose proof (@step_erase T K (LineIxAt i) l st) as Hs.
    unfold StateErase.result in Hs.
    destruct (@step T K (LineIxAt i) located_pos l st) as [bs st'].
    destruct (@step T K semantic_line_ix semantic_pos l (StateErase.state st))
      as [bs' st''].
    cbn [fst snd] in Hs |- *. injection Hs as Hbs Hst. subst bs' st''.
    rewrite Erase.blocks_app, IH. reflexivity.
Qed.

(* The semantic boundary the located parser is defined against: reading
   positions costs the parse nothing, because erasing them gives back the
   parse that never recorded any.  Both halves matter -- the provenance
   on the blocks, and the line indices the states accumulated, which the
   ambient instance writes as zero. *)
Theorem parse_blocks_located_erase : forall `{T : dtable} `{K : bconfig} s,
  Erase.of_blocks (@parse_blocks_located T K s) =
  @parse_blocks T K semantic_line_ix semantic_pos s.
Proof.
  intros T K s. unfold parse_blocks_located, parse_blocks.
  rewrite finish_lines_tagged_erase, split_lines_indexed_values.
  reflexivity.
Qed.
