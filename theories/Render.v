(* ai-disclosure: autonomous *)

(** * Canonical Djot rendering

   Djot rendering (AST -> djot source), modeled on djoths's Djot.hs,
   together with the canonical form it inverts.

   `cblock` is the canonical (renderable) view of a block: the parser's
   image, described by the data that determines it.  Renderability of a
   paragraph is phrased through the line classifier: the first line must
   classify as text (so the parse re-opens a paragraph there), interior
   lines merely nonblank (paragraphs cannot be interrupted), and the last
   line pre-stripped (the parser strips it, so a roundtripping AST cannot
   carry trailing whitespace).  A construct added to Line.v gets a cblock
   constructor, a canonical rendering, and a cb_ok obligation. *)

From Stdlib Require Import String Ascii List Bool PeanoNat.
From DjotV Require Import Strings Line Ast Attributes Parser.
From DjotV Require Document.
Import ListNotations.

Local Open Scope string_scope.

(* The delimiter table this file is read at.  Implicit, so nothing below
   mentions it: what it buys is that the statements quantify over the
   family rather than over djot's spelling. *)
Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
Block layout
============
*)

(* The renderer's canonical spellings, fixed once so both the rendering
   and the classification lemmas can refer to them. *)
Definition thematic_line : string := "* * * *".
(* A reference definition, on one line.  The space is not optional:
   `[l]:d` is not a definition, and neither is `[l]: d `.  An empty
   destination still gets the space, which the recognizer accepts as a
   whitespace run followed by an empty token. *)
Definition ref_line (label dest : string) : string :=
  "[" ++ label ++ "]: " ++ dest.
(* A key's lines.  A key over a paragraph goes on one line, the
   paragraph's first line as its value, when that line still reads as the
   same key with the same value; otherwise the label has a line of its
   own and the block starts on the next. *)
Definition key_line (label value : string) : string := label ++ ": " ++ value.

Definition key_inline_ok (label value : string) : bool :=
  let l := key_line label value in
  line_ok l && is_text l
  && match key_split l with
     | Some (lbl, v) => String.eqb lbl label && String.eqb v value
     | None => false
     end.

Definition key_lines (label : string) (para : bool) (ls : list string)
  : list string :=
  match ls with
  | l0 :: rest =>
      if para && key_inline_ok label l0
      then key_line label l0 :: rest
      else (label ++ ":") :: ls
  | [] => [label ++ ":"]
  end.

Lemma key_lines_cases :
  forall label para ls,
    key_lines label para ls = (label ++ ":") :: ls
    \/ exists l0 rest,
         ls = l0 :: rest /\ para = true /\ key_inline_ok label l0 = true
         /\ key_lines label para ls = key_line label l0 :: rest.
Proof.
  intros label para [|l0 rest]; [left; reflexivity|].
  cbn [key_lines]. destruct (para && key_inline_ok label l0)%bool eqn:E.
  - right. apply andb_true_iff in E as [Hp Hk]. exists l0, rest. auto.
  - left. reflexivity.
Qed.

Lemma key_inline_ok_parts :
  forall label value, key_inline_ok label value = true ->
    line_ok (key_line label value) = true
    /\ classify (key_line label value) = KText
    /\ key_split (key_line label value) = Some (label, value).
Proof.
  intros label value H. unfold key_inline_ok in H.
  apply andb_true_iff in H as [H Hsplit].
  apply andb_true_iff in H as [Hline Htext].
  apply is_text_classify in Htext.
  destruct (key_split (key_line label value)) as [[lbl v]|] eqn:E;
    [|discriminate Hsplit].
  apply andb_true_iff in Hsplit as [Hl Hv].
  apply String.eqb_eq in Hl, Hv. subst lbl v. auto.
Qed.

Definition code_close : string := "```".
Definition code_open (info : string) : string := "```" ++ info.

(* A table's two line shapes.  A cell is written with a space on each
   side, which keeps the two apart under the recognizer: a separator's
   cell must start immediately after its bar (`Line.sep_cell`), so a
   padded row can never be read as a separator and a cell may hold `---`
   or `:-:` with no escaping at all.

   The dashes are three wide whatever the column holds; nothing reads the
   width back. *)
Local Definition align_dashes (a : align) : string :=
  match a with
  | AlignDefault => "---"
  | AlignLeft => ":--"
  | AlignRight => "--:"
  | AlignCenter => ":-:"
  end.

Local Fixpoint sep_body (als : list align) : string :=
  match als with
  | [] => EmptyString
  | a :: rest => (align_dashes a ++ "|" ++ sep_body rest)%string
  end.

Definition sep_line (als : list align) : string := ("|" ++ sep_body als)%string.

Definition cells_line (cs : list string) : string := ("|" ++ cells_body cs)%string.

(* The canonical fence sits at column zero, so it strips nothing from its
   content lines -- which is what keeps `cb_lines` a left inverse of the
   parser for a code block wherever it is nested. *)
Lemma indent_of_code_open : forall info, indent_of (code_open info) = 0.
Proof. intros info. reflexivity. Qed.

(* Flatten per-block line lists into one line list, with a single blank
   line between blocks (and none at either end).  A document and a block
   quote's contents use the same layout, which is uniformity on the
   rendering side. *)
Fixpoint sep_lines (lss : list (list string)) : list string :=
  match lss with
  | [] => []
  | [ls] => ls
  | ls :: rest => (ls ++ EmptyString :: sep_lines rest)%list
  end.

Local Lemma quote_line_empty : quote_line EmptyString = quote_open.
Proof. unfold quote_line. apply append_empty_r. Qed.

(*
Canonical table rows
--------------------
*)

(* A canonical table row.  `Ast.Table` records, per cell, a type and an
   alignment; what a *source* row records is a line of cells and, for a
   header, the separator under it.  `CTHead` is the pair, and the
   alignment a `CTBody` gets is whatever the last `CTHead` set -- which
   is not a convention but the fold: `Step.table_fold` only ever changes
   the alignment in force at a separator, and a separator promotes the
   row before it, so a *body* row can never change alignment.

   That is the property this type exists to make structural.  Phrased on
   `list (list cell)` it would be a reachability condition on a fold;
   here it is the shape of the data, and `cb_ast` covers exactly the
   tables the parser can reach.

   The one reachable shape left out is a table whose leading rows are
   body rows aligned by a separator that precedes them (`|--:|` then
   `| b |`).  It needs a fourth piece of state -- the alignment in force
   before any header -- and nothing else in the view would use it. *)
Inductive ctrow : Type :=
  | CTBody (cells : list (list cinline))
  | CTHead (aligns : list align) (cells : list (list cinline)).

Definition ctrow_cells (r : ctrow) : list (list cinline) :=
  match r with CTBody cs => cs | CTHead _ cs => cs end.

(* A header is two lines: its cells, then the separator that makes it
   one. *)
Definition ctrow_lines (r : ctrow) : list string :=
  match r with
  | CTBody cs => [cells_line (map ci_line cs)]
  | CTHead als cs => [cells_line (map ci_line cs); sep_line als]
  end.

(* `Step.cells_of` and `Step.head_of` with the canonical view's inlines in
   place of the inline parser's: the same positional alignment, defaulting
   past the end of the separator. *)
Local Fixpoint ccells_of (ct : cell_type) (als : list align) (cs : list (list cinline))
  : list cell :=
  match cs with
  | [] => []
  | c :: cs' =>
      match als with
      | [] => Cell ct AlignDefault (ci_inlines c) :: ccells_of ct [] cs'
      | a :: als' => Cell ct a (ci_inlines c) :: ccells_of ct als' cs'
      end
  end.

(* `Step.table_fold`, read on the canonical rows: the alignment in force
   is an accumulator that only a header changes. *)
Fixpoint ctable_cells (als : list align) (rows : list ctrow) : list (list cell) :=
  match rows with
  | [] => []
  | CTBody cs :: rest => ccells_of BodyCell als cs :: ctable_cells als rest
  | CTHead als' cs :: rest => ccells_of HeadCell als' cs :: ctable_cells als' rest
  end.

(* The rows the recognizer gives back, in source order: a header line is
   two of them, and the separator is the second. *)
Definition ctrow_trows (r : ctrow) : list trow :=
  match r with
  | CTBody cs => [TCells (map ci_line cs)]
  | CTHead als cs => [TCells (map ci_line cs); TSep als]
  end.

(* Both line shapes open with a bar, which is what keeps a table's own
   lines out of every other recognizer's way -- the caption's included,
   since `Line.caption_open` wants a caret first. *)
Lemma caption_open_cells_line : forall cs, caption_open (cells_line cs) = None.
Proof. reflexivity. Qed.

Lemma caption_open_sep_line : forall als, caption_open (sep_line als) = None.
Proof. reflexivity. Qed.

Lemma is_blank_cells_line : forall cs, is_blank (cells_line cs) = false.
Proof. reflexivity. Qed.

Lemma is_blank_sep_line : forall als, is_blank (sep_line als) = false.
Proof. reflexivity. Qed.

(* A separator is spelled out of bars, colons and hyphens, so unlike a
   row of cells it carries no obligation at all. *)
Lemma line_ok_sep_line : forall als, line_ok (sep_line als) = true.
Proof.
  intros als. unfold line_ok, nonblank.
  rewrite is_blank_sep_line.
  assert (Hnl : no_nl (sep_line als) = true).
  { unfold sep_line. rewrite no_nl_append.
    assert (Hb : no_nl (sep_body als) = true).
    { induction als as [|a als IH]; [reflexivity|].
      cbn [sep_body]. rewrite !no_nl_append, IH. destruct a; reflexivity. }
    rewrite Hb. reflexivity. }
  rewrite Hnl. cbn [andb]. apply String.eqb_eq. reflexivity.
Qed.

(* The parser's fold, on a canonical table, is the canonical fold.  Both
   halves are the same positional walk with the inline layer's answer in
   place of the view's, so each is one induction over the cells. *)
Local Lemma cells_of_ccells_of :
  forall ct als cs,
    forallb cis_ok cs = true ->
    cells_of ct als (map ci_line cs) = ccells_of ct als cs.
Proof.
  intros ct als cs. revert als.
  induction cs as [|c cs IH]; intros als Hok; [reflexivity|].
  cbn [forallb] in Hok. apply andb_true_iff in Hok as [Hc Hcs].
  cbn [map cells_of ccells_of]. rewrite (parse_inline_line_ci c Hc).
  destruct als as [|a als]; rewrite (IH _ Hcs); reflexivity.
Qed.

(* Promoting the row a separator sits under: the cells keep their
   inlines and take the separator's alignments, which is `ccells_of` at
   the header type. *)
Local Lemma head_of_ccells_of :
  forall als als0 cs,
    head_of als (ccells_of BodyCell als0 cs) = ccells_of HeadCell als cs.
Proof.
  intros als als0 cs. revert als als0.
  induction cs as [|c cs IH]; intros als als0; [reflexivity|].
  destruct als0 as [|a0 als0']; destruct als as [|a als'];
    cbn [ccells_of head_of]; rewrite IH; reflexivity.
Qed.

Lemma table_fold_ctable_cells :
  forall rows als acc,
    forallb (fun r => forallb cis_ok (ctrow_cells r)) rows = true ->
    table_fold (flat_map ctrow_trows rows) als acc
    = (rev acc ++ ctable_cells als rows)%list.
Proof.
  induction rows as [|r rows IH]; intros als acc Hok.
  - cbn [flat_map ctable_cells table_fold]. rewrite app_nil_r. reflexivity.
  - cbn [forallb] in Hok. apply andb_true_iff in Hok as [Hr Hrows].
    destruct r as [cs|als' cs]; cbn [ctrow_cells] in Hr;
      cbn [ctrow_trows flat_map app table_fold ctable_cells].
    + rewrite (cells_of_ccells_of BodyCell als cs Hr), (IH _ _ Hrows).
      cbn [rev]. rewrite <- app_assoc. reflexivity.
    + rewrite (cells_of_ccells_of BodyCell als cs Hr).
      rewrite head_of_ccells_of, (IH _ _ Hrows).
      cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

(*
Canonical blocks
================
*)

(* A block described by the source data that determines it: a paragraph
   by its lines, a code block by its info string and content lines, a
   quote by the canonical blocks inside it.  One constructor per block
   construct the roundtrip covers.

   The list-valued constructor makes `cblock` a nested inductive.  A
   quote's or div's contents recurse through `map` directly, but a list's
   list of items needs a hand-inlined fixpoint (Rocq rejects the mutual
   recursion), so each projection carries one and each gets an equation
   lemma recovering the `map`/`forallb` form the proofs use. *)
Inductive cblock : Type :=
  (* A paragraph's within-line content, one `list cinline` per source
     line: the block layer owns line structure, `Inline.v` owns what sits
     inside a line, and a `SoftBreak` is exactly the seam between them. *)
  | CPara (lss : list (list cinline))
  | CThematic
  | CCode (info : string) (content : list string)
  | CRaw (format : string) (content : list string)
  | CHeading (level : nat) (lss : list (list cinline))
  | CQuote (inner : list cblock)
  | CCallout (kind : string) (fold : option callout_fold)
      (title : list cinline) (inner : list cblock)
  (* A canonical div: `:::` at both ends, no class, and its name, if it
     has one, after the opening fence.  The fence length is fixed for the
     same reason `CCode`'s is: content that would close it early is
     excluded by `cb_ok` rather than escaped by growing the fence. *)
  | CDiv (name : string) (inner : list cblock)
  (* `list_kind` (`OrderedList.v`) is the list flavour: bullet,
     definition, task, or an ordered scheme with its delimiter and start,
     which are the only data the markers depend on. *)
  | CList (k : list_kind) (sp : list_spacing) (items : list (list cblock))
  (* A reference definition, which is a leaf: `cb_ok` keeps its label and
     destination within what one line can carry, and the document's
     reference map is derived from the block rather than stored here. *)
  | CRef (label : string) (dest : string)
  (* A table, as the rows its source spells.  No caption: a caption is
     read by the table's own continuation rule rather than by `classify`
     (`Line.caption_open`), so it is the one part of the construct that
     is not a line shape, and `cb_ok` would have to state it as one. *)
  | CTable (rows : list ctrow)
  (* A source-level stable address.  Only the id subset of block
     attributes is canonical here; the wrapper preserves whether the id
     was explicit, which the document pass's AST cannot recover. *)
  | CId (id : string) (inner : cblock)
  (* One inline label, then a child at the same column on the next line,
     or a paragraph's first line after the colon (`key_lines`). *)
  | CKey (label : cinline) (inner : cblock).

(* The two projections a cblock sits between: its source lines... *)
Fixpoint cb_lines (cb : cblock) : list string :=
  let itemss :=
    fix goitems (iss : list (list cblock)) : list (list string) :=
      match iss with
      | [] => []
      | it :: rest => sep_lines (map cb_lines it) :: goitems rest
      end in
  match cb with
  | CPara lss => map ci_line lss
  | CThematic => [thematic_line]
  | CCode info content => (code_open info :: content ++ [code_close])%list
  | CRaw format content =>
      (code_open (String "="%char format) :: content ++ [code_close])%list
  | CHeading lvl lss => map (heading_line lvl) (map ci_line lss)
  | CQuote inner => map quote_line (sep_lines (map cb_lines inner))
  | CCallout kind fold title inner =>
      quote_line (callout_header_line kind fold (ci_line title))
      :: map quote_line (sep_lines (map cb_lines inner))
  | CDiv name inner =>
      (div_open_line div_fence name :: sep_lines (map cb_lines inner) ++ [div_fence])%list
  (* Each item's own lines, then the markers its kind supplies and the
     layout its spacing supplies: `Parser.ck_items` and
     `Parser.list_lines`, which is exactly the shape `ck_uniformity`
     inverts.  A bullet list's marker is the same on every item; a
     decimal list's is not, which is why the markers go on here rather
     than inside the per-item map. *)
  | CList k sp items =>
      list_lines sp (map litem_lines (ck_items k (itemss items)))
  | CRef label dest => [ref_line label dest]
  | CTable rows => flat_map ctrow_lines rows
  | CId id inner => ("{#" ++ id ++ "}") :: cb_lines inner
  | CKey label inner =>
      key_lines (ci_text [label])
        (match inner with CPara _ => true | _ => false end) (cb_lines inner)
  end.

(* ...and the AST node the parser builds from those lines.  Roundtrip is
   then: cb_lines, rendered and reparsed, gives back cb_ast. *)
Fixpoint cb_ast (cb : cblock) : node block :=
  let itemsof :=
    fix goitems (iss : list (list cblock)) : list blocks :=
      match iss with [] => [] | it :: rest => map cb_ast it :: goitems rest end in
  match cb with
  | CPara lss => mk (Para (ci_para lss))
  | CThematic => mk ThematicBreak
  | CCode info content => mk (CodeBlock info (join_nl content))
  | CRaw format content => mk (RawBlock format (join_nl content))
  | CHeading lvl lss => mk (Heading lvl (ci_para lss))
  | CQuote inner => mk (BlockQuote (map cb_ast inner))
  | CCallout kind fold title inner =>
      mk (Ext_callout kind fold (ci_inlines title) (map cb_ast inner))
  | CDiv name inner => mk (Div name (map cb_ast inner))
  | CList k sp items => mk (ck_block k sp (itemsof items))
  | CRef label dest => mk (RefDef label dest)
  | CTable rows => mk (Table (mk []) (map (fun r => mk (map mk r)) (ctable_cells [] rows)))
  | CId id inner => add_attr [("id", id)] (cb_ast inner)
  | CKey label inner => mk (Ext_keyed [ci_ast label] (cb_ast inner))
  end.

(* The container equations.  All hold by conversion: an inlined
   `fix goitems` and `map` applied to the same body are the same term to
   the kernel, so these name the `map` form rather than proving it. *)
Lemma cb_ast_quote :
  forall inner, cb_ast (CQuote inner) = mk (BlockQuote (map cb_ast inner)).
Proof. reflexivity. Qed.

Lemma cb_lines_quote :
  forall inner,
    cb_lines (CQuote inner) = map quote_line (sep_lines (map cb_lines inner)).
Proof. reflexivity. Qed.

Lemma cb_ast_list :
  forall k sp items,
    cb_ast (CList k sp items) = mk (ck_block k sp (map (map cb_ast) items)).
Proof. reflexivity. Qed.

(* An item's own lines, before the marker and the continuation pad go on
   -- what the parser reparses the item as, by `Parser.ck_uniformity`. *)
Definition item_lines (it : list cblock) : list string :=
  sep_lines (map cb_lines it).

Lemma cb_lines_list :
  forall k sp items,
    cb_lines (CList k sp items)
    = list_lines sp (map litem_lines (ck_items k (map item_lines items))).
Proof. reflexivity. Qed.

(* Induction over cblocks that reaches into containers: the generated
   `cblock_ind` does not descend into `CQuote`'s list or `CList`'s list of
   lists.  P for a block, Q for a list of them (a quote's contents, or one
   list item), R for a list of item lists (a whole `CList`'s items), which
   packages "Q holds for every item". *)
Definition cblock_ind2
  (P : cblock -> Prop) (Q : list cblock -> Prop) (R : list (list cblock) -> Prop)
  (hpara : forall ls, P (CPara ls))
  (hthem : P CThematic)
  (hcode : forall info content, P (CCode info content))
  (hraw : forall format content, P (CRaw format content))
  (hhead : forall lvl ls, P (CHeading lvl ls))
  (hquote : forall inner, Q inner -> P (CQuote inner))
  (hcallout : forall kind fold title inner,
      Q inner -> P (CCallout kind fold title inner))
  (hdiv : forall name inner, Q inner -> P (CDiv name inner))
  (hlist : forall k sp items, R items -> P (CList k sp items))
  (href : forall label dest, P (CRef label dest))
  (htable : forall rows, P (CTable rows))
  (hid : forall id inner, P inner -> P (CId id inner))
  (hkey : forall label inner, P inner -> P (CKey label inner))
  (hnil : Q [])
  (hcons : forall c rest, P c -> Q rest -> Q (c :: rest))
  (hrnil : R [])
  (hrcons : forall item items, Q item -> R items -> R (item :: items))
  : forall cb, P cb :=
  fix go (cb : cblock) : P cb :=
    let golist :=
      fix golist (cs : list cblock) : Q cs :=
        match cs with
        | [] => hnil
        | c :: rest => hcons c rest (go c) (golist rest)
        end in
    match cb with
    | CPara ls => hpara ls
    | CThematic => hthem
    | CCode info content => hcode info content
    | CRaw format content => hraw format content
    | CHeading lvl ls => hhead lvl ls
    | CQuote inner => hquote inner (golist inner)
    | CCallout kind fold title inner =>
        hcallout kind fold title inner (golist inner)
    | CDiv name inner => hdiv name inner (golist inner)
    | CList k sp items =>
        hlist k sp items
          ((fix golistlist (iss : list (list cblock)) : R iss :=
              match iss with
              | [] => hrnil
              | it :: rest => hrcons it rest (golist it) (golistlist rest)
              end) items)
    | CRef label dest => href label dest
    | CTable rows => htable rows
    | CId id inner => hid id inner (go inner)
    | CKey label inner => hkey label inner (go inner)
    end.

Definition blocks_of_cblocks (cbs : list cblock) : blocks := map cb_ast cbs.

(* Plain-text paragraphs and headings: one `Str` per line.  `cb_lines
   (cpara ls) = ls` when no line needs escaping, so a test written
   against source lines keeps reading that way. *)
Definition cline (s : string) : list cinline := [CIStr s].
Definition cpara (ls : list string) : cblock := CPara (map cline ls).
Definition cheading (lvl : nat) (ls : list string) : cblock :=
  CHeading lvl (map cline ls).

Local Lemma map_ci_line_cline :
  forall ls, map ci_line (map cline ls) = map escape_end ls.
Proof.
  induction ls as [|s ls IH]; [reflexivity|].
  cbn [map cline]. rewrite IH. reflexivity.
Qed.

(* `cpara` is faithful: it names the paragraph whose content is `ls`,
   which it renders escaped.  The two coincide, and the statement reads
   as the plain `= ls` a reader expects, exactly when no line needs
   escaping, which is every example here.

   Nothing consumes this: it is what a reader of a `cpara`-spelled example
   would otherwise take on trust, and the first thing to break if
   `cline`, `ci_line` or `needs_escape` drifts. *)
Local Lemma cb_lines_cpara : forall ls, cb_lines (cpara ls) = map escape_end ls.
Proof. intros ls. cbn [cb_lines cpara]. apply map_ci_line_cline. Qed.

(*
Renderability
-------------
*)

(* A canonical paragraph: nonempty; its first line classifies as text
   and carries no key connective (so reparsing opens a paragraph there
   rather than another block, and not a key either); every line is
   nonblank and newline-free; and the last line already has no trailing
   whitespace, since the parser would strip it.

   `keyless` is the first-line condition keys add, and it sits beside
   `is_text` for the same reason: both are about what the line *opens*,
   and keyed-blocks 3.5 says continuation lines are never tested.  With
   the setting off it is `true` for every line. *)
Definition para_ok (ls : list string) : bool :=
  match ls with
  | [] => false
  | a :: _ =>
      is_text a
      && keyless a
      && forallb line_ok ls
      && forallb (fun l => negb (bcuts l)) ls
      && String.eqb (strip_trailing_ws (last ls EmptyString))
           (last ls EmptyString)
  end.

(* A canonical code block: valid info string, and content lines that are
   newline-free and do not close a 3-backtick fence.  Content lines may
   be blank or look like any other construct: fences are verbatim. *)
Definition code_ok (info : string) (content : list string) : bool :=
  all_info_chars info
  && forallb
       (fun l => no_nl l && negb (fence_close (Fence "`"%char 3 info) l))
       content.

Definition raw_ok (format : string) (content : list string) : bool :=
  code_ok (String "="%char format) content.

(* A canonical heading: a real level, and text lines that are nonblank
   and newline-free with the last one pre-stripped (the parser strips
   it).  Unlike a paragraph there is no first-line classification
   condition: the hashes make every rendered line a heading line, and the
   text is never reclassified.  Nonempty for the same reason a quote is:
   `Heading lvl []` renders to no lines at all. *)
Definition heading_ok (lvl : nat) (ls : list string) : bool :=
  Nat.leb 1 lvl
  && nonempty ls
  && forallb line_ok ls
  && (bheading_continues || Nat.eqb (List.length ls) 1)%bool
  && String.eqb (strip_trailing_ws (last ls EmptyString)) (last ls EmptyString).

(* A quote opener must stay an ordinary quote when callouts are enabled. *)
Definition quote_header_safe (inner : list cblock) : bool :=
  match sep_lines (map cb_lines inner) with
  | [] => true
  | l :: _ =>
      match quote_header l with
      | None => true | Some _ => false
      end
  end.

(* A callout title is what a one-line heading's content may be. *)
Definition callout_title_ok (title : list cinline) : bool :=
  match title with
  | [] => true
  | _ =>
      line_ok (ci_line title)
      && String.eqb (strip_trailing_ws (ci_line title)) (ci_line title)
  end.

(* Tight/loose, on the item's lines rather than on its block tree.

   The tree is the wrong domain: a gap loosens the enclosing list unless
   a list claims it -- either the next non-blank line opens one, or one
   is already open where the gap falls -- and the tree does not record
   where blanks sit relative to markers.  Two items of the same shape,
   both a block then a gap then a paragraph, part ways on it: `["- b";
   ""; "t"]` leaves the list tight because the gap is the inner list's
   trailing blank, and `["a"; ""; "t"]` loosens it.

   `Parser.lines_loose` is the rule itself, and it is what
   `Parser.list_uniformity` proves the parser implements. *)
Definition item_forces_loose (item : list cblock) : bool :=
  item_loose (item_lines item).

Definition items_force_loose (items : list (list cblock)) : bool :=
  existsb item_forces_loose items.

(* Whether a separator blank in the loose rendering actually reaches the
   list.  It does not when the item before it ends with a nested list:
   the blank is that list's trailing blank, exempt from tightness, and
   `Parser.step` gives it to the inner list.  Mirrors
   `Parser.seps_loosen`, which is what `list_uniformity` carries, and it
   is why a multi-item list is not automatically spellable `Loose`. *)
Definition items_seps_loosen (items : list (list cblock)) : bool :=
  seps_loosen (map item_lines items).

Definition is_clist (cb : cblock) : bool :=
  match cb with CList _ _ _ => true | _ => false end.

Definition is_cid (cb : cblock) : bool :=
  match cb with CId _ _ => true | _ => false end.

(* What the parser still has open when the block's lines run out.  An id
   wrapper is a line in front of its block and changes nothing about the
   end of it, which is why `cb_pair_ok` reads these of its first argument
   and `is_clist` -- a question about the first line -- of its second. *)
Fixpoint ends_clist (cb : cblock) : bool :=
  match cb with
  | CList _ _ _ => true
  | CId _ inner => ends_clist inner
  | CKey _ inner => ends_clist inner
  | _ => false
  end.

Fixpoint ends_ctable (cb : cblock) : bool :=
  match cb with
  | CTable _ => true
  | CId _ inner => ends_ctable inner
  | CKey _ inner => ends_ctable inner
  | _ => false
  end.

Local Fixpoint is_cref (cb : cblock) : bool :=
  match cb with
  | CRef _ _ => true
  | CId _ inner => is_cref inner
  | CKey _ inner => is_cref inner
  | _ => false
  end.

Lemma id_chars_ok_no_nl :
  forall id, id_chars_ok id = true -> no_nl id = true.
Proof.
  induction id as [|c rest IH]; intros H; [reflexivity|].
  cbn [id_chars_ok] in H. apply andb_true_iff in H as [Hc Hr].
  cbn [no_nl]. destruct (Ascii.eqb c "010") eqn:E.
  - assert (Hw : attr_ws c = true).
    { unfold attr_ws. rewrite E.
      destruct (is_ws c), (Ascii.eqb c "012"), (Ascii.eqb c "011"); reflexivity. }
    unfold is_id_char in Hc. rewrite Hw in Hc. discriminate.
  - rewrite (IH Hr). reflexivity.
Qed.

(* A table stays open across the blank that separates it from the next
   block -- a caption may still follow, across any number of blanks -- so
   what ends it is the next block's first line.  `Line.caption_open` is
   not a `line_kind`, so unlike a row this cannot be excluded once and
   for all by `para_ok`'s `is_text`; it is a condition on the *pair*.

   Vacuous, and deliberately not proved so.  A canonical first line
   is nonblank, and `^` is in `InlineView.needs_escape` (the footnote marker
   forces it) so none begins with a caret -- but the second half is a
   fact about the inline layer's escape set, and the roundtrip should not
   rest on it silently.  `no_canonical_caption_opener` pins it. *)
Local Definition closes_table (cb : cblock) : bool :=
  match cb_lines cb with
  | [] => false
  | a :: _ =>
      negb (is_blank a)
      && match caption_open a with Some _ => false | None => true end
  end.

(** The two ways an adjacent pair fails to roundtrip as two AST nodes.
    Two lists: the separating blank makes the parser continue the first
    as loose.  A block after a table: it has to be one whose first line
    closes the table rather than captioning it.  Both are properties of a
    sequence, not of either block alone. *)
Definition cb_pair_ok (c1 c2 : cblock) : bool :=
  (negb (ends_clist c1 && is_clist c2)
   && (negb (ends_ctable c1) || closes_table c2))%bool.

Fixpoint cb_pairs_ok (cbs : list cblock) : bool :=
  match cbs with
  | [] => true
  | c1 :: rest =>
      match rest with
      | [] => true
      | c2 :: _ => cb_pair_ok c1 c2 && cb_pairs_ok rest
      end
  end.

(* Regression: the recursive call slides by one block, so every adjacent
   pair is tested.  Recursing on the tail *after* c2 instead would test
   pairs 1-2, 3-4, ... and miss the offending pair in the third example.
   Three blocks is the shortest input that tells the two apart. *)
Section PairTests.
  Let l : cblock := CList LKBullet Tight [[cpara ["a"]]].
  Let p : cblock := cpara ["p"].

  Example cb_pairs_ok_pair : cb_pairs_ok [l; l] = false.
  Proof. reflexivity. Qed.

  Example cb_pairs_ok_separated : cb_pairs_ok [l; p; l] = true.
  Proof. reflexivity. Qed.

  Example cb_pairs_ok_second_pair : cb_pairs_ok [p; l; l] = false.
  Proof. reflexivity. Qed.

  Example cb_pairs_ok_run : cb_pairs_ok [l; l; l] = false.
  Proof. reflexivity. Qed.

  Example cb_pairs_ok_singleton : cb_pairs_ok [l] = true.
  Proof. reflexivity. Qed.
End PairTests.

(* An item's rendered lines have to satisfy `Parser.item_ok`, which is
   the hypothesis of `Parser.list_uniformity` -- the theorem that says an
   item's contents parse exactly as they would at top level, whatever
   they are.  Spelled out, it asks that "- " does not turn the item's
   first line into a thematic break (classify tests thematic breaks
   before list markers -- the one condition quotes and headings never
   needed, since "> " and "# " are not marker-shaped), that the item
   neither starts nor ends blank, and that no fence is left open inside
   it.

   Nothing here mentions nesting: a list inside a list item clears these
   exactly as flat content does, which is why the fragment covers it. *)

(* The roundtrip hypothesis: this cblock renders to lines that parse back
   to it.  A new construct adds its obligation here.

   A quote must be nonempty: its rendering is its contents' lines with a
   prefix, so an empty quote would render to nothing at all.  The parser
   can build `BlockQuote []` (from a bare ">"), so that one value sits
   outside the canonical view (see cb_ok_quote).  A list's items are each
   held to the same nonempty-and-cb_ok-and-cb_pairs_ok standard as a
   quote's contents (`inner_ok`, reused per item), plus `item_ok` on the
   item's rendering (above) and a spacing condition tying `sp` back to
   what item_forces_loose can prove about the specific rendering: tight
   needs no gap to force looseness anywhere; loose needs either two or
   more items (list_lines then always inserts a forcing blank itself) or
   an internal gap to justify the single-item case, where no inter-item
   blank exists at all. *)
(* What one line can carry back: a label that ends where its bracket does,
   is not a footnote's, and holds no line break, and a destination that is
   one whitespace-free run.  These are `Wf.wf_block`'s conditions on
   `RefDef` plus `no_nl` on the label, which wf leaves to the source line
   and a canonical block has to state for itself. *)
Definition ref_ok (label dest : string) : bool :=
  no_char "]"%char label && negb (is_footnote_label label)
  && no_nl label && no_ws dest.

Local Lemma ref_ok_parts :
  forall label dest,
    ref_ok label dest = true ->
    no_char "]"%char label = true /\ is_footnote_label label = false
    /\ no_nl label = true /\ no_ws dest = true.
Proof.
  intros label dest H. unfold ref_ok in H.
  apply andb_true_iff in H as [H Hd].
  apply andb_true_iff in H as [H Hnl].
  apply andb_true_iff in H as [Hlbl Hfn].
  apply negb_true_iff in Hfn.
  repeat split; assumption.
Qed.

Lemma ref_ok_classify :
  forall label dest,
    ref_ok label dest = true -> classify (ref_line label dest) = KRef label dest.
Proof.
  intros label dest H. apply ref_ok_parts in H as (Hlbl & Hfn & _ & Hd).
  unfold ref_line. apply classify_canonical_ref; assumption.
Qed.

(* The line a definition renders to is a line the parser could have read
   back: nonblank, newline-free, and flush left. *)
Lemma ref_line_ok :
  forall label dest, ref_ok label dest = true -> line_ok (ref_line label dest) = true.
Proof.
  intros label dest H. apply ref_ok_parts in H as (_ & _ & Hnl & Hd).
  unfold line_ok, ref_line, nonblank.
  rewrite !no_nl_append, Hnl, (no_ws_no_nl _ Hd).
  cbn [append is_blank is_ws drop_leading_ws no_nl negb andb].
  apply String.eqb_eq. reflexivity.
Qed.

(* The whole of a row's block obligation: the line it renders to scans
   back as the row it was rendered from.  One decidable test, in the
   shape `para_ok` states its first-line condition -- and it is what
   subsumes every hazard a cell could carry (a bare bar, an unclosed
   verbatim, a cell that reads as a separator). *)
Local Definition row_reparses (r : trow) (l : string) : bool :=
  match classify l with KRow r' => trow_eqb r' r | _ => false end.

(* A definition item may not begin with a reference definition.
   `Ast.def_split` steps over one to find the term (djot.js does, and
   the term is inlines with nowhere to record what stood before it), so
   `: [r]: u` / blank / `t` and `: t` / blank / `[r]: u` have the same
   AST.  The renderer produces the second, and this is `cb_ok` saying so.
   `CRef` is the only leaf that reaches `Ast.invisible_block`: the view
   has no footnote definition. *)
(* A definition item's head is also where its term comes from, and
   `Ast.def_split` drops that paragraph's attributes, so a named head
   cannot round-trip and the canonical view has no spelling for one. *)
Local Definition cdef_head_ok (it : list cblock) : bool :=
  match it with c :: _ => negb (is_cid c || is_cref c) | [] => true end.

Definition ck_content_ok (k : list_kind) (items : list (list cblock)) : bool :=
  match k with
  | LKDef => forallb cdef_head_ok items
  | _ => true
  end.

(* A canonical row: cells that are canonical inlines, a line the
   recognizer gives back, and -- for a header -- one alignment per cell,
   since the AST records the alignment on the cell and a separator wider
   than its row would have nowhere to put the excess. *)
Definition ctrow_ok (r : ctrow) : bool :=
  let cs := ctrow_cells r in
  nonempty cs
  && forallb cis_ok cs
  && line_ok (cells_line (map ci_line cs))
  && row_reparses (TCells (map ci_line cs)) (cells_line (map ci_line cs))
  && match r with
     | CTBody _ => true
     | CTHead als _ =>
         Nat.eqb (List.length als) (List.length cs)
         && row_reparses (TSep als) (sep_line als)
     end.

Local Lemma row_reparses_classify :
  forall r l, row_reparses r l = true -> classify l = KRow r.
Proof.
  intros r l H. unfold row_reparses in H.
  destruct (classify l) eqn:E; try discriminate.
  apply trow_eqb_eq in H. rewrite H. reflexivity.
Qed.

Lemma ctrow_ok_parts :
  forall r, ctrow_ok r = true ->
    nonempty (ctrow_cells r) = true
    /\ forallb cis_ok (ctrow_cells r) = true
    /\ line_ok (cells_line (map ci_line (ctrow_cells r))) = true
    /\ classify (cells_line (map ci_line (ctrow_cells r)))
       = KRow (TCells (map ci_line (ctrow_cells r))).
Proof.
  intros r H. unfold ctrow_ok in H.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H Hrep].
  apply andb_true_iff in H as [H Hlok].
  apply andb_true_iff in H as [Hne Hcis].
  repeat split; try assumption. apply row_reparses_classify, Hrep.
Qed.

Lemma ctrow_ok_head :
  forall als cs, ctrow_ok (CTHead als cs) = true ->
    List.length als = List.length cs /\ classify (sep_line als) = KRow (TSep als).
Proof.
  intros als cs H. unfold ctrow_ok in H.
  apply andb_true_iff in H as [_ H].
  apply andb_true_iff in H as [Hlen Hrep].
  cbn [ctrow_cells] in Hlen.
  split; [apply PeanoNat.Nat.eqb_eq, Hlen | apply row_reparses_classify, Hrep].
Qed.

(* The rendered label must open as text, split at the appended colon,
   and decode without losing trailing whitespace.  Testing the split
   also excludes labels whose inline syntax has precedence as a block. *)
Definition ckey_label_ok (label : cinline) : bool :=
  let src := ci_text [label] in
  let l := src ++ ":" in
  cis_ok [label] && line_ok l && is_text l
  && String.eqb (strip_trailing_ws src) src
  && match key_split l with
     | Some (lbl, value) => String.eqb lbl src && String.eqb value ""
     | None => false
     end.

Lemma ckey_label_ok_parts :
  forall label, ckey_label_ok label = true ->
    cis_ok [label] = true /\ line_ok (ci_text [label] ++ ":") = true
    /\ classify (ci_text [label] ++ ":") = KText
    /\ strip_trailing_ws (ci_text [label]) = ci_text [label]
    /\ key_split (ci_text [label] ++ ":") = Some (ci_text [label], "").
Proof.
  intros label H. unfold ckey_label_ok in H.
  apply andb_true_iff in H as [H Hsplit].
  apply andb_true_iff in H as [H Hstrip].
  apply andb_true_iff in H as [H Htext].
  apply andb_true_iff in H as [Hcis Hline].
  apply String.eqb_eq in Hstrip. apply is_text_classify in Htext.
  destruct (key_split (ci_text [label] ++ ":")) as [[lbl value]|] eqn:E;
    [|discriminate Hsplit].
  apply andb_true_iff in Hsplit as [Hl Hv].
  apply String.eqb_eq in Hl, Hv. subst lbl value.
  repeat split; assumption.
Qed.

(* A canonical div's name: none, or a word the opener reads back whole,
   which is a name only with `bdiv_names`. *)
Definition div_name_ok (name : string) : bool :=
  String.eqb name EmptyString || (bdiv_names && div_word_ok name).

Lemma div_name_ok_word : forall name, div_name_ok name = true -> div_word_ok name = true.
Proof.
  intros name H. unfold div_name_ok in H. apply orb_true_iff in H as [H|H].
  - apply String.eqb_eq in H. subst name. reflexivity.
  - apply andb_true_iff in H as [_ H]. exact H.
Qed.

Lemma div_name_ok_block :
  forall name bs, div_name_ok name = true -> div_block name bs = mk (Div name bs).
Proof.
  intros name bs H. apply div_block_named. unfold div_name_ok in H.
  apply orb_true_iff in H as [H|H]; [rewrite H, orb_true_r; reflexivity|].
  apply andb_true_iff in H as [H _]. rewrite H. reflexivity.
Qed.

Fixpoint cb_ok (cb : cblock) : bool :=
  let inner_ok :=
    fix go (cs : list cblock) : bool :=
      match cs with
      | [] => false                        (* empty quote/item: not renderable *)
      | [c] => cb_ok c
      | c :: rest => (cb_ok c && go rest)%bool
      end in
  (* Unlike `inner_ok`, the empty case is `true`: an empty div renders. *)
  let divs_ok :=
    fix godiv (cs : list cblock) : bool :=
      match cs with
      | [] => true
      | c :: rest => (cb_ok c && godiv rest)%bool
      end in
  let items_ok :=
    fix goitems (iss : list (list cblock)) : bool :=
      match iss with
      | [] => true
      | it :: rest => (inner_ok it && goitems rest)%bool
      end in
  match cb with
  (* The block obligation is on the rendered lines, unchanged; the inline
     obligation is `cis_ok` per line.  Splitting it this way is what keeps
     the block conditions (first line classifies as text, nothing blank,
     last line pre-stripped) stated where they were. *)
  | CPara lss => para_ok (map ci_line lss) && forallb cis_ok lss
  | CThematic => true
  | CCode info content =>
      code_ok info content
      && match info with
         | String "="%char _ => negb braw_blocks
         | _ => true
         end
  | CRaw format content => braw_blocks && raw_ok format content
  | CHeading lvl lss => heading_ok lvl (map ci_line lss) && forallb cis_ok lss
  | CQuote inner => inner_ok inner && cb_pairs_ok inner && quote_header_safe inner
  | CCallout kind fold title inner =>
      bcallouts && callout_kind_ok kind && callout_title_ok title
      && cis_ok title && divs_ok inner && cb_pairs_ok inner
  (* A div's contents may be empty (`:::` then `:::` is a legal,
     contentless div in djot.js), so this is the one container
     without `inner_ok`'s nonempty obligation.  `div_content_ok` is the
     side condition of Parser.div_uniformity, specialised to the lines
     this rendering produces. *)
  | CDiv name inner =>
      bdivs && div_name_ok name && divs_ok inner && cb_pairs_ok inner
      && div_content_ok (sep_lines (map cb_lines inner))
  | CList k sp items =>
      nonempty items && items_ok items
      && ck_ok k (List.length items)
      && forallb (fun it => item_ok (ck_first k) (item_lines it)) items
      && forallb cb_pairs_ok items
      && match sp with
         | Tight => negb (items_force_loose items)
         | Loose => items_seps_loosen items || items_force_loose items
         end
      && ck_content_ok k items
  | CRef label dest => ref_ok label dest
  (* Nonempty for the reason a quote is: a table with no rows renders to
     no lines at all.  The parser can build one (`|---|` alone), so that
     value sits outside the canonical view. *)
  | CTable rows => btables && nonempty rows && forallb ctrow_ok rows
  (* Nested wrappers would render as consecutive specs, whose later id
     overwrites the earlier one.  That source has only one AST value, so
     it is not canonical. *)
  | CId id inner =>
      battrs && explicit_id_ok id && negb (is_cid inner) && cb_ok inner
  | CKey label inner =>
      bkeyed && ckey_label_ok label && cb_ok inner
      && key_content_ok (cb_lines inner) (PPara [])
  end.

Lemma cb_ok_key_parts :
  forall label inner, cb_ok (CKey label inner) = true ->
    bkeyed = true /\ ckey_label_ok label = true /\ cb_ok inner = true
    /\ key_content_ok (cb_lines inner) (PPara []) = true.
Proof.
  intros label inner H. cbn [cb_ok] in H.
  repeat rewrite andb_true_iff in H. tauto.
Qed.

Lemma cb_ok_id :
  forall id inner,
    cb_ok (CId id inner)
    = (battrs && explicit_id_ok id && negb (is_cid inner) && cb_ok inner)%bool.
Proof. reflexivity. Qed.

(* cb_ok's `inner_ok` helper, spelled out: a quote's contents or a list
   item are renderable exactly when nonempty and every cblock in them is
   cb_ok.  One fact, reused for both cb_ok_quote and cb_ok_list. *)
Local Lemma inner_ok_eq :
  forall cs,
    (fix go (cs : list cblock) : bool :=
       match cs with
       | [] => false
       | [c] => cb_ok c
       | c :: rest => (cb_ok c && go rest)%bool
       end) cs
    = (nonempty cs && forallb cb_ok cs)%bool.
Proof.
  induction cs as [|c rest IH]; [reflexivity|].
  destruct rest as [|c2 rest'].
  - cbn [forallb nonempty]. rewrite andb_true_r. reflexivity.
  - change ((fix go (cs : list cblock) : bool :=
               match cs with [] => false | [c0] => cb_ok c0
               | c0 :: r => (cb_ok c0 && go r)%bool end) (c :: c2 :: rest'))
      with (cb_ok c &&
            (fix go (cs : list cblock) : bool :=
               match cs with [] => false | [c0] => cb_ok c0
               | c0 :: r => (cb_ok c0 && go r)%bool end) (c2 :: rest'))%bool.
    rewrite IH. cbn [nonempty forallb]. reflexivity.
Qed.

(* The two arms that split into a block obligation on the rendered lines
   and an inline one per line. *)
Lemma cb_ok_para :
  forall lss,
    cb_ok (CPara lss)
    = (para_ok (map ci_line lss) && forallb cis_ok lss)%bool.
Proof. reflexivity. Qed.

Lemma cb_ok_heading :
  forall lvl lss,
    cb_ok (CHeading lvl lss)
    = (heading_ok lvl (map ci_line lss) && forallb cis_ok lss)%bool.
Proof. reflexivity. Qed.

Lemma cb_ok_quote :
  forall inner,
    cb_ok (CQuote inner)
    = (nonempty inner && forallb cb_ok inner && cb_pairs_ok inner
       && quote_header_safe inner)%bool.
Proof. intros inner. unfold cb_ok. rewrite inner_ok_eq. reflexivity. Qed.

(* The div analogues.  `divs_ok` collapses to a plain `forallb` because
   it has no nonempty case to carry. *)
Local Lemma divs_ok_eq :
  forall cs,
    (fix godiv (cs : list cblock) : bool :=
       match cs with
       | [] => true
       | c :: rest => (cb_ok c && godiv rest)%bool
       end) cs
    = forallb cb_ok cs.
Proof. induction cs as [|c rest IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma cb_ok_callout :
  forall kind fold title inner,
    cb_ok (CCallout kind fold title inner) =
      (bcallouts && callout_kind_ok kind && callout_title_ok title
       && cis_ok title && forallb cb_ok inner && cb_pairs_ok inner)%bool.
Proof. intros. unfold cb_ok. rewrite divs_ok_eq. reflexivity. Qed.

Lemma cb_ok_div :
  forall name inner,
    cb_ok (CDiv name inner)
    = (bdivs && div_name_ok name && forallb cb_ok inner && cb_pairs_ok inner
       && div_content_ok (sep_lines (map cb_lines inner)))%bool.
Proof. intros name inner. unfold cb_ok. rewrite divs_ok_eq. reflexivity. Qed.

Lemma cb_ast_div :
  forall name inner, cb_ast (CDiv name inner) = mk (Div name (map cb_ast inner)).
Proof. reflexivity. Qed.

Lemma cb_lines_div :
  forall name inner,
    cb_lines (CDiv name inner)
    = (div_open_line div_fence name
         :: sep_lines (map cb_lines inner) ++ [div_fence])%list.
Proof. reflexivity. Qed.

Definition cblocks_ok (cbs : list cblock) : bool :=
  (forallb cb_ok cbs && cb_pairs_ok cbs)%bool.

(* The two halves of a pair condition, in the form `parse_cblock`'s
   boundary hypothesis wants them. *)
Lemma cb_pair_ok_nonlist :
  forall c1 c2, ends_clist c1 = true -> cb_pair_ok c1 c2 = true -> is_clist c2 = false.
Proof.
  intros c1 c2 Hc H. unfold cb_pair_ok in H.
  apply andb_true_iff in H as [H _]. apply negb_true_iff in H.
  rewrite Hc in H. cbn [andb] in H. exact H.
Qed.

Lemma cb_pair_ok_closes :
  forall c1 c2 a rest,
    ends_ctable c1 = true -> cb_pair_ok c1 c2 = true -> cb_lines c2 = a :: rest ->
    is_blank a = false /\ caption_open a = None.
Proof.
  intros c1 c2 a rest Hc H Hl. unfold cb_pair_ok in H.
  apply andb_true_iff in H as [_ H]. rewrite Hc in H. cbn [negb orb] in H.
  unfold closes_table in H. rewrite Hl in H.
  apply andb_true_iff in H as [Hb Hcap]. apply negb_true_iff in Hb.
  split; [exact Hb|]. destruct (caption_open a); [discriminate|reflexivity].
Qed.

Lemma cblocks_ok_parts :
  forall cbs, cblocks_ok cbs = true ->
    forallb cb_ok cbs = true /\ cb_pairs_ok cbs = true.
Proof.
  intros cbs H. unfold cblocks_ok in H. apply andb_true_iff in H. exact H.
Qed.

(* cb_ok's `items_ok` helper, spelled out via inner_ok_eq per item. *)
Local Lemma items_ok_eq :
  forall items,
    (fix goitems (iss : list (list cblock)) : bool :=
       match iss with
       | [] => true
       | it :: rest =>
           ((fix go (cs : list cblock) : bool :=
               match cs with
               | [] => false
               | [c] => cb_ok c
               | c :: r => (cb_ok c && go r)%bool
               end) it && goitems rest)%bool
       end) items
    = forallb (fun it => nonempty it && forallb cb_ok it)%bool items.
Proof.
  induction items as [|it rest IH]; [reflexivity|].
  cbn [forallb]. rewrite <- IH, <- inner_ok_eq. reflexivity.
Qed.

Lemma cb_ok_list :
  forall k sp items,
    cb_ok (CList k sp items)
    = (nonempty items
       && forallb (fun it => nonempty it && forallb cb_ok it)%bool items
       && ck_ok k (List.length items)
       && forallb (fun it => item_ok (ck_first k) (item_lines it)) items
       && forallb cb_pairs_ok items
       && match sp with
          | Tight => negb (items_force_loose items)
          | Loose => items_seps_loosen items || items_force_loose items
          end
       && ck_content_ok k items)%bool.
Proof.
  intros k sp items. unfold cb_ok. fold cb_ok. rewrite items_ok_eq. reflexivity.
Qed.

Lemma cb_ok_table :
  forall rows,
    cb_ok (CTable rows) =
    (btables && nonempty rows && forallb ctrow_ok rows)%bool.
Proof. reflexivity. Qed.

Lemma cb_lines_table :
  forall rows, cb_lines (CTable rows) = flat_map ctrow_lines rows.
Proof. reflexivity. Qed.

Lemma cb_ast_table :
  forall rows,
    cb_ast (CTable rows) = mk (Table (mk []) (map (fun r => mk (map mk r)) (ctable_cells [] rows))).
Proof. reflexivity. Qed.

(*
The renderer
============
*)

(* `InlineView.inline_lines` recovers a paragraph's lines from its inlines. *)

(* Render one block to its djot source *lines*.  Line-valued rather than
   string-valued because djot's block structure is line structure: a
   quote's rendering is its contents' lines with a prefix on each, which
   a string-valued renderer could only express by re-splitting.

   The list cases mirror `cb_lines`: each item's own lines first, then
   `Parser.ck_items` puts the markers on.  All five ordered styles render;
   roman and alpha carry a canonicality condition decimal does not, but it
   lives in `ck_ok` and so is `cb_ok`'s business, not the renderer's --
   this function is total and unconditional. *)

(* Which numbering scheme an `OrderedList` node's attributes name.  The
   inverse of `ck_block`'s ordered arms, which is what `render_ck_list`
   needs: rendering a list that `ck_block k` built has to recover `k`. *)
Local Definition lk_of_ol (oa : ordered_list_attributes) : list_kind :=
  match ol_style oa with
  | Decimal => LKDecimal (ol_delim oa) (ol_start oa)
  | RomanLower => LKRoman false (ol_delim oa) (ol_start oa)
  | RomanUpper => LKRoman true (ol_delim oa) (ol_start oa)
  | LetterLower => LKAlpha false (ol_delim oa) (ol_start oa)
  | LetterUpper => LKAlpha true (ol_delim oa) (ol_start oa)
  end.

(* A table's rows, back to source.  A header row is followed by the
   separator its own cells' alignments spell, which is where the
   alignment of the body rows after it comes from too, so nothing has to
   be emitted for them.  The one exception: a table whose first row is a
   body row already carrying an alignment was aligned by a separator that
   preceded it, and that separator has to come back. *)
Local Definition cell_text (c : cell) : string :=
  match c with Cell _ _ ils => hd EmptyString (inline_lines ils EmptyString) end.

Local Definition cell_align (c : cell) : align := match c with Cell _ al _ => al end.

Definition render_row (r : list cell) : list string :=
  (cells_line (map cell_text r)
   :: match r with
      | Cell HeadCell _ _ :: _ => [sep_line (map cell_align r)]
      | _ => []
      end)%list.

Local Definition initial_sep (rows : list (list cell)) : list string :=
  match rows with
  | (Cell BodyCell a _ :: _) as r :: _ =>
      if align_eqb a AlignDefault then [] else [sep_line (map cell_align r)]
  | _ => []
  end.

Definition table_lines (rows : list (list cell)) : list string :=
  (initial_sep rows ++ flat_map render_row rows)%list.

(* A paragraph's source lines.  `inline_lines` ends a line at each
   top-level break; a break inside a container is a newline in its text,
   split off here. *)
Definition text_lines (ils : inlines) : list string :=
  split_lines (join_nl (inline_lines ils EmptyString)).

Local Definition caption_lines (ils : inlines) : list string :=
  match text_lines ils with
  | [] => ["^"]
  | l :: rest => ("^ " ++ l)%string :: rest
  end.

(* A task item's source lines, as the renderer spells them.  The
   continuation prefix is six columns wide for both statuses.  An empty
   item omits the trailing separator space, the shape `Line.task_check`
   accepts. *)
Local Definition task_open (chk : task_status) : string :=
  match chk with Complete => "- [x] " | Incomplete => "- [ ] " end.

Local Definition task_empty (chk : task_status) : string :=
  match chk with Complete => "- [x]" | Incomplete => "- [ ]" end.

Local Definition task_litem_lines (it : task_status * list string) : list string :=
  match it with
  | (chk, []) => [task_empty chk]
  | (chk, l0 :: more) =>
      ((task_open chk ++ l0)%string
       :: map (fun l => (blanks 6 ++ l)%string) more)%list
  end.

(* Any other item's source lines.  An empty item is its marker alone,
   without the separator space, as for a task. *)
Local Definition item_or_marker_lines (it : litem) : list string :=
  match snd it with
  | [] => [strip_trailing_ws (mk_open (fst it))]
  | _ => litem_lines it
  end.

Local Lemma map_item_or_marker_lines :
  forall k lss, forallb nonempty lss = true ->
    map item_or_marker_lines (ck_items k lss) = map litem_lines (ck_items k lss).
Proof.
  intros k lss H. rewrite <- (ck_items_lines k lss) in H.
  induction (ck_items k lss) as [|[m L] rest IH]; [reflexivity|].
  cbn [map forallb snd] in *. apply andb_true_iff in H as [HL Hrest].
  rewrite (IH Hrest). destruct L; [discriminate HL|reflexivity].
Qed.

(* A node's attributes, as the line before its block.  An unnamed div's
   class goes on its fence instead when it is one word and comes first:
   an attribute line's class replaces the fence's, so two words have to
   go on the line, and a fence's class reads back ahead of the line's
   attributes.  A named div's fence holds its name, and with `bdiv_names`
   a fence's word is a name, so a class stays on the line. *)
Definition attr_lines (a : attr) : list string :=
  match a with [] => [] | _ => [attr_spec a] end.

Definition fence_class (a : attr) (b : block) : string :=
  match b with
  | Div EmptyString _ =>
      if bdiv_names then EmptyString else
      match a with
      | (k, c) :: _ =>
          if String.eqb k "class" && class_word_ok c then c else EmptyString
      | [] => EmptyString
      end
  | _ => EmptyString
  end.

Lemma fence_class_nil : forall b, fence_class [] b = EmptyString.
Proof.
  intros b. destruct b; try reflexivity. destruct name; [|reflexivity].
  cbn [fence_class]. destruct bdiv_names; reflexivity.
Qed.

Definition drop_class (cls : string) (a : attr) : attr :=
  if String.eqb cls EmptyString then a
  else filter (fun kv => negb (String.eqb (fst kv) "class")) a.

(* A div's fence is three colons unless its body would close that early,
   and then one longer than the longest closer in the body.  The test is
   the one the canonical fragment asks of a div (`div_content_ok`). *)
Local Definition closer_run (l : string) : nat :=
  let (n, r) := count_run ":" (drop_leading_ws l) in
  if Nat.leb 3 n && is_blank r then n else 0.

Definition div_fence_for (body : list string) : string :=
  if div_content_ok body then div_fence
  else chars ":" (Nat.max 3 (S (list_max (map closer_run body)))).

(* A footnote's body sits under its label, indented so that every line
   belongs to it; blank lines stay blank. *)
Local Definition note_indent (l : string) : string :=
  match l with EmptyString => EmptyString | _ => ("  " ++ l)%string end.

(* A block with its attributes [a], to djot source lines.  A section is its
   blocks: its attributes came off its heading, and the line in front of
   the section is the line in front of the heading. *)
Fixpoint render_lines (a : attr) (b : block) : list string :=
  let itemss :=
    fix goitems (items : list (node blocks)) : list (list string) :=
      match items with
      | [] => []
      | Node _ _ it :: rest =>
          sep_lines (map (fun n => render_lines (node_attrs n) (node_contents n)) it)
          :: goitems rest
      end in
  let taskitemss :=
    fix gotasks (items : list (node (task_status * blocks)))
      : list (task_status * list string) :=
      match items with
      | [] => []
      | Node _ _ (chk, it) :: rest =>
          (chk, sep_lines
                  (map (fun n => render_lines (node_attrs n) (node_contents n)) it))
          :: gotasks rest
      end in
  (* A definition item's lines are its definition's, with the term put
     back at the head as the paragraph it was split from.  An absent term
     puts nothing back, which is what makes `: # h` render as one line. *)
  let defitemss :=
    fix godefs (its : list (node (node inlines * node blocks))) : list (list string) :=
      match its with
      | [] => []
      | Node _ _ (Node _ _ term, Node _ _ it) :: rest =>
          sep_lines
            ((match term with
              | [] => []
              | _ => [text_lines term]
              end)
             ++ map (fun n => render_lines (node_attrs n) (node_contents n)) it)%list
          :: godefs rest
      end in
  let cls := fence_class a b in
  (attr_lines (drop_class cls a) ++
   match b with
   | Para ils => text_lines ils
   | Heading lvl ils => map (heading_line lvl) (text_lines ils)
   | ThematicBreak => [thematic_line]
   | CodeBlock lang text =>
       (code_open lang :: split_lines text ++ [code_close])%list
   | RawBlock fmt text =>
       (code_open ("=" ++ fmt)%string :: split_lines text ++ [code_close])%list
   | BlockQuote bs =>
       map quote_line
         (sep_lines (map (fun n => render_lines (node_attrs n) (node_contents n)) bs))
   | Ext_callout kind fold title bs =>
       (quote_line
          (callout_header_line kind fold (String.concat " " (text_lines title)))
        :: map quote_line
          (sep_lines (map (fun n => render_lines (node_attrs n) (node_contents n)) bs)))%list
   | Div name bs =>
       let body := sep_lines (map (fun n => render_lines (node_attrs n) (node_contents n)) bs) in
       let word := match name with EmptyString => cls | _ => name end in
       (div_open_line (div_fence_for body) word :: body ++ [div_fence_for body])%list
   | Section bs =>
       sep_lines (map (fun n => render_lines (node_attrs n) (node_contents n)) bs)
   | BulletList sp items =>
       list_lines sp (map item_or_marker_lines (ck_items LKBullet (itemss items)))
   | DefinitionList sp its =>
       list_lines sp (map item_or_marker_lines (ck_items LKDef (defitemss its)))
   | OrderedList oa sp items =>
       list_lines sp (map item_or_marker_lines (ck_items (lk_of_ol oa) (itemss items)))
   | TaskList sp items =>
       list_lines sp (map task_litem_lines (taskitemss items))
   | RefDef label dest => [ref_line label dest]
   | FootnoteDef label bs =>
       ("[^" ++ label ++ "]:")%string
       :: map note_indent
            (sep_lines (map (fun n => render_lines (node_attrs n) (node_contents n)) bs))
   | Ext_keyed label inner =>
       key_lines
         (String.concat "" (map (fun n => inline_text (node_contents n)) label))
         (match inner with Node _ [] (Para _) => true | _ => false end)
         (render_lines (node_attrs inner) (node_contents inner))
   | Table cap rows =>
       (table_lines (map (fun r => map node_contents (node_contents r)) rows)
        ++ match node_contents cap with
           | [] => []
           | c => caption_lines c
           end)%list
   end)%list.

Definition render_block_lines (b : block) : list string := render_lines [] b.

(* One node's lines: its attribute line, then its block's. *)
Definition render_node_lines (n : node block) : list string :=
  render_lines (node_attrs n) (node_contents n).

Definition render_blocks_lines (bs : blocks) : list (list string) :=
  map render_node_lines bs.

(* Every canonical block but a named one is `mk`-wrapped, which is what
   makes `add_attr` on top of it a one-key attribute set. *)
Lemma cb_ast_mk : forall cb, is_cid cb = false -> exists x, cb_ast cb = mk x.
Proof.
  intros cb H. destruct cb; try (eexists; reflexivity); discriminate H.
Qed.

Lemma render_node_lines_mk :
  forall x, render_node_lines (mk x) = render_block_lines x.
Proof. reflexivity. Qed.

(* Attributes other than a class only add their line: the class is the
   one a div can move onto its fence. *)
Lemma render_lines_noclass :
  forall a x,
    alist_lookup "class" a = None ->
    render_lines a x = (attr_lines a ++ render_block_lines x)%list.
Proof.
  intros a x H.
  assert (Hc : forall name bs, fence_class a (Div name bs) = EmptyString).
  { intros name bs. destruct name; [|reflexivity]. cbn [fence_class].
    destruct bdiv_names; [reflexivity|]. destruct a as [|[k v] a']; [reflexivity|].
    cbn [alist_lookup] in H.
    destruct (String.eqb "class" k) eqn:E; [discriminate H|].
    rewrite String.eqb_sym, E. reflexivity. }
  unfold render_block_lines.
  destruct x; cbn [render_lines drop_class attr_lines String.eqb app];
    try (rewrite Hc, fence_class_nil; reflexivity); reflexivity.
Qed.

Lemma render_block_div :
  forall name bs,
    div_content_ok (sep_lines (render_blocks_lines bs)) = true ->
    render_block_lines (Div name bs)
    = (div_open_line div_fence name
         :: sep_lines (render_blocks_lines bs) ++ [div_fence])%list.
Proof.
  intros name bs H. unfold render_block_lines.
  cbn [render_lines]. rewrite fence_class_nil.
  cbn [drop_class attr_lines String.eqb app].
  change (map (fun n => render_lines (node_attrs n) (node_contents n)) bs)
    with (render_blocks_lines bs).
  unfold div_fence_for. rewrite H. destruct name; reflexivity.
Qed.

Lemma render_block_quote :
  forall bs,
    render_block_lines (BlockQuote bs)
    = map quote_line (sep_lines (render_blocks_lines bs)).
Proof. reflexivity. Qed.

(* What a definition item has to look like for the split to be
   invertible.  Two ways it is not.  A paragraph with no inlines would
   contribute a line and no term, so rendering would lose it -- and
   nothing canonical spells one, which is `ci_para_nonempty` below.  And
   a leading reference or footnote definition is one `def_split` steps
   *over*, so the term it finds sits behind it in the source and in
   front of it in the rendering: the two spellings have the same AST,
   and `cb_ok` picks the one the renderer produces. *)
Local Definition has_attrs (a : attr) : bool :=
  match a with [] => false | _ => true end.

Local Definition def_head_ok (bs : blocks) : bool :=
  match bs with
  | Node _ a (Para ils) :: _ => nonempty ils && negb (has_attrs a)
  | Node _ _ x :: _ => negb (invisible_block x)
  | [] => true
  end.

(* Every item renders to a line, so no item comes out as a bare marker. *)
Definition ck_render_ok (k : list_kind) (items : list blocks) : bool :=
  (forallb (fun it => nonempty (sep_lines (render_blocks_lines it))) items
   && match k with
      | LKDef => forallb def_head_ok items
      | LKTask checks => Nat.eqb (length checks) (length items)
      | _ => true
      end)%bool.

Local Lemma render_forallb_map :
  forall {A B : Type} (f : B -> bool) (g : A -> B) xs,
    forallb f (map g xs) = forallb (fun x => f (g x)) xs.
Proof. induction xs as [|x xs IH]; [reflexivity|cbn; rewrite IH; reflexivity]. Qed.

Local Lemma forallb_item_ok_nonempty :
  forall m items,
    forallb (fun it => item_ok m (item_lines it)) items = true ->
    forallb (fun it => nonempty (item_lines it)) items = true.
Proof.
  intros m items. induction items as [|it rest IH]; [reflexivity|].
  cbn [forallb]. intros H. apply andb_true_iff in H as [Hit Hrest].
  apply andb_true_iff. split.
  - destruct (item_lines it); [discriminate Hit|reflexivity].
  - apply IH, Hrest.
Qed.

(* The list equation at every kind, which is what `cb_lines_list` has to
   be matched against.  `ck_block` picks the constructor and `ck_items`
   the markers, so the flavours share one statement. *)
Lemma render_ck_list :
  forall k sp items,
    ck_render_ok k items = true ->
    render_block_lines (ck_block k sp items)
    = list_lines sp
        (map litem_lines
           (ck_items k (map (fun it => sep_lines (render_blocks_lines it)) items))).
Proof.
  assert (H : forall items,
            (fix goitems (its : list (node blocks)) : list (list string) :=
               match its with
               | [] => []
               | Node _ _ it :: rest =>
                   sep_lines (map (fun n => render_lines (node_attrs n) (node_contents n)) it)
                   :: goitems rest
               end) (map mk items)
            = map (fun it => sep_lines (render_blocks_lines it)) items).
  { induction items as [|it rest IH]; [reflexivity|].
    cbn [map]. rewrite IH. reflexivity. }
  assert (Hdef : forall items,
             forallb def_head_ok items = true ->
             (fix godefs (its : list (node (node inlines * node blocks)))
                 : list (list string) :=
                match its with
                | [] => []
                | Node _ _ (Node _ _ term, Node _ _ it) :: rest =>
                    sep_lines
                      ((match term with
                        | [] => []
                        | _ => [text_lines term]
                        end)
                       ++ map (fun n => render_lines (node_attrs n) (node_contents n)) it)%list
                    :: godefs rest
                end) (def_items items)
             = map (fun it => sep_lines (render_blocks_lines it)) items).
  { unfold def_items. induction items as [|it rest IH]; [reflexivity|].
    cbn [map forallb]. intros Hok. apply andb_true_iff in Hok as [Hit Hrest].
    rewrite (IH Hrest). f_equal.
    destruct it as [|[q b x] more]; [reflexivity|].
    destruct x; cbn [def_head_ok invisible_block negb] in Hit;
      try discriminate Hit;
      cbn [def_node def_item def_split invisible_block mk]; try reflexivity.
    (* the paragraph case: the split fires at the head, and `def_head_ok`
       says the term it takes is not empty and carries no attributes -- the split
       drops the paragraph's attributes, so a spec line here would have
       nothing to come back to. *)
    destruct ils as [|i ils']; [discriminate Hit|].
    apply andb_true_iff in Hit as [_ Hid]. apply negb_true_iff in Hid.
    destruct b as [|kv b]; [|discriminate Hid].
    reflexivity. }
  intros [| |checks|d start|up d start|up d start] sp items Hrok;
    [| | | | destruct up | destruct up ];
    unfold render_block_lines;
    cbn [ck_block render_lines fence_class drop_class attr_lines String.eqb app
         lk_of_ol roman_sty alpha_sty
         ol_style ol_delim ol_start];
    unfold ck_render_ok in Hrok; apply andb_true_iff in Hrok as [Hne Hrok];
    assert (Hne' : forallb nonempty
                     (map (fun it => sep_lines (render_blocks_lines it)) items) = true)
      by (rewrite render_forallb_map; exact Hne);
    try solve [rewrite H, (map_item_or_marker_lines _ _ Hne'); reflexivity].
  - rewrite (Hdef items Hrok), (map_item_or_marker_lines _ _ Hne'). reflexivity.
  - clear Hne'. apply Nat.eqb_eq in Hrok. rename Hrok into Hlen.
    f_equal.
    revert checks Hlen Hne. induction items as [|it items IH];
      intros [|chk checks] Hlen Hne; try discriminate; [reflexivity|].
    cbn [length forallb] in Hlen, Hne. injection Hlen as Hlen.
    apply andb_true_iff in Hne as [Hit Hitems].
    cbn [task_items render_lines ck_items task_ck_items map fst snd mk].
    destruct (sep_lines (render_blocks_lines it)) as [|l0 more] eqn:E;
      [discriminate Hit|].
    change (fun n : node block =>
              render_lines (node_attrs n) (node_contents n))
      with render_node_lines.
    fold (render_blocks_lines it). rewrite E.
    cbn [task_litem_lines litem_lines indent_lines mk_open mk_cont].
    destruct chk; cbn [task_open]; f_equal; apply IH; assumption.
Qed.

(* A canonical paragraph has content: `para_ok` asks `is_text` of the
   first line, and an empty line is blank. *)
Local Lemma ci_para_nonempty :
  forall lss, para_ok (map ci_line lss) = true -> nonempty (ci_para lss) = true.
Proof.
  intros [|cis rest] H; [discriminate|].
  destruct rest as [|cis2 rest'].
  - rewrite ci_para_one. destruct cis as [|c cs]; [|reflexivity].
    cbn [map ci_line ci_text para_ok] in H. discriminate.
  - rewrite ci_para_cons2. destruct (ci_inlines cis); reflexivity.
Qed.

(* `render_ck_list`'s hypothesis, discharged for every canonical list.
   A `CPara` is the only cblock whose AST is a paragraph, and the lemma
   above says it is not an empty one -- so the condition is a fact about
   the canonical view rather than a clause `cb_ok` has to carry. *)
Lemma ck_render_ok_cb :
  forall k items,
    forallb (forallb cb_ok) items = true ->
    ck_ok k (length items) = true ->
    forallb (fun it => item_ok (ck_first k) (item_lines it)) items = true ->
    map (fun it => sep_lines (render_blocks_lines (map cb_ast it))) items
      = map item_lines items ->
    ck_content_ok k items = true ->
    ck_render_ok k (map (map cb_ast) items) = true.
Proof.
  intros k items H Hck Hitem Hrender Hcont.
  unfold ck_render_ok. apply andb_true_iff. split.
  { pose proof (forallb_item_ok_nonempty _ _ Hitem) as Hnonempty.
    rewrite <- render_forallb_map in Hnonempty.
    rewrite <- Hrender in Hnonempty.
    rewrite render_forallb_map in Hnonempty.
    rewrite render_forallb_map. exact Hnonempty. }
  destruct k as [| |checks|d start|up d start|up d start]; try reflexivity.
  - cbn [ck_content_ok] in Hcont.
    clear Hck Hitem Hrender.
    induction items as [|it rest IH]; [reflexivity|].
    cbn [map forallb] in H, Hcont |- *. apply andb_true_iff in H as [Hit Hrest].
    apply andb_true_iff in Hcont as [Hhead Hconts].
    rewrite (IH Hrest Hconts), andb_true_r.
    destruct it as [|c more]; [reflexivity|].
    cbn [forallb] in Hit. apply andb_true_iff in Hit as [Hc _].
    destruct c; cbn [map cb_ast def_head_ok has_attrs mk node_contents
                     invisible_block negb andb];
      try reflexivity; try discriminate Hhead.
    + cbn [cb_ok] in Hc. apply andb_true_iff in Hc as [Hp _].
      rewrite (ci_para_nonempty _ Hp). reflexivity.
    + destruct k; reflexivity.
  - apply Nat.eqb_eq. cbn [ck_ok] in Hck.
    apply andb_true_iff in Hck as [_ Hck]. apply Nat.eqb_eq in Hck.
    rewrite length_map. exact Hck.
Qed.

(* The table equation `render_cb_lines` has to be matched against.  Each
   half is one induction: a cell's text is its inlines' one line, and a
   header's separator is its cells' alignments read back off the AST --
   which is why `ctrow_ok` asks for one alignment per cell.

   `initial_sep` never fires on a canonical table: the view has no way to
   spell a leading body row that is already aligned. *)
Local Lemma cell_text_ci : forall ct al c, cell_text (Cell ct al (ci_inlines c)) = ci_line c.
Proof.
  intros ct al c. unfold cell_text.
  rewrite <- (app_nil_r (ci_inlines c)), inline_lines_ci_inlines by reflexivity.
  reflexivity.
Qed.

Local Lemma map_cell_text_ccells :
  forall ct als cs, map cell_text (ccells_of ct als cs) = map ci_line cs.
Proof.
  intros ct als cs. revert als.
  induction cs as [|c cs IH]; intros als; [reflexivity|].
  destruct als as [|a als']; cbn [ccells_of map]; rewrite cell_text_ci, IH;
    reflexivity.
Qed.

Local Lemma map_cell_align_ccells :
  forall ct als cs,
    List.length als = List.length cs ->
    map cell_align (ccells_of ct als cs) = als.
Proof.
  intros ct als cs. revert als.
  induction cs as [|c cs IH]; intros [|a als'] Hlen;
    try (cbn [List.length] in Hlen; discriminate); [reflexivity|].
  cbn [ccells_of map cell_align]. cbn [List.length] in Hlen.
  rewrite IH by (injection Hlen; auto). reflexivity.
Qed.

Local Lemma render_row_body_cells :
  forall als c cs,
    render_row (ccells_of BodyCell als (c :: cs))
    = [cells_line (map ci_line (c :: cs))].
Proof.
  intros als c cs. destruct als as [|a als'];
    unfold render_row; cbn [ccells_of map];
    rewrite cell_text_ci, map_cell_text_ccells; reflexivity.
Qed.

Local Lemma render_row_head_cells :
  forall als c cs,
    List.length als = List.length (c :: cs) ->
    render_row (ccells_of HeadCell als (c :: cs))
    = [cells_line (map ci_line (c :: cs)); sep_line als].
Proof.
  intros [|a als'] c cs Hlen; [cbn [List.length] in Hlen; discriminate|].
  unfold render_row. cbn [ccells_of map cell_align].
  rewrite cell_text_ci, map_cell_text_ccells.
  rewrite (map_cell_align_ccells HeadCell als' cs)
    by (cbn [List.length] in Hlen; injection Hlen; auto).
  reflexivity.
Qed.

Local Lemma render_row_ctrow :
  forall als r, ctrow_ok r = true ->
  render_row (match r with
              | CTBody cs => ccells_of BodyCell als cs
              | CTHead als' cs => ccells_of HeadCell als' cs
              end)
  = ctrow_lines r.
Proof.
  intros als [cs|als' cs] H; unfold ctrow_ok in H; cbn [ctrow_cells] in H.
  - apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [Hne _].
    destruct cs as [|c cs']; [discriminate Hne|].
    cbn [ctrow_lines]. apply render_row_body_cells.
  - apply andb_true_iff in H as [H Hhead].
    apply andb_true_iff in Hhead as [Hlen _].
    apply PeanoNat.Nat.eqb_eq in Hlen.
    apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [Hne _].
    destruct cs as [|c cs']; [discriminate Hne|].
    cbn [ctrow_lines]. apply render_row_head_cells. exact Hlen.
Qed.

Local Lemma flat_map_render_row_ctable :
  forall rows als, forallb ctrow_ok rows = true ->
  flat_map render_row (ctable_cells als rows) = flat_map ctrow_lines rows.
Proof.
  induction rows as [|r rows IH]; intros als Hok; [reflexivity|].
  cbn [forallb] in Hok. apply andb_true_iff in Hok as [Hr Hrows].
  destruct r as [cs|als' cs]; cbn [ctable_cells flat_map];
    rewrite (render_row_ctrow als _ Hr).
  - rewrite (IH als Hrows). reflexivity.
  - rewrite (IH als' Hrows). reflexivity.
Qed.

Local Lemma initial_sep_ctable :
  forall rows, initial_sep (ctable_cells [] rows) = [].
Proof.
  intros [|r rows]; [reflexivity|].
  destruct r as [cs|als' cs].
  - destruct cs as [|c cs']; reflexivity.
  - destruct cs as [|c cs']; [reflexivity|].
    destruct als' as [|a als0]; reflexivity.
Qed.

Lemma table_lines_ctable :
  forall rows, forallb ctrow_ok rows = true ->
  table_lines (ctable_cells [] rows) = flat_map ctrow_lines rows.
Proof.
  intros rows Hok. unfold table_lines.
  rewrite (initial_sep_ctable rows), (flat_map_render_row_ctable rows [] Hok).
  reflexivity.
Qed.

(* Blocks separated by a blank line: the separator the parser reads back
   as "end the current block". *)
Definition render_djot (bs : blocks) : string :=
  String.concat nl (sep_lines (render_blocks_lines bs)).

(*
Documents
---------

A parsed document back to source.  The document pass added two things
the source did not spell, and moved one thing out of the tree:

- A heading's id, when the pass derived it, is left out.  The test is the
  heading text's base id: the pass gives a heading exactly that id when
  it is free, and it is free again in the rendering, since every id taken
  before the heading is taken there too.  A heading whose id was
  disambiguated (`a-1`) keeps it, spelled out.
- A section is its blocks (`render_lines`).
- Footnote definitions come back after the blocks, in the order of the
  document's note table.  Where they stood in the source is not kept. *)

Local Definition drop_id_if (v : string) (a : attr) : attr :=
  match alist_lookup "id" a with
  | Some v' =>
      if String.eqb v v' then filter (fun kv => negb (String.eqb (fst kv) "id")) a
      else a
  | None => a
  end.

Local Definition base_id (ils : inlines) : string :=
  Document.id_base (Document.inlines_text ils).

(* Recursion is on the block, with its node's position and attributes
   alongside, which is the shape the guard accepts (`Undo.pass_block`). *)
Fixpoint drop_auto_ids (b : block) (p : pos) (a : attr) {struct b} : node block :=
  let go :=
    fix go (bs : blocks) : blocks :=
      match bs with
      | [] => []
      | Node p' a' x :: rest => drop_auto_ids x p' a' :: go rest
      end in
  let goits :=
    fix goits (its : list (node blocks)) : list (node blocks) :=
      match its with
      | [] => []
      | Node ip ia it :: rest => Node ip ia (go it) :: goits rest
      end in
  match b with
  | Heading lvl ils => Node p (drop_id_if (base_id ils) a) (Heading lvl ils)
  | Section bs =>
      let a' := match bs with
                | Node _ _ (Heading _ ils) :: _ => drop_id_if (base_id ils) a
                | _ => a
                end in
      Node p a' (Section (go bs))
  | BlockQuote bs => Node p a (BlockQuote (go bs))
  | Ext_callout kind fold title bs =>
      Node p a (Ext_callout kind fold title (go bs))
  | Div name bs => Node p a (Div name (go bs))
  | FootnoteDef l bs => Node p a (FootnoteDef l (go bs))
  | BulletList sp its => Node p a (BulletList sp (goits its))
  | OrderedList oa sp its => Node p a (OrderedList oa sp (goits its))
  | TaskList sp its =>
      Node p a (TaskList sp
        ((fix gotasks (ts : list (node (task_status * blocks))) :=
            match ts with
            | [] => []
            | Node ip ia (chk, it) :: rest => Node ip ia (chk, go it) :: gotasks rest
            end) its))
  | DefinitionList sp its =>
      Node p a (DefinitionList sp
        ((fix godefs (ds : list (node (node inlines * node blocks))) :=
            match ds with
            | [] => []
            | Node ip ia (term, Node dp da it) :: rest =>
                Node ip ia (term, Node dp da (go it)) :: godefs rest
            end) its))
  | Ext_keyed label (Node p' a' x) => Node p a (Ext_keyed label (drop_auto_ids x p' a'))
  | _ => Node p a b
  end.

Definition doc_source_blocks (d : doc) : blocks :=
  (map (fun n => match n with Node p a x => drop_auto_ids x p a end) (doc_blocks d)
   ++ map (fun ln => mk (FootnoteDef (fst ln) (snd ln))) (doc_footnotes d))%list.

Definition render_doc (d : doc) : string := render_djot (doc_source_blocks d).

End WithTable.

(* `cb_pairs_ok`'s caption conjunct, on the one pair that could reach it:
   `^` is in `InlineView.needs_escape`, so a paragraph of literal `^ cap`
   renders `\^ cap` and the pair is accepted.  Read at djot's own table,
   since the escape set is where the answer comes from. *)
Example no_canonical_caption_opener :
  cb_pairs_ok [CTable [CTBody [[CIStr "a"]]]; cpara ["^ cap"]] = true.
Proof. reflexivity. Qed.
