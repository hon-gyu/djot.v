(* Djot rendering (AST -> djot source), modeled on djoths's Djot.hs,
   together with the canonical form it inverts.

   `cblock` is the canonical (renderable) view of a block: the parser's
   image, described by the data that determines it.  Renderability of a
   paragraph is phrased through the line classifier: the first line must
   *classify* as text (so the parse re-opens a paragraph there), interior
   lines merely nonblank (paragraphs cannot be interrupted), the last
   line pre-stripped (the parser strips it, so a roundtripping AST cannot
   carry trailing whitespace).  Each new construct added to Line.v gets a
   cblock constructor, a canonical rendering, and a cb_ok obligation —
   that is the whole roundtrip extension recipe. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Line Ast Parser.
Import ListNotations.

Local Open Scope string_scope.

(*
Block layout
============
*)

(* The renderer's canonical spellings, fixed once so both the rendering
   and the classification lemmas can refer to them. *)
Definition thematic_line : string := "* * * *".
Definition code_close : string := "```".
Definition code_open (info : string) : string := "```" ++ info.
Definition quote_open : string := "> ".
Definition quote_line (l : string) : string := quote_open ++ l.

(* Flatten per-block line lists into one line list, with a single blank
   line between blocks (and none at either end).  This is the layout
   both a document and a block quote's contents use — which is
   uniformity, on the rendering side. *)
Fixpoint sep_lines (lss : list (list string)) : list string :=
  match lss with
  | [] => []
  | [ls] => ls
  | ls :: rest => (ls ++ EmptyString :: sep_lines rest)%list
  end.

Lemma quote_line_empty : quote_line EmptyString = quote_open.
Proof. unfold quote_line. apply append_empty_r. Qed.

(*
Canonical blocks
================
*)

(* A block described by the source data that determines it — a paragraph
   by its lines, a code block by its info string and content lines, a
   quote by the canonical blocks inside it.  One constructor per block
   construct the roundtrip covers.

   The list-valued constructor makes `cblock` a nested inductive, so the
   three projections below use hand-inlined fixpoints (Rocq rejects the
   mutual-recursion spelling) and each gets a `_quote` lemma recovering
   the `map`/`forallb` form the proofs actually use. *)
Inductive cblock : Type :=
  | CPara (ls : list string)
  | CThematic
  | CCode (info : string) (content : list string)
  | CQuote (inner : list cblock).

(* The two projections a cblock sits between: its source lines... *)
Fixpoint cb_lines (cb : cblock) : list string :=
  let quoted :=
    fix go (cs : list cblock) : list string :=
      match cs with
      | [] => []
      | [c] => map quote_line (cb_lines c)
      | c :: rest => (map quote_line (cb_lines c) ++ quote_open :: go rest)%list
      end in
  match cb with
  | CPara ls => ls
  | CThematic => [thematic_line]
  | CCode info content => (code_open info :: content ++ [code_close])%list
  | CQuote inner => quoted inner
  end.

(* ...and the AST node the parser builds from those lines.  Roundtrip is
   then: cb_lines, rendered and reparsed, gives back cb_ast. *)
Fixpoint cb_ast (cb : cblock) : node block :=
  let asts :=
    fix go (cs : list cblock) : blocks :=
      match cs with [] => [] | c :: rest => cb_ast c :: go rest end in
  match cb with
  | CPara ls => mk (Para (para_inlines ls))
  | CThematic => mk ThematicBreak
  | CCode info content => fence_block (Fence "`"%char 3 info) content
  | CQuote inner => mk (BlockQuote (asts inner))
  end.

(* Peel a quote back open, so the inlined fixpoint above has a name the
   telescoping lemma can mention. *)
Definition unquote (n : node block) : blocks :=
  match node_contents n with BlockQuote bs => bs | _ => [] end.

Lemma cb_ast_quote :
  forall inner, cb_ast (CQuote inner) = mk (BlockQuote (map cb_ast inner)).
Proof.
  assert (H : forall cs, unquote (cb_ast (CQuote cs)) = map cb_ast cs).
  { induction cs as [|c rest IH]; [reflexivity|].
    change (unquote (cb_ast (CQuote (c :: rest))))
      with (cb_ast c :: unquote (cb_ast (CQuote rest))).
    rewrite IH. reflexivity. }
  intros inner.
  change (cb_ast (CQuote inner))
    with (mk (BlockQuote (unquote (cb_ast (CQuote inner))))).
  rewrite H. reflexivity.
Qed.

Lemma cb_lines_quote :
  forall inner,
    cb_lines (CQuote inner) = map quote_line (sep_lines (map cb_lines inner)).
Proof.
  induction inner as [|c rest IH]; [reflexivity|].
  destruct rest as [|c2 rest'].
  - reflexivity.
  - change (cb_lines (CQuote (c :: c2 :: rest')))
      with (map quote_line (cb_lines c)
            ++ quote_open :: cb_lines (CQuote (c2 :: rest')))%list.
    rewrite IH.
    cbn [map sep_lines]. rewrite map_app. cbn [map].
    rewrite quote_line_empty. reflexivity.
Qed.

(* Rocq's generated cblock_ind does not descend into CQuote's list, so
   every proof over cblocks needs this two-predicate version: P for a
   block, Q for a list of them, each feeding the other. *)
Definition cblock_ind2
  (P : cblock -> Prop) (Q : list cblock -> Prop)
  (hpara : forall ls, P (CPara ls))
  (hthem : P CThematic)
  (hcode : forall info content, P (CCode info content))
  (hquote : forall inner, Q inner -> P (CQuote inner))
  (hnil : Q [])
  (hcons : forall c rest, P c -> Q rest -> Q (c :: rest))
  : forall cb, P cb :=
  fix go (cb : cblock) : P cb :=
    match cb with
    | CPara ls => hpara ls
    | CThematic => hthem
    | CCode info content => hcode info content
    | CQuote inner =>
        hquote inner
          ((fix golist (cs : list cblock) : Q cs :=
              match cs with
              | [] => hnil
              | c :: rest => hcons c rest (go c) (golist rest)
              end) inner)
    end.

Definition doc_of_cblocks (cbs : list cblock) : doc :=
  {| doc_blocks := map cb_ast cbs
   ; doc_footnotes := []
   ; doc_references := []
   ; doc_auto_references := []
   ; doc_auto_identifiers := [] |}.

(*
Renderability
-------------
*)

(* A canonical paragraph: nonempty; its first line classifies as text (so
   reparsing opens a paragraph there rather than another block); every
   line is nonblank and newline-free; and the last line already has no
   trailing whitespace, since the parser would strip it. *)
Definition para_ok (ls : list string) : bool :=
  match ls with
  | [] => false
  | a :: _ =>
      is_text a
      && forallb line_ok ls
      && String.eqb (strip_trailing_ws (last ls EmptyString))
           (last ls EmptyString)
  end.

(* A canonical code block: valid info string, and content lines that are
   newline-free and do not close a 3-backtick fence.  Content lines may
   be blank or look like any other construct — fences are verbatim. *)
Definition code_ok (info : string) (content : list string) : bool :=
  all_info_chars info
  && forallb
       (fun l => no_nl l && negb (fence_close (Fence "`"%char 3 info) l))
       content.

(* The roundtrip hypothesis: this cblock renders to lines that parse back
   to it.  A new construct adds its obligation here.

   A quote must be nonempty: its rendering is its contents' lines with a
   prefix, so an empty quote would render to nothing at all.  The parser
   *can* build `BlockQuote []` (from a bare ">"), so that one value sits
   outside the canonical view — see cb_ok_quote. *)
Fixpoint cb_ok (cb : cblock) : bool :=
  let inner_ok :=
    fix go (cs : list cblock) : bool :=
      match cs with
      | [] => false                        (* empty quote: not renderable *)
      | [c] => cb_ok c
      | c :: rest => (cb_ok c && go rest)%bool
      end in
  match cb with
  | CPara ls => para_ok ls
  | CThematic => true
  | CCode info content => code_ok info content
  | CQuote inner => inner_ok inner
  end.

Lemma cb_ok_quote :
  forall inner,
    cb_ok (CQuote inner) = (nonempty inner && forallb cb_ok inner)%bool.
Proof.
  induction inner as [|c rest IH]; [reflexivity|].
  destruct rest as [|c2 rest'].
  - cbn [forallb nonempty]. rewrite andb_true_r. reflexivity.
  - change (cb_ok (CQuote (c :: c2 :: rest')))
      with (cb_ok c && cb_ok (CQuote (c2 :: rest')))%bool.
    rewrite IH. cbn [nonempty forallb]. reflexivity.
Qed.

(*
The renderer
============
*)

(* Recover the lines of a paragraph from its inlines: Str extends the
   current line, SoftBreak ends it.  (Other inline constructors don't
   occur in the fragment; they contribute nothing.) *)

Fixpoint inline_lines (ils : inlines) (cur : string) : list string :=
  match ils with
  | [] => [cur]
  | Node _ _ (Str s) :: rest => inline_lines rest (cur ++ s)
  | Node _ _ SoftBreak :: rest => cur :: inline_lines rest EmptyString
  | _ :: rest => inline_lines rest cur
  end.

(* Render one block to its djot source *lines*.  Line-valued rather than
   string-valued because djot's block structure is line structure: a
   quote's rendering is its contents' lines with a prefix on each, which
   a string-valued renderer could only express by re-splitting.

   Same hand-inlined fixpoint as cb_lines, and for the same reason. *)
Fixpoint render_block_lines (b : block) : list string :=
  let quoted :=
    fix go (ns : list (node block)) : list string :=
      match ns with
      | [] => []
      | [Node _ _ x] => map quote_line (render_block_lines x)
      | Node _ _ x :: rest =>
          (map quote_line (render_block_lines x) ++ quote_open :: go rest)%list
      end in
  match b with
  | Para ils => inline_lines ils EmptyString
  | ThematicBreak => [thematic_line]
  | CodeBlock lang text =>
      (code_open lang :: split_lines text ++ [code_close])%list
  | RawBlock fmt text =>
      (code_open ("=" ++ fmt) :: split_lines text ++ [code_close])%list
  | BlockQuote bs => quoted bs
  | _ => []   (* TODO: extend with the parser, construct by construct *)
  end.

Definition render_blocks_lines (bs : blocks) : list (list string) :=
  map (fun n => render_block_lines (node_contents n)) bs.

Lemma render_block_quote :
  forall bs,
    render_block_lines (BlockQuote bs)
    = map quote_line (sep_lines (render_blocks_lines bs)).
Proof.
  induction bs as [|n rest IH]; [reflexivity|].
  destruct n as [p a x]. destruct rest as [|n2 rest'].
  - reflexivity.
  - change (render_block_lines (BlockQuote (Node p a x :: n2 :: rest')))
      with (map quote_line (render_block_lines x)
            ++ quote_open :: render_block_lines (BlockQuote (n2 :: rest')))%list.
    rewrite IH.
    unfold render_blocks_lines. cbn [map sep_lines].
    rewrite map_app. cbn [map]. rewrite quote_line_empty. reflexivity.
Qed.

(* Blocks separated by a blank line — the separator the parser reads back
   as "end the current block". *)
Definition render_djot (d : doc) : string :=
  String.concat nl (sep_lines (render_blocks_lines (doc_blocks d))).

(* Rendering is now a single join over one flat line list, so the
   roundtrip's split side is just split/join inversion (Strings.v) —
   there is no separate "paragraph layout" notion to invert. *)
