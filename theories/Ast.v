(* The djot AST, transcribed from djoths (src/Djot/AST.hs) with djot.js
   (src/ast.ts) as tie-breaker where they disagree.

   Representation choices:
   - ByteString -> string  (Rocq strings are byte lists; extracted to
     native OCaml strings via ExtrOcamlNativeString)
   - Seq a -> list a
   - Map  -> association list keyed by normalized labels
   - Int  -> nat

   Well-formedness will be layered on top as an inductive family (wf_block)
   rather than baked into these types; see the Phase 1 plan. *)

From Stdlib Require Import String Ascii List Bool.
Import ListNotations.

Local Open Scope string_scope.

(*
Attributes and positions
========================
*)

(* Attributes are key/value pairs in source order (djoths uses a Map;
   an alist keeps the representation extraction-friendly). *)
Definition attr : Type := list (string * string).

Fixpoint lookup_attr (k : string) (a : attr) : option string :=
  match a with
  | [] => None
  | (k', v) :: rest => if String.eqb k k' then Some v else lookup_attr k rest
  end.

(* djoths's `integrate`: later-inserted keys win, except "class", whose
   values concatenate (space-separated, left operand's classes first). *)

Definition integrate (kv : string * string) (kvs : attr) : attr :=
  let (k, v) := kv in
  match lookup_attr k kvs with
  | None => (k, v) :: kvs
  | Some v' =>
      if String.eqb k "class"
      then (k, v ++ " " ++ v')
           :: filter (fun p => negb (String.eqb (fst p) "class")) kvs
      else kvs
  end.

(* Merge two attribute sets, integrating a's bindings into b one by one. *)
Definition attr_union (a b : attr) : attr := fold_right integrate b a.

(* Source positions: start line/col, end line/col.  Carried for fidelity
   with the oracles; the harness skips sourcepos cases, so nothing renders
   these yet. *)

Inductive pos : Type :=
  | NoPos
  | SomePos (sl sc el ec : nat).

(* Every AST element is wrapped in a node carrying its position and
   attributes; `inline` and `block` below are the payloads. *)
Inductive node (A : Type) : Type :=
  | Node (p : pos) (a : attr) (x : A).

Arguments Node {A} p a x.

(* The bare node: no position, no attributes.  Everything the parser
   currently builds is `mk`-wrapped, so proofs can compute through it. *)
Definition mk {A : Type} (x : A) : node A := Node NoPos [] x.

Definition node_contents {A : Type} (n : node A) : A :=
  match n with Node _ _ x => x end.

Definition add_attr {A : Type} (a : attr) (n : node A) : node A :=
  match n with Node p a' x => Node p (attr_union a' a) x end.

(*
Inline elements
===============
*)

Inductive math_style : Type := DisplayMath | InlineMath.

(* A link/image target: an inline URL, or a label resolved against the
   document's reference_map. *)
Inductive target : Type :=
  | Direct (url : string)
  | Reference (label : string).

Inductive quote_type : Type := SingleQuotes | DoubleQuotes.

(* Inline content.  Only Str and SoftBreak are produced so far — the
   parser has no inline pass yet; paragraphs become one Str per source
   line, separated by SoftBreak (see Parser.para_inlines). *)
Inductive inline : Type :=
  | Str (s : string)
  | Emph (ils : list (node inline))
  | Strong (ils : list (node inline))
  | Highlight (ils : list (node inline))
  | Insert (ils : list (node inline))
  | Delete (ils : list (node inline))
  | Superscript (ils : list (node inline))
  | Subscript (ils : list (node inline))
  | Verbatim (s : string)
  | Symbol (s : string)
  | Math (style : math_style) (s : string)
  | Link (ils : list (node inline)) (tgt : target)
  | Image (ils : list (node inline)) (tgt : target)
  | Span (ils : list (node inline))
  | FootnoteReference (label : string)
  | UrlLink (url : string)
  | EmailLink (email : string)
  | RawInline (format : string) (s : string)
  | NonBreakingSpace
  | Quoted (qt : quote_type) (ils : list (node inline))
  | SoftBreak
  | HardBreak.

Definition inlines : Type := list (node inline).

(*
Block elements
==============
*)

(* Tight lists render item contents inline; loose ones wrap in paragraphs. *)
Inductive list_spacing : Type := Tight | Loose.

Inductive ordered_list_style : Type :=
  | Decimal | LetterUpper | LetterLower | RomanUpper | RomanLower.

Inductive ordered_list_delim : Type :=
  | RightPeriod | RightParen | LeftRightParen.

Record ordered_list_attributes : Type := OLAttrs
  { ol_style : ordered_list_style
  ; ol_delim : ordered_list_delim
  ; ol_start : nat }.

Inductive task_status : Type := Complete | Incomplete.

Inductive align : Type := AlignLeft | AlignRight | AlignCenter | AlignDefault.

Inductive cell_type : Type := HeadCell | BodyCell.

Inductive cell : Type :=
  | Cell (ct : cell_type) (al : align) (ils : inlines).

(* Block content.  Produced so far: Para, ThematicBreak, CodeBlock,
   RawBlock (see Parser.parse_lines); the rest are transcribed from the
   oracles ahead of the parser reaching them. *)
Inductive block : Type :=
  | Para (ils : inlines)
  | Section (bs : list (node block))
  | Heading (level : nat) (ils : inlines)
  | BlockQuote (bs : list (node block))
  | CodeBlock (lang : string) (code : string)
  | Div (bs : list (node block))
  | OrderedList (attrs : ordered_list_attributes) (sp : list_spacing)
      (items : list (list (node block)))
  | BulletList (sp : list_spacing) (items : list (list (node block)))
  | TaskList (sp : list_spacing)
      (items : list (task_status * list (node block)))
  | DefinitionList (sp : list_spacing)
      (items : list (inlines * list (node block)))
  | ThematicBreak
  | Table (caption : option (list (node block))) (rows : list (list cell))
  | RawBlock (format : string) (contents : string).

Definition blocks : Type := list (node block).

(*
Documents
=========
*)

(* Labels are normalized by collapsing runs of whitespace to single
   spaces and trimming (djoths normalizeLabel). *)

Definition is_label_ws (c : ascii) : bool :=
  (Ascii.eqb c " " || Ascii.eqb c "009" || Ascii.eqb c "013"
   || Ascii.eqb c "010")%char%bool.

Fixpoint words_aux (s : string) (cur : string) (acc : list string)
  : list string :=
  match s with
  | EmptyString =>
      match cur with EmptyString => acc | _ => cur :: acc end
  | String c s' =>
      if is_label_ws c
      then match cur with
           | EmptyString => words_aux s' EmptyString acc
           | _ => words_aux s' EmptyString (cur :: acc)
           end
      else words_aux s' (cur ++ String c EmptyString) acc
  end.

Definition normalize_label (s : string) : string :=
  String.concat " " (rev (words_aux s EmptyString [])).

(* Footnote bodies and link references, keyed by normalized label.  Look
   them up through lookup_note / lookup_reference, which normalize the
   key first — never with alist_lookup directly. *)
Definition note_map : Type := list (string * blocks).
Definition reference_map : Type := list (string * (string * attr)).

Fixpoint alist_lookup {A : Type} (k : string) (m : list (string * A))
  : option A :=
  match m with
  | [] => None
  | (k', v) :: rest =>
      if String.eqb k k' then Some v else alist_lookup k rest
  end.

Definition lookup_note (label : string) (m : note_map) : option blocks :=
  alist_lookup (normalize_label label) m.

Definition lookup_reference (label : string) (m : reference_map)
  : option (string * attr) :=
  alist_lookup (normalize_label label) m.

(* A whole document: the block tree plus the side tables the inline pass
   will resolve against (auto_* are the ones djot derives from headings). *)
Record doc : Type := Doc
  { doc_blocks : blocks
  ; doc_footnotes : note_map
  ; doc_references : reference_map
  ; doc_auto_references : reference_map
  ; doc_auto_identifiers : list string }.

Definition empty_doc : doc := Doc [] [] [] [] [].
