(* The djot AST, transcribed from djoths (src/Djot/AST.hs) with djot.js
   (src/ast.ts) as tie-breaker where they disagree.

   Representation choices:
   - ByteString -> string  (Rocq strings are byte lists; extracted to
     native OCaml strings via ExtrOcamlNativeString)
   - Seq a -> list a
   - Map  -> association list keyed by normalized labels
   - Int  -> nat *)

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

(* CR: what does it mean that it's "extraction-friendly"? Extracting to OCaml? *)

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

(*
Insertion-order update
----------------------

djot.js builds attributes as a JS object and assigns into it, so a key
already present keeps its position and takes the new value, while a new
key lands at the end.  `attr_union` above cannot express that — it
prepends — and attribute *order* is observable in the rendered tag, so
the block-attribute path (Attributes.v, Parser.v) uses these instead. *)

Fixpoint attr_set (k v : string) (a : attr) : attr :=
  match a with
  | [] => [(k, v)]
  | (k', v') :: rest =>
      if String.eqb k k'
      then (k, v) :: rest
      else (k', v') :: attr_set k v rest
  end.

(* Classes accumulate space-separated rather than overwrite, both within
   one attribute spec and across consecutive ones (djot.js parse.ts:536,
   :521). *)
Definition attr_add_class (v : string) (a : attr) : attr :=
  match lookup_attr "class" a with
  | None => attr_set "class" v a
  | Some old => attr_set "class" (old ++ " " ++ v) a
  end.

(* One key/value into a set, with the class rule. *)
Definition attr_put (kv : string * string) (a : attr) : attr :=
  if String.eqb (fst kv) "class"
  then attr_add_class (snd kv) a
  else attr_set (fst kv) (snd kv) a.

(* `-block_attributes` folding a finished spec into the pending set. *)
Definition attr_merge (new acc : attr) : attr :=
  fold_left (fun acc' kv => attr_put kv acc') new acc.

(* `addBlockAttributes` (parse.ts:183): the pending set onto the node a
   block opens with.  Plain assignment — no class rule here, which is
   djot.js's behaviour and not obviously intended. *)
Definition attr_apply (pending a : attr) : attr :=
  fold_left (fun a' kv => attr_set (fst kv) (snd kv) a') pending a.

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

(* Attach pending block attributes to the first of the blocks a container
   produced.  djot.js attaches them when the container *opens*
   (parse.ts:183); here a container is only reified when it closes, so
   the attachment point is the head of what it emitted.  Nothing emitted
   is nothing to attach to. *)
Definition decorate_head (pending : attr) (bs : blocks) : blocks :=
  match bs with
  | [] => []
  | Node p a x :: rest => Node p (attr_apply pending a) x :: rest
  end.

(* Decoration only ever touches the head, so appending after it is the
   same as appending before — provided there is a head. *)
Lemma decorate_head_cons_app :
  forall pending b bs cs,
    (decorate_head pending (b :: bs) ++ cs)%list
    = decorate_head pending ((b :: bs) ++ cs)%list.
Proof. intros pending b bs cs. destruct b. reflexivity. Qed.

(* Rocq's generated `block_ind` does not descend into a container's
   contents: `blocks` is `list (node block)`, two type constructors away
   from `block`, and the guard checker will not follow that.  So every
   proof by induction over the AST needs this two-predicate version —
   P for a block, Q for a block list, each feeding the other.  (Render.v
   carries `cblock_ind2` for the canonical view, for the same reason.)

   The list and table constructors get no induction hypothesis for the
   blocks they hold: their cases must be discharged outright.  Nothing
   produces or traverses them yet, and filling them in is mechanical once
   lists land — a caller that needs those hypotheses finds out at once,
   because the case becomes unprovable. *)
Definition block_ind2
  (P : block -> Prop) (Q : blocks -> Prop)
  (hpara : forall ils, P (Para ils))
  (hsection : forall bs, Q bs -> P (Section bs))
  (hheading : forall lvl ils, P (Heading lvl ils))
  (hquote : forall bs, Q bs -> P (BlockQuote bs))
  (hcode : forall lang code, P (CodeBlock lang code))
  (hdiv : forall bs, Q bs -> P (Div bs))
  (holist : forall attrs sp items, P (OrderedList attrs sp items))
  (hblist : forall sp items, P (BulletList sp items))
  (htlist : forall sp items, P (TaskList sp items))
  (hdlist : forall sp items, P (DefinitionList sp items))
  (hthematic : P ThematicBreak)
  (htable : forall caption rows, P (Table caption rows))
  (hraw : forall format contents, P (RawBlock format contents))
  (hnil : Q [])
  (hcons : forall p a x rest, P x -> Q rest -> Q (Node p a x :: rest))
  : forall b, P b :=
  fix go (b : block) : P b :=
    let golist :=
      fix golist (ns : blocks) : Q ns :=
        match ns with
        | [] => hnil
        | Node p a x :: rest => hcons p a x rest (go x) (golist rest)
        end in
    match b with
    | Para ils => hpara ils
    | Section bs => hsection bs (golist bs)
    | Heading lvl ils => hheading lvl ils
    | BlockQuote bs => hquote bs (golist bs)
    | CodeBlock lang code => hcode lang code
    | Div bs => hdiv bs (golist bs)
    | OrderedList attrs sp items => holist attrs sp items
    | BulletList sp items => hblist sp items
    | TaskList sp items => htlist sp items
    | DefinitionList sp items => hdlist sp items
    | ThematicBreak => hthematic
    | Table caption rows => htable caption rows
    | RawBlock format contents => hraw format contents
    end.

(*
Documents
=========
*)

(* Splitting a string into `sep`-free tokens, empty ones dropped.  Both
   djot string-to-key derivations are an instance: collapse runs of a
   character class, drop them at the ends, join what is left with a fixed
   separator.  Labels use whitespace (below); auto-identifiers use a wider
   class (Document.is_id_sep). *)

Fixpoint words_aux (sep : ascii -> bool) (s : string) (cur : string)
  (acc : list string) : list string :=
  match s with
  | EmptyString =>
      match cur with EmptyString => acc | _ => cur :: acc end
  | String c s' =>
      if sep c
      then match cur with
           | EmptyString => words_aux sep s' EmptyString acc
           | _ => words_aux sep s' EmptyString (cur :: acc)
           end
      else words_aux sep s' (cur ++ String c EmptyString) acc
  end.

(* Tokens in source order.  The accumulator above builds them reversed. *)
Definition words (sep : ascii -> bool) (s : string) : list string :=
  rev (words_aux sep s EmptyString []).

(* Labels are normalized by collapsing runs of whitespace to single
   spaces and trimming (djoths normalizeLabel). *)

Definition is_label_ws (c : ascii) : bool :=
  (Ascii.eqb c " " || Ascii.eqb c "009" || Ascii.eqb c "013"
   || Ascii.eqb c "010")%char%bool.

Definition normalize_label (s : string) : string :=
  String.concat " " (words is_label_ws s).

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
