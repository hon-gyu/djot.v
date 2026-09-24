(* ai-disclosure: autonomous *)

(** * Abstract syntax tree

   The Djot AST, transcribed from djoths (src/Djot/AST.hs).  Where djoths
   and djot.js (src/ast.ts) disagree, djot.js, the reference
   implementation, decides.

   Representation choices:
   - ByteString -> string  (extracted to native OCaml strings)
   - Seq a -> list a
   - Map  -> association list keyed by normalized labels
   - Int  -> nat

   Every node carries attributes and a source position.  [Render] defines
   the canonical subset on which rendering to source is invertible. *)

From Stdlib Require Import String Ascii List Bool.
Import ListNotations.

Local Open Scope string_scope.

(*
Attributes
==========

Association lists
-----------------

Attribute sets and the document's reference map are both string-keyed
alists.  Look-ups take the first match.  `alist_set` assigns the way a JS
object does: a key already present keeps its position and takes the new
value, and a new key goes at the end.
*)

Fixpoint alist_lookup {A : Type} (k : string) (m : list (string * A))
  : option A :=
  match m with
  | [] => None
  | (k', v) :: rest =>
      if String.eqb k k' then Some v else alist_lookup k rest
  end.

Fixpoint alist_set {A : Type} (k : string) (v : A) (m : list (string * A))
  : list (string * A) :=
  match m with
  | [] => [(k, v)]
  | (k', v') :: rest =>
      if String.eqb k k'
      then (k, v) :: rest
      else (k', v') :: alist_set k v rest
  end.

(* Setting never empties a map. *)
Local Lemma alist_set_cons :
  forall A k (v : A) m, exists x r, alist_set k v m = (x :: r)%list.
Proof.
  intros A k v [|[k' v'] m]; cbn [alist_set]; [eauto|].
  destruct (String.eqb k k'); eauto.
Qed.

(* Key/value pairs in source order.  An alist rather than a `Map`, so
   that it extracts to a plain OCaml list. *)
Definition attr : Type := list (string * string).

Module Attr.

(*
Merging by union
----------------
*)

(* Integrate one binding into a set.  A key already present keeps its
   value, except "class", whose values concatenate with the new one
   first. *)
Local Definition integrate (kv : string * string) (kvs : attr) : attr :=
  let (k, v) := kv in
  match alist_lookup k kvs with
  | None => (k, v) :: kvs
  | Some v' =>
      if String.eqb k "class"
      then (k, v ++ " " ++ v')
           :: filter (fun p => negb (String.eqb (fst p) "class")) kvs
      else kvs
  end.

(* Merge [a] into [b].  For a repeated key the rightmost binding wins, and
   classes concatenate left to right.  New keys are prepended. *)
Local Definition union (a b : attr) : attr := fold_right integrate b a.

(*
Merging by assignment
---------------------

Assignment keeps attribute order the way djot.js does, and order is
observable in a rendered tag, so block attributes use these rather than
`union`.
*)

Definition set (k v : string) (a : attr) : attr := alist_set k v a.

(* Classes accumulate, space-separated, within one attribute spec and
   across consecutive ones. *)
Definition add_class (v : string) (a : attr) : attr :=
  match alist_lookup "class" a with
  | None => set "class" v a
  | Some old => set "class" (old ++ " " ++ v) a
  end.

(* One binding into a set, with the class rule. *)
Local Definition put (kv : string * string) (a : attr) : attr :=
  if String.eqb (fst kv) "class"
  then add_class (snd kv) a
  else set (fst kv) (snd kv) a.

(* Fold a finished attribute spec into the pending set. *)
Definition merge (new acc : attr) : attr :=
  fold_left (fun acc' kv => put kv acc') new acc.

(* A one-binding spec merged into nothing is that binding. *)
Lemma merge_one : forall kv, merge [kv] [] = [kv].
Proof.
  intros [k v]. unfold merge, put, add_class, set.
  cbn [fold_left fst snd].
  destruct (String.eqb k "class") eqn:E;
    [apply String.eqb_eq in E; subst k|];
    cbn [alist_lookup alist_set]; reflexivity.
Qed.

(* Merging never empties a set. *)
Local Lemma put_cons :
  forall kv a, exists x r, put kv a = (x :: r)%list.
Proof.
  intros kv a. unfold put, add_class, set.
  destruct (String.eqb (fst kv) "class"); [|apply alist_set_cons].
  destruct (alist_lookup "class" a); apply alist_set_cons.
Qed.

Lemma merge_cons :
  forall a kv acc, exists x r, merge a (kv :: acc)%list = (x :: r)%list.
Proof.
  induction a as [|y a IH]; intros kv acc; [exists kv, acc; reflexivity|].
  unfold merge in *; cbn [fold_left].
  destruct (put y (kv :: acc)%list) as [|z r] eqn:E;
    [destruct (put_cons y (kv :: acc)%list) as [? [? E']];
     rewrite E' in E; discriminate|].
  apply IH.
Qed.

(* The pending set onto the attributes of the block it decorates.  Plain
   assignment: classes do not accumulate here, as in djot.js. *)
Local Definition apply_pending (pending a : attr) : attr :=
  fold_left (fun a' kv => set (fst kv) (snd kv) a') pending a.

End Attr.

(*
Positions
=========
*)

(* A point in the source.  [spot_rem] counts bytes from the point to the
   end of its line, excluding the terminator.  Counting from the right
   means that removing a container prefix from a line does not move a
   point in the part that remains. *)
Record spot : Type := Spot
  { spot_line : nat
  ; spot_rem : nat }.

(* Source ranges are half-open. *)
Record span : Type := SrcSpan
  { span_start : spot
  ; span_stop : spot }.

(* The byte the inline scanner is dispatching.  An observation only: the
   semantic driver uses the inert instance below, and the located driver
   supplies the two ends of each byte. *)
Class InlineCursor : Type := CursorAt
  { cursor_start : spot
  ; cursor_stop : spot
  ; cursor_origin : spot }.

#[export] Instance semantic_inline_cursor : InlineCursor :=
  CursorAt (Spot 0 0) (Spot 0 0) (Spot 0 0).

(* Authored syntax that belongs to a node without widening its range.
   The fence roles also tell an unterminated fence from a closed one. *)
Inductive syntax_role : Type :=
  | RAttrSpec
  | ROpenFence
  | RCloseFence.

(* Ranges of the source-bearing parts of the AST that are not nodes (list
   items, definition items, table rows and cells), parallel to the
   parent's children. *)
Inductive parts : Type :=
  | PNone
  | PItems (items : list span)
  | PDefItems (items : list (span * span * span))
  | PTable (caption : option span) (rows : list (span * list span)).

Record provenance : Type := Provenance
  { node_span : span
  ; syntax_spans : list (syntax_role * span)
  ; part_spans : parts }.

Inductive pos : Type :=
  | NoPos
  | SomePos (p : provenance).

(* Every AST element is wrapped in a node carrying its position and
   attributes; `inline` and `block` below are the payloads. *)
Inductive node (A : Type) : Type :=
  | Node (p : pos) (a : attr) (x : A).

Arguments Node {A} p a x.

Definition node_provenance {A : Type} (n : node A) : option provenance :=
  match n with
  | Node NoPos _ _ => None
  | Node (SomePos p) _ _ => Some p
  end.

(* The bare node: no position, no attributes. *)
Definition mk {A : Type} (x : A) : node A := Node NoPos [] x.

Definition node_contents {A : Type} (n : node A) : A :=
  match n with Node _ _ x => x end.

Definition node_attrs {A : Type} (n : node A) : attr :=
  match n with Node _ a _ => a end.

Definition add_attr {A : Type} (a : attr) (n : node A) : node A :=
  match n with Node p a' x => Node p (Attr.union a' a) x end.

Lemma add_attr_mk :
  forall A (a : attr) (x : A), add_attr a (mk x) = Node NoPos a x.
Proof. reflexivity. Qed.

(* How a parse tags the nodes it builds.  The parser is written once
   against this class, and the instance decides whether provenance reaches
   the AST: `semantic_pos` records nothing, `located_pos` records it.
   Throughout the development, "semantic" means the position-free reading.
   A file that opens no policy context resolves to `semantic_pos`, where
   `posnode p x` is `mk x` by conversion.

   `pos_records` asks the same question without a provenance in hand, so
   a pass that reads a node's existing provenance can test the policy
   first and stay the identity at the semantic instance.  `pos_off` ties
   the two answers together. *)
Class PosPolicy : Type := PosOf
  { mkpos : provenance -> pos
  ; pos_records : bool
  ; pos_off : pos_records = false -> forall p, mkpos p = NoPos }.

#[export] Instance semantic_pos : PosPolicy :=
  PosOf (fun _ => NoPos) false (fun _ _ => eq_refl).

Definition located_pos : PosPolicy :=
  PosOf SomePos true (fun H => ltac:(discriminate H)).

(* The constructor the parser builds nodes with.  Attributes are attached
   afterwards. *)
Definition posnode `{PosPolicy} {A : Type} (p : provenance) (x : A) : node A :=
  Node (mkpos p) [] x.

(* A span stored in a scanner's own state rather than on a node.  Under a
   policy that records nothing it is `null_span`, so such a state holds no
   coordinates and erasing it is the identity. *)
Definition null_span : span := SrcSpan (Spot 0 0) (Spot 0 0).

Definition pspan `{PosPolicy} (r : span) : span :=
  if pos_records then r else null_span.

Local Lemma pspan_semantic : forall r, @pspan semantic_pos r = null_span.
Proof. reflexivity. Qed.

(* Provenance that is just a range. *)
Definition prov_at (r : span) : provenance := Provenance r [] PNone.

(* A range with the authored syntax that belongs to it: a fence's own
   lines, an attribute spec. *)
Definition prov_with (r : span) (rs : list (syntax_role * span))
  : provenance := Provenance r rs PNone.

(* Attribute specs, in source order, as the roles they become. *)
Definition attr_roles (specs : list span) : list (syntax_role * span) :=
  map (fun r => (RAttrSpec, r)) specs.

(* Provenance onto a node already built, keeping its attributes.  Blocks
   are built by helpers that know their shape and not their source, so
   provenance is attached where the source is known: at the state that
   closes.  Tests the policy before the node, so under a policy that
   records nothing it is the identity by conversion on any node. *)
Definition set_pos `{PosPolicy} {A : Type} (p : provenance) (n : node A)
  : node A :=
  match mkpos p with
  | NoPos => n
  | q => match n with Node _ a x => Node q a x end
  end.

Local Lemma set_pos_mk :
  forall `{PosPolicy} A (p : provenance) (x : A),
    set_pos p (mk x) = posnode p x.
Proof.
  intros. unfold set_pos, posnode, mk. destruct (mkpos p); reflexivity.
Qed.

(* Provenance onto the head of what a container emitted, which is the
   block the container is. *)
Definition pos_head `{PosPolicy} {A : Type} (p : provenance)
  (ns : list (node A)) : list (node A) :=
  match mkpos p with
  | NoPos => ns
  | _ => match ns with
         | [] => []
         | n :: rest => (set_pos p n :: rest)%list
         end
  end.

(* Authored syntax onto a node built earlier: an attribute spec settles
   before the block it decorates is emitted, and a fence's lines arrive
   one at a time.  Tests the policy first, so it is the identity by
   conversion when nothing is recorded. *)
Definition add_roles `{PosPolicy} {A : Type}
  (rs : list (syntax_role * span)) (n : node A) : node A :=
  if pos_records then
    match n with
    | Node (SomePos p) a x =>
        Node (SomePos (Provenance (node_span p)
                         (syntax_spans p ++ rs)%list (part_spans p))) a x
    | _ => n
    end
  else n.

Definition add_roles_head `{PosPolicy} {A : Type}
  (rs : list (syntax_role * span)) (ns : list (node A)) : list (node A) :=
  if pos_records then
    match ns with
    | [] => []
    | n :: rest => (add_roles rs n :: rest)%list
    end
  else ns.

Local Lemma add_roles_off :
  forall `{PosPolicy} A rs (n : node A),
    pos_records = false -> add_roles rs n = n.
Proof. intros. unfold add_roles. rewrite H0. reflexivity. Qed.

Local Lemma add_roles_head_off :
  forall `{PosPolicy} A rs (ns : list (node A)),
    pos_records = false -> add_roles_head rs ns = ns.
Proof. intros. unfold add_roles_head. rewrite H0. reflexivity. Qed.

(* The range from the first node's start to the last node's stop: the
   range of a `Section` the document pass builds from a heading and the
   blocks under it. *)
Local Definition hull_pos `{PosPolicy} {A : Type} (ns : list (node A)) : pos :=
  if pos_records then
    match ns with
    | [] => NoPos
    | first :: _ =>
        match node_provenance first, node_provenance (List.last ns first) with
        | Some p, Some q =>
            SomePos (prov_at (SrcSpan (span_start (node_span p))
                                      (span_stop (node_span q))))
        | _, _ => NoPos
        end
    end
  else NoPos.

(* The same, keeping the first node's authored syntax: a heading's id
   moves onto the section it opens, and the spec that authored it moves
   with it. *)
Definition hull_pos_with `{PosPolicy} {A : Type} (ns : list (node A)) : pos :=
  match hull_pos ns with
  | NoPos => NoPos
  | SomePos p =>
      match ns with
      | [] => SomePos p
      | first :: _ =>
          match node_provenance first with
          | Some q => SomePos (Provenance (node_span p) (syntax_spans q)
                                 (part_spans p))
          | None => SomePos p
          end
      end
  end.

Local Lemma hull_pos_with_semantic :
  forall A (ns : list (node A)), @hull_pos_with semantic_pos A ns = NoPos.
Proof. reflexivity. Qed.

Local Lemma hull_pos_off :
  forall `{PosPolicy} A (ns : list (node A)),
    pos_records = false -> hull_pos ns = NoPos.
Proof. intros. unfold hull_pos. rewrite H0. reflexivity. Qed.

(* At the semantic instance the wrappers are the identity. *)
Local Lemma hull_pos_semantic :
  forall A (ns : list (node A)), @hull_pos semantic_pos A ns = NoPos.
Proof. reflexivity. Qed.

Local Lemma add_roles_semantic :
  forall A rs (n : node A), @add_roles semantic_pos A rs n = n.
Proof. reflexivity. Qed.

Local Lemma add_roles_head_semantic :
  forall A rs (ns : list (node A)), @add_roles_head semantic_pos A rs ns = ns.
Proof. reflexivity. Qed.

Local Lemma pos_head_semantic :
  forall A (p : provenance) (ns : list (node A)),
    @pos_head semantic_pos A p ns = ns.
Proof. reflexivity. Qed.

Local Lemma set_pos_semantic :
  forall A (p : provenance) (n : node A), @set_pos semantic_pos A p n = n.
Proof. reflexivity. Qed.

(* Removes the wrappers at the semantic instance.  They reduce away by
   conversion, but `rewrite` is syntactic. *)
Ltac nopos :=
  rewrite ?set_pos_semantic, ?pos_head_semantic, ?add_roles_semantic,
    ?add_roles_head_semantic, ?hull_pos_semantic, ?hull_pos_with_semantic.

Local Lemma set_pos_located :
  forall A (p : provenance) (q : pos) (a : attr) (x : A),
    @set_pos located_pos A p (Node q a x) = Node (SomePos p) a x.
Proof. reflexivity. Qed.

Local Lemma posnode_semantic :
  forall A (p : provenance) (x : A), @posnode semantic_pos A p x = mk x.
Proof. reflexivity. Qed.

Local Lemma posnode_located :
  forall A (p : provenance) (x : A),
    @posnode located_pos A p x = Node (SomePos p) [] x.
Proof. reflexivity. Qed.

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

(* Inline content.  `InlineScan.para_inlines` produces it one paragraph at a
   time, with the source lines joined by SoftBreak.  A symbol is a node
   rather than text: its default HTML is the literal `:name:`, which HTML
   alone cannot tell apart from text. *)
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
  (* Extension, not djot (`.project/wikilinks.md`): `[[target|alias]]`,
     and `![[...]]` with `embed` set.  Both halves are source as written;
     what a target denotes is the consumer's. *)
  | Wikilink (embed : bool) (target : string) (alias : option string)
  | RawInline (format : string) (s : string)
  | NonBreakingSpace
  | Quoted (qt : quote_type) (ils : list (node inline))
  | SoftBreak
  | HardBreak.

Definition inlines : Type := list (node inline).

(* Induction over inlines that reaches into containers.  The generated
   principle stops at `list (node inline)`. *)
Definition inline_ind2
  (P : inline -> Prop) (Q : inlines -> Prop)
  (hstr : forall s, P (Str s))
  (hemph : forall ils, Q ils -> P (Emph ils))
  (hstrong : forall ils, Q ils -> P (Strong ils))
  (hhigh : forall ils, Q ils -> P (Highlight ils))
  (hins : forall ils, Q ils -> P (Insert ils))
  (hdel : forall ils, Q ils -> P (Delete ils))
  (hsup : forall ils, Q ils -> P (Superscript ils))
  (hsub : forall ils, Q ils -> P (Subscript ils))
  (hverb : forall s, P (Verbatim s))
  (hsym : forall s, P (Symbol s))
  (hmath : forall st s, P (Math st s))
  (hlink : forall ils tgt, Q ils -> P (Link ils tgt))
  (himage : forall ils tgt, Q ils -> P (Image ils tgt))
  (hspan : forall ils, Q ils -> P (Span ils))
  (hfoot : forall label, P (FootnoteReference label))
  (hurl : forall url, P (UrlLink url))
  (hmail : forall email, P (EmailLink email))
  (hwiki : forall embed target alias, P (Wikilink embed target alias))
  (hraw : forall format s, P (RawInline format s))
  (hnbsp : P NonBreakingSpace)
  (hquoted : forall qt ils, Q ils -> P (Quoted qt ils))
  (hsoft : P SoftBreak)
  (hhard : P HardBreak)
  (hnil : Q [])
  (hcons : forall p a x rest, P x -> Q rest -> Q (Node p a x :: rest))
  : forall i, P i :=
  fix go (i : inline) : P i :=
    let golist :=
      fix golist (ns : inlines) : Q ns :=
        match ns with
        | [] => hnil
        | Node p a x :: rest => hcons p a x rest (go x) (golist rest)
        end in
    match i with
    | Str s => hstr s
    | Emph ils => hemph ils (golist ils)
    | Strong ils => hstrong ils (golist ils)
    | Highlight ils => hhigh ils (golist ils)
    | Insert ils => hins ils (golist ils)
    | Delete ils => hdel ils (golist ils)
    | Superscript ils => hsup ils (golist ils)
    | Subscript ils => hsub ils (golist ils)
    | Verbatim s => hverb s
    | Symbol s => hsym s
    | Math st s => hmath st s
    | Link ils tgt => hlink ils tgt (golist ils)
    | Image ils tgt => himage ils tgt (golist ils)
    | Span ils => hspan ils (golist ils)
    | FootnoteReference label => hfoot label
    | UrlLink url => hurl url
    | EmailLink email => hmail email
    | Wikilink embed target alias => hwiki embed target alias
    | RawInline format s => hraw format s
    | NonBreakingSpace => hnbsp
    | Quoted qt ils => hquoted qt ils (golist ils)
    | SoftBreak => hsoft
    | HardBreak => hhard
    end.

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

Definition align_eqb (a b : align) : bool :=
  match a, b with
  | AlignLeft, AlignLeft | AlignRight, AlignRight
  | AlignCenter, AlignCenter | AlignDefault, AlignDefault => true
  | _, _ => false
  end.

Lemma align_eqb_eq : forall a b, align_eqb a b = true -> a = b.
Proof. intros [] []; (reflexivity || discriminate). Qed.

Inductive cell : Type :=
  | Cell (ct : cell_type) (al : align) (ils : inlines).

(* Block content.  `Section` is built by the document pass
   (`Document.sectionize`); every other constructor by the block
   parser. *)
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
  (* A caption is inline content, as djot.js parses it (djoths has
     blocks).  Keeping it inline also keeps `Table` a leaf for
     `block_ind2`. *)
  | Table (caption : option inlines) (rows : list (list cell))
  | RawBlock (format : string) (contents : string)
  (* The source form of a footnote definition.  The document pass moves
     its children into `doc_footnotes`; the block stays so that the source
     has an image in the roundtrip. *)
  | FootnoteDef (label : string) (children : list (node block))
  (* A link-reference definition.  A block that renders to no HTML, so
     that the source line has an image in the roundtrip;
     `Document.doc_pass` derives the reference map from it. *)
  | RefDef (label : string) (dest : string)
  (* Extension, not djot (`.project/keyed-blocks.md`): a label and the one
     block it names.  A single block rather than a list, so the one-block
     scope is forced by the type.  The label is inlines because the
     parser builds it with `para_inlines`; that it is one element is the
     canonical view's condition. *)
  | Keyed (label : inlines) (b : node block).

Definition blocks : Type := list (node block).

(* Induction over blocks that reaches into containers.  The generated
   `block_ind` stops at `list (node block)`, so this takes one predicate
   per nesting shape: P for a block, Q for a block list, R for list items,
   D for definition items, K for task items.  `Table` holds only inlines
   and is a leaf. *)
Definition block_ind2
  (P : block -> Prop) (Q : blocks -> Prop) (R : list blocks -> Prop)
  (D : list (inlines * blocks) -> Prop)
  (K : list (task_status * blocks) -> Prop)
  (hpara : forall ils, P (Para ils))
  (hsection : forall bs, Q bs -> P (Section bs))
  (hheading : forall lvl ils, P (Heading lvl ils))
  (hquote : forall bs, Q bs -> P (BlockQuote bs))
  (hcode : forall lang code, P (CodeBlock lang code))
  (hdiv : forall bs, Q bs -> P (Div bs))
  (holist : forall attrs sp items, R items -> P (OrderedList attrs sp items))
  (hblist : forall sp items, R items -> P (BulletList sp items))
  (htlist : forall sp items, K items -> P (TaskList sp items))
  (hdlist : forall sp items, D items -> P (DefinitionList sp items))
  (hthematic : P ThematicBreak)
  (htable : forall caption rows, P (Table caption rows))
  (hraw : forall format contents, P (RawBlock format contents))
  (hfoot : forall label bs, Q bs -> P (FootnoteDef label bs))
  (hrefdef : forall label dest, P (RefDef label dest))
  (* Its one block reaches the caller as a singleton list, so a key needs
     no hypothesis of its own. *)
  (hkeyed : forall label b, Q [b] -> P (Keyed label b))
  (hnil : Q [])
  (hcons : forall p a x rest, P x -> Q rest -> Q (Node p a x :: rest))
  (hinil : R [])
  (hicons : forall it rest, Q it -> R rest -> R (it :: rest))
  (hdnil : D [])
  (hdcons : forall term it rest, Q it -> D rest -> D ((term, it) :: rest))
  (hknil : K [])
  (hkcons : forall chk it rest, Q it -> K rest -> K ((chk, it) :: rest))
  : forall b, P b :=
  fix go (b : block) : P b :=
    let golist :=
      fix golist (ns : blocks) : Q ns :=
        match ns with
        | [] => hnil
        | Node p a x :: rest => hcons p a x rest (go x) (golist rest)
        end in
    let goitems :=
      fix goitems (its : list blocks) : R its :=
        match its with
        | [] => hinil
        | it :: rest => hicons it rest (golist it) (goitems rest)
        end in
    let gotasks :=
      fix gotasks (its : list (task_status * blocks)) : K its :=
        match its with
        | [] => hknil
        | (chk, it) :: rest =>
            hkcons chk it rest (golist it) (gotasks rest)
        end in
    let godefs :=
      fix godefs (its : list (inlines * blocks)) : D its :=
        match its with
        | [] => hdnil
        | (term, it) :: rest =>
            hdcons term it rest (golist it) (godefs rest)
        end in
    match b with
    | Para ils => hpara ils
    | Section bs => hsection bs (golist bs)
    | Heading lvl ils => hheading lvl ils
    | BlockQuote bs => hquote bs (golist bs)
    | CodeBlock lang code => hcode lang code
    | Div bs => hdiv bs (golist bs)
    | OrderedList attrs sp items => holist attrs sp items (goitems items)
    | BulletList sp items => hblist sp items (goitems items)
    | TaskList sp items => htlist sp items (gotasks items)
    | DefinitionList sp items => hdlist sp items (godefs items)
    | ThematicBreak => hthematic
    | Table caption rows => htable caption rows
    | RawBlock format contents => hraw format contents
    | FootnoteDef label bs => hfoot label bs (golist bs)
    | RefDef label dest => hrefdef label dest
    | Keyed label b => hkeyed label b (golist [b])
    end.

(*
Assembling blocks
-----------------
*)

(* Pending block attributes onto the first block a container emitted.  A
   container is built only when it closes, so the head of its output is
   the block it opened with.  Nothing emitted is nothing to attach to. *)
Definition decorate_head (pending : attr) (bs : blocks) : blocks :=
  match bs with
  | [] => []
  | Node p a x :: rest => Node p (Attr.apply_pending pending a) x :: rest
  end.

(* Decoration touches only the head, so on a nonempty list it commutes
   with appending. *)
Lemma decorate_head_cons_app :
  forall pending b bs cs,
    (decorate_head pending (b :: bs) ++ cs)%list
    = decorate_head pending ((b :: bs) ++ cs)%list.
Proof. intros pending b bs cs. destruct b. reflexivity. Qed.

(* Blocks the term search in `def_split` steps over: a reference or
   footnote definition contributes no content to an item, so it is never
   the term. *)
Definition invisible_block (b : block) : bool :=
  match b with RefDef _ _ | FootnoteDef _ _ => true | _ => false end.

(* Split a definition item into term and body, when the item closes.  If
   its first visible block is a paragraph, the paragraph's inlines are the
   term and the paragraph is dropped, attributes included, since a term
   has nowhere to put them.  Otherwise there is no split and the item
   keeps everything. *)
Fixpoint def_split (bs : blocks) : option (inlines * blocks) :=
  match bs with
  | [] => None
  | Node q a x :: rest =>
      match x with
      | Para ils => Some (ils, rest)
      | _ =>
          if invisible_block x
          then match def_split rest with
               | Some (ils, more) => Some (ils, Node q a x :: more)
               | None => None
               end
          else None
      end
  end.

Definition def_item (bs : blocks) : inlines * blocks :=
  match def_split bs with
  | Some r => r
  | None => ([], bs)
  end.

Lemma def_item_some :
  forall bs r, def_split bs = Some r -> def_item bs = r.
Proof. intros bs r H. unfold def_item. rewrite H. reflexivity. Qed.

Lemma def_item_none :
  forall bs, def_split bs = None -> def_item bs = ([], bs).
Proof. intros bs H. unfold def_item. rewrite H. reflexivity. Qed.

Definition def_items (its : list blocks) : list (inlines * blocks) :=
  map def_item its.

(* Pair a task list's statuses with its items.  Recursion is on the items,
   so a short status list pads with `Incomplete` rather than dropping
   items as `combine` would.  The parser keeps the two the same length
   (`Step.list_next`). *)
Fixpoint task_items (chks : list task_status) (its : list blocks)
  : list (task_status * blocks) :=
  match its with
  | [] => []
  | it :: rest =>
      match chks with
      | [] => (Incomplete, it) :: task_items [] rest
      | c :: cs => (c, it) :: task_items cs rest
      end
  end.

Module Erase.

(*
Erasure
=======

Forget provenance throughout a tree, keeping attributes and payloads: the
located parse agrees with the semantic one up to erasure.  Erasure is deep
where the located parse records positions.  A keyed block's label is not
erased, since the located parse records none in it.
*)

Fixpoint of_inline (i : inline) : inline :=
  let go :=
    fix go (ils : inlines) : inlines :=
      match ils with
      | [] => []
      | Node _ a x :: rest => Node NoPos a (of_inline x) :: go rest
      end in
  match i with
  | Emph ils => Emph (go ils)
  | Strong ils => Strong (go ils)
  | Highlight ils => Highlight (go ils)
  | Insert ils => Insert (go ils)
  | Delete ils => Delete (go ils)
  | Superscript ils => Superscript (go ils)
  | Subscript ils => Subscript (go ils)
  | Link ils tgt => Link (go ils) tgt
  | Image ils tgt => Image (go ils) tgt
  | Span ils => Span (go ils)
  | Quoted qt ils => Quoted qt (go ils)
  | x => x
  end.

Definition inode (n : node inline) : node inline :=
  match n with Node _ a x => Node NoPos a (of_inline x) end.

Fixpoint of_inlines (ils : inlines) : inlines :=
  match ils with
  | [] => []
  | n :: rest => inode n :: of_inlines rest
  end.

Lemma inlines_cons : forall (n : node inline) (l : inlines),
  of_inlines (n :: l)%list = (inode n :: of_inlines l)%list.
Proof. reflexivity. Qed.

(* The traversal inside [of_inline] is [of_inlines]; the guard
   condition is why it cannot be spelled as one mutual fixpoint. *)
Lemma inline_children : forall ils : inlines,
  (fix go (ils : inlines) : inlines :=
     match ils with
     | [] => []
     | Node _ a x :: rest => Node NoPos a (of_inline x) :: go rest
     end) ils = of_inlines ils.
Proof.
  induction ils as [|[p a x] ils IH]; [reflexivity|].
  cbn [of_inlines inode]. rewrite IH. reflexivity.
Qed.

Lemma inlines_map : forall (xs : inlines),
  of_inlines xs = map inode xs.
Proof.
  induction xs as [|n xs IH]; [reflexivity|].
  rewrite inlines_cons, IH. reflexivity.
Qed.

Local Lemma inlines_app : forall (xs ys : inlines),
  of_inlines (xs ++ ys)%list =
  (of_inlines xs ++ of_inlines ys)%list.
Proof. intros xs ys. rewrite !inlines_map. apply map_app. Qed.

Lemma inlines_rev : forall (xs : inlines),
  of_inlines (rev xs) = rev (of_inlines xs).
Proof. intros xs. rewrite !inlines_map. apply map_rev. Qed.

Definition of_cell (c : cell) : cell :=
  match c with Cell ct al ils => Cell ct al (of_inlines ils) end.

Definition row (r : list cell) : list cell := map of_cell r.

Fixpoint of_block (b : block) : block :=
  let go :=
    fix go (bs : blocks) : blocks :=
      match bs with
      | [] => []
      | Node _ a x :: rest => Node NoPos a (of_block x) :: go rest
      end in
  let goitems :=
    fix goitems (items : list blocks) : list blocks :=
      match items with
      | [] => []
      | item :: rest => go item :: goitems rest
      end in
  match b with
  | Para ils => Para (of_inlines ils)
  | Section bs => Section (go bs)
  | Heading lvl ils => Heading lvl (of_inlines ils)
  | BlockQuote bs => BlockQuote (go bs)
  | Div bs => Div (go bs)
  | OrderedList attrs sp items => OrderedList attrs sp (goitems items)
  | BulletList sp items => BulletList sp (goitems items)
  | TaskList sp items =>
      TaskList sp
        ((fix gotasks (items : list (task_status * blocks)) :=
            match items with
            | [] => []
            | (status, item) :: rest =>
                (status, go item) :: gotasks rest
            end) items)
  | DefinitionList sp items =>
      DefinitionList sp
        ((fix godefs (items : list (inlines * blocks)) :=
            match items with
            | [] => []
            | (term, item) :: rest =>
                (of_inlines term, go item) :: godefs rest
            end) items)
  | Table caption rows =>
      Table (option_map of_inlines caption) (map row rows)
  | FootnoteDef label bs => FootnoteDef label (go bs)
  | Keyed label (Node _ a x) =>
      Keyed label (Node NoPos a (of_block x))
  | x => x
  end.

Fixpoint of_blocks (bs : blocks) : blocks :=
  match bs with
  | [] => []
  | Node _ a b :: rest =>
      Node NoPos a (of_block b) :: of_blocks rest
  end.

Lemma blocks_app : forall (xs ys : blocks),
  of_blocks (xs ++ ys)%list =
  (of_blocks xs ++ of_blocks ys)%list.
Proof.
  induction xs as [|[p a b] xs IH]; intros ys; cbn; rewrite ?IH; reflexivity.
Qed.

Lemma blocks_rev : forall (xs : blocks),
  of_blocks (rev xs) = rev (of_blocks xs).
Proof.
  induction xs as [|[p a b] xs IH].
  - reflexivity.
  - cbn [rev]. rewrite blocks_app. cbn [of_blocks].
    rewrite IH. reflexivity.
Qed.

(* `set_pos` writes only a node's position, so erasure sees through it. *)
Lemma blocks_set_pos : forall (p : provenance) (n : node block) rest,
  of_blocks (@set_pos located_pos block p n :: rest)%list =
  of_blocks (n :: rest)%list.
Proof. intros p [q a b] rest; reflexivity. Qed.

(* The term is a paragraph's inlines, so the split commutes with erasure
   on both halves. *)
Local Lemma def_split_erase : forall bs,
  def_split (of_blocks bs) =
  option_map (fun r => (of_inlines (fst r), of_blocks (snd r)))
    (def_split bs).
Proof.
  induction bs as [|[p a b] rest IH]; [reflexivity|].
  destruct b; cbn [of_blocks of_block def_split invisible_block] in *;
    try reflexivity;
    try (rewrite IH; destruct (def_split rest); reflexivity).
  - rewrite IH. destruct (def_split rest) as [[ils more]|]; cbn.
    + fold of_blocks. reflexivity.
    + reflexivity.
  - rewrite IH. destruct (def_split rest) as [[ils more]|]; reflexivity.
  - destruct b. reflexivity.
Qed.

Local Lemma def_item_erase : forall bs,
  (fst (def_item (of_blocks bs)), snd (def_item (of_blocks bs))) =
  (of_inlines (fst (def_item bs)), of_blocks (snd (def_item bs))).
Proof.
  intros bs. unfold def_item. rewrite def_split_erase.
  destruct (def_split bs) as [[term rest]|]; reflexivity.
Qed.

Lemma def_items_erase : forall items,
  (fix go (items : list (inlines * blocks)) :=
     match items with
     | [] => []
     | (term, item) :: rest =>
         (of_inlines term, of_blocks item) :: go rest
     end) (def_items items) = def_items (map of_blocks items).
Proof.
  induction items as [|item rest IH]; [reflexivity|].
  cbn [def_items map]. fold def_items. unfold def_items in IH.
  rewrite <- IH. pose proof (def_item_erase item) as H.
  destruct (def_item item) as [term item'];
    destruct (def_item (of_blocks item)) as [term' item''];
    cbn in H |- *.
  injection H as -> ->. reflexivity.
Qed.

Lemma task_items_erase : forall checks items,
  (fix go (items : list (task_status * blocks)) :=
     match items with
     | [] => []
     | (status, item) :: rest => (status, of_blocks item) :: go rest
     end) (task_items checks items) =
  task_items checks (map of_blocks items).
Proof.
  intros checks items. revert checks.
  induction items as [|item rest IH]; intros checks; [reflexivity|].
  destruct checks as [|check checks]; cbn [task_items map];
    unfold task_items in IH; rewrite IH; reflexivity.
Qed.

End Erase.

(*
Documents
=========
*)

(* Split a string into `sep`-free tokens, dropping empty ones.  Label
   normalization (below) and auto-identifiers (`Document.is_id_sep`) both
   collapse runs of a character class this way. *)
Local Fixpoint words_aux (sep : ascii -> bool) (s : string) (cur : string)
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

(* Tokens in source order; the accumulator above builds them reversed. *)
Definition words (sep : ascii -> bool) (s : string) : list string :=
  rev (words_aux sep s EmptyString []).

(* Labels are normalized by collapsing runs of whitespace to single
   spaces and trimming. *)
Local Definition is_label_ws (c : ascii) : bool :=
  (Ascii.eqb c " " || Ascii.eqb c "009" || Ascii.eqb c "013"
   || Ascii.eqb c "010")%char%bool.

Definition normalize_label (s : string) : string :=
  String.concat " " (words is_label_ws s).

(* Footnote bodies and link references, keyed by normalized label.  Look
   them up with lookup_note / lookup_reference, which normalize the key
   first, never with alist_lookup directly. *)
Definition note_map : Type := list (string * blocks).
Definition reference_map : Type := list (string * (string * attr)).

Local Definition lookup_note (label : string) (m : note_map) : option blocks :=
  alist_lookup (normalize_label label) m.

Definition lookup_reference (label : string) (m : reference_map)
  : option (string * attr) :=
  alist_lookup (normalize_label label) m.

(* A whole document: the block tree and the side tables the inline pass
   resolves against.  The auto_ tables are the ones derived from
   headings. *)
Record doc : Type := Doc
  { doc_blocks : blocks
  ; doc_footnotes : note_map
  ; doc_references : reference_map
  ; doc_auto_references : reference_map
  ; doc_auto_identifiers : list string }.

Local Definition empty_doc : doc := Doc [] [] [] [] [].
