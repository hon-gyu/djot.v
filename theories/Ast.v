(* ai-disclosure: autonomous *)

(** * Abstract syntax tree

   The Djot AST, transcribed from djoths (src/Djot/AST.hs) with djot.js
   (src/ast.ts) as tie-breaker where they disagree.

   Representation choices:
   - ByteString -> string  (Rocq strings are byte lists; extracted to
     native OCaml strings via ExtrOcamlNativeString)
   - Seq a -> list a
   - Map  -> association list keyed by normalized labels
   - Int  -> nat

   Nodes carry attributes and source positions uniformly. The executable
   parser produces this syntax; [Render] separately defines the canonical
   subset for which source rendering is invertible. *)

From Stdlib Require Import String Ascii List Bool.
Import ListNotations.

Local Open Scope string_scope.

(*
Attributes and positions
========================

Association lists
-----------------

Attribute sets and the document's reference map are both string-keyed
alists, and share these two operations.  Look-ups take the first match;
`alist_set` assigns JS-object style, so a key already present keeps its
position and takes the new value while a new key lands at the end
(djot.js `references[lab] = r`, parse.ts:336).
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

(* Setting never empties a map.  `Inline.oattach_list` needs it: it
   decorates whatever node resolution finds, and the invariant is
   phrased as "the head is not a plain `Str`" -- where *plain* means no
   attributes.  A node that already carries some must keep carrying
   some. *)
Local Lemma alist_set_cons :
  forall A k (v : A) m, exists x r, alist_set k v m = (x :: r)%list.
Proof.
  intros A k v [|[k' v'] m]; cbn [alist_set]; [eauto|].
  destruct (String.eqb k k'); eauto.
Qed.

(*
Attributes
----------
*)

(* Key/value pairs in source order.  

<decision>
djoths uses a Map; an alist keeps the representation extraction-friendly 
(Gallina list -> OCaml list), where Stdlib's `Map` would have to have 
its functor instantiated first.
</decision>
*)
Definition attr : Type := list (string * string).

Fixpoint lookup_attr (k : string) (a : attr) : option string :=
  match a with
  | [] => None
  | (k', v) :: rest => if String.eqb k k' then Some v else lookup_attr k rest
  end.

(*
Merging, djoths
---------------
*)


(* later-inserted keys win, except "class", whose values
concatenate (space-separated, left operand's classes first).  Reached
only through `add_attr`, and `cb_ok` admits no nested `CId`, so the one
canonical call site has an empty left operand. *)
Local Definition integrate (kv : string * string) (kvs : attr) : attr :=
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
Local Definition attr_union (a b : attr) : attr := fold_right integrate b a.

(*
Merging, djot.js
----------------

djot.js builds attributes as a JS object and assigns into it, so a key
already present keeps its position and takes the new value, while a new
key lands at the end.  `attr_union` above cannot express that -- it
prepends -- and attribute *order* is observable in the rendered tag, so
the block-attribute path (Attributes.v, Parser.v) uses these instead.
*)

Definition attr_set (k v : string) (a : attr) : attr := alist_set k v a.

(* Classes accumulate space-separated rather than overwrite, both within
   one attribute spec and across consecutive ones (djot.js parse.ts:536,
   :521). *)
Definition attr_add_class (v : string) (a : attr) : attr :=
  match lookup_attr "class" a with
  | None => attr_set "class" v a
  | Some old => attr_set "class" (old ++ " " ++ v) a
  end.

(* One key/value into a set, with the class rule. *)
Local Definition attr_put (kv : string * string) (a : attr) : attr :=
  if String.eqb (fst kv) "class"
  then attr_add_class (snd kv) a
  else attr_set (fst kv) (snd kv) a.

(* `-block_attributes` folding a finished spec into the pending set. *)
Definition attr_merge (new acc : attr) : attr :=
  fold_left (fun acc' kv => attr_put kv acc') new acc.

(* A one-key spec folded into nothing is that key.  The canonical id
   path is the caller: an explicit `{#i}` is a spec of exactly one
   binding, merged into an empty pending set. *)
Lemma attr_merge_one : forall kv, attr_merge [kv] [] = [kv].
Proof.
  intros [k v]. unfold attr_merge, attr_put, attr_add_class, attr_set.
  cbn [fold_left fst snd].
  destruct (String.eqb k "class") eqn:E;
    [apply String.eqb_eq in E; subst k|];
    cbn [lookup_attr alist_set]; reflexivity.
Qed.

(* Merging never empties a set; see `alist_set_cons`. *)
Local Lemma attr_put_cons :
  forall kv a, exists x r, attr_put kv a = (x :: r)%list.
Proof.
  intros kv a. unfold attr_put, attr_add_class, attr_set.
  destruct (String.eqb (fst kv) "class"); [|apply alist_set_cons].
  destruct (lookup_attr "class" a); apply alist_set_cons.
Qed.

Lemma attr_merge_cons :
  forall a kv acc, exists x r, attr_merge a (kv :: acc)%list = (x :: r)%list.
Proof.
  induction a as [|y a IH]; intros kv acc; [exists kv, acc; reflexivity|].
  unfold attr_merge in *; cbn [fold_left].
  destruct (attr_put y (kv :: acc)%list) as [|z r] eqn:E;
    [destruct (attr_put_cons y (kv :: acc)%list) as [? [? E']];
     rewrite E' in E; discriminate|].
  apply IH.
Qed.

(* `addBlockAttributes` (parse.ts:184): the pending set onto the node a
   block opens with.  Plain assignment -- no class rule here, which is
   djot.js's behaviour and not obviously intended. *)
Local Definition attr_apply (pending a : attr) : attr :=
  fold_left (fun a' kv => attr_set (fst kv) (snd kv) a') pending a.

(* A point in the source.  [spot_rem] counts bytes from the point to the
   end of its line (the line terminator is not part of the line).  The
   right-hand coordinate is deliberate: container parsing repeatedly
   removes prefixes, and prefixing a line must not move a point in the
   suffix that remains. *)
Record spot : Type := Spot
  { spot_line : nat
  ; spot_rem : nat }.

(* Source ranges are half-open. *)
Record span : Type := SrcSpan
  { span_start : spot
  ; span_stop : spot }.

(* The byte the inline scanner is dispatching.  Like [LineIx], this is
   an observation only: the semantic driver installs the inert instance
   below, while the located driver supplies the two ends of each byte.
   Keeping it implicit lets the grammar stay one definition. *)
Class InlineCursor : Type := CursorAt
  { cursor_start : spot
  ; cursor_stop : spot
  ; cursor_origin : spot }.

#[export] Instance semantic_inline_cursor : InlineCursor :=
  CursorAt (Spot 0 0) (Spot 0 0) (Spot 0 0).

(* Authored syntax which belongs to a node without widening the semantic
   node's own range.  The fence roles are also how a consumer distinguishes
   an unterminated fence from one with a closing line. *)
Inductive syntax_role : Type :=
  | RAttrSpec
  | ROpenFence
  | RCloseFence.

(* Some source-bearing parts of the semantic AST are not [node]s.  Keep
   their ranges parallel to their parent's children rather than changing
   the semantic tree merely to carry provenance. *)
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

(* The bare node: no position, no attributes.  Everything the parser
   currently builds is `mk`-wrapped, so proofs can compute through it. *)
Definition mk {A : Type} (x : A) : node A := Node NoPos [] x.

Definition node_contents {A : Type} (n : node A) : A :=
  match n with Node _ _ x => x end.

Definition node_attrs {A : Type} (n : node A) : attr :=
  match n with Node _ a _ => a end.

Definition add_attr {A : Type} (a : attr) (n : node A) : node A :=
  match n with Node p a' x => Node p (attr_union a' a) x end.

(* A bare node has nothing to merge with, so the set `add_attr` leaves is
   the one it was handed.  `Roundtrip.render_cb_lines` is the caller:
   every canonical block but a named one is `mk`-wrapped. *)
Lemma add_attr_mk :
  forall A (a : attr) (x : A), add_attr a (mk x) = Node NoPos a x.
Proof. reflexivity. Qed.

(* How a parse tags the nodes it builds.  One grammar, two observations:
   the parser is written once against this class, and an instance decides
   whether the provenance it computes reaches the AST.

   `semantic_pos` discards it, so `posnode p x` is `mk x` by conversion
   (`posnode_semantic`) and a statement written at that instance is the
   statement it was before locations existed.  A file that opens no
   policy context resolves `mkpos` to it, which is why nothing outside
   the located driver changes; `Check @thm` on a statement that is meant
   to hold for every policy is what shows the binder is really there.

   `pos_records` is the same question asked without a provenance to
   hand.  A pass that extends provenance a node already carries has to
   look inside the node, and looking inside it is what stops it reducing
   against an arbitrary one; asking the policy first is what keeps it an
   identity.  `pos_off` is the field that makes the answer mean
   something. *)
Class PosPolicy : Type := PosOf
  { mkpos : provenance -> pos
  ; pos_records : bool
  ; pos_off : pos_records = false -> forall p, mkpos p = NoPos }.

#[export] Instance semantic_pos : PosPolicy :=
  PosOf (fun _ => NoPos) false (fun _ _ => eq_refl).

Definition located_pos : PosPolicy :=
  PosOf SomePos true (fun H => ltac:(discriminate H)).

(* The one constructor the parser builds nodes with.  Attributes are
   attached afterwards, as they are today (`add_attr`). *)
Definition posnode `{PosPolicy} {A : Type} (p : provenance) (x : A) : node A :=
  Node (mkpos p) [] x.

(* Erasure of one node: what the located parse has to agree with the
   semantic one on.  Attributes are not provenance and stay. *)
Definition erase_node {A : Type} (n : node A) : node A :=
  match n with Node _ a x => Node NoPos a x end.

(* A span a scan *stores* in its own state, as opposed to one a node
   carries.  Asked of the policy, so that a state built by a policy which
   records nothing holds no coordinates at all -- which is what makes
   erasure of such a state the identity, and the inline refinement one
   equation instead of an equation and an invariant over the state. *)
Definition null_span : span := SrcSpan (Spot 0 0) (Spot 0 0).

Definition pspan `{PosPolicy} (r : span) : span :=
  if pos_records then r else null_span.

Lemma pspan_semantic : forall r, @pspan semantic_pos r = null_span.
Proof. reflexivity. Qed.

(* A node whose provenance is just its range: no authored syntax beside
   it, no non-node parts under it. *)
Definition prov_at (r : span) : provenance := Provenance r [] PNone.

(* The same with the authored syntax that belongs to the node without
   widening it: a fence's own lines, an attribute spec. *)
Definition prov_with (r : span) (rs : list (syntax_role * span))
  : provenance := Provenance r rs PNone.

(* Attribute specs, in source order, as the roles they become. *)
Definition attr_roles (specs : list span) : list (syntax_role * span) :=
  map (fun r => (RAttrSpec, r)) specs.

(* The same, applied to a node already built.  Every block the parser
   assembles is built by a helper that knows the block's shape and not
   its source, so provenance is attached where the source is known: at
   the state that closes.  Attributes the helper set are kept. *)
(* Written as a test on the policy's answer rather than on the node, so
   that a policy which records nothing leaves the node it was handed --
   by conversion, for an arbitrary node.  Every statement about the
   semantic parse is then the statement it was before locations
   existed, with no rewriting anywhere. *)
Definition set_pos `{PosPolicy} {A : Type} (p : provenance) (n : node A)
  : node A :=
  match mkpos p with
  | NoPos => n
  | q => match n with Node _ a x => Node q a x end
  end.

Lemma set_pos_mk :
  forall `{PosPolicy} A (p : provenance) (x : A),
    set_pos p (mk x) = posnode p x.
Proof.
  intros. unfold set_pos, posnode, mk. destruct (mkpos p); reflexivity.
Qed.

(* Provenance on the head of a list a container emitted.  The head is
   the block the container is: `key_close` and `decorate_head` both
   build one there. *)
Definition pos_head `{PosPolicy} {A : Type} (p : provenance)
  (ns : list (node A)) : list (node A) :=
  match mkpos p with
  | NoPos => ns
  | _ => match ns with
         | [] => []
         | n :: rest => (set_pos p n :: rest)%list
         end
  end.

(* Authored syntax that belongs to a node built earlier: an attribute
   spec settles before the block it decorates is emitted, and a fence's
   lines are known one at a time.  Unlike `set_pos` this has to read the
   provenance the node already carries, so it asks the policy first and
   is the identity by conversion when the answer is that nothing is
   recorded. *)
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

Lemma add_roles_off :
  forall `{PosPolicy} A rs (n : node A),
    pos_records = false -> add_roles rs n = n.
Proof. intros. unfold add_roles. rewrite H0. reflexivity. Qed.

Lemma add_roles_head_off :
  forall `{PosPolicy} A rs (ns : list (node A)),
    pos_records = false -> add_roles_head rs ns = ns.
Proof. intros. unfold add_roles_head. rewrite H0. reflexivity. Qed.

(* The hull of what a list of nodes covers: the first one's start to the
   last one's stop.  A `Section` is built by the document pass out of a
   heading and the blocks under it, so its range is theirs; it is a
   region of the source, not an invented span. *)
Definition hull_pos `{PosPolicy} {A : Type} (ns : list (node A)) : pos :=
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

(* The same, keeping the authored syntax of the node the hull opens
   with.  The document pass moves a heading's id onto the section it
   opens, and the spec that authored the id has to be reachable from
   whatever carries it. *)
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

Lemma hull_pos_with_semantic :
  forall A (ns : list (node A)), @hull_pos_with semantic_pos A ns = NoPos.
Proof. reflexivity. Qed.

Lemma hull_pos_off :
  forall `{PosPolicy} A (ns : list (node A)),
    pos_records = false -> hull_pos ns = NoPos.
Proof. intros. unfold hull_pos. rewrite H0. reflexivity. Qed.

(* At the semantic instance the wrappers are the identity. *)
Lemma hull_pos_semantic :
  forall A (ns : list (node A)), @hull_pos semantic_pos A ns = NoPos.
Proof. reflexivity. Qed.

Lemma add_roles_semantic :
  forall A rs (n : node A), @add_roles semantic_pos A rs n = n.
Proof. reflexivity. Qed.

Lemma add_roles_head_semantic :
  forall A rs (ns : list (node A)), @add_roles_head semantic_pos A rs ns = ns.
Proof. reflexivity. Qed.

Lemma pos_head_semantic :
  forall A (p : provenance) (ns : list (node A)),
    @pos_head semantic_pos A p ns = ns.
Proof. reflexivity. Qed.

Lemma set_pos_semantic :
  forall A (p : provenance) (n : node A), @set_pos semantic_pos A p n = n.
Proof. reflexivity. Qed.

(* A proof that has just reduced a closing arm meets the wrappers and
   nothing else.  They are the identity at the semantic instance, but
   `rewrite` is syntactic, so it needs saying. *)
Ltac nopos :=
  rewrite ?set_pos_semantic, ?pos_head_semantic, ?add_roles_semantic,
    ?add_roles_head_semantic, ?hull_pos_semantic, ?hull_pos_with_semantic.

Lemma set_pos_located :
  forall A (p : provenance) (q : pos) (a : attr) (x : A),
    @set_pos located_pos A p (Node q a x) = Node (SomePos p) a x.
Proof. reflexivity. Qed.

(* What erasing a located node gives: the node the semantic parse built
   at the same site.  The wrapper is the only thing between them. *)
Lemma erase_set_pos :
  forall `{PosPolicy} A (p : provenance) (n : node A),
    erase_node (set_pos p n) = erase_node n.
Proof.
  intros. unfold set_pos. destruct (mkpos p); [reflexivity|].
  destruct n; reflexivity.
Qed.

Lemma posnode_semantic :
  forall A (p : provenance) (x : A), @posnode semantic_pos A p x = mk x.
Proof. reflexivity. Qed.

Lemma posnode_located :
  forall A (p : provenance) (x : A),
    @posnode located_pos A p x = Node (SomePos p) [] x.
Proof. reflexivity. Qed.

Lemma erase_posnode :
  forall `{PosPolicy} A (p : provenance) (x : A),
    erase_node (posnode p x) = @posnode semantic_pos A p x.
Proof. intros. unfold posnode. destruct (mkpos p); reflexivity. Qed.

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

(* Inline content.  `Inline.para_inlines` is the pass that produces it,
   one call per paragraph, with the source lines joined by SoftBreak.
   The scanner also preserves symbols as nodes: their default HTML is
   literal `:name:`, so HTML comparison alone cannot distinguish them
   from text. *)
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
  (* `[[target|alias]]`, and `![[...]]` with `embed` set.  Both halves are
     source as written; what a target denotes is the consumer's. *)
  | Wikilink (embed : bool) (target : string) (alias : option string)
  | RawInline (format : string) (s : string)
  | NonBreakingSpace
  | Quoted (qt : quote_type) (ils : list (node inline))
  | SoftBreak
  | HardBreak.

Definition inlines : Type := list (node inline).

(* The two-predicate induction `block_ind2` is, for the inline tree: an
   `inlines` is two type constructors away from `inline`, so the
   generated principle stops at a container's children.  Every proof
   about a traversal of an inline tree needs this. *)
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

(* A wikilink's display text: the alias if there is one, else the target. *)
Definition wiki_display (target : string) (alias : option string) : string :=
  match alias with Some d => d | None => target end.

(* The ordinary link a wikilink renders as. *)
Definition wiki_desugar (embed : bool) (target : string) (alias : option string)
  : inline :=
  let ils := [mk (Str (wiki_display target alias))] in
  if embed then Image ils (Direct target) else Link ils (Direct target).

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

(* Decided equality on alignments, which the canonical view needs to
   compare a rendered separator against the one it meant. *)
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

(* Block content.  Every constructor but `Section` is produced by
   `Parser.parse_lines`; that one is transcribed from the oracles ahead
   of the parser reaching it (`Wf.supported` is the record). *)
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
  (* A caption's content is inline: djot.js opens it with
     `content: ContentType.Inline` (block.ts:237-240), and a continuation
     line is more inline text, never a block.  djoths spells it
     `Caption Blocks` (AST.hs:241); the narrower type is the one the
     oracle's own container type states, and it keeps `Table` a leaf for
     `block_ind2`. *)
  | Table (caption : option inlines) (rows : list (list cell))
  | RawBlock (format : string) (contents : string)
  (* Retained source form of a footnote definition.  The document pass
     later moves its children into `doc_footnotes`; keeping it here gives
     the block source an image for the roundtrip theorem. *)
  | FootnoteDef (label : string) (children : list (node block))
  (* A link-reference definition.  djot.js keeps these out of the block
     tree entirely, in `doc.references`; here the definition stays a block
     that renders to no HTML, and `Document.doc_pass` reads the map off
     the tree.  Keeping it means the source line has somewhere to
     round-trip *to*, which is what `Roundtrip.v` quantifies over — the
     map is derived from it, never the other way. *)
  | RefDef (label : string) (dest : string)
  (* A label paired with the one block it names.  Not djot's: it is the
     keyed-block extension of `.project/keyed-blocks.md`, and it holds a
     single block rather than a list because the scope is exactly one, so
     "the key takes the first block and nothing after it" is forced by
     the type rather than checked.  The label is a list only because the
     parser builds it with `para_inlines`; that it is one element is the
     canonical view's condition, not `wf_block`'s. *)
  | Keyed (label : inlines) (b : node block).

Definition blocks : Type := list (node block).

(* Forget source provenance throughout a tree while preserving attributes
   and semantic payloads.  [erase_node] above is deliberately shallow;
   these are the deep traversals the refinement is stated with.

   Deep exactly where the located parse records positions: a paragraph's
   and a heading's inlines, and a definition term, which is a paragraph's.
   A keyed block's label is still built by the ambient instance.  Table
   cells and captions are scanned under the recording policy, so their
   inline children are erased too. *)
Fixpoint erase_inline (i : inline) : inline :=
  let go :=
    fix go (ils : inlines) : inlines :=
      match ils with
      | [] => []
      | Node _ a x :: rest => Node NoPos a (erase_inline x) :: go rest
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

Definition erase_inode (n : node inline) : node inline :=
  match n with Node _ a x => Node NoPos a (erase_inline x) end.

Fixpoint erase_inlines (ils : inlines) : inlines :=
  match ils with
  | [] => []
  | n :: rest => erase_inode n :: erase_inlines rest
  end.

Lemma erase_inlines_cons : forall (n : node inline) (l : inlines),
  erase_inlines (n :: l)%list = (erase_inode n :: erase_inlines l)%list.
Proof. reflexivity. Qed.

(* The traversal inside [erase_inline] is [erase_inlines]; the guard
   condition is why it cannot be spelled as one mutual fixpoint. *)
Lemma erase_inline_children : forall ils : inlines,
  (fix go (ils : inlines) : inlines :=
     match ils with
     | [] => []
     | Node _ a x :: rest => Node NoPos a (erase_inline x) :: go rest
     end) ils = erase_inlines ils.
Proof.
  induction ils as [|[p a x] ils IH]; [reflexivity|].
  cbn [erase_inlines erase_inode]. rewrite IH. reflexivity.
Qed.

Lemma erase_inlines_map : forall (xs : inlines),
  erase_inlines xs = map erase_inode xs.
Proof.
  induction xs as [|n xs IH]; [reflexivity|].
  rewrite erase_inlines_cons, IH. reflexivity.
Qed.

Lemma erase_inlines_app : forall (xs ys : inlines),
  erase_inlines (xs ++ ys)%list =
  (erase_inlines xs ++ erase_inlines ys)%list.
Proof. intros xs ys. rewrite !erase_inlines_map. apply map_app. Qed.

Definition erase_cell (c : cell) : cell :=
  match c with Cell ct al ils => Cell ct al (erase_inlines ils) end.

Definition erase_row (r : list cell) : list cell := map erase_cell r.

Lemma erase_inlines_rev : forall (xs : inlines),
  erase_inlines (rev xs) = rev (erase_inlines xs).
Proof. intros xs. rewrite !erase_inlines_map. apply map_rev. Qed.


Fixpoint erase_block (b : block) : block :=
  let go :=
    fix go (bs : blocks) : blocks :=
      match bs with
      | [] => []
      | Node _ a x :: rest => Node NoPos a (erase_block x) :: go rest
      end in
  let goitems :=
    fix goitems (items : list blocks) : list blocks :=
      match items with
      | [] => []
      | item :: rest => go item :: goitems rest
      end in
  match b with
  | Para ils => Para (erase_inlines ils)
  | Section bs => Section (go bs)
  | Heading lvl ils => Heading lvl (erase_inlines ils)
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
                (erase_inlines term, go item) :: godefs rest
            end) items)
  | Table caption rows =>
      Table (option_map erase_inlines caption) (map erase_row rows)
  | FootnoteDef label bs => FootnoteDef label (go bs)
  | Keyed label (Node _ a x) =>
      Keyed label (Node NoPos a (erase_block x))
  | x => x
  end.

Fixpoint erase_blocks (bs : blocks) : blocks :=
  match bs with
  | [] => []
  | Node _ a b :: rest =>
      Node NoPos a (erase_block b) :: erase_blocks rest
  end.

Lemma erase_blocks_app : forall (xs ys : blocks),
  erase_blocks (xs ++ ys)%list =
  (erase_blocks xs ++ erase_blocks ys)%list.
Proof.
  induction xs as [|[p a b] xs IH]; intros ys; cbn; rewrite ?IH; reflexivity.
Qed.

Lemma erase_blocks_rev : forall (xs : blocks),
  erase_blocks (rev xs) = rev (erase_blocks xs).
Proof.
  induction xs as [|[p a b] xs IH].
  - reflexivity.
  - cbn [rev]. rewrite erase_blocks_app. cbn [erase_blocks].
    rewrite IH. reflexivity.
Qed.

(* `set_pos` and `pos_head` write a node's position and nothing else, so
   erasure sees straight through them.  Both are stated over a whole list
   because that is the shape every caller has: a block just built, in
   front of what the state below it emitted. *)
Lemma erase_blocks_set_pos : forall (p : provenance) (n : node block) rest,
  erase_blocks (@set_pos located_pos block p n :: rest)%list =
  erase_blocks (n :: rest)%list.
Proof. intros p [q a b] rest; reflexivity. Qed.

Lemma erase_blocks_pos_head : forall (p : provenance) (bs : blocks),
  erase_blocks (@pos_head located_pos block p bs) = erase_blocks bs.
Proof. intros p [|[q a b] rest]; reflexivity. Qed.

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

(* What djot.js keeps out of the block tree: a reference definition goes
   to `doc.references` and a footnote definition to `doc.footnotes`
   before `-list_item` runs, so neither is ever `children[0]` and neither
   can stand between an item and its term.  We keep both as blocks for
   the roundtrip's sake, so the search has to step over them.  Both
   oracles agree that `: [r]: u` / blank / `t` has `t` as its term. *)
Definition invisible_block (b : block) : bool :=
  match b with RefDef _ _ | FootnoteDef _ _ => true | _ => false end.

(* The term/definition split, at the point a list item closes.  djot.js
   runs it at `-list_item` (parse.ts:883-900): if the item's first child
   is a paragraph, its *inlines* become the term and the paragraph is
   dropped; otherwise the term is empty and the item keeps everything.
   So the term is a fold over what the item already emitted, never a
   revision of it, which is why a definition list needs no state of its
   own.

   The paragraph's attributes go with it.  That is djot.js's behaviour
   and not an omission: a term is inline content, with nowhere to put
   them, so `: {#i}` / `  t` yields a `dt` holding `t` and no id. *)
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

(* Pairing a task list's per-item checkboxes onto its items.  Recursion
   is on the *items*, not on the pair, so a short status list pads rather
   than truncating: `combine` would silently drop items, and every lemma
   about this fold would have to carry a length hypothesis to say it does
   not.  The parser pushes the two lists together (`Step.list_next`), so
   the padding is unreachable. *)
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

(* The term is a paragraph's inlines, so erasure reaches it through the
   paragraph: the split commutes with erasure on both halves. *)
Lemma def_split_erase : forall bs,
  def_split (erase_blocks bs) =
  option_map (fun r => (erase_inlines (fst r), erase_blocks (snd r)))
    (def_split bs).
Proof.
  induction bs as [|[p a b] rest IH]; [reflexivity|].
  destruct b; cbn [erase_blocks erase_block def_split invisible_block] in *;
    try reflexivity;
    try (rewrite IH; destruct (def_split rest); reflexivity).
  - rewrite IH. destruct (def_split rest) as [[ils more]|]; cbn.
    + fold erase_blocks. reflexivity.
    + reflexivity.
  - rewrite IH. destruct (def_split rest) as [[ils more]|]; reflexivity.
  - destruct b. reflexivity.
Qed.

Lemma def_item_erase : forall bs,
  (fst (def_item (erase_blocks bs)), snd (def_item (erase_blocks bs))) =
  (erase_inlines (fst (def_item bs)), erase_blocks (snd (def_item bs))).
Proof.
  intros bs. unfold def_item. rewrite def_split_erase.
  destruct (def_split bs) as [[term rest]|]; reflexivity.
Qed.

Lemma def_items_erase : forall items,
  (fix go (items : list (inlines * blocks)) :=
     match items with
     | [] => []
     | (term, item) :: rest =>
         (erase_inlines term, erase_blocks item) :: go rest
     end) (def_items items) = def_items (map erase_blocks items).
Proof.
  induction items as [|item rest IH]; [reflexivity|].
  cbn [def_items map]. fold def_items. unfold def_items in IH.
  rewrite <- IH. pose proof (def_item_erase item) as H.
  destruct (def_item item) as [term item'];
    destruct (def_item (erase_blocks item)) as [term' item''];
    cbn in H |- *.
  injection H as -> ->. reflexivity.
Qed.

Lemma task_items_erase : forall checks items,
  (fix go (items : list (task_status * blocks)) :=
     match items with
     | [] => []
     | (status, item) :: rest => (status, erase_blocks item) :: go rest
     end) (task_items checks items) =
  task_items checks (map erase_blocks items).
Proof.
  intros checks items. revert checks.
  induction items as [|item rest IH]; intros checks; [reflexivity|].
  destruct checks as [|check checks]; cbn [task_items map];
    unfold task_items in IH; rewrite IH; reflexivity.
Qed.



(* Rocq's generated `block_ind` does not descend into a container's
   contents: `blocks` is `list (node block)`, two type constructors away
   from `block`, and the guard checker will not follow that.  So every
   proof by induction over the AST needs this two-predicate version —
   P for a block, Q for a block list, each feeding the other.  (Render.v
   carries `cblock_ind2` for the canonical view, for the same reason.)

   `BulletList` holds a list *of* block lists, one more constructor deep
   again, so it needs a third predicate `R` with its own nil/cons — which
   is what `Document.assign_ids` traversing list items forced.
   `DefinitionList` holds a list of *pairs*, which is not `R`'s type, so
   it gets a fourth predicate `D` of its own; the term half is inlines
   and so contributes no hypothesis.  `TaskList`'s pairs are a third
   type again, hence `K`.  `Section` is the one container left without a
   hypothesis and must be discharged outright; nothing produces one yet,
   and a caller that needs one finds out at once, because the case
   becomes unprovable.  `Table` is not among them: its cells and its
   caption hold inlines, so it is a leaf like `Para`. *)
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
     no hypothesis of its own beyond the one every container has. *)
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
Documents
=========
*)

(* Splitting a string into `sep`-free tokens, empty ones dropped.  Both
   djot string-to-key derivations are an instance: collapse runs of a
   character class, drop them at the ends, join what is left with a fixed
   separator.  Labels use whitespace (below); auto-identifiers use a wider
   class (Document.is_id_sep). *)

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

(* Tokens in source order.  The accumulator above builds them reversed. *)
Definition words (sep : ascii -> bool) (s : string) : list string :=
  rev (words_aux sep s EmptyString []).

(* Labels are normalized by collapsing runs of whitespace to single
   spaces and trimming (djoths normalizeLabel). *)

Local Definition is_label_ws (c : ascii) : bool :=
  (Ascii.eqb c " " || Ascii.eqb c "009" || Ascii.eqb c "013"
   || Ascii.eqb c "010")%char%bool.

Definition normalize_label (s : string) : string :=
  String.concat " " (words is_label_ws s).

(* Footnote bodies and link references, keyed by normalized label.  Look
   them up through lookup_note / lookup_reference, which normalize the
   key first — never with alist_lookup directly. *)
Definition note_map : Type := list (string * blocks).
Definition reference_map : Type := list (string * (string * attr)).

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
