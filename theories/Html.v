(* ai-disclosure: autonomous *)

(* HTML rendering, targeting byte-identical agreement with djot.js's
   renderer, the authority.  djoths's serialization diverges on attribute
   order, section wrapping and task items, and we follow djot.js on all
   three (`.project/djotjs-divergences.md`).

   The renderer builds an output tree (`helt`) and `serialize` writes it
   out.  So a tag is opened and closed by one constructor rather than by
   two string literals, and escaping happens in exactly two places --
   `render_attrs` for a value, `serialize_elt` for text.  `serialize_lt_tags`
   at the end of the file is what that buys: every `<` in the output opens
   or closes a tag, so no source text can produce one. *)

From Stdlib Require Import String Ascii List Bool Arith Lia.
From DjotV Require Import Strings Ast Parser Document.
Import ListNotations.

Local Open Scope string_scope.

Local Definition escape_char (c : ascii) : string :=
  match c with
  | "&"%char => "&amp;"
  | "<"%char => "&lt;"
  | ">"%char => "&gt;"
  | _ => String c EmptyString
  end.

Local Fixpoint escape (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => escape_char c ++ escape s'
  end.

(* Attribute values escape the quote as well (djot.js escapeAttribute). *)
Local Definition escape_attr_char (c : ascii) : string :=
  match c with
  | """"%char => "&quot;"
  | _ => escape_char c
  end.

Local Fixpoint escape_attr (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => escape_attr_char c ++ escape_attr s'
  end.

(* Rendered in source order, each as ` key="value"`, so that the empty
   attribute set contributes nothing to a tag. *)
Local Definition render_attrs (a : attr) : string :=
  String.concat ""
    (map (fun kv => " " ++ fst kv ++ "=""" ++ escape_attr (snd kv) ++ """") a).

(*
The output tree
===============

The renderer builds this and `serialize` writes it out, rather than
concatenating strings directly.  Two things follow that a flat string
cannot express.

A tag is opened and closed by one constructor, so an unbalanced one
cannot be written down.  And source text reaches the output only through
`HText`, which `serialize` escapes, so `HRaw` is the whole of how an
unescaped byte gets out -- reachable from a document only through a raw
block or a raw inline, and otherwise carrying a constant this file
chose.
*)

Inductive helt : Type :=
  | HText (s : string)
  | HRaw (s : string)
  (* An element with no closing tag.  `self` spells it `<tag/>`, which
     djot.js does for the task-list checkbox and nowhere else. *)
  | HVoid (tag : string) (self : bool) (attrs : attr)
  (* `nls` is djot.js's `newlines`: 2 puts a newline after the opening
     tag and after the closing one, 1 after the closing one only, 0
     neither.

     Attributes are one list, in output order.  What djot.js calls
     `extraAttrs` -- what a construct contributes itself, ahead of the
     node's own -- is just the front of it. *)
  | HElem (tag : string) (nls : nat) (attrs : attr) (kids : list helt).

Local Definition open_tag (tag : string) (self : bool) (a : attr) : string :=
  "<" ++ tag ++ render_attrs a ++ (if self then "/>" else ">").

(* Recursion on the element with the children walked by an inner `fix`,
   which is what the guard checker accepts through `list helt` -- a plain
   fixpoint on the list is rejected, since `kids` is not a subterm of the
   list being matched.  `serialize_elt_elem` below recovers the equation
   that spelling costs. *)
Local Fixpoint serialize_elt (e : helt) : string :=
  let go :=
    fix go (es : list helt) : string :=
      match es with
      | [] => ""
      | e' :: rest => serialize_elt e' ++ go rest
      end in
  match e with
  | HText s => escape s
  | HRaw s => s
  | HVoid tag self a => open_tag tag self a
  | HElem tag nls a kids =>
      open_tag tag false a
      ++ (if Nat.leb 2 nls then nl else "")
      ++ go kids ++ "</" ++ tag ++ ">"
      ++ (if Nat.leb 1 nls then nl else "")
  end.

Fixpoint serialize (es : list helt) : string :=
  match es with
  | [] => ""
  | e :: rest => serialize_elt e ++ serialize rest
  end.

Local Lemma serialize_elt_elem : forall tag nls a kids,
  serialize_elt (HElem tag nls a kids)
  = open_tag tag false a
    ++ (if Nat.leb 2 nls then nl else "")
    ++ serialize kids ++ "</" ++ tag ++ ">"
    ++ (if Nat.leb 1 nls then nl else "").
Proof.
  intros tag nls a kids. cbn [serialize_elt].
  assert (H : forall ks,
    (fix go (es : list helt) : string :=
       match es with
       | [] => ""
       | e' :: rest => serialize_elt e' ++ go rest
       end) ks = serialize ks).
  { induction ks as [|k ks' IH]; [reflexivity|].
    cbn [serialize]. rewrite <- IH. reflexivity. }
  rewrite H. reflexivity.
Qed.

(* Induction that reaches the children, in the shape `Render.cblock_ind2`
   established: the inner `fix` is what carries `P` through `list helt`. *)
Local Definition helt_ind2
  (P : helt -> Prop) (Q : list helt -> Prop)
  (htext : forall s, P (HText s))
  (hraw : forall s, P (HRaw s))
  (hvoid : forall tag self a, P (HVoid tag self a))
  (helem : forall tag nls a kids, Q kids -> P (HElem tag nls a kids))
  (hnil : Q [])
  (hcons : forall e es, P e -> Q es -> Q (e :: es))
  : forall e, P e :=
  fix go (e : helt) : P e :=
    let golist :=
      fix golist (es : list helt) : Q es :=
        match es with
        | [] => hnil
        | e' :: rest => hcons e' rest (go e') (golist rest)
        end in
    match e with
    | HText s => htext s
    | HRaw s => hraw s
    | HVoid tag self a => hvoid tag self a
    | HElem tag nls a kids => helem tag nls a kids (golist kids)
    end.

Local Definition helts_ind2
  (P : helt -> Prop) (Q : list helt -> Prop)
  (htext : forall s, P (HText s))
  (hraw : forall s, P (HRaw s))
  (hvoid : forall tag self a, P (HVoid tag self a))
  (helem : forall tag nls a kids, Q kids -> P (HElem tag nls a kids))
  (hnil : Q [])
  (hcons : forall e es, P e -> Q es -> Q (e :: es))
  : forall es, Q es :=
  fix golist (es : list helt) : Q es :=
    match es with
    | [] => hnil
    | e :: rest =>
        hcons e rest
          (helt_ind2 P Q htext hraw hvoid helem hnil hcons e) (golist rest)
    end.

(*
Serializing in one pass
-----------------------

`serialize` is the specification: every lemma about the output is
stated against it.  Run as written it copies the output once per level
of `++`, which is quadratic in the document.  `serialize_flat` lists the
pieces in output order, prepending to an accumulator, and joins them
once; `serialize_flat_serialize` says it is the same string.
*)

Local Fixpoint pieces_elt (e : helt) (acc : list string) : list string :=
  let go :=
    fix go (es : list helt) (acc : list string) : list string :=
      match es with
      | [] => acc
      | e' :: rest => pieces_elt e' (go rest acc)
      end in
  match e with
  | HText s => escape s :: acc
  | HRaw s => s :: acc
  | HVoid tag self a => open_tag tag self a :: acc
  | HElem tag nls a kids =>
      open_tag tag false a :: (if Nat.leb 2 nls then nl else "")
      :: go kids ("</" :: tag :: ">" :: (if Nat.leb 1 nls then nl else "") :: acc)
  end.

Local Fixpoint pieces (es : list helt) (acc : list string) : list string :=
  match es with
  | [] => acc
  | e :: rest => pieces_elt e (pieces rest acc)
  end.

Definition serialize_flat (es : list helt) : string :=
  String.concat "" (pieces es []).

Local Lemma concat_empty_cons : forall x l,
  String.concat "" (x :: l) = x ++ String.concat "" l.
Proof.
  intros x [|y l]; cbn [String.concat]; [|reflexivity].
  symmetry. apply append_empty_r.
Qed.

Local Lemma pieces_elt_elem : forall tag nls a kids acc,
  pieces_elt (HElem tag nls a kids) acc
  = open_tag tag false a :: (if Nat.leb 2 nls then nl else "")
    :: pieces kids ("</" :: tag :: ">" :: (if Nat.leb 1 nls then nl else "") :: acc).
Proof. reflexivity. Qed.

Lemma serialize_flat_serialize : forall es, serialize_flat es = serialize es.
Proof.
  assert (H : forall es acc,
    String.concat "" (pieces es acc) = serialize es ++ String.concat "" acc).
  { apply (helts_ind2
      (fun e => forall acc,
         String.concat "" (pieces_elt e acc) = serialize_elt e ++ String.concat "" acc)
      (fun es => forall acc,
         String.concat "" (pieces es acc) = serialize es ++ String.concat "" acc)).
    - intros s acc. apply concat_empty_cons.
    - intros s acc. apply concat_empty_cons.
    - intros tag self a acc. apply concat_empty_cons.
    - intros tag nls a kids IH acc.
      rewrite pieces_elt_elem, serialize_elt_elem, !concat_empty_cons, IH,
        !concat_empty_cons, !append_assoc. reflexivity.
    - intros acc. reflexivity.
    - intros e es IHe IHes acc. cbn [pieces serialize].
      rewrite IHe, IHes, append_assoc. reflexivity. }
  intros es. unfold serialize_flat. rewrite H. apply append_empty_r.
Qed.

(* A task item's checkbox. *)
Local Definition checkbox_elt (chk : task_status) : helt :=
  HVoid "input" true
    ([("disabled", ""); ("type", "checkbox")]
     ++ match chk with Complete => [("checked", "")] | Incomplete => [] end)%list.

(* What a resolved reference definition contributes.  Its attributes are
   extra in the same sense as `href`, so they precede the node's own, but
   a key the node carries itself wins: an entry is copied only when the
   node has none.  Without the filter `[ref][]{title=bar}` against a
   `{title=foo}` definition renders two `title`s.  A `class` join is
   unreachable from here, since it needs an extra `class`, which this
   filter admits only when the node has none to join with. *)
Local Definition ref_extra (a0 a : attr) : attr :=
  filter (fun kv => match alist_lookup (fst kv) a with
                    | Some _ => false
                    | None => true
                    end) a0.

(* An ordered list's `start` and `type`.  Both are omitted at their HTML
   defaults (start 1, decimal numbering), and both precede the node's own
   attributes, as extra attributes always do. *)
Local Definition ol_attrs (oa : ordered_list_attributes) : attr :=
  ((if Nat.eqb (ol_start oa) 1
    then [] else [("start", nat_str (ol_start oa))])
   ++ (match ol_style oa with
       | Decimal => []
       | LetterLower => [("type", "a")]
       | LetterUpper => [("type", "A")]
       | RomanLower => [("type", "i")]
       | RomanUpper => [("type", "I")]
       end))%list.

(*
Inlines
=======
*)

(* An image's `alt` is the plain text of its children, not their HTML:
   each node's text, a break as a newline, containers recursing.  Only
   the constructs the parser builds are covered; the rest contribute
   nothing here in any case. *)
Local Fixpoint plain_text (il : inline) : string :=
  let go :=
    fix go (ns : list (node inline)) : string :=
      match ns with
      | [] => ""
      | Node _ _ x :: rest => plain_text x ++ go rest
      end in
  match il with
  | Str s | Verbatim s | Math _ s | RawInline _ s => s
  | UrlLink s | EmailLink s => s
  | Ext_wikilink _ t al => wiki_display t al
  | Emph ns | Strong ns | Highlight ns | Insert ns | Delete ns
  | Superscript ns | Subscript ns | Span ns | Quoted _ ns
  | Link ns _ | Image ns _ => go ns
  | SoftBreak | HardBreak => nl
  | NonBreakingSpace => " "
  | FootnoteReference _ | Symbol _ => ""
  end.

Local Definition plain_texts (ns : list (node inline)) : string :=
  String.concat "" (map (fun n => plain_text (node_contents n)) ns).

(*
Rendering, against the document's reference map
===============================================

`refs` is the map a `Reference` target resolves against: the document's
explicit definitions followed by the implicit heading ones, appended so
that `alist_lookup`'s first-match rule prefers the explicit one.  It is a
section variable rather than a threaded argument because every recursion
here would otherwise carry it unchanged.
*)

Section WithRefs.
Context (refs : reference_map).

(* A node's own attributes render on its own tag, after any the
   construct contributes itself.  A `Str` has no tag of its own, so an
   attributed one is wrapped in a `<span>` and a bare one left alone:
   `foo{.a}` is a `Str` carrying attributes in the AST and a span only in
   the output. *)
Local Fixpoint render_inline (il : inline) (a : attr) : list helt :=
  let render_ils :=
    fix go (ns : list (node inline)) : list helt :=
      match ns with
      | [] => []
      | Node _ a' x :: rest => (render_inline x a' ++ go rest)%list
      end in
  match il with
  | Str s =>
      match a with
      | [] => [HText s]
      | _ => [HElem "span" 0 a [HText s]]
      end
  | Emph ils => [HElem "em" 0 a (render_ils ils)]
  | Strong ils => [HElem "strong" 0 a (render_ils ils)]
  | Highlight ils => [HElem "mark" 0 a (render_ils ils)]
  | Insert ils => [HElem "ins" 0 a (render_ils ils)]
  | Delete ils => [HElem "del" 0 a (render_ils ils)]
  | Superscript ils => [HElem "sup" 0 a (render_ils ils)]
  | Subscript ils => [HElem "sub" 0 a (render_ils ils)]
  | Verbatim s => [HElem "code" 0 a [HText s]]
  | Symbol s => [HText (":" ++ s ++ ":")]
  (* a span carrying the class, with the content in TeX delimiters and
     escaped as text *)
  | Math InlineMath s =>
      [HElem "span" 0 [("class", "math inline")] [HText ("\(" ++ s ++ "\)")]]
  | Math DisplayMath s =>
      [HElem "span" 0 [("class", "math display")] [HText ("\[" ++ s ++ "\]")]]
  (* `href` is an extra attribute, so it precedes the node's own and is
     omitted entirely when the target is an unresolved reference: djot.js
     drops the attribute (with a warning) when a label does not resolve.
     A resolved reference contributes the definition's attributes through
     `ref_extra`, which are extra in the same sense and so also precede
     the node's. *)
  | Link ils (Direct url) =>
      [HElem "a" 0 (("href", url) :: a) (render_ils ils)]
  | Link ils (Reference label) =>
      match lookup_reference label refs with
      | Some (url, a0) =>
          [HElem "a" 0
             (("href", url) :: ref_extra a0 a ++ a)%list (render_ils ils)]
      | None => [HElem "a" 0 a (render_ils ils)]
      end
  (* `alt` precedes `src`, both extra attributes, in that order *)
  | Image ils (Direct url) =>
      [HVoid "img" false
         (("alt", plain_texts ils) :: ("src", url) :: a)]
  | Image ils (Reference label) =>
      match lookup_reference label refs with
      | Some (url, a0) =>
          [HVoid "img" false
             (("alt", plain_texts ils) :: ("src", url)
              :: ref_extra a0 a ++ a)%list]
      | None => [HVoid "img" false (("alt", plain_texts ils) :: a)]
      end
  | Span ils => [HElem "span" 0 a (render_ils ils)]
  | FootnoteReference _ => [] (* numbered on the `_foot` path *)
  (* An autolink renders as its own text under an `href`, which is an
     extra attribute and so precedes the node's own.  The two kinds
     differ only in the `mailto:` an email prefixes to the destination;
     the text shown is the region either way. *)
  | UrlLink url => [HElem "a" 0 (("href", url) :: a) [HText url]]
  | EmailLink addr =>
      [HElem "a" 0 (("href", "mailto:" ++ addr) :: a) [HText addr]]
  (* A wikilink renders as the link it desugars to; `render_wikilink`
     states it.  Spelled out rather than a call, which would not be
     structural. *)
  | Ext_wikilink false t al =>
      [HElem "a" 0 (("href", t) :: a) [HText (wiki_display t al)]]
  | Ext_wikilink true t al =>
      [HVoid "img" false (("alt", wiki_display t al) :: ("src", t) :: a)]
  (* Raw content in a format the renderer does not speak contributes
     nothing at all, attributes included: the text is emitted only for
     `html`, and never in a wrapper element. *)
  | RawInline fmt s => if String.eqb fmt "html" then [HRaw s] else []
  (* The one constant this file writes unescaped. *)
  | NonBreakingSpace => [HRaw "&nbsp;"]
  (* The curly quotes are the whole of what a quoted span renders as:
     the children between the two characters, and no element. *)
  | Quoted SingleQuotes ils =>
      ([HText lsquo] ++ render_ils ils ++ [HText rsquo])%list
  | Quoted DoubleQuotes ils =>
      ([HText ldquo] ++ render_ils ils ++ [HText rdquo])%list
  | SoftBreak => [HText nl]
  | HardBreak => [HVoid "br" false []; HText nl]
  end.

Local Definition render_inlines (ils : inlines) : list helt :=
  (fix go (ns : inlines) : list helt :=
    match ns with
    | [] => []
    | Node _ a x :: rest => (render_inline x a ++ go rest)%list
    end) ils.

(* Section 5 of the wikilink spec: a wikilink renders as the ordinary
   link it desugars to, attributes included. *)
Local Lemma render_wikilink : forall embed t al a,
  render_inline (Ext_wikilink embed t al) a = render_inline (wiki_desugar embed t al) a.
Proof. intros [|] t al a; reflexivity. Qed.

(*
Table rows
----------

Cells hold inlines only, so the whole of a table renders without
touching `render_block`'s recursion.  Alignment is a style attribute on
the cell, and `AlignDefault` carries none. *)

Local Definition align_attr (al : align) : attr :=
  match al with
  | AlignDefault => []
  | AlignLeft => [("style", "text-align: left;")]
  | AlignRight => [("style", "text-align: right;")]
  | AlignCenter => [("style", "text-align: center;")]
  end.

Local Definition render_cell (c : cell) : helt :=
  match c with
  | Cell ct al ils =>
      let tag := match ct with HeadCell => "th" | BodyCell => "td" end in
      HElem tag 1 (align_attr al) (render_inlines ils)
  end.

Definition render_row (r : list cell) : helt :=
  HElem "tr" 2 [] (map render_cell r).

Local Definition render_caption (caption : option inlines) : list helt :=
  match caption with
  | None => []
  | Some ils => [HElem "caption" 1 [] (render_inlines ils)]
  end.

(*
Blocks
======
*)

(* `tight` is rendering state, not a property of the block being
   rendered: a list sets it for its children and restores it on the way
   out, and nothing else changes it.  So it survives a block quote or a
   div, and every paragraph below a tight item is emitted bare until
   another list resets it: `- > a` renders `<blockquote>a</blockquote>`.

   The node's attributes ride alongside its payload, since they belong
   on the opening tag, but recursion has to be on `block`: `list (node
   block)` is two type constructors deep, which the guard checker will
   not follow from a `node block` argument. *)
Local Fixpoint render_block (tight : bool) (b : block) (a : attr) {struct b}
  : list helt :=
  (* Takes the flag as an argument so that one list recursion serves both
     the containers, which pass it through, and the items, which set it. *)
  let render_bs_at :=
    fix go (t : bool) (ns : list (node block)) : list helt :=
      match ns with
      | [] => []
      | Node _ a' x :: rest => (render_block t x a' ++ go t rest)%list
      end in
  let render_bs := render_bs_at tight in
  let render_items :=
    fix goi (sp : list_spacing) (its : list (list (node block))) {struct its}
      : list helt :=
      match its with
      | [] => []
      | it :: rest =>
          (HElem "li" 2 []
             (render_bs_at (match sp with Tight => true | Loose => false end) it)
           :: goi sp rest)%list
      end in
  (* A `dd` is rendered at the incoming tightness, not at the list's:
     djot.js's definition list carries no tightness flag, so a definition
     inside a tight bullet item renders bare, and `sp` is read by nothing
     here.  The roundtrip reads it, since it records the blank lines the
     source had. *)
  let render_def_items :=
    fix god (its : list (inlines * list (node block))) {struct its}
      : list helt :=
      match its with
      | [] => []
      | (term, it) :: rest =>
          (HElem "dt" 1 [] (render_inlines term)
           :: HElem "dd" 2 [] (render_bs it)
           :: god rest)%list
      end in
  (* A task item's checkbox, ahead of its content and outside whatever
     the tightness does to that content.  The `<ul>` carries
     `class="task-list"` before the node's own attributes, the order
     `ol_attrs` already establishes. *)
  let render_task_items :=
    fix got (sp : list_spacing)
      (its : list (task_status * list (node block))) {struct its}
      : list helt :=
      match its with
      | [] => []
      | (st, it) :: rest =>
          (HElem "li" 2 []
             (checkbox_elt st :: HText nl
              :: render_bs_at
                   (match sp with Tight => true | Loose => false end) it)%list
           :: got sp rest)%list
      end in
  match b with
  (* A tight paragraph loses its tag, keeping the newline the tag
     carried.  Its attributes go with the tag, as in djot.js. *)
  | Para ils =>
      if tight then (render_inlines ils ++ [HText nl])%list
      else [HElem "p" 1 a (render_inlines ils)]
  | Section bs => [HElem "section" 2 a (render_bs bs)]
  | Heading lvl ils =>
      [HElem ("h" ++ nat_str lvl) 1 a (render_inlines ils)]
  | BlockQuote bs => [HElem "blockquote" 2 a (render_bs bs)]
  (* The language is escaped as an attribute value. *)
  | CodeBlock lang code =>
      [HElem "pre" 1 a
         [HElem "code" 0
            (match lang with
             | EmptyString => []
             | _ => [("class", "language-" ++ lang)]
             end) [HText code]]]
  | Div bs => [HElem "div" 2 a (render_bs bs)]
  | OrderedList oa sp items =>
      [HElem "ol" 2 (ol_attrs oa ++ a)%list (render_items sp items)]
  | BulletList sp items => [HElem "ul" 2 a (render_items sp items)]
  | TaskList sp items =>
      [HElem "ul" 2 (("class", "task-list") :: a) (render_task_items sp items)]
  | DefinitionList _ items => [HElem "dl" 2 a (render_def_items items)]
  | ThematicBreak => [HVoid "hr" false a; HText nl]
  | Table caption rows =>
      [HElem "table" 2 a
         (render_caption caption ++ map render_row rows)%list]
  | RawBlock fmt contents =>
      if String.eqb fmt "html" then [HRaw contents] else []
  (* A reference definition is not content: djot.js keeps it out of the
     block tree entirely and emits nothing for it. *)
  | RefDef _ _ => []
  (* Collected by the later document pass; while it remains in the block
     tree it is metadata rather than visible document content. *)
  | FootnoteDef _ _ => []
  (* djot.js does not have this construct, so there is no image to match.  A
     one-term description list says "this names that" while keeping the
     label as inline content, which a label carried in an attribute could
     not.  The class keeps the construct distinct from an ordinary
     one-term definition list.  `.project/keyed-blocks.md` 9.3 records
     the choice. *)
  | Ext_keyed label b =>
      [HElem "dl" 2 (("class", "keyed") :: a)
         [HElem "dt" 1 [] (render_inlines label);
          HElem "dd" 2 [] (render_bs [b])]]
  end.

Local Definition render_node (n : node block) : list helt :=
  match n with Node _ a b => render_block false b a end.

Definition render_blocks (bs : blocks) : list helt :=
  flat_map render_node bs.

(* Footnote indices are assigned by the HTML traversal, including traversals
   through note bodies.  Keeping this path beside the stateless renderer
   leaves the latter useful for its existing local callers while making the
   document entry point agree with djot.js. *)
Record foot_state : Type := FootState
  { foot_numbers : list (string * nat)
  ; foot_next : nat
  }.

Definition foot_initial : foot_state := FootState [] 1.

Local Definition number_footnote (label : string) (st : foot_state)
  : foot_state * nat * bool :=
  let label := normalize_label label in
  match alist_lookup label (foot_numbers st) with
  | Some n => (st, n, false)
  | None =>
      let n := foot_next st in
      (FootState ((foot_numbers st ++ [(label, n)])%list) (S n), n, true)
  end.

Local Fixpoint render_inline_foot (st : foot_state) (il : inline) (a : attr)
  {struct il} : foot_state * list helt :=
  let render_ils :=
    fix go (st0 : foot_state) (ns : list (node inline))
      : foot_state * list helt :=
      match ns with
      | [] => (st0, [])
      | Node _ a' x :: rest =>
          let '(st1, s1) := render_inline_foot st0 x a' in
          let '(st2, s2) := go st1 rest in
          (st2, (s1 ++ s2)%list)
      end in
  match il with
  | Emph ils =>
      let '(st', s) := render_ils st ils in (st', [HElem "em" 0 a s])
  | Strong ils =>
      let '(st', s) := render_ils st ils in (st', [HElem "strong" 0 a s])
  | Highlight ils =>
      let '(st', s) := render_ils st ils in (st', [HElem "mark" 0 a s])
  | Insert ils =>
      let '(st', s) := render_ils st ils in (st', [HElem "ins" 0 a s])
  | Delete ils =>
      let '(st', s) := render_ils st ils in (st', [HElem "del" 0 a s])
  | Superscript ils =>
      let '(st', s) := render_ils st ils in (st', [HElem "sup" 0 a s])
  | Subscript ils =>
      let '(st', s) := render_ils st ils in (st', [HElem "sub" 0 a s])
  | Span ils =>
      let '(st', s) := render_ils st ils in (st', [HElem "span" 0 a s])
  | Quoted q ils =>
      let '(st', s) := render_ils st ils in
      match q with
      | SingleQuotes => (st', ([HText lsquo] ++ s ++ [HText rsquo])%list)
      | DoubleQuotes => (st', ([HText ldquo] ++ s ++ [HText rdquo])%list)
      end
  | Link ils target =>
      let '(st', s) := render_ils st ils in
      match target with
      | Direct url => (st', [HElem "a" 0 (("href", url) :: a) s])
      | Reference label =>
          match lookup_reference label refs with
          | Some (url, a0) =>
              (st', [HElem "a" 0
                       (("href", url) :: ref_extra a0 a ++ a)%list s])
          | None => (st', [HElem "a" 0 a s])
          end
      end
  (* Image children become alt text and are not visited by djot.js's HTML
     traversal, so a syntactically nested reference does not get a number. *)
  | Image _ _ => (st, render_inline il a)
  | FootnoteReference label =>
      let '(st', n, first) := number_footnote label st in
      let sn := nat_str n in
      (st', [HElem "a" 0
               ((if first then [("id", ("fnref" ++ sn)%string)] else [])
                ++ [("href", ("#fn" ++ sn)%string); ("role", "doc-noteref")]
                ++ a)%list
               [HElem "sup" 0 [] [HText sn]]])
  | _ => (st, render_inline il a)
  end.

(* Right recursion, each node's output put in front of the rest's: an
   accumulator appended at the back would copy the output so far once per
   node. *)
Local Definition render_inlines_foot (st : foot_state) (ils : inlines)
  : foot_state * list helt :=
  (fix go (st0 : foot_state) (ns : inlines) : foot_state * list helt :=
     match ns with
     | [] => (st0, [])
     | Node _ a x :: rest =>
         let '(st1, s1) := render_inline_foot st0 x a in
         let '(st2, s2) := go st1 rest in
         (st2, (s1 ++ s2)%list)
     end) st ils.

(* The table renderers again, threading the footnote counter: a cell may
   carry a footnote reference, and it is numbered in source order like
   any other. *)
Local Definition render_cell_foot (st : foot_state) (c : cell)
  : foot_state * helt :=
  match c with
  | Cell ct al ils =>
      let tag := match ct with HeadCell => "th" | BodyCell => "td" end in
      let '(st', s) := render_inlines_foot st ils in
      (st', HElem tag 1 (align_attr al) s)
  end.

Local Fixpoint render_cells_foot (st : foot_state) (r : list cell)
  : foot_state * list helt :=
  match r with
  | [] => (st, [])
  | c :: rest =>
      let '(st1, e) := render_cell_foot st c in
      let '(st2, es) := render_cells_foot st1 rest in
      (st2, e :: es)
  end.

Local Fixpoint render_rows_foot (st : foot_state) (rows : list (list cell))
  : foot_state * list helt :=
  match rows with
  | [] => (st, [])
  | r :: rest =>
      let '(st1, cells) := render_cells_foot st r in
      let '(st2, es) := render_rows_foot st1 rest in
      (st2, HElem "tr" 2 [] cells :: es)
  end.

Local Definition render_caption_foot (st : foot_state) (caption : option inlines)
  : foot_state * list helt :=
  match caption with
  | None => (st, [])
  | Some ils =>
      let '(st', s) := render_inlines_foot st ils in
      (st', [HElem "caption" 1 [] s])
  end.

Local Fixpoint render_block_foot (st : foot_state) (tight : bool)
  (b : block) (a : attr) {struct b} : foot_state * list helt :=
  let render_bs_at :=
    fix go (st0 : foot_state) (t : bool) (ns : list (node block))
      : foot_state * list helt :=
      match ns with
      | [] => (st0, [])
      | Node _ a' x :: rest =>
          let '(st1, s1) := render_block_foot st0 t x a' in
          let '(st2, s2) := go st1 t rest in
          (st2, (s1 ++ s2)%list)
      end in
  let render_items :=
    fix goi (st0 : foot_state) (sp : list_spacing)
      (its : list (list (node block))) {struct its}
      : foot_state * list helt :=
      match its with
      | [] => (st0, [])
      | it :: rest =>
          let t := match sp with Tight => true | Loose => false end in
          let '(st1, s1) := render_bs_at st0 t it in
          let '(st2, s2) := goi st1 sp rest in
          (st2, HElem "li" 2 [] s1 :: s2)
      end in
  let render_task_items :=
    fix got (st0 : foot_state) (sp : list_spacing)
      (its : list (task_status * list (node block))) {struct its}
      : foot_state * list helt :=
      match its with
      | [] => (st0, [])
      | (chk, it) :: rest =>
          let t := match sp with Tight => true | Loose => false end in
          let '(st1, s1) := render_bs_at st0 t it in
          let '(st2, s2) := got st1 sp rest in
          (st2, HElem "li" 2 [] (checkbox_elt chk :: HText nl :: s1) :: s2)
      end in
  let render_def_items :=
    fix god (st0 : foot_state) (its : list (inlines * list (node block)))
      {struct its} : foot_state * list helt :=
      match its with
      | [] => (st0, [])
      | (term, it) :: rest =>
          let '(st1, s1) := render_inlines_foot st0 term in
          let '(st2, s2) := render_bs_at st1 tight it in
          let '(st3, s3) := god st2 rest in
          (st3, HElem "dt" 1 [] s1 :: HElem "dd" 2 [] s2 :: s3)
      end in
  match b with
  | Para ils =>
      let '(st', s) := render_inlines_foot st ils in
      if tight then (st', (s ++ [HText nl])%list)
      else (st', [HElem "p" 1 a s])
  | Heading lvl ils =>
      let '(st', s) := render_inlines_foot st ils in
      (st', [HElem ("h" ++ nat_str lvl) 1 a s])
  | Section bs =>
      let '(st', s) := render_bs_at st tight bs in
      (st', [HElem "section" 2 a s])
  | BlockQuote bs =>
      let '(st', s) := render_bs_at st tight bs in
      (st', [HElem "blockquote" 2 a s])
  | Div bs =>
      let '(st', s) := render_bs_at st tight bs in
      (st', [HElem "div" 2 a s])
  | OrderedList oa sp items =>
      let '(st', s) := render_items st sp items in
      (st', [HElem "ol" 2 (ol_attrs oa ++ a)%list s])
  | BulletList sp items =>
      let '(st', s) := render_items st sp items in
      (st', [HElem "ul" 2 a s])
  (* As `render_block`, with the counter threaded: a footnote reference
     inside a definition would otherwise fall through to the stateless
     path and be dropped. *)
  | DefinitionList _ items =>
      let '(st', s) := render_def_items st items in
      (st', [HElem "dl" 2 a s])
  | TaskList sp items =>
      let '(st', s) := render_task_items st sp items in
      (st', [HElem "ul" 2 (("class", "task-list") :: a) s])
  | Table caption rows =>
      let '(st1, s1) := render_caption_foot st caption in
      let '(st2, s2) := render_rows_foot st1 rows in
      (st2, [HElem "table" 2 a (s1 ++ s2)%list])
  (* The label is inline content like a term's, so a note referenced
     from it is numbered here rather than dropped by the stateless
     path. *)
  | Ext_keyed label b =>
      let '(st1, s1) := render_inlines_foot st label in
      let '(st2, s2) := render_bs_at st1 tight [b] in
      (st2, [HElem "dl" 2 (("class", "keyed") :: a)
               [HElem "dt" 1 [] s1; HElem "dd" 2 [] s2]])
  | _ => (st, render_block tight b a)
  end.

(* Right recursion, as `render_inlines_foot`. *)
Definition render_blocks_foot (st : foot_state) (bs : blocks)
  : foot_state * list helt :=
  (fix go (st0 : foot_state) (ns : blocks) : foot_state * list helt :=
     match ns with
     | [] => (st0, [])
     | Node _ a b :: rest =>
         let '(st1, s1) := render_block_foot st0 false b a in
         let '(st2, s2) := go st1 rest in
         (st2, (s1 ++ s2)%list)
     end) st bs.

Local Definition note_backlink (n : nat) : helt :=
  HElem "a" 0
    [("href", "#fnref" ++ nat_str n); ("role", "doc-backlink")]
    [HText "↩︎"].

(* The backlink goes inside the note's last paragraph where there is one
   and in a paragraph of its own otherwise.  djot.js decides that by
   matching `/<\/p>[\r\n]*$/` against the rendered string (`addBacklink`);
   on the tree it is a look at the last element, which is the same
   question asked of the structure rather than of its serialization. *)
Local Definition add_backlink (body : list helt) (n : nat) : list helt :=
  match rev body with
  | HElem tag nls a kids :: earlier =>
      if String.eqb tag "p"
      then rev (HElem tag nls a (kids ++ [note_backlink n])%list :: earlier)
      else (body ++ [HElem "p" 1 [] [note_backlink n]])%list
  | _ => (body ++ [HElem "p" 1 [] [note_backlink n]])%list
  end.

Local Fixpoint render_note_defs (st : foot_state) (notes : note_map)
  : foot_state * list (string * list helt) :=
  match notes with
  | [] => (st, [])
  | (label, bs) :: rest =>
      let '(st1, body) := render_blocks_foot st bs in
      let '(st2, rendered) := render_note_defs st1 rest in
      (st2, (label, body) :: rendered)
  end.

Local Fixpoint label_at (n : nat) (numbers : list (string * nat)) : option string :=
  match numbers with
  | [] => None
  | (label, n') :: rest =>
      if Nat.eqb n n' then Some label else label_at n rest
  end.

Local Definition rendered_note_at (n : nat) (st : foot_state)
  (rendered : list (string * list helt)) : list helt :=
  match label_at n (foot_numbers st) with
  | None => []
  | Some label =>
      match alist_lookup label rendered with Some s => s | None => [] end
  end.

Local Fixpoint render_note_items (fuel n : nat) (st : foot_state)
  (rendered : list (string * list helt)) : list helt :=
  match fuel with
  | O => []
  | S fuel' =>
      HElem "li" 2 [("id", "fn" ++ nat_str n)]
        (add_backlink (rendered_note_at n st rendered) n)
      :: render_note_items fuel' (S n) st rendered
  end.

Local Definition render_document_foot (blocks : blocks) (notes : note_map)
  : list helt :=
  let '(st1, body) := render_blocks_foot foot_initial blocks in
  if Nat.eqb (foot_next st1) 1 then body
  else
    let '(st2, rendered) := render_note_defs st1 notes in
    (body
     ++ [HElem "section" 2 [("role", "doc-endnotes")]
           [HVoid "hr" false []; HText nl;
            HElem "ol" 2 []
              (render_note_items (foot_next st2 - 1) 1 st2 rendered)]])%list.

End WithRefs.

(* Reference lookup changes only attributes on link and image elements.
   Erasing attributes from the output tree exposes the stable structure,
   including the text and nesting of inline children. *)
Fixpoint erase_helt_attrs (h : helt) : helt :=
  match h with
  | HText s => HText s
  | HRaw s => HRaw s
  | HVoid tag self _ => HVoid tag self []
  | HElem tag nls _ kids => HElem tag nls [] (map erase_helt_attrs kids)
  end.

Theorem render_inline_reference_shape :
  forall il refs refs' a,
    map erase_helt_attrs (render_inline refs il a) =
    map erase_helt_attrs (render_inline refs' il a).
Proof.
  apply (inline_ind2
    (fun il => forall refs refs' a,
      map erase_helt_attrs (render_inline refs il a) =
      map erase_helt_attrs (render_inline refs' il a))
    (fun ils => forall refs refs',
      map erase_helt_attrs (render_inlines refs ils) =
      map erase_helt_attrs (render_inlines refs' ils)));
    intros; cbn [render_inline render_inlines erase_helt_attrs];
    try reflexivity.
  all: try (cbn [map erase_helt_attrs]; f_equal; f_equal;
            exact (H refs refs')).
  - destruct tgt as [url|label].
    + cbn [map erase_helt_attrs]. f_equal. f_equal. exact (H refs refs').
    + destruct (lookup_reference label refs) as [[url a0]|];
        destruct (lookup_reference label refs') as [[url' a0']|];
        cbn [map erase_helt_attrs]; f_equal; f_equal;
        exact (H refs refs').
  - destruct tgt as [url|label]; [reflexivity|].
    destruct (lookup_reference label refs) as [[url a0]|];
      destruct (lookup_reference label refs') as [[url' a0']|]; reflexivity.
  - destruct qt; cbn [map erase_helt_attrs]; repeat rewrite map_app;
      f_equal; f_equal; exact (H refs refs').
  - rewrite !map_app. f_equal;
      [exact (H refs refs' a)|exact (H0 refs refs')].
Qed.

Theorem render_inlines_reference_shape :
  forall ils refs refs',
    map erase_helt_attrs (render_inlines refs ils) =
    map erase_helt_attrs (render_inlines refs' ils).
Proof.
  induction ils as [|[p a x] rest IH]; intros refs refs'; [reflexivity|].
  cbn [render_inlines]. rewrite !map_app.
  f_equal; [apply render_inline_reference_shape|apply IH].
Qed.

Local Definition foot_shape (x y : foot_state * list helt) : Prop :=
  fst x = fst y /\ map erase_helt_attrs (snd x) = map erase_helt_attrs (snd y).

Local Lemma foot_shape_elem : forall x y tag nls a a',
  foot_shape x y ->
  foot_shape
    (let '(st, s) := x in (st, [HElem tag nls a s]))
    (let '(st, s) := y in (st, [HElem tag nls a' s])).
Proof.
  intros [st s] [st' s'] tag nls a a' [Hs Hshape].
  unfold foot_shape in *. cbn [fst snd] in *. subst st'.
  split; [reflexivity|]. cbn [map erase_helt_attrs].
  rewrite Hshape. reflexivity.
Qed.

Theorem render_inline_foot_reference_shape :
  forall il st a refs refs',
    foot_shape (render_inline_foot refs st il a)
               (render_inline_foot refs' st il a).
Proof.
  pose (Q := fun (ils : inlines) => forall st refs refs',
    foot_shape (render_inlines_foot refs st ils) (render_inlines_foot refs' st ils)).
  apply (inline_ind2
    (fun il => forall st a refs refs',
      foot_shape (render_inline_foot refs st il a)
                 (render_inline_foot refs' st il a)) Q);
    intros; cbn [render_inline_foot];
    try (unfold foot_shape; split; reflexivity);
    try (eapply foot_shape_elem; exact (H st refs refs')).
  - destruct tgt as [url|label].
    + eapply foot_shape_elem. exact (H st refs refs').
    + destruct (lookup_reference label refs) as [[url a0]|];
        destruct (lookup_reference label refs') as [[url' a0']|];
        eapply foot_shape_elem; exact (H st refs refs').
  - unfold foot_shape. cbn [fst snd].
    split; [reflexivity|apply render_inline_reference_shape].
  - destruct qt.
    + change (foot_shape
        (let '(u,v) := render_inlines_foot refs st ils in
         (u, ([HText lsquo] ++ v ++ [HText rsquo])%list))
        (let '(u,v) := render_inlines_foot refs' st ils in
         (u, ([HText lsquo] ++ v ++ [HText rsquo])%list))).
      destruct (render_inlines_foot refs st ils) as [s1 o1] eqn:E1.
      destruct (render_inlines_foot refs' st ils) as [s2 o2] eqn:E2.
      specialize (H st refs refs'). unfold Q, foot_shape in H.
      rewrite E1, E2 in H. cbn [fst snd] in H.
      destruct H as [Hs Ho]. unfold foot_shape. cbn [fst snd].
      split; [exact Hs|]. repeat rewrite map_app. rewrite Ho. reflexivity.
    + change (foot_shape
        (let '(u,v) := render_inlines_foot refs st ils in
         (u, ([HText ldquo] ++ v ++ [HText rdquo])%list))
        (let '(u,v) := render_inlines_foot refs' st ils in
         (u, ([HText ldquo] ++ v ++ [HText rdquo])%list))).
      destruct (render_inlines_foot refs st ils) as [s1 o1] eqn:E1.
      destruct (render_inlines_foot refs' st ils) as [s2 o2] eqn:E2.
      specialize (H st refs refs'). unfold Q, foot_shape in H.
      rewrite E1, E2 in H. cbn [fst snd] in H.
      destruct H as [Hs Ho]. unfold foot_shape. cbn [fst snd].
      split; [exact Hs|]. repeat rewrite map_app. rewrite Ho. reflexivity.
  - unfold Q. intros st refs refs'. cbn [render_inlines_foot].
    destruct (render_inline_foot refs st x a) as [s1 o1] eqn:E1.
    destruct (render_inline_foot refs' st x a) as [s2 o2] eqn:E2.
    pose proof (H st a refs refs') as Hhead.
    unfold foot_shape in Hhead. rewrite E1, E2 in Hhead.
    cbn [fst snd] in Hhead. destruct Hhead as [Hs Ho]. subst s2.
    change (foot_shape
      (let '(u,v) := render_inlines_foot refs s1 rest in (u, (o1 ++ v)%list))
      (let '(u,v) := render_inlines_foot refs' s1 rest in (u, (o2 ++ v)%list))).
    destruct (render_inlines_foot refs s1 rest) as [s3 o3] eqn:E3.
    destruct (render_inlines_foot refs' s1 rest) as [s4 o4] eqn:E4.
    pose proof (H0 s1 refs refs') as Htail.
    unfold Q, foot_shape in Htail. rewrite E3, E4 in Htail.
    cbn [fst snd] in Htail. destruct Htail as [Hs HoTail].
    unfold foot_shape. cbn [fst snd].
    split; [exact Hs|]. rewrite !map_app, Ho, HoTail. reflexivity.
Qed.

Local Lemma render_inlines_foot_cons : forall refs st p a x rest,
  render_inlines_foot refs st (Node p a x :: rest)
  = let '(st1, s1) := render_inline_foot refs st x a in
    let '(st2, s2) := render_inlines_foot refs st1 rest in
    (st2, (s1 ++ s2)%list).
Proof. reflexivity. Qed.

Theorem render_inlines_foot_reference_shape :
  forall ils st refs refs',
    foot_shape (render_inlines_foot refs st ils)
               (render_inlines_foot refs' st ils).
Proof.
  induction ils as [|[p a x] rest IH]; intros st refs refs';
    [split; reflexivity|].
  rewrite !render_inlines_foot_cons.
  destruct (render_inline_foot refs st x a) as [s1 o1] eqn:E1.
  destruct (render_inline_foot refs' st x a) as [s2 o2] eqn:E2.
  pose proof (render_inline_foot_reference_shape x st a refs refs') as Hx.
  unfold foot_shape in Hx. rewrite E1, E2 in Hx.
  cbn [fst snd] in Hx. destruct Hx as [Hs Ho]. subst s2.
  destruct (render_inlines_foot refs s1 rest) as [s3 o3] eqn:E3.
  destruct (render_inlines_foot refs' s1 rest) as [s4 o4] eqn:E4.
  pose proof (IH s1 refs refs') as Hr.
  unfold foot_shape in Hr. rewrite E3, E4 in Hr.
  cbn [fst snd] in Hr. destruct Hr as [Hs Hr].
  unfold foot_shape. cbn [fst snd].
  split; [exact Hs|]. rewrite !map_app, Ho, Hr. reflexivity.
Qed.

Local Lemma render_caption_foot_reference_shape :
  forall caption st refs refs',
    foot_shape (render_caption_foot refs st caption)
               (render_caption_foot refs' st caption).
Proof.
  intros [ils|] st refs refs'; [|unfold foot_shape; split; reflexivity].
  cbn [render_caption_foot].
  apply foot_shape_elem, render_inlines_foot_reference_shape.
Qed.

Local Definition foot_cell_shape (x y : foot_state * helt) : Prop :=
  fst x = fst y /\ erase_helt_attrs (snd x) = erase_helt_attrs (snd y).

Local Lemma render_cell_foot_reference_shape :
  forall c st refs refs',
    foot_cell_shape (render_cell_foot refs st c)
                    (render_cell_foot refs' st c).
Proof.
  intros [ct al ils] st refs refs'. cbn [render_cell_foot].
  destruct (render_inlines_foot refs st ils) as [s1 o1] eqn:E1.
  destruct (render_inlines_foot refs' st ils) as [s2 o2] eqn:E2.
  pose proof (render_inlines_foot_reference_shape ils st refs refs') as H.
  unfold foot_shape in H. rewrite E1, E2 in H.
  cbn [fst snd] in H. destruct H as [Hs Ho].
  unfold foot_cell_shape. cbn [fst snd erase_helt_attrs].
  split; [exact Hs|]. rewrite Ho. reflexivity.
Qed.

Local Lemma render_cells_foot_reference_shape :
  forall cells st refs refs',
    foot_shape (render_cells_foot refs st cells)
               (render_cells_foot refs' st cells).
Proof.
  induction cells as [|c rest IH]; intros st refs refs';
    [unfold foot_shape; cbn; split; reflexivity|].
  cbn [render_cells_foot].
  destruct (render_cell_foot refs st c) as [s1 e1] eqn:E1.
  destruct (render_cell_foot refs' st c) as [s2 e2] eqn:E2.
  pose proof (render_cell_foot_reference_shape c st refs refs') as Hhead.
  unfold foot_cell_shape in Hhead. rewrite E1, E2 in Hhead.
  cbn [fst snd] in Hhead. destruct Hhead as [Hs He]. subst s2.
  destruct (render_cells_foot refs s1 rest) as [s3 es1] eqn:E3.
  destruct (render_cells_foot refs' s1 rest) as [s4 es2] eqn:E4.
  pose proof (IH s1 refs refs') as Htail.
  unfold foot_shape in Htail. rewrite E3, E4 in Htail.
  cbn [fst snd] in Htail. destruct Htail as [Ht Ho].
  unfold foot_shape. cbn [fst snd map].
  split; [exact Ht|]. rewrite He, Ho. reflexivity.
Qed.

Local Lemma render_rows_foot_reference_shape :
  forall rows st refs refs',
    foot_shape (render_rows_foot refs st rows)
               (render_rows_foot refs' st rows).
Proof.
  induction rows as [|row rest IH]; intros st refs refs';
    [unfold foot_shape; cbn; split; reflexivity|].
  cbn [render_rows_foot].
  destruct (render_cells_foot refs st row) as [s1 es1] eqn:E1.
  destruct (render_cells_foot refs' st row) as [s2 es2] eqn:E2.
  pose proof (render_cells_foot_reference_shape row st refs refs') as Hhead.
  unfold foot_shape in Hhead. rewrite E1, E2 in Hhead.
  cbn [fst snd] in Hhead. destruct Hhead as [Hs He]. subst s2.
  destruct (render_rows_foot refs s1 rest) as [s3 out1] eqn:E3.
  destruct (render_rows_foot refs' s1 rest) as [s4 out2] eqn:E4.
  pose proof (IH s1 refs refs') as Htail.
  unfold foot_shape in Htail. rewrite E3, E4 in Htail.
  cbn [fst snd] in Htail. destruct Htail as [Ht Ho].
  unfold foot_shape. cbn [fst snd map erase_helt_attrs].
  split; [exact Ht|]. rewrite He, Ho. reflexivity.
Qed.

Local Definition render_bs_foot (refs : reference_map) (st : foot_state)
  (tight : bool) (bs : blocks) : foot_state * list helt :=
  (fix go (st0 : foot_state) (t : bool) (ns : blocks)
     : foot_state * list helt :=
     match ns with
     | [] => (st0, [])
     | Node _ a b :: rest =>
         let '(st1, s1) := render_block_foot refs st0 t b a in
         let '(st2, s2) := go st1 t rest in
         (st2, (s1 ++ s2)%list)
     end) st tight bs.

Local Definition render_items_foot (refs : reference_map)
  : foot_state -> list_spacing -> list blocks -> foot_state * list helt :=
  fix goi (st : foot_state) (sp : list_spacing) (items : list blocks)
    {struct items} : foot_state * list helt :=
    match items with
    | [] => (st, [])
    | it :: rest =>
        let t := match sp with Tight => true | Loose => false end in
        let '(st1, s1) := render_bs_foot refs st t it in
        let '(st2, s2) := goi st1 sp rest in
        (st2, HElem "li" 2 [] s1 :: s2)
    end.

Local Definition render_task_items_foot (refs : reference_map)
  : foot_state -> list_spacing -> list (task_status * blocks)
    -> foot_state * list helt :=
  fix got (st : foot_state) (sp : list_spacing)
    (items : list (task_status * blocks)) {struct items}
    : foot_state * list helt :=
    match items with
    | [] => (st, [])
    | (chk, it) :: rest =>
        let t := match sp with Tight => true | Loose => false end in
        let '(st1, s1) := render_bs_foot refs st t it in
        let '(st2, s2) := got st1 sp rest in
        (st2, HElem "li" 2 [] (checkbox_elt chk :: HText nl :: s1) :: s2)
    end.

Local Definition render_def_items_foot (refs : reference_map) (tight : bool)
  : foot_state -> list (inlines * blocks) -> foot_state * list helt :=
  fix god (st : foot_state) (items : list (inlines * blocks))
    {struct items} : foot_state * list helt :=
    match items with
    | [] => (st, [])
    | (term, it) :: rest =>
        let '(st1, s1) := render_inlines_foot refs st term in
        let '(st2, s2) := render_bs_foot refs st1 tight it in
        let '(st3, s3) := god st2 rest in
        (st3, HElem "dt" 1 [] s1 :: HElem "dd" 2 [] s2 :: s3)
    end.

Local Lemma foot_shape_bind :
  forall {A} (x y : foot_state * list helt)
    (f g : foot_state -> list helt -> foot_state * A)
    (R : foot_state * A -> foot_state * A -> Prop),
    foot_shape x y ->
    (forall st o o', map erase_helt_attrs o = map erase_helt_attrs o' ->
       R (f st o) (g st o')) ->
    R (let '(st, o) := x in f st o) (let '(st, o) := y in g st o).
Proof.
  intros A [st o] [st' o'] f g R [Hs Ho] H. cbn [fst snd] in *. subst st'.
  exact (H st o o' Ho).
Qed.

Theorem render_block_foot_reference_shape :
  forall b st tight a refs refs',
    foot_shape (render_block_foot refs st tight b a)
               (render_block_foot refs' st tight b a).
Proof.
  intros b. induction b using block_ind2 with
    (Q := fun bs => forall st t refs refs',
       foot_shape (render_bs_foot refs st t bs) (render_bs_foot refs' st t bs))
    (R := fun its => forall st sp refs refs',
       foot_shape (render_items_foot refs st sp its)
                  (render_items_foot refs' st sp its))
    (K := fun its => forall st sp refs refs',
       foot_shape (render_task_items_foot refs st sp its)
                  (render_task_items_foot refs' st sp its))
    (D := fun its => forall st t refs refs',
       foot_shape (render_def_items_foot refs t st its)
                  (render_def_items_foot refs' t st its));
    intros; cbn [render_block_foot];
    unfold render_bs_foot, render_items_foot, render_task_items_foot,
      render_def_items_foot; cbn iota beta;
    repeat (eapply foot_shape_bind;
      [first [apply IHb | apply IHb0 | exact (IHb _ tight refs refs')
             | apply render_inlines_foot_reference_shape
             | apply render_caption_foot_reference_shape
             | apply render_rows_foot_reference_shape]|];
      intros ? ? ? ?);
    try destruct tight;
    unfold foot_shape; cbn [fst snd]; split; try reflexivity;
    cbn [map erase_helt_attrs]; rewrite ?map_app; congruence.
Qed.

Local Lemma render_blocks_foot_cons : forall refs st p a b rest,
  render_blocks_foot refs st (Node p a b :: rest)
  = let '(st1, s1) := render_block_foot refs st false b a in
    let '(st2, s2) := render_blocks_foot refs st1 rest in
    (st2, (s1 ++ s2)%list).
Proof. reflexivity. Qed.

Theorem render_blocks_foot_reference_shape :
  forall bs st refs refs',
    foot_shape (render_blocks_foot refs st bs)
               (render_blocks_foot refs' st bs).
Proof.
  induction bs as [|[p a b] rest IH]; intros st refs refs';
    [split; reflexivity|].
  rewrite !render_blocks_foot_cons.
  eapply foot_shape_bind;
    [apply render_block_foot_reference_shape|intros st1 o o' Ho].
  eapply foot_shape_bind; [apply IH|intros st2 r r' Hr].
  unfold foot_shape. cbn [fst snd].
  split; [reflexivity|]. rewrite !map_app, Ho, Hr. reflexivity.
Qed.

(* Note bodies are keyed by label; only the bodies' attributes may differ. *)
Local Definition erase_rendered (r : list (string * list helt))
  : list (string * list helt) :=
  map (fun p => (fst p, map erase_helt_attrs (snd p))) r.

Local Definition notes_shape (x y : foot_state * list (string * list helt))
  : Prop :=
  fst x = fst y /\ erase_rendered (snd x) = erase_rendered (snd y).

Local Lemma render_note_defs_reference_shape :
  forall notes st refs refs',
    notes_shape (render_note_defs refs st notes)
                (render_note_defs refs' st notes).
Proof.
  induction notes as [|[label bs] rest IH]; intros st refs refs';
    [split; reflexivity|].
  cbn [render_note_defs].
  eapply foot_shape_bind;
    [apply render_blocks_foot_reference_shape|intros st1 o o' Ho].
  destruct (render_note_defs refs st1 rest) as [s2 r2] eqn:E2.
  destruct (render_note_defs refs' st1 rest) as [s3 r3] eqn:E3.
  pose proof (IH st1 refs refs') as [Hs Hr].
  rewrite E2, E3 in Hs, Hr. cbn [fst snd] in Hs, Hr.
  split; [exact Hs|]. unfold erase_rendered in *. cbn [map fst snd].
  rewrite Ho, Hr. reflexivity.
Qed.

Local Lemma alist_lookup_erase_rendered : forall k r,
  alist_lookup k (erase_rendered r) =
  option_map (map erase_helt_attrs) (alist_lookup k r).
Proof.
  intros k r. induction r as [|[k' v] rest IH]; [reflexivity|].
  cbn [erase_rendered map alist_lookup fst snd].
  destruct (String.eqb k k'); [reflexivity|exact IH].
Qed.

Local Lemma rendered_note_at_reference_shape : forall n st r r',
  erase_rendered r = erase_rendered r' ->
  map erase_helt_attrs (rendered_note_at n st r) =
  map erase_helt_attrs (rendered_note_at n st r').
Proof.
  intros n st r r' Hr. unfold rendered_note_at.
  destruct (label_at n (foot_numbers st)) as [label|]; [|reflexivity].
  pose proof (alist_lookup_erase_rendered label r) as E.
  rewrite Hr, alist_lookup_erase_rendered in E.
  destruct (alist_lookup label r), (alist_lookup label r');
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. symmetry. exact E.
Qed.

Local Lemma add_backlink_reference_shape : forall body body' n,
  map erase_helt_attrs body = map erase_helt_attrs body' ->
  map erase_helt_attrs (add_backlink body n) =
  map erase_helt_attrs (add_backlink body' n).
Proof.
  intros body body' n H. unfold add_backlink.
  assert (Hr : map erase_helt_attrs (rev body) =
               map erase_helt_attrs (rev body'))
    by (rewrite !map_rev, H; reflexivity).
  destruct (rev body) as [|h t], (rev body') as [|h' t'];
    cbn [map] in Hr; try discriminate;
    [rewrite !map_app, H; reflexivity|].
  injection Hr as Hh Ht.
  destruct h, h'; cbn [erase_helt_attrs] in Hh; try discriminate;
    try (rewrite !map_app, H; reflexivity).
  injection Hh as Htag Hnls Hkids. subst tag0 nls0.
  destruct (String.eqb tag "p");
    [|rewrite !map_app, H; reflexivity].
  rewrite !map_rev. cbn [map erase_helt_attrs].
  rewrite !map_app, Hkids, Ht. reflexivity.
Qed.

Local Lemma render_note_items_reference_shape : forall fuel n st r r',
  erase_rendered r = erase_rendered r' ->
  map erase_helt_attrs (render_note_items fuel n st r) =
  map erase_helt_attrs (render_note_items fuel n st r').
Proof.
  induction fuel as [|fuel IH]; intros n st r r' Hr; [reflexivity|].
  cbn [render_note_items map erase_helt_attrs].
  rewrite (add_backlink_reference_shape _ _ n
             (rendered_note_at_reference_shape n st r r' Hr)).
  rewrite (IH (S n) st r r' Hr). reflexivity.
Qed.

Theorem render_document_foot_reference_shape : forall bs notes refs refs',
  map erase_helt_attrs (render_document_foot refs bs notes) =
  map erase_helt_attrs (render_document_foot refs' bs notes).
Proof.
  intros bs notes refs refs'. unfold render_document_foot.
  pose proof (render_blocks_foot_reference_shape bs foot_initial refs refs')
    as Hb.
  destruct (render_blocks_foot refs foot_initial bs) as [s1 b1].
  destruct (render_blocks_foot refs' foot_initial bs) as [s1' b1'].
  destruct Hb as [Hs Hb]. cbn [fst snd] in Hs, Hb. subst s1'.
  destruct (Nat.eqb (foot_next s1) 1); [exact Hb|].
  pose proof (render_note_defs_reference_shape notes s1 refs refs') as Hn.
  destruct (render_note_defs refs s1 notes) as [s2 r].
  destruct (render_note_defs refs' s1 notes) as [s2' r'].
  destruct Hn as [Hs Hr]. cbn [fst snd] in Hs, Hr. subst s2'.
  rewrite !map_app, Hb. cbn [map erase_helt_attrs].
  rewrite (render_note_items_reference_shape _ 1 s2 r r' Hr). reflexivity.
Qed.

(* The local block renderer uses this recursion at each container. *)
Local Definition render_bs_at (refs : reference_map) (tight : bool) (bs : blocks)
  : list helt :=
  (fix go (t : bool) (ns : blocks) : list helt :=
     match ns with
     | [] => []
     | Node _ a b :: rest => (render_block refs t b a ++ go t rest)%list
     end) tight bs.

Local Lemma render_bs_at_flat_map : forall refs tight bs,
  render_bs_at refs tight bs =
  flat_map (fun n => match n with Node _ a b => render_block refs tight b a end) bs.
Proof.
  intros refs tight bs. induction bs as [|[p a b] rest IH]; [reflexivity|].
  cbn [render_bs_at flat_map]. rewrite <- IH. reflexivity.
Qed.

Theorem render_blocks_reference_shape :
  forall bs refs refs',
    map erase_helt_attrs (render_blocks refs bs) =
    map erase_helt_attrs (render_blocks refs' bs).
Proof.
  pose (Q := fun (bs : blocks) => forall tight refs refs',
    map erase_helt_attrs
      (flat_map (fun n => match n with Node _ a b => render_block refs tight b a end) bs) =
    map erase_helt_attrs
      (flat_map (fun n => match n with Node _ a b => render_block refs' tight b a end) bs)).
  assert (Hb : forall b tight a refs refs',
    map erase_helt_attrs (render_block refs tight b a) =
    map erase_helt_attrs (render_block refs' tight b a)).
  { intros b. induction b using block_ind2 with
      (Q := Q) (R := Forall Q)
      (D := Forall (fun ti => Q (snd ti)))
      (K := Forall (fun ti => Q (snd ti)));
      intros; try reflexivity.
    - destruct tight; cbn [render_block map erase_helt_attrs];
        [rewrite !map_app|];
        rewrite (render_inlines_reference_shape ils refs refs'); reflexivity.
    - cbn [render_block map erase_helt_attrs]. f_equal. f_equal.
      change (map erase_helt_attrs (render_bs_at refs tight bs) =
              map erase_helt_attrs (render_bs_at refs' tight bs)).
      rewrite !render_bs_at_flat_map. exact (IHb tight refs refs').
    - cbn [render_block map erase_helt_attrs].
      rewrite (render_inlines_reference_shape ils refs refs'). reflexivity.
    - cbn [render_block map erase_helt_attrs]. f_equal. f_equal.
      change (map erase_helt_attrs (render_bs_at refs tight bs) =
              map erase_helt_attrs (render_bs_at refs' tight bs)).
      rewrite !render_bs_at_flat_map. exact (IHb tight refs refs').
    - cbn [render_block map erase_helt_attrs]. f_equal. f_equal.
      change (map erase_helt_attrs (render_bs_at refs tight bs) =
              map erase_helt_attrs (render_bs_at refs' tight bs)).
      rewrite !render_bs_at_flat_map. exact (IHb tight refs refs').
    - cbn [render_block map erase_helt_attrs]. f_equal. f_equal.
      induction IHb as [|it rest Hit Hrest IH]; [reflexivity|].
      cbn [map erase_helt_attrs]. f_equal.
      + f_equal.
        change (map erase_helt_attrs
                  (render_bs_at refs (match sp with Tight => true | Loose => false end) it) =
                map erase_helt_attrs
                  (render_bs_at refs' (match sp with Tight => true | Loose => false end) it)).
        rewrite !render_bs_at_flat_map. exact (Hit _ refs refs').
      + exact IH.
    - cbn [render_block map erase_helt_attrs]. f_equal. f_equal.
      induction IHb as [|it rest Hit Hrest IH]; [reflexivity|].
      cbn [map erase_helt_attrs]. f_equal.
      + f_equal.
        change (map erase_helt_attrs
                  (render_bs_at refs (match sp with Tight => true | Loose => false end) it) =
                map erase_helt_attrs
                  (render_bs_at refs' (match sp with Tight => true | Loose => false end) it)).
        rewrite !render_bs_at_flat_map. exact (Hit _ refs refs').
      + exact IH.
    - cbn [render_block map erase_helt_attrs]. f_equal. f_equal.
      induction IHb as [|[st it] rest Hit Hrest IH]; [reflexivity|].
      cbn [map erase_helt_attrs]. f_equal. f_equal. f_equal. f_equal.
      change (map erase_helt_attrs
                (render_bs_at refs (match sp with Tight => true | Loose => false end) it) =
              map erase_helt_attrs
                (render_bs_at refs' (match sp with Tight => true | Loose => false end) it)).
      rewrite !render_bs_at_flat_map. exact (Hit _ refs refs').
      exact IH.
    - cbn [render_block map erase_helt_attrs]. f_equal. f_equal.
      induction IHb as [|[term it] rest Hit Hrest IH]; [reflexivity|].
      cbn [map erase_helt_attrs].
      rewrite (render_inlines_reference_shape term refs refs').
      f_equal. f_equal. f_equal.
      change (map erase_helt_attrs (render_bs_at refs tight it) =
              map erase_helt_attrs (render_bs_at refs' tight it)).
      rewrite !render_bs_at_flat_map. exact (Hit tight refs refs').
      exact IH.
    - cbn [render_block map erase_helt_attrs]. f_equal. f_equal.
      rewrite !map_app. f_equal.
      + destruct caption as [ils|]; cbn [render_caption map erase_helt_attrs];
          [rewrite (render_inlines_reference_shape ils refs refs')|]; reflexivity.
      + induction rows as [|row rest IH]; [reflexivity|].
        cbn [map]. f_equal.
        * cbn [render_row erase_helt_attrs]. f_equal.
          induction row as [|[ct al ils] row IHrow]; [reflexivity|].
          cbn [map render_cell erase_helt_attrs].
          rewrite (render_inlines_reference_shape ils refs refs').
          f_equal. exact IHrow.
        * exact IH.
    - cbn [render_block map erase_helt_attrs].
      rewrite (render_inlines_reference_shape label refs refs').
      destruct b as [p a' x]. cbn [flat_map map] in IHb |- *.
      rewrite !app_nil_r in *. f_equal. f_equal. f_equal. f_equal. f_equal.
      specialize (IHb tight refs refs').
      cbn [flat_map map] in IHb. rewrite !app_nil_r in IHb. exact IHb.
    - unfold Q. intros. reflexivity.
    - unfold Q in *. intros tight refs refs'. cbn [flat_map].
      rewrite !map_app. f_equal; [apply IHb|apply IHb0].
    - constructor.
    - constructor; assumption.
    - constructor.
    - constructor; assumption.
    - constructor.
    - constructor; assumption. }
  intros bs refs refs'. induction bs as [|[p a b] rest IH]; [reflexivity|].
  cbn [render_blocks render_node flat_map]. rewrite !map_app.
  f_equal; [apply Hb|exact IH].
Qed.

(* Explicit definitions first, so a label defined both ways resolves to
   the explicit one. *)
Local Definition doc_refs (d : doc) : reference_map :=
  (doc_references d ++ doc_auto_references d)%list.

(* The output tree of a whole document, named because the safety
   statements below are about it rather than about its serialization. *)
Definition html_tree (d : doc) : list helt :=
  render_document_foot (doc_refs d) (doc_blocks d) (doc_footnotes d).

(* Reference definitions reach the output only through link and image
   attributes, and footnote numbering does not depend on them. *)
Theorem html_tree_reference_shape : forall d d',
  doc_blocks d = doc_blocks d' ->
  doc_footnotes d = doc_footnotes d' ->
  map erase_helt_attrs (html_tree d) = map erase_helt_attrs (html_tree d').
Proof.
  intros d d' Hb Hn. unfold html_tree. rewrite Hb, Hn.
  apply render_document_foot_reference_shape.
Qed.

Definition render_html (d : doc) : string := serialize_flat (html_tree d).

(* The document renderer: djot in, HTML out. *)
Definition convert (s : string) : string := render_html (parse_doc s).

Example convert_two_paras :
  convert "hi
there

bye" = "<p>hi
there</p>
<p>bye</p>
".
Proof. reflexivity. Qed.

Example convert_list_tight :
  convert "- a
- b" = "<ul>
<li>
a
</li>
<li>
b
</li>
</ul>
".
Proof. reflexivity. Qed.

Example convert_list_loose :
  convert "- a

- b" = "<ul>
<li>
<p>a</p>
</li>
<li>
<p>b</p>
</li>
</ul>
".
Proof. reflexivity. Qed.

(* Tightness is rendering state, so it reaches a paragraph nested inside
   a container within the item -- the witness that a per-item match on
   direct children gets wrong. *)
Example convert_list_tight_through_quote :
  convert "- > a" = "<ul>
<li>
<blockquote>
a
</blockquote>
</li>
</ul>
".
Proof. reflexivity. Qed.

(* ...and a loose item keeps the tag in the same position. *)
Example convert_list_loose_through_quote :
  convert "- > a

- b" = "<ul>
<li>
<blockquote>
<p>a</p>
</blockquote>
</li>
<li>
<p>b</p>
</li>
</ul>
".
Proof. reflexivity. Qed.

(* A nested list inside a tight item keeps its own tags; only the
   paragraph loses its <p>. *)
Example convert_list_nested :
  convert "- a

  - b" = "<ul>
<li>
a
<ul>
<li>
b
</li>
</ul>
</li>
</ul>
".
Proof. reflexivity. Qed.

(*
Task lists
==========

Read off djot.js (`.project/260822.task-lists.md`).
*)

Example convert_tasklist :
  convert "- [ ] a
- [x] b" = "<ul class=""task-list"">
<li>
<input disabled="""" type=""checkbox""/>
a
</li>
<li>
<input disabled="""" type=""checkbox"" checked=""""/>
b
</li>
</ul>
".
Proof. reflexivity. Qed.

(* The checkbox is outside the tightness: it sits between `<li>` and the
   item's content whether or not that content keeps its `<p>`. *)
Example convert_tasklist_loose :
  convert "- [ ] a

- [x] b" = "<ul class=""task-list"">
<li>
<input disabled="""" type=""checkbox""/>
<p>a</p>
</li>
<li>
<input disabled="""" type=""checkbox"" checked=""""/>
<p>b</p>
</li>
</ul>
".
Proof. reflexivity. Qed.

(* A task list and a bullet list do not merge: `-X` and `-` are
   different styles, so the first list closes. *)
Example convert_tasklist_not_bullet :
  convert "- [ ] a
- b" = "<ul class=""task-list"">
<li>
<input disabled="""" type=""checkbox""/>
a
</li>
</ul>
<ul>
<li>
b
</li>
</ul>
".
Proof. reflexivity. Qed.

(* The class precedes the node's own attributes, as `ol_attrs` does. *)
Example convert_tasklist_attrs :
  convert "{#i}
- [ ] a" = "<ul class=""task-list"" id=""i"">
<li>
<input disabled="""" type=""checkbox""/>
a
</li>
</ul>
".
Proof. reflexivity. Qed.

(* A marker with nothing after it is an item with no content. *)
Example convert_tasklist_empty :
  convert "- [ ]" = "<ul class=""task-list"">
<li>
<input disabled="""" type=""checkbox""/>
</li>
</ul>
".
Proof. reflexivity. Qed.

(*
Definition lists
================

Read off djot.js (`.project/260822.definition-lists.md`).
*)

(* The term is the item's first paragraph, and the blank line is what
   separates it from the definition -- without one they are the same
   paragraph and the definition is empty. *)
Example convert_deflist :
  convert ": apple

  red fruit" = "<dl>
<dt>apple</dt>
<dd>
<p>red fruit</p>
</dd>
</dl>
".
Proof. reflexivity. Qed.

Example convert_deflist_term_only :
  convert ": apple
  red fruit" = "<dl>
<dt>apple
red fruit</dt>
<dd>
</dd>
</dl>
".
Proof. reflexivity. Qed.

(* An item whose first block is not a paragraph has an empty term and
   keeps everything.  The heading's auto-identifier is
   `Document.Ids.of_block` reaching into a definition. *)
Example convert_deflist_no_term :
  convert ": # h" = "<dl>
<dt></dt>
<dd>
<h1 id=""h"">h</h1>
</dd>
</dl>
".
Proof. reflexivity. Qed.

(* A bare marker is a list of one empty item. *)
Example convert_deflist_bare :
  convert ":" = "<dl>
<dt></dt>
<dd>
</dd>
</dl>
".
Proof. reflexivity. Qed.

(* Two colons are not a marker and three are a div: `classify` tests
   `div_open` before `list_marker`. *)
Example convert_deflist_two_colons :
  convert ":: a" = "<p>:: a</p>
".
Proof. reflexivity. Qed.

Example convert_deflist_three_colons :
  convert "::: a
:::" = "<div class=""a"">
</div>
".
Proof. reflexivity. Qed.

(* The `dd` is rendered at the *incoming* tightness, not at the list's:
   a definition inside a tight bullet item loses its `<p>`, and the blank
   line inside it arms the definition list rather than the bullet list,
   so the outer list stays tight.  Both halves are djot.js's, and djoths
   renders the first `<dd>` bare in *both* documents. *)
Example convert_deflist_inherits_tight :
  convert "- : t

    d
- x" = "<ul>
<li>
<dl>
<dt>t</dt>
<dd>
d
</dd>
</dl>
</li>
<li>
x
</li>
</ul>
".
Proof. reflexivity. Qed.

(*
Reference resolution
====================
*)

Example convert_reference_resolved :
  convert "[a]: /u

[text][a]" = "<p><a href=""/u"">text</a></p>
".
Proof. reflexivity. Qed.

(* A collapsed reference takes its label from the link text. *)
Example convert_reference_collapsed :
  convert "[a]: /u

[a][]" = "<p><a href=""/u"">a</a></p>
".
Proof. reflexivity. Qed.

(* The definition's own attributes follow the destination and precede
   the node's own. *)
Example convert_reference_attributes :
  convert "{#x .c}
[a]: /u

[a][]" = "<p><a href=""/u"" id=""x"" class=""c"">a</a></p>
".
Proof. reflexivity. Qed.

(* A key the link carries itself wins, and the definition's copy is
   dropped rather than emitted beside it. *)
Example convert_reference_attributes_link_wins :
  convert "{title=foo .a}
[a]: /u

[a][]{title=bar .b}" = "<p><a href=""/u"" title=""bar"" class=""b"">a</a></p>
".
Proof. reflexivity. Qed.

(* Per key, not all-or-nothing: the definition keeps what the link does
   not spell. *)
Example convert_reference_attributes_merge_by_key :
  convert "{title=foo}
[a]: /u

[a][]{.b}" = "<p><a href=""/u"" title=""foo"" class=""b"">a</a></p>
".
Proof. reflexivity. Qed.

(* An unresolved label renders as a targetless link, as djot.js does
   (with a warning we do not emit). *)
Example convert_reference_unresolved :
  convert "[a][b]" = "<p><a>a</a></p>
".
Proof. reflexivity. Qed.

(* An implicit heading reference resolves when no explicit definition
   claims the label; an explicit one wins. *)
Example convert_reference_auto :
  convert "# Intro

[Intro][]" = "<section id=""Intro"">
<h1>Intro</h1>
<p><a href=""#Intro"">Intro</a></p>
</section>
".
Proof. reflexivity. Qed.

(* A heading with an explicit id still registers the implicit reference,
   pointed at the id the spec gave it. *)
Example convert_reference_auto_explicit_id :
  convert "{#foo}
# Intro

[Intro][]" = "<section id=""foo"">
<h1>Intro</h1>
<p><a href=""#foo"">Intro</a></p>
</section>
".
Proof. reflexivity. Qed.

Example convert_reference_explicit_beats_auto :
  convert "# Intro

[Intro]: /elsewhere

[Intro][]" = "<section id=""Intro"">
<h1>Intro</h1>
<p><a href=""/elsewhere"">Intro</a></p>
</section>
".
Proof. reflexivity. Qed.

Example convert_reference_image :
  convert "[a]: /i.png

![alt][a]" = "<p><img alt=""alt"" src=""/i.png""></p>
".
Proof. reflexivity. Qed.

(* Footnote numbers follow first reference order, not definition order. *)
Example convert_footnotes_reference_order :
  convert "[^b] [^a]

[^a]: A

[^b]: B" = "<p><a id=""fnref1"" href=""#fn1"" role=""doc-noteref""><sup>1</sup></a> <a id=""fnref2"" href=""#fn2"" role=""doc-noteref""><sup>2</sup></a></p>
<section role=""doc-endnotes"">
<hr>
<ol>
<li id=""fn1"">
<p>B<a href=""#fnref1"" role=""doc-backlink"">↩︎</a></p>
</li>
<li id=""fn2"">
<p>A<a href=""#fnref2"" role=""doc-backlink"">↩︎</a></p>
</li>
</ol>
</section>
".
Proof. reflexivity. Qed.

Example convert_footnote_repeated_reference :
  convert "[^a] [^a]

[^a]: A" = "<p><a id=""fnref1"" href=""#fn1"" role=""doc-noteref""><sup>1</sup></a> <a href=""#fn1"" role=""doc-noteref""><sup>1</sup></a></p>
<section role=""doc-endnotes"">
<hr>
<ol>
<li id=""fn1"">
<p>A<a href=""#fnref1"" role=""doc-backlink"">↩︎</a></p>
</li>
</ol>
</section>
".
Proof. reflexivity. Qed.

(* Undefined references retain their numbered slot and an empty note body. *)
Example convert_footnote_undefined :
  convert "[^z]" = "<p><a id=""fnref1"" href=""#fn1"" role=""doc-noteref""><sup>1</sup></a></p>
<section role=""doc-endnotes"">
<hr>
<ol>
<li id=""fn1"">
<p><a href=""#fnref1"" role=""doc-backlink"">↩︎</a></p>
</li>
</ol>
</section>
".
Proof. reflexivity. Qed.

(* Rendering note bodies can discover and number further notes. *)
Example convert_footnote_reference_in_note :
  convert "[^a]

[^a]: A [^b]

[^b]: B" = "<p><a id=""fnref1"" href=""#fn1"" role=""doc-noteref""><sup>1</sup></a></p>
<section role=""doc-endnotes"">
<hr>
<ol>
<li id=""fn1"">
<p>A <a id=""fnref2"" href=""#fn2"" role=""doc-noteref""><sup>2</sup></a><a href=""#fnref1"" role=""doc-backlink"">↩︎</a></p>
</li>
<li id=""fn2"">
<p>B<a href=""#fnref2"" role=""doc-backlink"">↩︎</a></p>
</li>
</ol>
</section>
".
Proof. reflexivity. Qed.

(* A table: alignment is a style attribute, a header row is `th`, and a
   cell's footnote reference is numbered in source order like any other
   (all three measured against djot.js). *)
Example convert_table_aligned :
  convert "| a | b |
|---|--:|
| c | d |"
  = "<table>
<tr>
<th>a</th>
<th style=""text-align: right;"">b</th>
</tr>
<tr>
<td>c</td>
<td style=""text-align: right;"">d</td>
</tr>
</table>
".
Proof. vm_compute. reflexivity. Qed.

(* Separators alone: a table with no rows, which djot.js renders as an
   empty table rather than as nothing. *)
Example convert_table_no_rows :
  convert "|---|" = "<table>
</table>
".
Proof. vm_compute. reflexivity. Qed.

Example convert_table_footnote_cell :
  convert "| a[^n] |

[^n]: note"
  = "<table>
<tr>
<td>a<a id=""fnref1"" href=""#fn1"" role=""doc-noteref""><sup>1</sup></a></td>
</tr>
</table>
<section role=""doc-endnotes"">
<hr>
<ol>
<li id=""fn1"">
<p>note<a href=""#fnref1"" role=""doc-backlink"">↩︎</a></p>
</li>
</ol>
</section>
".
Proof. vm_compute. reflexivity. Qed.

(* A fence's language is an attribute value and is escaped as one, so a
   language carrying a quote cannot break out of the attribute. *)
Example convert_code_lang_escaped :
  convert "``` a""onx=""y
z
```"
  = "<pre><code class=""language-a&quot;onx=&quot;y"">z
</code></pre>
".
Proof. vm_compute. reflexivity. Qed.

(* The chosen keyed-block HTML shape.  `.project/keyed-blocks.md` 9.3
   records why the label is a term rather than an attribute or heading. *)
Example render_keyed_description_list :
  serialize (render_blocks []
    [mk (Ext_keyed [mk (Str "foo")] (mk (Para [mk (Str "bar")])))])
  = "<dl class=""keyed"">
<dt>foo</dt>
<dd>
<p>bar</p>
</dd>
</dl>
".
Proof. vm_compute. reflexivity. Qed.

(* Both halves are reached by the numbering traversal: a label's note and
   a block's each take an index, where the stateless fallback would have
   dropped both. *)
Example render_keyed_numbers_both_notes :
  foot_next (fst (render_blocks_foot [] foot_initial
    [mk (Ext_keyed [mk (FootnoteReference "a")]
           (mk (Para [mk (FootnoteReference "b")])))])) = 3.
Proof. vm_compute. reflexivity. Qed.

(*
Output safety
=============

The one thing the tree makes statable that a flat string could not.

`serialize` writes a `<` when it opens or closes a tag and at no other
time, because the two routes from a document into the output -- text and
attribute values -- both go through an escaper that removes it.  So the
count of `<` in the output is determined by the tree's shape alone, and
no byte of source text can add one.

Two hypotheses carry the conditions this rests on rather than leaving
them as coincidences of the call sites.  `HRaw` is excluded, since it is
the deliberate hole (a raw block, a raw inline, or the one entity this
file writes).  And a tag name and an attribute *key* must carry no `<`
themselves: `render_attrs` escapes a value but emits a key as it stands,
which is safe only because `Attributes.is_key_char` admits no `<`.
Saying so here is what turns that into a stated condition.
*)

Fixpoint count_char (c : ascii) (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c' s' =>
      (if Ascii.eqb c c' then 1 else 0) + count_char c s'
  end.

Local Lemma count_char_app : forall c s1 s2,
  count_char c (s1 ++ s2) = count_char c s1 + count_char c s2.
Proof.
  intros c s1 s2. induction s1 as [|c' s1' IH]; cbn; [reflexivity|].
  rewrite IH. lia.
Qed.

Definition lt_char : ascii := "<"%char.

Local Lemma escape_no_lt : forall s, count_char lt_char (escape s) = 0.
Proof.
  induction s as [|c s' IH]; cbn [escape]; [reflexivity|].
  rewrite count_char_app, IH, Nat.add_0_r.
  unfold escape_char; destruct c as [b0 b1 b2 b3 b4 b5 b6 b7];
    destruct b0, b1, b2, b3, b4, b5, b6, b7; reflexivity.
Qed.

Local Lemma escape_attr_no_lt : forall s, count_char lt_char (escape_attr s) = 0.
Proof.
  induction s as [|c s' IH]; cbn [escape_attr]; [reflexivity|].
  rewrite count_char_app, IH, Nat.add_0_r.
  unfold escape_attr_char, escape_char;
    destruct c as [b0 b1 b2 b3 b4 b5 b6 b7];
    destruct b0, b1, b2, b3, b4, b5, b6, b7; reflexivity.
Qed.

Local Definition no_lt (s : string) : bool := Nat.eqb (count_char lt_char s) 0.

Local Definition attr_ok (a : attr) : bool := forallb (fun kv => no_lt (fst kv)) a.

Local Lemma count_char_concat : forall c l,
  count_char c (String.concat "" l)
  = fold_right (fun s n => count_char c s + n) 0 l.
Proof.
  intros c. induction l as [|x l' IH]; [reflexivity|].
  rewrite concat_empty_cons, count_char_app, IH. reflexivity.
Qed.

Local Lemma render_attrs_no_lt : forall a,
  attr_ok a = true -> count_char lt_char (render_attrs a) = 0.
Proof.
  intros a. unfold render_attrs, attr_ok. rewrite count_char_concat.
  induction a as [|kv a' IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hk Ha].
  unfold no_lt in Hk. apply Nat.eqb_eq in Hk.
  cbn [map fold_right]. rewrite IH by exact Ha.
  rewrite !count_char_app, escape_attr_no_lt, Hk. reflexivity.
Qed.

(* The two hypotheses, as functions on the tree.  Both take the shape
   `serialize_elt` does -- an outer fixpoint on the element, an inner one
   on the children -- and pay for it with the same equation lemma. *)
Local Fixpoint helt_ok (e : helt) : bool :=
  let go :=
    fix go (es : list helt) : bool :=
      match es with
      | [] => true
      | e' :: rest => (helt_ok e' && go rest)%bool
      end in
  match e with
  | HText _ => true
  | HRaw _ => false
  | HVoid tag _ a => (no_lt tag && attr_ok a)%bool
  | HElem tag _ a kids => (no_lt tag && attr_ok a && go kids)%bool
  end.

Fixpoint helts_ok (es : list helt) : bool :=
  match es with
  | [] => true
  | e :: rest => (helt_ok e && helts_ok rest)%bool
  end.

Local Lemma helt_ok_elem : forall tag nls a kids,
  helt_ok (HElem tag nls a kids)
  = (no_lt tag && attr_ok a && helts_ok kids)%bool.
Proof.
  intros tag nls a kids. cbn [helt_ok].
  assert (H : forall ks,
    (fix go (es : list helt) : bool :=
       match es with
       | [] => true
       | e' :: rest => (helt_ok e' && go rest)%bool
       end) ks = helts_ok ks).
  { induction ks as [|k ks' IH]; [reflexivity|].
    cbn [helts_ok]. rewrite <- IH. reflexivity. }
  rewrite H. reflexivity.
Qed.

(* Two per element with a closing tag, one per element without. *)
Local Fixpoint helt_tags (e : helt) : nat :=
  let go :=
    fix go (es : list helt) : nat :=
      match es with
      | [] => 0
      | e' :: rest => helt_tags e' + go rest
      end in
  match e with
  | HText _ => 0
  | HRaw _ => 0
  | HVoid _ _ _ => 1
  | HElem _ _ _ kids => 2 + go kids
  end.

Fixpoint helts_tags (es : list helt) : nat :=
  match es with
  | [] => 0
  | e :: rest => helt_tags e + helts_tags rest
  end.

Local Lemma helt_tags_elem : forall tag nls a kids,
  helt_tags (HElem tag nls a kids) = 2 + helts_tags kids.
Proof.
  intros tag nls a kids. cbn [helt_tags].
  assert (H : forall ks,
    (fix go (es : list helt) : nat :=
       match es with
       | [] => 0
       | e' :: rest => helt_tags e' + go rest
       end) ks = helts_tags ks).
  { induction ks as [|k ks' IH]; [reflexivity|].
    cbn [helts_tags]. rewrite <- IH. reflexivity. }
  rewrite H. reflexivity.
Qed.

Local Lemma open_tag_lt : forall tag self a,
  no_lt tag = true -> attr_ok a = true ->
  count_char lt_char (open_tag tag self a) = 1.
Proof.
  intros tag self a Ht Ha. unfold open_tag, no_lt in *.
  apply Nat.eqb_eq in Ht.
  cbn [count_char Ascii.eqb].
  rewrite !count_char_app, Ht, (render_attrs_no_lt _ Ha).
  destruct self; reflexivity.
Qed.

(** Every `<` in the output opens or closes a tag.  So no byte of source
    text can produce one: the count is fixed by the tree's shape. *)
Theorem serialize_lt_tags : forall es,
  helts_ok es = true ->
  count_char lt_char (serialize es) = helts_tags es.
Proof.
  apply (helts_ind2
    (fun e => helt_ok e = true ->
              count_char lt_char (serialize_elt e) = helt_tags e)
    (fun es => helts_ok es = true ->
               count_char lt_char (serialize es) = helts_tags es)).
  - intros s _. cbn [serialize_elt helt_tags]. apply escape_no_lt.
  - intros s H. discriminate H.
  - intros tag self a H. cbn [helt_ok helt_tags] in *.
    apply andb_true_iff in H as [Ht Ha]. apply open_tag_lt; assumption.
  - intros tag nls a kids IH H.
    rewrite helt_ok_elem in H. rewrite helt_tags_elem, serialize_elt_elem.
    apply andb_true_iff in H as [H' Hk].
    apply andb_true_iff in H' as [Ht Ha].
    rewrite !count_char_app, (open_tag_lt _ false _ Ht Ha), (IH Hk).
    unfold no_lt in Ht. apply Nat.eqb_eq in Ht. rewrite Ht.
    destruct (Nat.leb 2 nls), (Nat.leb 1 nls); cbn; lia.
  - intros _. reflexivity.
  - intros e es IHe IHes H. cbn [helts_ok helts_tags serialize] in *.
    apply andb_true_iff in H as [He Hes].
    rewrite count_char_app, (IHe He), (IHes Hes). reflexivity.
Qed.

(* The key condition has teeth.  `render_attrs` escapes a value but emits
   a key as it stands, so a key carrying `<` puts a tag in the output
   that no element asked for -- three `<` where the tree has two.  What
   keeps that unreachable from a document is `Attributes.is_key_char`,
   which admits letters, digits, `_`, `:` and `-` and nothing else. *)
Example attr_key_lt_injects :
  let bad := [HElem "p" 1 [("x<img src=y", "")] []] in
  helts_ok bad = false
  /\ count_char lt_char (serialize bad) = 3
  /\ helts_tags bad = 2.
Proof. vm_compute. repeat split. Qed.

(* What the parser produces satisfies it, so the theorem applies to real
   documents -- attributes, headings, task lists, footnotes and a quote
   inside a note all pass. *)
Example convert_tree_ok :
  helts_ok (html_tree (parse_doc "{#i .c}
# h[^n]

- [ ] a *b* <s>

| x |

[^n]: > q")) = true.
Proof. vm_compute. reflexivity. Qed.

(* Except through the deliberate hole.  A raw inline or a raw block is
   the one way a document puts bytes in the output unexamined, and
   `helt_ok` refuses it rather than pretending otherwise -- so the
   theorem says nothing about a document that uses one, which is the
   honest reading of what `{=html}` means. *)
Example convert_tree_raw_excluded :
  helts_ok (html_tree (parse_doc "`<script>`{=html}")) = false.
Proof. vm_compute. reflexivity. Qed.
