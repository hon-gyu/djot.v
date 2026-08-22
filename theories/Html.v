(* ai-disclosure: autonomous *)

(* HTML rendering, targeting byte-identical agreement with djot.js's
   renderer (the authority; see .project/oracle-disagreements.md — djoths's
   serialization diverges on attribute order, section wrapping, and task
   items, and we follow djot.js on all three).

   Phase 1 status: paragraphs are rendered faithfully; the remaining
   constructors have placeholder output (empty or skeletal) that will be
   filled in alongside the parser, driven by the corpus diff. *)

From Stdlib Require Import String Ascii List.
From DjotV Require Import Strings Ast Parser Document.
Import ListNotations.

Local Open Scope string_scope.

Definition escape_char (c : ascii) : string :=
  match c with
  | "&"%char => "&amp;"
  | "<"%char => "&lt;"
  | ">"%char => "&gt;"
  | _ => String c EmptyString
  end.

Fixpoint escape (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => escape_char c ++ escape s'
  end.

(* Attribute values escape the quote as well (djot.js escapeAttribute). *)
Definition escape_attr_char (c : ascii) : string :=
  match c with
  | """"%char => "&quot;"
  | _ => escape_char c
  end.

Fixpoint escape_attr (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => escape_attr_char c ++ escape_attr s'
  end.

(* Rendered in source order, each as ` key="value"`, so that the empty
   attribute set contributes nothing to a tag. *)
Definition render_attrs (a : attr) : string :=
  String.concat ""
    (map (fun kv => " " ++ fst kv ++ "=""" ++ escape_attr (snd kv) ++ """") a).

(* What a resolved reference definition contributes.  Its attributes are
   extra in the same sense as `href`, so they precede the node's own --
   but a key the node carries itself wins, since djot.js copies an entry
   into `extraAttr` only when the node has none (html.ts:430-436).
   Without the filter `[ref][]{title=bar}` against a `{title=foo}`
   definition renders two `title`s.

   The `class` join beside it (html.ts:112-118) is unreachable from here:
   it needs an extra `class`, which this filter admits only when the node
   has none to join with. *)
Definition ref_extra (a0 a : attr) : attr :=
  filter (fun kv => match lookup_attr (fst kv) a with
                    | Some _ => false
                    | None => true
                    end) a0.

(* An ordered list's `start` and `type`, djot.js html.ts:251-259.  Both
   are omitted at their HTML defaults — start 1, decimal numbering — and
   both precede the node's own attributes, because `renderAttributes`
   emits `extraAttrs` first (html.ts:76-88). *)
Definition ol_attrs (oa : ordered_list_attributes) : string :=
  (if Nat.eqb (ol_start oa) 1
   then "" else " start=""" ++ nat_str (ol_start oa) ++ """")
  ++ (match ol_style oa with
      | Decimal => ""
      | LetterLower => " type=""a"""
      | LetterUpper => " type=""A"""
      | RomanLower => " type=""i"""
      | RomanUpper => " type=""I"""
      end).

(*
Inlines
=======
*)

(* An image's `alt` is the plain text of its children, not their HTML:
   djot.js's `getStringContent` (parse.ts:33) pushes each node's `text`
   field, turns a break into a newline, and otherwise recurses.  Only the
   constructs the parser builds are covered; the rest contribute nothing
   here in any case. *)
Fixpoint plain_text (il : inline) : string :=
  let go :=
    fix go (ns : list (node inline)) : string :=
      match ns with
      | [] => ""
      | Node _ _ x :: rest => plain_text x ++ go rest
      end in
  match il with
  | Str s | Verbatim s | Symbol s | Math _ s | RawInline _ s => s
  | UrlLink s | EmailLink s => s
  | Emph ns | Strong ns | Highlight ns | Insert ns | Delete ns
  | Superscript ns | Subscript ns | Span ns | Quoted _ ns
  | Link ns _ | Image ns _ => go ns
  | SoftBreak | HardBreak => nl
  | NonBreakingSpace => " "
  | FootnoteReference _ => ""
  end.

Definition plain_texts (ns : list (node inline)) : string :=
  String.concat "" (map (fun n => plain_text (node_contents n)) ns).

(*
Rendering, against the document's reference map
===============================================

`refs` is the map a `Reference` target resolves against: the document's
explicit definitions followed by the implicit heading ones, appended so
that `alist_lookup`'s first-match rule is djot.js's `references[lab] ||
autoReferences[lab]` (html.ts:420).  It is a section variable rather than
a threaded argument because every recursion here would otherwise carry it
unchanged.
*)
Section WithRefs.
Context (refs : reference_map).

(* A node's own attributes render on its own tag, after any the
   construct contributes itself ("extra attributes" in html.ts, which
   emits them first).  A `Str` has no tag of its own, so djot.js wraps an
   attributed one in a `<span>` and leaves a bare one alone
   (html.ts:246) -- which is why `foo{.a}` is a `str` carrying attributes
   in the AST and a span only in the output. *)
Fixpoint render_inline (il : inline) (a : attr) : string :=
  let render_ils :=
    fix go (ns : list (node inline)) : string :=
      match ns with
      | [] => ""
      | Node _ a' x :: rest => render_inline x a' ++ go rest
      end in
  let ats := render_attrs a in
  match il with
  | Str s =>
      match a with
      | [] => escape s
      | _ => "<span" ++ ats ++ ">" ++ escape s ++ "</span>"
      end
  | Emph ils => "<em" ++ ats ++ ">" ++ render_ils ils ++ "</em>"
  | Strong ils => "<strong" ++ ats ++ ">" ++ render_ils ils ++ "</strong>"
  | Highlight ils => "<mark" ++ ats ++ ">" ++ render_ils ils ++ "</mark>"
  | Insert ils => "<ins" ++ ats ++ ">" ++ render_ils ils ++ "</ins>"
  | Delete ils => "<del" ++ ats ++ ">" ++ render_ils ils ++ "</del>"
  | Superscript ils => "<sup" ++ ats ++ ">" ++ render_ils ils ++ "</sup>"
  | Subscript ils => "<sub" ++ ats ++ ">" ++ render_ils ils ++ "</sub>"
  | Verbatim s => "<code" ++ ats ++ ">" ++ escape s ++ "</code>"
  | Symbol s => ":" ++ escape s ++ ":"
  (* djot.js emits a span carrying the class and wraps the content in
     TeX delimiters, escaping it as text (`html.ts:330-338`). *)
  | Math InlineMath s =>
      "<span class=""math inline"">\(" ++ escape s ++ "\)</span>"
  | Math DisplayMath s =>
      "<span class=""math display"">\[" ++ escape s ++ "\]</span>" 
  (* `href` is an extra attribute, so it precedes the node's own and is
     omitted entirely when the target is an unresolved reference: djot.js
     drops the attribute (with a warning) when a label does not resolve.
     A resolved reference contributes the definition's attributes through
     `ref_extra`, which are extra in the same sense and so also precede
     the node's. *)
  | Link ils (Direct url) =>
      "<a href=""" ++ escape_attr url ++ """" ++ ats ++ ">"
      ++ render_ils ils ++ "</a>"
  | Link ils (Reference label) =>
      match lookup_reference label refs with
      | Some (url, a0) =>
          "<a href=""" ++ escape_attr url ++ """"
          ++ render_attrs (ref_extra a0 a) ++ ats
          ++ ">" ++ render_ils ils ++ "</a>"
      | None => "<a" ++ ats ++ ">" ++ render_ils ils ++ "</a>"
      end
  (* `alt` precedes `src`, both extra attributes, in that order
     (html.ts:452). *)
  | Image ils (Direct url) =>
      "<img alt=""" ++ escape_attr (plain_texts ils)
        ++ """ src=""" ++ escape_attr url ++ """" ++ ats ++ ">"
  | Image ils (Reference label) =>
      match lookup_reference label refs with
      | Some (url, a0) =>
          "<img alt=""" ++ escape_attr (plain_texts ils)
            ++ """ src=""" ++ escape_attr url ++ """"
            ++ render_attrs (ref_extra a0 a) ++ ats ++ ">"
      | None => "<img alt=""" ++ escape_attr (plain_texts ils) ++ """"
                ++ ats ++ ">"
      end
  | Span ils => "<span" ++ ats ++ ">" ++ render_ils ils ++ "</span>"
  | FootnoteReference _ => "" (* TODO Phase 1 *)
  (* An autolink renders as its own text under an `href`, which is an
     extra attribute and so precedes the node's own -- `renderTag("a",
     node, extraAttr)` (html.ts:470-481).  The two kinds differ only in
     the `mailto:` an email prefixes to the destination; the text shown
     is the region either way. *)
  | UrlLink url =>
      "<a href=""" ++ escape_attr url ++ """" ++ ats ++ ">"
      ++ escape url ++ "</a>"
  | EmailLink addr =>
      "<a href=""mailto:" ++ escape_attr addr ++ """" ++ ats ++ ">"
      ++ escape addr ++ "</a>"
  (* Raw content in a format the renderer does not speak contributes
     nothing at all, attributes included -- `html.ts:396-402` emits the
     text only for `html` and never a wrapper element. *)
  | RawInline fmt s => if String.eqb fmt "html" then s else ""
  | NonBreakingSpace => "&nbsp;"
  (* The curly quotes are the whole of what a quoted span renders as:
     djot.js wraps the children in the two characters and emits no
     element (`html.ts:353-358`). *)
  | Quoted SingleQuotes ils => lsquo ++ render_ils ils ++ rsquo
  | Quoted DoubleQuotes ils => ldquo ++ render_ils ils ++ rdquo
  | SoftBreak => nl
  | HardBreak => "<br>" ++ nl
  end.

Definition render_inlines (ils : inlines) : string :=
  String.concat "" (map (fun n => match n with
                                  | Node _ a x => render_inline x a
                                  end) ils).

(*
Table rows
----------

Cells hold inlines only, so the whole of a table renders without
touching `render_block`'s recursion.  Alignment is a style attribute on
the cell, and `AlignDefault` carries none (html.ts, and confirmed
against the oracle on every combination in `tables.test`). *)

Definition align_attr (al : align) : string :=
  match al with
  | AlignDefault => ""
  | AlignLeft => " style=""text-align: left;"""
  | AlignRight => " style=""text-align: right;"""
  | AlignCenter => " style=""text-align: center;"""
  end.

Definition render_cell (c : cell) : string :=
  match c with
  | Cell ct al ils =>
      let tag := match ct with HeadCell => "th" | BodyCell => "td" end in
      "<" ++ tag ++ align_attr al ++ ">" ++ render_inlines ils
      ++ "</" ++ tag ++ ">" ++ nl
  end.

Definition render_row (r : list cell) : string :=
  "<tr>" ++ nl ++ String.concat "" (map render_cell r) ++ "</tr>" ++ nl.

Definition render_caption (caption : option inlines) : string :=
  match caption with
  | None => ""
  | Some ils => "<caption>" ++ render_inlines ils ++ "</caption>" ++ nl
  end.

(*
Blocks
======
*)

(* `tight` is rendering state, not a property of the block being
   rendered: djot.js sets it in `renderChildren` on any node carrying a
   `tight` field — only a list does — and restores it on the way out
   (html.ts:140-150).  So it survives a block quote or a div, and every
   paragraph below a tight item is emitted bare until another list resets
   it.  A per-item match on direct children is *not* the same rule:
   `- > a` renders `<blockquote>a</blockquote>` in djot.js and used to
   render `<blockquote><p>a</p></blockquote>` here.

   The node's attributes ride alongside its payload: they belong on the
   opening tag (today only the auto-identifiers the whole-document pass
   puts on sections and quoted headings), but recursion still has to be
   on `block` — `list (node block)` is two type constructors deep, which
   the guard checker will not follow from a `node block` argument. *)
Fixpoint render_block (tight : bool) (b : block) (a : attr) {struct b}
  : string :=
  (* Takes the flag as an argument so that one list recursion serves both
     the containers, which pass it through, and the items, which set it. *)
  let render_bs_at :=
    fix go (t : bool) (ns : list (node block)) : string :=
      match ns with
      | [] => ""
      | Node _ a' x :: rest => render_block t x a' ++ go t rest
      end in
  let render_bs := render_bs_at tight in
  let render_items :=
    fix goi (sp : list_spacing) (its : list (list (node block))) {struct its}
      : string :=
      match its with
      | [] => ""
      | it :: rest =>
          "<li>" ++ nl
          ++ render_bs_at (match sp with Tight => true | Loose => false end) it
          ++ "</li>" ++ nl ++ goi sp rest
      end in
  (* A `dd` is rendered at the *incoming* tightness, not at the list's:
     djot.js's `definition_list` node carries no `tight` field where
     every other list does (parse.ts:824-857), and `renderChildren` only
     overrides the flag for a node that has one (html.ts:140-148).  So a
     definition inside a tight bullet item renders bare, and `sp` is
     read by nothing here.  It is not dead: the roundtrip reads it, since
     it is what records the blank lines the source had. *)
  let render_def_items :=
    fix god (its : list (inlines * list (node block))) {struct its}
      : string :=
      match its with
      | [] => ""
      | (term, it) :: rest =>
          "<dt>" ++ render_inlines term ++ "</dt>" ++ nl
          ++ "<dd>" ++ nl ++ render_bs it ++ "</dd>" ++ nl
          ++ god rest
      end in
  (* A task item's checkbox, ahead of its content and outside whatever
     the tightness does to that content (html.ts:219-229).  The `<ul>`
     carries `class="task-list"` before the node's own attributes, the
     order `ol_attrs` already establishes. *)
  let render_task_items :=
    fix got (sp : list_spacing)
      (its : list (task_status * list (node block))) {struct its} : string :=
      match its with
      | [] => ""
      | (st, it) :: rest =>
          "<li>" ++ nl
          ++ "<input disabled="""" type=""checkbox"""
          ++ (match st with Complete => " checked=""""" | Incomplete => "" end)
          ++ "/>" ++ nl
          ++ render_bs_at (match sp with Tight => true | Loose => false end) it
          ++ "</li>" ++ nl ++ got sp rest
      end in
  let ats := render_attrs a in
  match b with
  (* A tight paragraph loses its tag, keeping the newline the tag carried.
     Its attributes go with the tag; djot.js drops them the same way, and
     nothing produces them here yet. *)
  | Para ils =>
      if tight then render_inlines ils ++ nl
      else "<p" ++ ats ++ ">" ++ render_inlines ils ++ "</p>" ++ nl
  | Section bs =>
      "<section" ++ ats ++ ">" ++ nl ++ render_bs bs ++ "</section>" ++ nl
  | Heading lvl ils =>
      "<h" ++ nat_str lvl ++ ats ++ ">" ++ render_inlines ils
      ++ "</h" ++ nat_str lvl ++ ">" ++ nl
  | BlockQuote bs =>
      "<blockquote" ++ ats ++ ">" ++ nl ++ render_bs bs
      ++ "</blockquote>" ++ nl
  | CodeBlock lang code =>
      "<pre" ++ ats ++ "><code"
      ++ (match lang with
          | EmptyString => ""
          | _ => " class=""language-" ++ lang ++ """"
          end)
      ++ ">" ++ escape code ++ "</code></pre>" ++ nl
  | Div bs => "<div" ++ ats ++ ">" ++ nl ++ render_bs bs ++ "</div>" ++ nl
  | OrderedList oa sp items =>
      "<ol" ++ ol_attrs oa ++ ats ++ ">" ++ nl
      ++ render_items sp items ++ "</ol>" ++ nl
  | BulletList sp items =>
      "<ul" ++ ats ++ ">" ++ nl ++ render_items sp items ++ "</ul>" ++ nl
  | TaskList sp items =>
      "<ul class=""task-list""" ++ ats ++ ">" ++ nl
      ++ render_task_items sp items ++ "</ul>" ++ nl
  | DefinitionList _ items =>
      "<dl" ++ ats ++ ">" ++ nl ++ render_def_items items ++ "</dl>" ++ nl
  | ThematicBreak => "<hr" ++ ats ++ ">" ++ nl
  | Table caption rows =>
      "<table" ++ ats ++ ">" ++ nl ++ render_caption caption
      ++ String.concat "" (map render_row rows) ++ "</table>" ++ nl
  | RawBlock fmt contents =>
      if String.eqb fmt "html" then contents else ""
  (* A reference definition is not content: djot.js keeps it out of the
     block tree entirely and emits nothing for it. *)
  | RefDef _ _ => ""
  (* Collected by the later document pass; while it remains in the block
     tree it is metadata rather than visible document content. *)
  | FootnoteDef _ _ => ""
  end.

Definition render_node (n : node block) : string :=
  match n with Node _ a b => render_block false b a end.

Definition render_blocks (bs : blocks) : string :=
  String.concat "" (map render_node bs).

(* Footnote indices are assigned by the HTML traversal, including traversals
   through note bodies.  Keeping this path beside the stateless renderer
   leaves the latter useful for its existing local callers while making the
   document entry point agree with djot.js. *)
Record foot_state : Type := FootState
  { foot_numbers : list (string * nat)
  ; foot_next : nat
  }.

Definition foot_initial : foot_state := FootState [] 1.

Definition number_footnote (label : string) (st : foot_state)
  : foot_state * nat * bool :=
  let label := normalize_label label in
  match alist_lookup label (foot_numbers st) with
  | Some n => (st, n, false)
  | None =>
      let n := foot_next st in
      (FootState ((foot_numbers st ++ [(label, n)])%list) (S n), n, true)
  end.

Fixpoint render_inline_foot (st : foot_state) (il : inline) (a : attr)
  {struct il} : foot_state * string :=
  let render_ils :=
    fix go (st0 : foot_state) (ns : list (node inline))
      : foot_state * string :=
      match ns with
      | [] => (st0, "")
      | Node _ a' x :: rest =>
          let '(st1, s1) := render_inline_foot st0 x a' in
          let '(st2, s2) := go st1 rest in
          (st2, s1 ++ s2)
      end in
  let ats := render_attrs a in
  match il with
  | Emph ils =>
      let '(st', s) := render_ils st ils in (st', "<em" ++ ats ++ ">" ++ s ++ "</em>")
  | Strong ils =>
      let '(st', s) := render_ils st ils in (st', "<strong" ++ ats ++ ">" ++ s ++ "</strong>")
  | Highlight ils =>
      let '(st', s) := render_ils st ils in (st', "<mark" ++ ats ++ ">" ++ s ++ "</mark>")
  | Insert ils =>
      let '(st', s) := render_ils st ils in (st', "<ins" ++ ats ++ ">" ++ s ++ "</ins>")
  | Delete ils =>
      let '(st', s) := render_ils st ils in (st', "<del" ++ ats ++ ">" ++ s ++ "</del>")
  | Superscript ils =>
      let '(st', s) := render_ils st ils in (st', "<sup" ++ ats ++ ">" ++ s ++ "</sup>")
  | Subscript ils =>
      let '(st', s) := render_ils st ils in (st', "<sub" ++ ats ++ ">" ++ s ++ "</sub>")
  | Span ils =>
      let '(st', s) := render_ils st ils in (st', "<span" ++ ats ++ ">" ++ s ++ "</span>")
  | Quoted q ils =>
      let '(st', s) := render_ils st ils in
      match q with
      | SingleQuotes => (st', lsquo ++ s ++ rsquo)
      | DoubleQuotes => (st', ldquo ++ s ++ rdquo)
      end
  | Link ils target =>
      let '(st', s) := render_ils st ils in
      match target with
      | Direct url =>
          (st', "<a href=""" ++ escape_attr url ++ """" ++ ats ++ ">" ++ s ++ "</a>")
      | Reference label =>
          match lookup_reference label refs with
          | Some (url, a0) =>
              (st', "<a href=""" ++ escape_attr url ++ """"
                    ++ render_attrs (ref_extra a0 a) ++ ats ++ ">" ++ s ++ "</a>")
          | None => (st', "<a" ++ ats ++ ">" ++ s ++ "</a>")
          end
      end
  (* Image children become alt text and are not visited by djot.js's HTML
     traversal, so a syntactically nested reference does not get a number. *)
  | Image _ _ => (st, render_inline il a)
  | FootnoteReference label =>
      let '(st', n, first) := number_footnote label st in
      let sn := nat_str n in
      (st', "<a" ++ (if first then " id=""fnref" ++ sn ++ """" else "")
            ++ " href=""#fn" ++ sn ++ """ role=""doc-noteref""" ++ ats
            ++ "><sup>" ++ sn ++ "</sup></a>")
  | _ => (st, render_inline il a)
  end.

Definition render_inlines_foot (st : foot_state) (ils : inlines)
  : foot_state * string :=
  fold_left
    (fun acc n =>
       let '(st0, out) := acc in
       let '(st1, s) :=
         match n with Node _ a x => render_inline_foot st0 x a end in
       (st1, out ++ s))
    ils (st, "").

(* The table renderers again, threading the footnote counter: a cell may
   carry a footnote reference, and it is numbered in source order like
   any other. *)
Definition render_cell_foot (st : foot_state) (c : cell) : foot_state * string :=
  match c with
  | Cell ct al ils =>
      let tag := match ct with HeadCell => "th" | BodyCell => "td" end in
      let '(st', s) := render_inlines_foot st ils in
      (st', "<" ++ tag ++ align_attr al ++ ">" ++ s ++ "</" ++ tag ++ ">" ++ nl)
  end.

Fixpoint render_cells_foot (st : foot_state) (r : list cell)
  : foot_state * string :=
  match r with
  | [] => (st, "")
  | c :: rest =>
      let '(st1, s1) := render_cell_foot st c in
      let '(st2, s2) := render_cells_foot st1 rest in
      (st2, s1 ++ s2)
  end.

Fixpoint render_rows_foot (st : foot_state) (rows : list (list cell))
  : foot_state * string :=
  match rows with
  | [] => (st, "")
  | r :: rest =>
      let '(st1, s1) := render_cells_foot st r in
      let '(st2, s2) := render_rows_foot st1 rest in
      (st2, "<tr>" ++ nl ++ s1 ++ "</tr>" ++ nl ++ s2)
  end.

Definition render_caption_foot (st : foot_state) (caption : option inlines)
  : foot_state * string :=
  match caption with
  | None => (st, "")
  | Some ils =>
      let '(st', s) := render_inlines_foot st ils in
      (st', "<caption>" ++ s ++ "</caption>" ++ nl)
  end.

Fixpoint render_block_foot (st : foot_state) (tight : bool)
  (b : block) (a : attr) {struct b} : foot_state * string :=
  let render_bs_at :=
    fix go (st0 : foot_state) (t : bool) (ns : list (node block))
      : foot_state * string :=
      match ns with
      | [] => (st0, "")
      | Node _ a' x :: rest =>
          let '(st1, s1) := render_block_foot st0 t x a' in
          let '(st2, s2) := go st1 t rest in
          (st2, s1 ++ s2)
      end in
  let render_items :=
    fix goi (st0 : foot_state) (sp : list_spacing)
      (its : list (list (node block))) {struct its} : foot_state * string :=
      match its with
      | [] => (st0, "")
      | it :: rest =>
          let t := match sp with Tight => true | Loose => false end in
          let '(st1, s1) := render_bs_at st0 t it in
          let '(st2, s2) := goi st1 sp rest in
          (st2, "<li>" ++ nl ++ s1 ++ "</li>" ++ nl ++ s2)
      end in
  let render_task_items :=
    fix got (st0 : foot_state) (sp : list_spacing)
      (its : list (task_status * list (node block))) {struct its}
      : foot_state * string :=
      match its with
      | [] => (st0, "")
      | (chk, it) :: rest =>
          let t := match sp with Tight => true | Loose => false end in
          let '(st1, s1) := render_bs_at st0 t it in
          let '(st2, s2) := got st1 sp rest in
          (st2, "<li>" ++ nl
                ++ "<input disabled="""" type=""checkbox"""
                ++ (match chk with
                    | Complete => " checked="""""
                    | Incomplete => ""
                    end)
                ++ "/>" ++ nl ++ s1 ++ "</li>" ++ nl ++ s2)
      end in
  let render_def_items :=
    fix god (st0 : foot_state) (its : list (inlines * list (node block)))
      {struct its} : foot_state * string :=
      match its with
      | [] => (st0, "")
      | (term, it) :: rest =>
          let '(st1, s1) := render_inlines_foot st0 term in
          let '(st2, s2) := render_bs_at st1 tight it in
          let '(st3, s3) := god st2 rest in
          (st3, "<dt>" ++ s1 ++ "</dt>" ++ nl
                ++ "<dd>" ++ nl ++ s2 ++ "</dd>" ++ nl ++ s3)
      end in
  let ats := render_attrs a in
  match b with
  | Para ils =>
      let '(st', s) := render_inlines_foot st ils in
      if tight then (st', s ++ nl)
      else (st', "<p" ++ ats ++ ">" ++ s ++ "</p>" ++ nl)
  | Heading lvl ils =>
      let '(st', s) := render_inlines_foot st ils in
      (st', "<h" ++ nat_str lvl ++ ats ++ ">" ++ s
            ++ "</h" ++ nat_str lvl ++ ">" ++ nl)
  | Section bs =>
      let '(st', s) := render_bs_at st tight bs in
      (st', "<section" ++ ats ++ ">" ++ nl ++ s ++ "</section>" ++ nl)
  | BlockQuote bs =>
      let '(st', s) := render_bs_at st tight bs in
      (st', "<blockquote" ++ ats ++ ">" ++ nl ++ s ++ "</blockquote>" ++ nl)
  | Div bs =>
      let '(st', s) := render_bs_at st tight bs in
      (st', "<div" ++ ats ++ ">" ++ nl ++ s ++ "</div>" ++ nl)
  | OrderedList oa sp items =>
      let '(st', s) := render_items st sp items in
      (st', "<ol" ++ ol_attrs oa ++ ats ++ ">" ++ nl ++ s ++ "</ol>" ++ nl)
  | BulletList sp items =>
      let '(st', s) := render_items st sp items in
      (st', "<ul" ++ ats ++ ">" ++ nl ++ s ++ "</ul>" ++ nl)
  (* As `render_block`, with the counter threaded: a footnote reference
     inside a definition would otherwise fall through to the stateless
     path and be dropped, which is the bug the table step found on this
     same line. *)
  | DefinitionList _ items =>
      let '(st', s) := render_def_items st items in
      (st', "<dl" ++ ats ++ ">" ++ nl ++ s ++ "</dl>" ++ nl)
  | TaskList sp items =>
      let '(st', s) := render_task_items st sp items in
      (st', "<ul class=""task-list""" ++ ats ++ ">" ++ nl ++ s ++ "</ul>" ++ nl)
  | Table caption rows =>
      let '(st1, s1) := render_caption_foot st caption in
      let '(st2, s2) := render_rows_foot st1 rows in
      (st2, "<table" ++ ats ++ ">" ++ nl ++ s1 ++ s2 ++ "</table>" ++ nl)
  | _ => (st, render_block tight b a)
  end.

Definition render_blocks_foot (st : foot_state) (bs : blocks)
  : foot_state * string :=
  fold_left
    (fun acc n =>
       let '(st0, out) := acc in
       let '(st1, s) :=
         match n with Node _ a b => render_block_foot st0 false b a end in
       (st1, out ++ s))
    bs (st, "").

Definition ends_with (suffix s : string) : bool :=
  let n := String.length s in
  let m := String.length suffix in
  String.eqb (String.substring (n - m) m s) suffix.

Definition note_backlink (n : nat) : string :=
  "<a href=""#fnref" ++ nat_str n ++ """ role=""doc-backlink"">↩︎</a>".

Fixpoint split_line_endings_rev (r endings : string) : string * string :=
  match r with
  | EmptyString => ("", endings)
  | String c rest =>
      if (Ascii.eqb c "010"%char || Ascii.eqb c "013"%char)%bool
      then split_line_endings_rev rest (String c endings)
      else (rev_string r, endings)
  end.

Definition split_trailing_line_endings (s : string) : string * string :=
  split_line_endings_rev (rev_string s) "".

Definition add_backlink (body : string) (n : nat) : string :=
  let back := note_backlink n in
  let '(core, endings) := split_trailing_line_endings body in
  if ends_with "</p>" core then
    String.substring 0 (String.length core - 4) core
    ++ back ++ "</p>" ++ endings
  else body ++ "<p>" ++ back ++ "</p>" ++ nl.

Fixpoint render_note_defs (st : foot_state) (notes : note_map)
  : foot_state * list (string * string) :=
  match notes with
  | [] => (st, [])
  | (label, bs) :: rest =>
      let '(st1, body) := render_blocks_foot st bs in
      let '(st2, rendered) := render_note_defs st1 rest in
      (st2, (label, body) :: rendered)
  end.

Fixpoint label_at (n : nat) (numbers : list (string * nat)) : option string :=
  match numbers with
  | [] => None
  | (label, n') :: rest =>
      if Nat.eqb n n' then Some label else label_at n rest
  end.

Definition rendered_note_at (n : nat) (st : foot_state)
  (rendered : list (string * string)) : string :=
  match label_at n (foot_numbers st) with
  | None => ""
  | Some label => match alist_lookup label rendered with Some s => s | None => "" end
  end.

Fixpoint render_note_items (fuel n : nat) (st : foot_state)
  (rendered : list (string * string)) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      "<li id=""fn" ++ nat_str n ++ """>" ++ nl
      ++ add_backlink (rendered_note_at n st rendered) n
      ++ "</li>" ++ nl ++ render_note_items fuel' (S n) st rendered
  end.

Definition render_document_foot (blocks : blocks) (notes : note_map) : string :=
  let '(st1, body) := render_blocks_foot foot_initial blocks in
  if Nat.eqb (foot_next st1) 1 then body
  else
    let '(st2, rendered) := render_note_defs st1 notes in
    body ++ "<section role=""doc-endnotes"">" ++ nl ++ "<hr>" ++ nl ++ "<ol>" ++ nl
    ++ render_note_items (foot_next st2 - 1) 1 st2 rendered
    ++ "</ol>" ++ nl ++ "</section>" ++ nl.

End WithRefs.

(* Explicit definitions first, so a label defined both ways resolves to
   the explicit one. *)
Definition doc_refs (d : doc) : reference_map :=
  (doc_references d ++ doc_auto_references d)%list.

Definition render_html (d : doc) : string :=
  render_document_foot (doc_refs d) (doc_blocks d) (doc_footnotes d).

(* The single entry point the harness extracts: djot in, HTML out. *)
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

Read off djot.js on 2026-08-22; see `.project/260822.task-lists` §1.
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

Each was read off djot.js on 2026-08-22; §1 of `.project/
260822.definition-lists` records the probes these came from.
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
   keeps everything (djot.js parse.ts:903-912).  The heading's
   auto-identifier is `Document.assign_ids` reaching into a definition. *)
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

(* Two colons are not a marker and three are a div: `getListStyles`
   answers with no style for "::", and `classify` tests `div_open`
   before `list_marker`. *)
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

Each of these was read off djot.js first.
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
