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

Fixpoint render_inline (il : inline) : string :=
  let render_ils :=
    fix go (ns : list (node inline)) : string :=
      match ns with
      | [] => ""
      | Node _ _ x :: rest => render_inline x ++ go rest
      end in
  match il with
  | Str s => escape s
  | Emph ils => "<em>" ++ render_ils ils ++ "</em>"
  | Strong ils => "<strong>" ++ render_ils ils ++ "</strong>"
  | Highlight ils => "<mark>" ++ render_ils ils ++ "</mark>"
  | Insert ils => "<ins>" ++ render_ils ils ++ "</ins>"
  | Delete ils => "<del>" ++ render_ils ils ++ "</del>"
  | Superscript ils => "<sup>" ++ render_ils ils ++ "</sup>"
  | Subscript ils => "<sub>" ++ render_ils ils ++ "</sub>"
  | Verbatim s => "<code>" ++ escape s ++ "</code>"
  | Symbol s => ":" ++ escape s ++ ":"
  | Math _ _ => ""            (* TODO Phase 1 *)
  (* `href` is an extra attribute, so it precedes the node's own and is
     omitted entirely when the target is an unresolved reference: the
     reference map is not carried here yet, and djot.js drops the
     attribute (with a warning) when a label does not resolve. *)
  | Link ils (Direct url) =>
      "<a href=""" ++ escape_attr url ++ """>" ++ render_ils ils ++ "</a>"
  | Link ils (Reference _) => "<a>" ++ render_ils ils ++ "</a>"
  (* `alt` precedes `src`, both extra attributes, in that order
     (html.ts:452). *)
  | Image ils (Direct url) =>
      "<img alt=""" ++ escape_attr (plain_texts ils)
        ++ """ src=""" ++ escape_attr url ++ """>"
  | Image ils (Reference _) =>
      "<img alt=""" ++ escape_attr (plain_texts ils) ++ """>"
  | Span ils => "<span>" ++ render_ils ils ++ "</span>"
  | FootnoteReference _ => "" (* TODO Phase 1 *)
  | UrlLink _ => ""           (* TODO Phase 1 *)
  | EmailLink _ => ""         (* TODO Phase 1 *)
  | RawInline _ _ => ""       (* TODO Phase 1 *)
  | NonBreakingSpace => "&nbsp;"
  | Quoted _ _ => ""          (* TODO Phase 1 *)
  | SoftBreak => nl
  | HardBreak => "<br>" ++ nl
  end.

Definition render_inlines (ils : inlines) : string :=
  String.concat "" (map (fun n => render_inline (node_contents n)) ils).

(*
Blocks
======
*)

(* The node's attributes ride alongside its payload: they belong on the
   opening tag (today only the auto-identifiers the whole-document pass
   puts on sections and quoted headings), but recursion still has to be
   on `block` — `list (node block)` is two type constructors deep, which
   the guard checker will not follow from a `node block` argument. *)
Fixpoint render_block (b : block) (a : attr) {struct b} : string :=
  let render_bs :=
    fix go (ns : list (node block)) : string :=
      match ns with
      | [] => ""
      | Node _ a' x :: rest => render_block x a' ++ go rest
      end in
  (* In a tight list a paragraph loses its <p>: the item's text is
     emitted bare, with the newline the tag would have carried.  Only
     paragraphs are affected — a nested list inside a tight item still
     renders as itself.  Attributes on such a paragraph have nowhere to
     go, and nothing produces them yet. *)
  let render_tight :=
    fix got (ns : list (node block)) : string :=
      match ns with
      | [] => ""
      | Node _ _ (Para ils) :: rest => render_inlines ils ++ nl ++ got rest
      | Node _ a' x :: rest => render_block x a' ++ got rest
      end in
  let render_items :=
    fix goi (sp : list_spacing) (its : list (list (node block))) {struct its}
      : string :=
      match its with
      | [] => ""
      | it :: rest =>
          "<li>" ++ nl
          ++ (match sp with Tight => render_tight it | Loose => render_bs it end)
          ++ "</li>" ++ nl ++ goi sp rest
      end in
  let ats := render_attrs a in
  match b with
  | Para ils => "<p" ++ ats ++ ">" ++ render_inlines ils ++ "</p>" ++ nl
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
  | TaskList _ _ => ""        (* TODO Phase 1 *)
  | DefinitionList _ _ => ""  (* TODO Phase 1 *)
  | ThematicBreak => "<hr" ++ ats ++ ">" ++ nl
  | Table _ _ => ""           (* TODO Phase 1 *)
  | RawBlock fmt contents =>
      if String.eqb fmt "html" then contents else ""
  (* A reference definition is not content: djot.js keeps it out of the
     block tree entirely and emits nothing for it. *)
  | RefDef _ _ => ""
  end.

Definition render_node (n : node block) : string :=
  match n with Node _ a b => render_block b a end.

Definition render_blocks (bs : blocks) : string :=
  String.concat "" (map render_node bs).

Definition render_html (d : doc) : string := render_blocks (doc_blocks d).

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
