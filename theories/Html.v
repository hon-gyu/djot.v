(* HTML rendering, targeting byte-identical agreement with djot.js's
   renderer (the authority; see .project/oracle-disagreements.md — djoths's
   serialization diverges on attribute order, section wrapping, and task
   items, and we follow djot.js on all three).

   Phase 1 status: paragraphs are rendered faithfully; the remaining
   constructors have placeholder output (empty or skeletal) that will be
   filled in alongside the parser, driven by the corpus diff. *)

From Stdlib Require Import String Ascii List DecimalString Decimal.
From DjotV Require Import Ast Parser.
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

Definition nl : string := String "010"%char EmptyString.

Definition nat_str (n : nat) : string := NilZero.string_of_uint (Nat.to_uint n).

(*
Inlines
=======
*)

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
  | Link _ _ => ""            (* TODO Phase 1 *)
  | Image _ _ => ""           (* TODO Phase 1 *)
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

Fixpoint render_block (b : block) : string :=
  let render_bs :=
    fix go (ns : list (node block)) : string :=
      match ns with
      | [] => ""
      | Node _ _ x :: rest => render_block x ++ go rest
      end in
  match b with
  | Para ils => "<p>" ++ render_inlines ils ++ "</p>" ++ nl
  | Section bs => "<section>" ++ nl ++ render_bs bs ++ "</section>" ++ nl
  (* The <hN> element is faithful; the `id` attribute and the enclosing
     <section> both come from the whole-document pass (auto-identifiers,
     level-driven section nesting) that does not exist yet, so heading
     output still differs from djot.js. *)
  | Heading lvl ils =>
      "<h" ++ nat_str lvl ++ ">" ++ render_inlines ils
      ++ "</h" ++ nat_str lvl ++ ">" ++ nl
  | BlockQuote bs =>
      "<blockquote>" ++ nl ++ render_bs bs ++ "</blockquote>" ++ nl
  | CodeBlock lang code =>
      "<pre><code"
      ++ (match lang with
          | EmptyString => ""
          | _ => " class=""language-" ++ lang ++ """"
          end)
      ++ ">" ++ escape code ++ "</code></pre>" ++ nl
  | Div bs => "<div>" ++ nl ++ render_bs bs ++ "</div>" ++ nl
  | OrderedList _ _ _ => ""   (* TODO Phase 1 *)
  | BulletList _ _ => ""      (* TODO Phase 1 *)
  | TaskList _ _ => ""        (* TODO Phase 1 *)
  | DefinitionList _ _ => ""  (* TODO Phase 1 *)
  | ThematicBreak => "<hr>" ++ nl
  | Table _ _ => ""           (* TODO Phase 1 *)
  | RawBlock fmt contents =>
      if String.eqb fmt "html" then contents else ""
  end.

Definition render_blocks (bs : blocks) : string :=
  String.concat "" (map (fun n => render_block (node_contents n)) bs).

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
