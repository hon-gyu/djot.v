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
Canonical blocks
================
*)

Inductive cblock : Type :=
  | CPara (ls : list string)
  | CThematic
  | CCode (info : string) (content : list string).

Definition thematic_line : string := "* * * *".
Definition code_close : string := "```".
Definition code_open (info : string) : string := "```" ++ info.

Definition cb_lines (cb : cblock) : list string :=
  match cb with
  | CPara ls => ls
  | CThematic => [thematic_line]
  | CCode info content => (code_open info :: content ++ [code_close])%list
  end.

Definition cb_ast (cb : cblock) : node block :=
  match cb with
  | CPara ls => mk (Para (para_inlines ls))
  | CThematic => mk ThematicBreak
  | CCode info content => fence_block (Fence "`"%char 3 info) content
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

Definition cb_ok (cb : cblock) : bool :=
  match cb with
  | CPara ls => para_ok ls
  | CThematic => true
  | CCode info content => code_ok info content
  end.

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

Definition render_block_djot (b : block) : string :=
  match b with
  | Para ils => String.concat nl (inline_lines ils EmptyString)
  | ThematicBreak => thematic_line
  | CodeBlock lang text => "```" ++ lang ++ nl ++ text ++ code_close
  | RawBlock fmt text => "```=" ++ fmt ++ nl ++ text ++ code_close
  | _ => ""   (* TODO: extend with the parser, construct by construct *)
  end.

Definition render_djot (d : doc) : string :=
  String.concat (nl ++ nl)
    (map (fun n => render_block_djot (node_contents n)) (doc_blocks d)).

(* Rendering of line lists, the form the roundtrip proof composes over. *)

Definition render_paras (lss : list (list string)) : string :=
  String.concat (nl ++ nl) (map (String.concat nl) lss).
