(* Djot rendering (AST -> djot source), modeled on djoths's Djot.hs.

   Phase 1 scope: the paragraph fragment the parser currently covers.
   `renderable` captures the canonical form this renderer inverts; the
   roundtrip theorem is in Roundtrip.v. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Ast Parser.
Import ListNotations.

Local Open Scope string_scope.

(*
Renderability of the paragraph fragment
=======================================

A canonical paragraph is `para_inlines lines` for a list of lines that
are nonblank, newline-free, and whose last line carries no trailing
whitespace (the parser strips it, so a roundtripping AST cannot have it).
*)

Fixpoint no_nl (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => negb (Ascii.eqb c "010") && no_nl s'
  end.

Definition line_ok (l : string) : bool :=
  negb (is_blank l) && no_nl l.

Definition para_ok (ls : list string) : bool :=
  match ls with
  | [] => false
  | _ => forallb line_ok ls
         && String.eqb (strip_trailing_ws (last ls EmptyString))
              (last ls EmptyString)
  end.

Definition doc_of_paras (lss : list (list string)) : doc :=
  {| doc_blocks := map (fun ls => mk (Para (para_inlines ls))) lss
   ; doc_footnotes := []
   ; doc_references := []
   ; doc_auto_references := []
   ; doc_auto_identifiers := [] |}.

(*
The renderer
------------
*)

Definition nl : string := String "010"%char EmptyString.

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
  | _ => ""   (* TODO: extend with the parser, construct by construct *)
  end.

Definition render_djot (d : doc) : string :=
  String.concat (nl ++ nl)
    (map (fun n => render_block_djot (node_contents n)) (doc_blocks d)).

(* Rendering of paragraph line lists, the form the roundtrip proof uses. *)

Definition render_para (ls : list string) : string := String.concat nl ls.

Definition render_paras (lss : list (list string)) : string :=
  String.concat (nl ++ nl) (map render_para lss).
