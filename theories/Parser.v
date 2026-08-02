(* Phase 0 toy parser: split input into lines, group runs of non-blank
   lines into paragraphs.  Total and structurally recursive — no fuel, no
   measure.  Serves as the smallest thing that can flow through
   extraction and the differential harness. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Ast.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope char_scope.

(*
Line-splitting
==============
*)

(* Append a reversed accumulator of chars as a string onto nothing —
   we build lines char by char, so keep the accumulator as a string
   built in reverse via cons at the end. *)

Fixpoint rev_string_aux (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c s' => rev_string_aux s' (String c acc)
  end.

Definition rev_string (s : string) : string := rev_string_aux s EmptyString.

(* Split on LF.  A trailing newline does not create a trailing empty
   line (matching how both oracles treat end of input). *)

Fixpoint split_lines_aux (s : string) (cur : string) : list string :=
  match s with
  | EmptyString =>
      match cur with
      | EmptyString => []
      | _ => [rev_string cur]
      end
  | String c s' =>
      if Ascii.eqb c "010"
      then rev_string cur :: split_lines_aux s' EmptyString
      else split_lines_aux s' (String c cur)
  end.

Definition split_lines (s : string) : list string := split_lines_aux s EmptyString.

(*
Blank lines and grouping
------------------------
*)

Definition is_ws (c : ascii) : bool :=
  Ascii.eqb c " " || Ascii.eqb c "009" || Ascii.eqb c "013".

Fixpoint is_blank (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => is_ws c && is_blank s'
  end.

(* Trailing whitespace is stripped at the end of a paragraph (but kept on
   interior lines) — observed djot.js/djoths behavior on para.test. *)

Definition strip_trailing_ws (s : string) : string :=
  rev_string
    ((fix drop (r : string) : string :=
        match r with
        | String c r' => if is_ws c then drop r' else r
        | EmptyString => EmptyString
        end) (rev_string s)).

(* Interleave SoftBreak between the lines of one paragraph. *)

Fixpoint para_inlines (l : list string) : inlines :=
  match l with
  | [] => []
  | [x] => [mk (Str (strip_trailing_ws x))]
  | x :: rest => mk (Str x) :: mk SoftBreak :: para_inlines rest
  end.

(* Group consecutive non-blank lines into paragraphs. *)

Fixpoint group_paras (lines : list string) (cur : list string) : blocks :=
  let flush := fun (k : blocks) =>
    match cur with
    | [] => k
    | _ => mk (Para (para_inlines (rev cur))) :: k
    end in
  match lines with
  | [] => flush []
  | l :: rest =>
      if is_blank l
      then flush (group_paras rest [])
      else group_paras rest (l :: cur)
  end.

Definition parse_doc (s : string) : doc :=
  {| doc_blocks := group_paras (split_lines s) []
   ; doc_footnotes := []
   ; doc_references := []
   ; doc_auto_references := []
   ; doc_auto_identifiers := [] |}.

(*
Sanity lemmas
-------------

Small facts that double as regression tests for the definitions. *)

Lemma split_lines_empty : split_lines "" = [].
Proof. reflexivity. Qed.

Lemma parse_doc_blank : doc_blocks (parse_doc "  ") = [].
Proof. reflexivity. Qed.

Example parse_two_paras :
  doc_blocks (parse_doc "hi
there

bye") =
  [ mk (Para [mk (Str "hi"); mk SoftBreak; mk (Str "there")])
  ; mk (Para [mk (Str "bye")]) ].
Proof. reflexivity. Qed.
