(* HTML rendering for the Phase 0 fragment, matching what djot.js and
   djoths emit for plain paragraphs: "<p>...</p>\n" with soft breaks
   preserved as newlines and &, <, > escaped. *)

From Stdlib Require Import String Ascii List.
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

Definition render_inline (il : inline) : string :=
  match il with
  | Str s => escape s
  | SoftBreak => nl
  end.

Definition render_block (b : block) : string :=
  match b with
  | Para ils => "<p>" ++ String.concat "" (map render_inline ils) ++ "</p>" ++ nl
  end.

Definition render_html (d : doc) : string :=
  String.concat "" (map render_block d).

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
