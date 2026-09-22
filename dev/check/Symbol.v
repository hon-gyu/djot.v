(* ai-disclosure: autonomous *)

(* Djot symbols are AST nodes even though djot.js renders them as their
   source spelling.  The HTML comparison alone cannot see the distinction. *)
From Stdlib Require Import String List.
From DjotV Require Import Ast Strings Inline Html.
Import ListNotations.
Open Scope string_scope.

Example symbol_node :
  parse_inline_line ":smile:" = [mk (Symbol "smile")].
Proof. vm_compute. reflexivity. Qed.

Example symbol_source_roundtrip :
  parse_inline_line (inline_text (Symbol "smile")) =
    [mk (Symbol "smile")].
Proof. vm_compute. reflexivity. Qed.

Example symbol_alias_bytes :
  parse_inline_line ":+1: :x-y_:" =
    [mk (Symbol "+1"); mk (Str " "); mk (Symbol "x-y_")].
Proof. vm_compute. reflexivity. Qed.

Example symbol_keeps_alias_hyphens :
  parse_inline_line ":a--b:" = [mk (Symbol "a--b")].
Proof. vm_compute. reflexivity. Qed.

Example symbol_followed_by_text :
  parse_inline_line ":ice:scream:" =
    [mk (Symbol "ice"); mk (Str "scream:")].
Proof. vm_compute. reflexivity. Qed.

Example escaped_symbol_is_text :
  parse_inline_line "\:smile:" = [mk (Str ":smile:")].
Proof. vm_compute. reflexivity. Qed.

Example unfinished_symbol_is_text :
  parse_inline_line ":not valid:" = [mk (Str ":not valid:")].
Proof. vm_compute. reflexivity. Qed.

Example empty_symbol_is_text :
  parse_inline_line "::" = [mk (Str "::")].
Proof. vm_compute. reflexivity. Qed.

(* An unclosed candidate keeps the ordinary inline reading of its bytes. *)
Example failed_symbol_keeps_smart_dash :
  Html.convert ":a--b" = ("<p>:a–b</p>" ++ nl).
Proof. vm_compute. reflexivity. Qed.

Example symbol_image_alt_is_empty :
  Html.convert "![a :smile: b](x)" =
    ("<p><img alt=""a  b"" src=""x""></p>" ++ nl).
Proof. vm_compute. reflexivity. Qed.
