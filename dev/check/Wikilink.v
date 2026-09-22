(* ai-disclosure: ai-generated *)

(*
Wikilinks, pinned
=================

Every row of `.project/wikilinks.md` sections 3, 7 and 9.4, as the
parser reads it with the setting on.  The spec is the reference: no djot
implementation has the construct, so nothing here is checked against an
oracle.  The last section pins what the setting changes for the rest of
the language, which is where it is not conservative.
*)

From Stdlib Require Import String List Ascii.
From DjotV Require Import Ast Strings Inline Parser Config Document Html.
From DjotVDev.check Require Import Located.
Import ListNotations.
Open Scope string_scope.

Definition wiki_table : dtable :=
  DTable (with_wikilinks true djot_config) eq_refl.

Local Notation W := (@parse_inline_line wiki_table).
Local Notation WBlocks := (@parse_blocks wiki_table djot_bconfig).

Definition wiki (t : string) : node inline := mk (Wikilink false t None).
Definition wiki_alias (t a : string) : node inline :=
  mk (Wikilink false t (Some a)).

(*
The worked examples (section 7)
-------------------------------
*)

Example w_plain :
  W "see [[Backlinks]] for more"
  = [mk (Str "see "); wiki "Backlinks"; mk (Str " for more")].
Proof. vm_compute. reflexivity. Qed.

Example w_alias :
  W "see [[Backlinks|the other direction]]"
  = [mk (Str "see "); wiki_alias "Backlinks" "the other direction"].
Proof. vm_compute. reflexivity. Qed.

Example w_two : W "[[a]] and [[b|c]]" = [wiki "a"; mk (Str " and "); wiki_alias "b" "c"].
Proof. vm_compute. reflexivity. Qed.

(* The closer is the first `]]`, and nothing looks inside the region. *)
Example w_nested : W "[[a [[b]] c]]" = [wiki "a [[b"; mk (Str " c]]")].
Proof. vm_compute. reflexivity. Qed.

(*
The region (sections 3.2 and 3.3)
---------------------------------
*)

Example w_single_rbrack : W "[[a]b]]" = [wiki "a]b"].
Proof. vm_compute. reflexivity. Qed.

(* A backslash protects the next byte and is kept. *)
Example w_escape_kept : W "[[a\]]]" = [wiki "a\]"].
Proof. vm_compute. reflexivity. Qed.

Example w_markup_is_source : W "[[*a*]]" = [wiki "*a*"].
Proof. vm_compute. reflexivity. Qed.

Example w_untrimmed : W "[[ a ]]" = [wiki " a "].
Proof. vm_compute. reflexivity. Qed.

(* The second `[` still sits at the start of the first one's scope. *)
Example w_after_text : W "x[[a]]" = [mk (Str "x"); wiki "a"].
Proof. vm_compute. reflexivity. Qed.

(*
Where a `[[` is not a wikilink (section 3.4)
--------------------------------------------
*)

Example w_row1_escaped : W "\[[a]]" = [mk (Str "[[a]]")].
Proof. vm_compute. reflexivity. Qed.

Example w_row2_not_at_start : W "[a[b]]" = [mk (Str "[a[b]]")].
Proof. vm_compute. reflexivity. Qed.

Example w_row3_empty : W "[[]]" = [mk (Str "[[]]")] /\ W "[[|b]]" = [mk (Str "[[|b]]")].
Proof. split; vm_compute; reflexivity. Qed.

(* ...and its closer is text, so it cannot close a link around it. *)
Example w_row3_inside_link :
  W "[x [[]] y](u)" = [mk (Link [mk (Str "x [[]] y")] (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

Example w_row4_unclosed : W "[[a" = [mk (Str "[[a")].
Proof. vm_compute. reflexivity. Qed.

Example w_row5_no_break :
  WBlocks "[[a
b]]" = [mk (Para [mk (Str "[[a"); mk SoftBreak; mk (Str "b]]")])].
Proof. vm_compute. reflexivity. Qed.

Example w_row6_verbatim : W "`[[a]]`" = [mk (Verbatim "[[a]]")].
Proof. vm_compute. reflexivity. Qed.

Example w_row7_embed : W "![[a]]" = [mk (Wikilink true "a" None)].
Proof. vm_compute. reflexivity. Qed.

Example w_row8_cell :
  WBlocks "| [[a|b]] |"
  = [mk (Table None [[Cell BodyCell AlignDefault [mk (Str "[[a")];
                      Cell BodyCell AlignDefault [mk (Str "b]]")]]])].
Proof. vm_compute. reflexivity. Qed.

Example w_row9_link_text : W "[[1]](u)" = [wiki "1"; mk (Str "(u)")].
Proof. vm_compute. reflexivity. Qed.

Example w_row10_link_inside : W "[[a](b)" = [mk (Str "[[a](b)")].
Proof. vm_compute. reflexivity. Qed.

(* Section 9.4: the row splitter leaves an escaped bar in its cell, and
   the region keeps the backslash. *)
Example w_cell_escaped_bar :
  WBlocks "| [[a\|b]] |"
  = [mk (Table None [[Cell BodyCell AlignDefault [wiki "a\|b"]]])].
Proof. vm_compute. reflexivity. Qed.

(*
Rendering (section 5)
---------------------
*)

Example w_html :
  render_html (parse_doc (T:=wiki_table) "[[a]] [[a|the other direction]] ![[a]]")
  = "<p><a href=""a"">a</a> <a href=""a"">the other direction</a> <img alt=""a"" src=""a""></p>
".
Proof. vm_compute. reflexivity. Qed.

(*
Source ranges
-------------

Byte ranges of a paragraph's inlines, as `Located.v` reads them.  The
node runs from its first bracket, or the `!` of an embed, to the closing
`]]`; an attribute spec after it widens it no more than it widens a
link.
*)

Definition wiki_ranges (s : string) : list (nat * nat) :=
  inline_walk 40 (line_table s)
    (first_para 20 (@parse_blocks_located wiki_table djot_bconfig s)).

Example r_wiki : wiki_ranges "p [[a]] q" = [(0, 2); (2, 7); (7, 9)].
Proof. vm_compute. reflexivity. Qed.

Example r_wiki_alias : wiki_ranges "p [[a|b]] q" = [(0, 2); (2, 9); (9, 11)].
Proof. vm_compute. reflexivity. Qed.

Example r_wiki_embed : wiki_ranges "p ![[a]] q" = [(0, 2); (2, 8); (8, 10)].
Proof. vm_compute. reflexivity. Qed.

Example r_wiki_attr : wiki_ranges "[[a]]{.c} x" = [(0, 5); (9, 11)].
Proof. vm_compute. reflexivity. Qed.

(* A decayed candidate is text, merged with the text around it. *)
Example r_wiki_empty : wiki_ranges "p [[]] q" = [(0, 8)].
Proof. vm_compute. reflexivity. Qed.

Example r_wiki_break :
  wiki_ranges "p [[a
b]] q" = [(0, 5); (5, 6); (6, 11)].
Proof. vm_compute. reflexivity. Qed.

(*
With the setting off
--------------------
*)

Example w_off : @parse_inline_line djot_table "[[a|b]]" = [mk (Str "[[a|b]]")].
Proof. vm_compute. reflexivity. Qed.
