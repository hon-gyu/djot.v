(* ai-disclosure: ai-generated *)

(*
Block ranges, pinned against djot.js
====================================

Every range below was read off `harness/oracles/djotjs-sourcepos.mjs
--trim` and is recorded beside the `Example` that asserts it.  Two
conventions make the comparison direct: the script prints 0-based
half-open byte ranges, and `resolve` here turns the parser's
end-anchored `spot`s into the same thing.

What the oracle does not decide is the attribute-spec ranges: djot.js
gives an attribute spec no position at all, so `RAttrSpec` is pinned
against the source text alone (plan F1, section 9).
*)

From Stdlib Require Import String List.
From DjotV Require Import Ast Strings Inline Step Parser Config.
Import ListNotations.
Open Scope string_scope.

Local Notation Located := (@parse_blocks_located djot_table djot_bconfig).

(* A missing byte would mean a spot outside its line, which is a bug
   rather than a range; it is spelled as a number no input can produce. *)
Definition byte_of (lines : list source_line) (p : spot) : nat :=
  match spot_byte lines p with Some b => b | None => 999 end.

Definition range_of (lines : list source_line) (r : span) : nat * nat :=
  (byte_of lines (span_start r), byte_of lines (span_stop r)).

(* Block ranges in document order, a parent before the blocks it
   contains.  Fuel because the walk is not structural in an argument
   Rocq can see; no document here is anywhere near the bound. *)
Fixpoint walk (d : nat) (lines : list source_line) (bs : blocks)
  : list (nat * nat) :=
  match d with
  | 0 => []
  | S d' =>
      match bs with
      | [] => []
      | n :: rest =>
          let here :=
            match node_provenance n with
            | Some p => range_of lines (node_span p)
            | None => (999, 999)
            end in
          let kids :=
            match node_contents n with
            | BlockQuote bs' | Div bs' | FootnoteDef _ bs' => walk d' lines bs'
            | BulletList _ items => flat_map (walk d' lines) items
            | OrderedList _ _ items => flat_map (walk d' lines) items
            | _ => []
            end in
          (here :: kids ++ walk d' lines rest)%list
      end
  end.

Definition ranges (s : string) : list (nat * nat) :=
  walk 20 (line_table s) (Located s).

Definition roles (s : string) : list (list (syntax_role * (nat * nat))) :=
  let lines := line_table s in
  map (fun n =>
         match node_provenance n with
         | Some p => map (fun e => (fst e, range_of lines (snd e)))
                       (syntax_spans p)
         | None => []
         end)
      (Located s).

(*
One block per line shape
------------------------
*)

(* heading [0,3), para [5,14) *)
Example r_heading_para : ranges "# h

para more
" = [(0, 3); (5, 14)].
Proof. vm_compute. reflexivity. Qed.

(* heading [0,5), heading [6,12) -- djot.js nests them in sections, which
   the block layer does not build; the heading ranges are the same. *)
Example r_two_headings : ranges "# one
## two
" = [(0, 5); (6, 12)].
Proof. vm_compute. reflexivity. Qed.

(* para [0,14): a thematic break does not interrupt a paragraph *)
Example r_para_runs_on : ranges "para
***
other
" = [(0, 14)].
Proof. vm_compute. reflexivity. Qed.

(* reference [0,11) *)
Example r_reference : ranges "[ref]: /url
" = [(0, 11)].
Proof. vm_compute. reflexivity. Qed.

(*
Containers, with what they contain
----------------------------------
*)

(* block_quote [0,16), para [2,16) -- the quote starts at its own marker,
   the paragraph at the first byte of content on the line *)
Example r_quote : ranges "> quoted
> still
" = [(0, 16); (2, 16)].
Proof. vm_compute. reflexivity. Qed.

(* div [0,19) including its closing fence, para [9,15) *)
Example r_div : ranges "::: warn
inside
:::
" = [(0, 19); (9, 15)].
Proof. vm_compute. reflexivity. Qed.

(* bullet_list [0,12), then the paragraphs of its two items: [2,3),
   [7,8), [11,12).  djot.js also spans the items themselves, [0,8) and
   [9,12); those are `parts` and are not built yet (plan F9). *)
Example r_loose_list : ranges "- a

  b
- c
" = [(0, 12); (2, 3); (7, 8); (11, 12)].
Proof. vm_compute. reflexivity. Qed.

(* footnote [0,17), para [6,17) *)
Example r_footnote : ranges "[^1]: note
  more
" = [(0, 17); (6, 17)].
Proof. vm_compute. reflexivity. Qed.

(* table [0,29).  Rows and cells are `parts`, not yet built. *)
Example r_table : ranges "| a | b |
|---|---|
| c | d |
" = [(0, 29)].
Proof. vm_compute. reflexivity. Qed.

(*
Attributes widen nothing
------------------------
*)

(* para [13,17), carrying both specs but starting after them *)
Example r_attr_para : ranges "{#id}
{.cls}
para
" = [(13, 17)].
Proof. vm_compute. reflexivity. Qed.

(* div [5,24), likewise *)
Example r_attr_div : ranges "{#i}
::: warn
inside
:::
" = [(5, 24); (14, 20)].
Proof. vm_compute. reflexivity. Qed.

(*
Fence lines, and whether a closer exists
----------------------------------------
*)

Example y_div_closed : roles "::: warn
inside
:::
" = [[(ROpenFence, (0, 8)); (RCloseFence, (16, 19))]].
Proof. vm_compute. reflexivity. Qed.

(* The input ended inside the div: no `RCloseFence`, which is the bit a
   consumer rewriting a generated region reads. *)
Example y_div_unclosed : roles "::: warn
inside
" = [[(ROpenFence, (0, 8))]].
Proof. vm_compute. reflexivity. Qed.

Example y_code_fence : roles "```py
x = 1
```
" = [[(ROpenFence, (0, 5)); (RCloseFence, (12, 15))]].
Proof. vm_compute. reflexivity. Qed.

(* Each authored spec, in source order.  No oracle: djot.js records
   none of these. *)
Example y_attr_specs : roles "{#id}
{.cls}
para
" = [[(RAttrSpec, (0, 5)); (RAttrSpec, (6, 12))]].
Proof. vm_compute. reflexivity. Qed.

(*
The semantic parse is untouched
-------------------------------

Not a range fact, but the one every range rests on: the located parse
and the parse every theorem is about differ only in what the nodes
carry.
*)

Example semantic_unchanged :
  map (@node_contents block) (Located "# h

para more
")
  = map (@node_contents block)
      (@parse_blocks djot_table djot_bconfig _ _ "# h

para more
").
Proof. vm_compute. reflexivity. Qed.
