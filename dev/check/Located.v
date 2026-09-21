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
From DjotV Require Import Ast Strings Inline Step Parser Config
  Render Document Html Generate.
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
Items, the first of the parts
-----------------------------

A list item is not a node, so its range lives in the parent's
provenance, parallel to the children (plan F9).  A definition list's
item splits further into a term and a definition; that is `PDefItems`
and is not built yet, so a `:` list reports the item as a whole.
*)

Definition item_ranges (s : string) : list (list (nat * nat)) :=
  let lines := line_table s in
  map (fun n =>
         match node_provenance n with
         | Some p =>
             match part_spans p with
             | PItems rs => map (range_of lines) rs
             | _ => []
             end
         | None => []
         end)
      (Located s).

(* list_item [0,8), list_item [9,12) *)
Example p_bullet_items : item_ranges "- a

  b
- c
" = [[(0, 8); (9, 12)]].
Proof. vm_compute. reflexivity. Qed.

(* list_item [0,6), [7,13) *)
Example p_ordered_items : item_ranges "1. one
2. two
" = [[(0, 6); (7, 13)]].
Proof. vm_compute. reflexivity. Qed.

(* task_list_item [0,7), [8,15) *)
Example p_task_items : item_ranges "- [ ] t
- [x] d
" = [[(0, 7); (8, 15)]].
Proof. vm_compute. reflexivity. Qed.

(* definition_list_item [0,13) *)
Example p_def_item : item_ranges ": term

  def
" = [[(0, 13)]].
Proof. vm_compute. reflexivity. Qed.

(*
Sections, from the document pass
--------------------------------

A section is not built from a line, so its range is the hull of the
heading and the blocks under it.  `walk` follows `Section` here as it
follows a quote.
*)

Fixpoint doc_walk (d : nat) (lines : list source_line) (bs : blocks)
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
            | Section bs' | BlockQuote bs' | Div bs' => doc_walk d' lines bs'
            | _ => []
            end in
          (here :: kids ++ doc_walk d' lines rest)%list
      end
  end.

Definition doc_ranges (s : string) : list (nat * nat) :=
  doc_walk 20 (line_table s)
    (doc_blocks (@parse_doc_located djot_table djot_bconfig s)).

(* section [0,16), heading [0,10), para [12,16) *)
Example r_section : doc_ranges "# Head *x*

para
" = [(0, 16); (0, 10); (12, 16)].
Proof. vm_compute. reflexivity. Qed.

(* section [0,17), heading [0,5), section [6,17), heading [6,17) -- the
   inner heading runs on to its continuation line, as it does in
   djot.js, and the section it opens is the same range. *)
Example r_nested_sections : doc_ranges "# one
## two
text
" = [(0, 17); (0, 5); (6, 17); (6, 17)].
Proof. vm_compute. reflexivity. Qed.

(* The id moves from the heading to the section it opens, as it does in
   djot.js, so the spec that authored the id moves with it: the section
   spans the heading, [10,16), and carries `{#anchor}` at [0,9).  That
   pair is what a duplicate-id diagnostic points at. *)
Definition doc_anchor (s : string) : list (attr * list (syntax_role * (nat * nat))) :=
  let lines := line_table s in
  map (fun n =>
         (node_attrs n,
          match node_provenance n with
          | Some p => map (fun e => (fst e, range_of lines (snd e)))
                        (syntax_spans p)
          | None => []
          end))
      (doc_blocks (@parse_doc_located djot_table djot_bconfig s)).

Example r_heading_anchor :
  doc_anchor "{#anchor}
# Head
" = [([("id", "anchor")], [(RAttrSpec, (0, 9))])].
Proof. vm_compute. reflexivity. Qed.

Example r_heading_anchor_span :
  doc_ranges "{#anchor}
# Head
" = [(10, 16); (10, 16)].
Proof. vm_compute. reflexivity. Qed.

(*
The semantic parse is untouched
-------------------------------

Not a range fact, but the one every range rests on: the located parse
and the parse every theorem is about differ only in what the nodes
carry.
*)

Example semantic_unchanged :
  erase_blocks (Located "# h

para more
")
  = @parse_blocks djot_table djot_bconfig _ _ "# h

para more
".
Proof. vm_compute. reflexivity. Qed.

(* And over the generated pool, where the documents are not chosen by
   hand: every canonical block at depth 1 renders the same HTML through
   the located parse as through the semantic one.  Depth 2 (3695
   documents) was run the same way and is clean; it is out of the build
   because it takes 29s against 0.9s here.  This is the evidence for the
   erasure theorem the plan owes at C2, not the theorem. *)
Definition html_of (bs : blocks) : string := render_html (doc_pass bs).

Definition agrees (c : cblock) : bool :=
  let s := render_djot (blocks_of_cblocks [c]) in
  String.eqb (html_of (Located s))
             (html_of (@parse_blocks djot_table djot_bconfig _ _ s)).

Example located_agrees_depth_1 : forallb agrees (accepted 1) = true.
Proof. vm_compute. reflexivity. Qed.

(*
Inline ranges, pinned against djot.js
=====================================

The inline scan on its own.  The block layer does not hand its stored
lines to the located scan yet, so these go through
`para_inlines_located` directly: a document that is one paragraph, its
lines with their indices, positions on.  Children follow their parent,
which is the order `djotjs-sourcepos.mjs` prints.
*)

Fixpoint inline_walk (d : nat) (lines : list source_line) (ils : inlines)
  : list (nat * nat) :=
  match d with
  | 0 => []
  | S d' =>
      match ils with
      | [] => []
      | n :: rest =>
          let here :=
            match node_provenance n with
            | Some p => range_of lines (node_span p)
            | None => (999, 999)
            end in
          let kids :=
            match node_contents n with
            | Emph k | Strong k | Highlight k | Insert k | Delete k
            | Superscript k | Subscript k | Span k | Quoted _ k
            | Link k _ | Image k _ => inline_walk d' lines k
            | _ => []
            end in
          (here :: kids ++ inline_walk d' lines rest)%list
      end
  end.

(* The paragraph the located parse built, wherever the document put it:
   the fixtures below go through `parse_blocks_located`, so they pin the
   ranges the block layer hands a consumer and not only the scan's. *)
Fixpoint first_para (d : nat) (bs : blocks) : inlines :=
  match d with
  | 0 => []
  | S d' =>
      match bs with
      | [] => []
      | n :: rest =>
          match node_contents n with
          | Para ils | Heading _ ils => ils
          | BlockQuote bs' | Div bs' | FootnoteDef _ bs' => first_para d' bs'
          | BulletList _ (item :: _) => first_para d' item
          | OrderedList _ _ (item :: _) => first_para d' item
          | _ => first_para d' rest
          end
      end
  end.

Definition para_ranges (s : string) : list (nat * nat) :=
  inline_walk 40 (line_table s) (first_para 20 (Located s)).

(*
One construct at a time
-----------------------

Each range below was read off `djotjs-sourcepos.mjs --trim`.  Two
differences are ours and are noted where they occur; everything else is
byte-for-byte djot.js.
*)

(* str [0,9) *)
Example i_text : para_ranges "para more" = [(0, 9)].
Proof. vm_compute. reflexivity. Qed.

(* str [0,2), strong [2,5), str [3,4), str [5,7) *)
Example i_strong : para_ranges "x *y* z" = [(0, 2); (2, 5); (3, 4); (5, 7)].
Proof. vm_compute. reflexivity. Qed.

(* A doubled run is two nested scopes, and each covers its own token. *)
Example i_strong_nested :
  para_ranges "a **b** c" = [(0, 2); (2, 7); (3, 6); (4, 5); (7, 9)].
Proof. vm_compute. reflexivity. Qed.

Example i_delim_mixed :
  para_ranges "g *a **b** c* h"
  = [(0, 2); (2, 13); (3, 5); (5, 10); (6, 9); (7, 8); (10, 12); (13, 15)].
Proof. vm_compute. reflexivity. Qed.

(* A marked token covers its braces. *)
Example i_marked : para_ranges "{*a*}" = [(0, 5); (2, 3)].
Proof. vm_compute. reflexivity. Qed.

(* ...and an attribute spec after it widens neither the node nor the text
   that follows, which starts after the spec. *)
Example i_marked_attr :
  para_ranges "f {*a*}{.c} g" = [(0, 2); (2, 7); (4, 5); (11, 13)].
Proof. vm_compute. reflexivity. Qed.

(* The intraword row: `_` opens inside a word. *)
Example i_emph_intraword :
  para_ranges "e a_b_c f" = [(0, 3); (3, 6); (4, 5); (6, 9)].
Proof. vm_compute. reflexivity. Qed.

(* A span crossing a line break: the break covers the terminator, and the
   text after it starts on the next line. *)
Example i_break_in_scope :
  para_ranges "a *b
c* d" = [(0, 2); (2, 7); (3, 4); (4, 5); (5, 6); (7, 9)].
Proof. vm_compute. reflexivity. Qed.

(* link [2,14), its label [3,7); the attribute spec is not part of it *)
Example i_link :
  para_ranges "a [link](dest){.c} b" = [(0, 2); (2, 14); (3, 7); (18, 20)].
Proof. vm_compute. reflexivity. Qed.

(* A `]` that makes no construct stays text, and the label runs past it. *)
Example i_link_inner_bracket :
  para_ranges "x [un]b](c) y" = [(0, 2); (2, 11); (3, 7); (11, 13)].
Proof. vm_compute. reflexivity. Qed.

Example i_reference :
  para_ranges "k [r][lbl] l" = [(0, 2); (2, 10); (3, 4); (10, 12)].
Proof. vm_compute. reflexivity. Qed.

Example i_footnote_ref :
  para_ranges "p [^fn] q" = [(0, 2); (2, 7); (7, 9)].
Proof. vm_compute. reflexivity. Qed.

(* Ours: the image starts at its `!`.  djot.js reports [3,15), starting at
   the `[`, which reads as an artifact of recovering the `!` at the close
   (plan F1). *)
Example i_image :
  para_ranges "i ![alt](i.png) j" = [(0, 2); (2, 15); (4, 7); (15, 17)].
Proof. vm_compute. reflexivity. Qed.

Example i_span_attr :
  para_ranges "s [txt]{.c} t" = [(0, 2); (2, 7); (3, 6); (11, 13)].
Proof. vm_compute. reflexivity. Qed.

Example i_verbatim : para_ranges "w `v` u" = [(0, 2); (2, 5); (5, 7)].
Proof. vm_compute. reflexivity. Qed.

(* A verbatim spanning a break: its start is the stop of whatever the
   scope emitted last, so the line it began on is recovered. *)
Example i_verbatim_break :
  para_ranges "v `a
b` w" = [(0, 2); (2, 7); (7, 9)].
Proof. vm_compute. reflexivity. Qed.

(* The line ended inside it: djot.js closes it too. *)
Example i_verbatim_unclosed :
  para_ranges "v `unclosed" = [(0, 2); (2, 11)].
Proof. vm_compute. reflexivity. Qed.

Example i_math : para_ranges "m $`e` n" = [(0, 2); (2, 6); (6, 8)].
Proof. vm_compute. reflexivity. Qed.

(* Ours: the node covers the `{=fmt}` that selects the format, which is
   part of the construct.  djot.js reports the verbatim alone, [2,5)
   (plan F1, section 4.4). *)
Example i_raw_inline :
  para_ranges "r `x`{=html} s" = [(0, 2); (2, 12); (12, 14)].
Proof. vm_compute. reflexivity. Qed.

Example i_url : para_ranges "u <http://a.b> v" = [(0, 2); (2, 14); (14, 16)].
Proof. vm_compute. reflexivity. Qed.

(* A backslash and a space: the node covers the space, as djot.js does,
   and the text before it stops at the backslash. *)
Example i_nbsp : para_ranges "a b\ c" = [(0, 3); (4, 5); (5, 6)].
Proof. vm_compute. reflexivity. Qed.

(* A hard break covers its terminator, and the whitespace the trim
   dropped is in neither node. *)
Example i_hard_break :
  para_ranges "a  \
c" = [(0, 1); (4, 5); (5, 6)].
Proof. vm_compute. reflexivity. Qed.

(*
Openers that decay
------------------

An abandoned opener is text, spanning the source it was written in, and
it merges with the text around it into one node whose range is the hull.
*)

Example i_delim_decays : para_ranges "a *b c" = [(0, 6)].
Proof. vm_compute. reflexivity. Qed.

Example i_bracket_decays : para_ranges "x [nope y" = [(0, 9)].
Proof. vm_compute. reflexivity. Qed.

Example i_destination_decays : para_ranges "n [u](a m" = [(0, 9)].
Proof. vm_compute. reflexivity. Qed.

(*
Through the containers
----------------------

The same scan reached from `parse_blocks_located`, where the stored line
is a suffix of its source line: the C4 witness, whose paragraph sits two
containers deep, and whose ranges are still djot.js's.
*)

(* block_quote [0,22), bullet_list [2,22), list_item [2,22),
   para [4,22), str [4,6), link [6,18), str [7,11) *)
Example i_witness_under_containers :
  para_ranges "> - a [link](dest){.c}
" = [(4, 6); (6, 18); (7, 11)].
Proof. vm_compute. reflexivity. Qed.

Example i_witness_blocks :
  ranges "> - a [link](dest){.c}
" = [(0, 22); (2, 22); (4, 22)].
Proof. vm_compute. reflexivity. Qed.

(* A heading's inlines are a paragraph's, and start after the marker. *)
Example i_heading_inlines :
  para_ranges "## a *b*
" = [(3, 5); (5, 8); (6, 7)].
Proof. vm_compute. reflexivity. Qed.

(*
The attribute spec an inline carries
------------------------------------

A span records the spec that attached to it, as `RAttrSpec`; a text run
does not, because resolution runs at the ambient policy -- `oresolve_go`
opens no policy context, so `oattach_list` cannot record one.  Section 1
of the plan wants both (the anchor a rename of an id points at), so this
is a gap and not a decision; it is pinned here so that closing it is
visible.
*)

Definition inline_roles (s : string)
  : list (attr * list (syntax_role * (nat * nat))) :=
  let lines := line_table s in
  map (fun n =>
         (node_attrs n,
          match node_provenance n with
          | Some p => map (fun e => (fst e, range_of lines (snd e)))
                        (syntax_spans p)
          | None => []
          end))
      (first_para 20 (Located s)).

Example i_span_spec : inline_roles "[s]{.c}" = [([("class", "c")], [(RAttrSpec, (3, 7))])].
Proof. vm_compute. reflexivity. Qed.

(* The gap: the spec attached, and its range was dropped. *)
Example i_text_spec_has_no_role :
  inline_roles "a{.c}" = [([("class", "c")], [])].
Proof. vm_compute. reflexivity. Qed.
