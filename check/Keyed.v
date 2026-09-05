(* ai-disclosure: ai-generated *)

(*
The key connective, pinned
==========================

`.project/keyed-blocks.md` defines the construct; this is every rule of
it that the parser implements, as a closed document apiece.  Sections 3
and 4, retraction (6), and the first three worked examples (7.1 to 7.3)
plus the nesting one (7.6).  Section 5 -- claiming a block out of column
-- is not implemented, and the example at the end of this file is what
the parser does instead.

The split rule itself is pinned line by line beside `Inline.key_split`;
here the unit is a document, and what is being checked is where the
block boundaries land.

Out of the dune build for `check/Markdown.v`'s reason: `vm_compute` over
whole documents is not something a parser edit should pay for.

```
dune build && rocq c -R _build/default/theories DjotV check/Keyed.v
```
*)

From Stdlib Require Import String List Ascii.
From DjotV Require Import Strings Ast Line Inline Parser Render Roundtrip.
Import ListNotations.
Open Scope string_scope.

Local Notation Djot := (@parse_blocks _ djot_bconfig).
Local Notation Key := (@parse_blocks _ keyed_bconfig).

Definition para (s : string) : node block :=
  mk (Para [mk (Str s)]).

(*
The setting is a mode
---------------------
*)

(* Non-conservative, which is the whole reason it is off by default: the
   same document parses differently, and the djot reading is a valid
   paragraph rather than an error. *)
Example keys_change_a_valid_document :
  Djot "foo: bar" = [para "foo: bar"]
  /\ Key "foo: bar" = [mk (Keyed [mk (Str "foo")] (para "bar"))].
Proof. split; vm_compute; reflexivity. Qed.

(*
7.1 Top level, line-final
-------------------------
*)

(* The key line opens no paragraph, so the marker on line 2 arrives with
   nothing open and starts a list normally.  No override is involved. *)
Example key_takes_a_list :
  Key "foo:
- bar
- baz"
  = [mk (Keyed [mk (Str "foo")]
           (mk (BulletList Tight [[para "bar"]; [para "baz"]])))].
Proof. vm_compute. reflexivity. Qed.

(*
7.2 Top level, inline
---------------------
*)

(* The value opens a paragraph, and that paragraph continues onto the
   lines after it like any other. *)
Example key_value_is_a_paragraph :
  Key "foo: bar
baz"
  = [mk (Keyed [mk (Str "foo")]
           (mk (Para [mk (Str "bar"); mk SoftBreak; mk (Str "baz")])))].
Proof. vm_compute. reflexivity. Qed.

(*
7.3 A key inside a list item, indented
--------------------------------------
*)

(* The direct answer to what djot cannot spell: a *tight* list item with
   a code block child.  Line 2 is indented past the marker, so the item
   takes it the ordinary way. *)
Example key_in_a_tight_item :
  Key "- foo:
  ```
  bar
  ```"
  = [mk (BulletList Tight
           [[mk (Keyed [mk (Str "foo")] (mk (CodeBlock "" "bar
")))]])].
Proof. vm_compute. reflexivity. Qed.

(*
7.6 Nesting keys
----------------
*)

(* One colon per line, one level per line.  Line 2 arrives with `foo`'s
   key open and nothing else, so it opens a key of its own. *)
Example keys_nest_by_line :
  Key "foo:
bar:
baz"
  = [mk (Keyed [mk (Str "foo")]
           (mk (Keyed [mk (Str "bar")] (para "baz"))))].
Proof. vm_compute. reflexivity. Qed.

(* And the one-line form is not sugar for the two-line one (3.3): a line
   is split at most once, so the second colon is the value's text. *)
Example one_key_per_line :
  Key "foo: bar: baz"
  = [mk (Keyed [mk (Str "foo")] (para "bar: baz"))].
Proof. vm_compute. reflexivity. Qed.

(* The value is inline content, never block syntax.  A list marker after
   the colon is text; the same marker on the next line is a list. *)
Example value_is_never_block_syntax :
  Key "foo: - bar" = [mk (Keyed [mk (Str "foo")] (para "- bar"))].
Proof. vm_compute. reflexivity. Qed.

(*
3.5 The split is asked once, when the line is classified
--------------------------------------------------------
*)

(* A paragraph is already open when its second line arrives, so a colon
   there is text.  This is why a key directly under a paragraph needs a
   blank line in front of it. *)
Example continuation_lines_are_never_tested :
  Key "foo
bar: baz"
  = [mk (Para [mk (Str "foo"); mk SoftBreak; mk (Str "bar: baz")])].
Proof. vm_compute. reflexivity. Qed.

(* A key opens from a text line only, so a heading's colon is a
   heading's. *)
Example a_heading_is_not_a_key :
  Key "# foo:" = [mk (Heading 1 [mk (Str "foo:")])].
Proof. vm_compute. reflexivity. Qed.

(* An escaped colon is not a connective, and the escape leaves the text
   it always was. *)
Example an_escaped_colon_is_text :
  Key "foo\: bar" = [para "foo: bar"].
Proof. vm_compute. reflexivity. Qed.

(* Nor is one with no space after it. *)
Example a_url_is_not_a_key :
  Key "http://x" = [para "http://x"].
Proof. vm_compute. reflexivity. Qed.

(* 3.2: to name the keyed node rather than the label, the attribute goes
   on its own line above.  A brace inside the label decorates the label. *)
Example an_attribute_line_names_the_node :
  Key "{#my-foo}
foo: bar"
  = [Node NoPos [("id", "my-foo")]
       (Keyed [mk (Str "foo")] (para "bar"))].
Proof. vm_compute. reflexivity. Qed.

(*
6 Retraction
------------

A key retracts when it is ended while nothing is open under it, and what
it retracts to is the key line as written.
*)

Example blank_retracts :
  Key "foo:

bar" = [para "foo:"; para "bar"].
Proof. vm_compute. reflexivity. Qed.

Example end_of_input_retracts :
  Key "foo:" = [para "foo:"].
Proof. vm_compute. reflexivity. Qed.

(* An enclosing container ending retracts it too, inside that container. *)
Example a_closing_quote_retracts :
  Key "> foo:
plain"
  = [mk (BlockQuote [para "foo:"]); para "plain"].
Proof. vm_compute. reflexivity. Qed.

Example a_closing_div_retracts :
  Key ":::
foo:
:::"
  = [mk (Div [para "foo:"])].
Proof. vm_compute. reflexivity. Qed.

(* And the two rows that say the test cannot be "a blank retracts": a
   blank reaches the key only when nothing under it claimed it first. *)
Example a_lists_blank_is_not_the_keys :
  Key "foo:
- a

- b"
  = [mk (Keyed [mk (Str "foo")]
           (mk (BulletList Loose [[para "a"]; [para "b"]])))].
Proof. vm_compute. reflexivity. Qed.

(* 6.2, the corner: an attribute spec starts something without producing
   a block, so the key does not retract at the blank and goes on to take
   the paragraph below it.  Accepted rather than repaired. *)
Example an_open_spec_holds_the_key_across_a_blank :
  Key "foo:
{#i}

bar"
  = [mk (Keyed [mk (Str "foo")] (para "bar"))].
Proof. vm_compute. reflexivity. Qed.

(* The same corner at end of input goes the other way: a lone attribute
   line contributes no block, so the key ends with none and retracts. *)
Example a_spec_alone_leaves_the_key_with_no_block :
  Key "foo:
{#i}" = [para "foo:"].
Proof. vm_compute. reflexivity. Qed.

(*
5.2 A block whose end nobody announces cannot be claimed out of column
----------------------------------------------------------------------
*)

(* Two list items, and `foo:` is not a key.  This is the reading the
   construct exists to protect, and it needs no rule of its own: the
   sibling marker closes the item, which ends the key while nothing is
   open under it. *)
Example a_sibling_marker_retracts :
  Key "- foo:
- bar"
  = Djot "- foo:
- bar".
Proof. vm_compute. reflexivity. Qed.

(*
Literal colons in canonical source
---------------------------------

The same spelling works in both modes.  The shared inline escape also
protects continuation lines and text inside containers; no first-line
renderer is needed.  Pin acceptance separately from roundtrip so these
documents cannot silently leave the canonical fragment.
*)

Example literal_colon_source :
  cb_lines (cpara ["Note: this matters."; "ends:"])
    = ["Note\: this matters\."; "ends\:"].
Proof. reflexivity. Qed.

Definition literal_colon_documents : list (list cblock) :=
  let p := cpara ["Note: this matters."; "ends:"] in
  [[p]; [cpara ["Note\: this matters."]];
   [CQuote [p]]; [CList LKBullet Tight [[p]]];
   [CId "note" p]; [p; p]].

Example literal_colon_documents_accepted :
  forallb (@cblocks_ok _ keyed_bconfig) literal_colon_documents = true.
Proof. vm_compute. reflexivity. Qed.

Example literal_colon_documents_roundtrip :
  forall cbs, In cbs literal_colon_documents ->
    Key (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof.
  intros cbs Hin. apply roundtrip_blocks.
  pose proof literal_colon_documents_accepted as H.
  rewrite forallb_forall in H. exact (H cbs Hin).
Qed.

Example literal_colon_source_with_keys_off :
  Djot (render_djot [para "Note: this matters."])
    = [para "Note: this matters."].
Proof. vm_compute. reflexivity. Qed.

(* Appending the connective to the escaped label must split at that
   final colon, and keep both the label's colon and the value's colon. *)
Example escaped_colon_label :
  let label := ci_line [CIStr "Note: this"] in
  key_split (label ++ ":") = Some (label, "")
  /\ Key (label ++ ":" ++ nl ++ ci_line [CIStr "value: text"])
    = [mk (Keyed [mk (Str "Note: this")] (para "value: text"))].
Proof. split; vm_compute; reflexivity. Qed.

(* Canonical keys retain both wrapper orders, nest, and leave the
   child's list/table boundary conditions visible to its next sibling. *)
Definition canonical_key_documents : list (list cblock) :=
  let key := CKey (CIStr "Note: this") in
  let p := cpara ["value: text"] in
  let l := CList LKBullet Tight [[p]] in
  let t := CTable [CTBody [[CIStr "cell"]]] in
  [[key p]; [key (CId "child" p)]; [CId "key" (key p)];
   [key (key p)]; [key (CCode "" ["code"])]; [key (CDiv [])];
   [CQuote [key p]]; [CDiv [key p]]; [CList LKBullet Tight [[key p]]];
   [key l; p]; [key l; key l]; [key t; p]; [key p; key p];
   [CKey (CIVerb "code") p];
   [CKey (CIDelim DStrong [CIStr "strong"]) p];
   [CKey (CILink false [CIStr "see"] "note") p];
   [CKey (CIRef false [CIStr "see"] "ref") p]].

Example canonical_key_documents_accepted :
  forallb (@cblocks_ok _ keyed_bconfig) canonical_key_documents = true.
Proof. vm_compute. reflexivity. Qed.

Example canonical_key_documents_roundtrip :
  forall cbs, In cbs canonical_key_documents ->
    Key (render_djot (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
Proof.
  intros cbs Hin. apply roundtrip_blocks.
  pose proof canonical_key_documents_accepted as H.
  rewrite forallb_forall in H. exact (H cbs Hin).
Qed.

Example canonical_key_source :
  render_djot [cb_ast (CKey (CIStr "Note: this") (CId "child" (cpara ["value: text"])))]
    = "Note\: this:" ++ nl ++ "{#child}" ++ nl ++ "value\: text".
Proof. reflexivity. Qed.

Example canonical_key_exclusions :
  let p := cpara ["value"] in
  (@cb_ok _ djot_bconfig (CKey (CIStr "key") p),
   @cb_ok _ keyed_bconfig (CKey (CIStr "") p),
   @cb_ok _ keyed_bconfig (CKey (CIStr "trailing ") p),
   @cb_ok _ keyed_bconfig (CKey (CINote "note") p))
    = (false, false, false, false).
Proof. vm_compute. reflexivity. Qed.

Example keyed_list_boundary :
  let l := CList LKBullet Tight [[cpara ["a"]]] in
  @cblocks_ok _ keyed_bconfig [CKey (CIStr "key") l; l] = false.
Proof. vm_compute. reflexivity. Qed.

(* A blank before a child retracts; an unfinished attribute prefix has
   no child to promise to the key.  Neither may pass the prefix check. *)
Example key_content_requires_a_child :
  (@key_content_ok _ keyed_bconfig [""] (PPara []),
   @key_content_ok _ keyed_bconfig ["{#i}"] (PPara []),
   @key_content_ok _ keyed_bconfig ["{#i}"; "value"] (PPara []))
    = (false, false, true).
Proof. vm_compute. reflexivity. Qed.

(*
Section 5 is not implemented
----------------------------

A block at a column the enclosing container would refuse is still
refused: the list ends at line 2, the key retracts, and the fence and
the second marker are read outside it.  Section 5 would make this one
list whose first item is `Keyed "foo"` over the code block.  The cost of
getting there is `.project/keyed-blocks.md` 9.2, and this example is
what has to change when it is paid.
*)

Example out_of_column_is_not_claimed :
  Key "- foo:
```
bar
```
- baz"
  = [mk (BulletList Tight [[para "foo:"]]);
     mk (CodeBlock "" "bar
");
     mk (BulletList Tight [[para "baz"]])].
Proof. vm_compute. reflexivity. Qed.
