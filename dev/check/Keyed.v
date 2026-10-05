(* ai-disclosure: ai-generated *)

(*
The key connective, pinned
==========================

`.project/keyed-blocks.md` defines the construct; this is every rule of
it that the parser implements, as a closed document apiece.  Sections 3
to 6, including claiming a block out of column (5), and every worked
example of section 7.

The split rule itself is pinned line by line beside `InlineScan.key_split`;
here the unit is a document, and what is being checked is where the
block boundaries land.
*)

From Stdlib Require Import String List Ascii.
From DjotV Require Import Strings Ast Line Inline Parser Render Roundtrip.
Import ListNotations.
Open Scope string_scope.

Local Notation Djot := (@parse_blocks _ djot_bconfig _ _).
Local Notation Key := (@parse_blocks _ keyed_bconfig _ _).

(* 7.5 is the one worked example that needs a second setting as well as
   keys: a sublist must be able to interrupt its item's paragraph, which
   djot does not allow and `sublist_bconfig` does.  Keys neither supply
   that nor stand in for it, so it is the one document below stated
   against a composed configuration. *)
Definition keyed_sublist_bconfig : bconfig := with_keyed true sublist_bconfig.
Local Notation KeySub := (@parse_blocks _ keyed_sublist_bconfig _ _).

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
  /\ Key "foo: bar" = [mk (Ext_keyed [mk (Str "foo")] (para "bar"))].
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
  = [mk (Ext_keyed [mk (Str "foo")]
           (mk (BulletList "-" Tight [mk [para "bar"]; mk [para "baz"]])))].
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
  = [mk (Ext_keyed [mk (Str "foo")]
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
  = [mk (BulletList "-" Tight
           [mk [mk (Ext_keyed [mk (Str "foo")] (mk (CodeBlock "" "bar
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
  = [mk (Ext_keyed [mk (Str "foo")]
           (mk (Ext_keyed [mk (Str "bar")] (para "baz"))))].
Proof. vm_compute. reflexivity. Qed.

(* And the one-line form is not sugar for the two-line one (3.3): a line
   is split at most once, so the second colon is the value's text. *)
Example one_key_per_line :
  Key "foo: bar: baz"
  = [mk (Ext_keyed [mk (Str "foo")] (para "bar: baz"))].
Proof. vm_compute. reflexivity. Qed.

(* The value is inline content, never block syntax.  A list marker after
   the colon is text; the same marker on the next line is a list. *)
Example value_is_never_block_syntax :
  Key "foo: - bar" = [mk (Ext_keyed [mk (Str "foo")] (para "- bar"))].
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
       (Ext_keyed [mk (Str "foo")] (para "bar"))].
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
  = [mk (Div "" [para "foo:"])].
Proof. vm_compute. reflexivity. Qed.

(* And the two rows that say the test cannot be "a blank retracts": a
   blank reaches the key only when nothing under it claimed it first. *)
Example a_lists_blank_is_not_the_keys :
  Key "foo:
- a

- b"
  = [mk (Ext_keyed [mk (Str "foo")]
           (mk (BulletList "-" Loose [mk [para "a"]; mk [para "b"]])))].
Proof. vm_compute. reflexivity. Qed.

(* 6.2, the corner: an attribute spec starts something without producing
   a block, so the key does not retract at the blank and goes on to take
   the paragraph below it.  Accepted rather than repaired. *)
Example an_open_spec_holds_the_key_across_a_blank :
  Key "foo:
{#i}

bar"
  = [mk (Ext_keyed [mk (Str "foo")] (para "bar"))].
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
    = ["Note\: this matters."; "ends\:"].
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
    Key (@render_djot _ keyed_bconfig (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
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
    = [mk (Ext_keyed [mk (Str "Note: this")] (para "value: text"))].
Proof. split; vm_compute; reflexivity. Qed.

(* Canonical keys retain both wrapper orders, nest, and leave the
   child's list/table boundary conditions visible to its next sibling. *)
Definition canonical_key_documents : list (list cblock) :=
  let key := CKey (CIStr "Note: this") in
  let p := cpara ["value: text"] in
  let l := CList LKBullet Tight [[p]] in
  let t := CTable [CTBody [[CIStr "cell"]]] in
  [[key p]; [key (CId "child" p)]; [CId "key" (key p)];
   [key (key p)]; [key (CCode "" ["code"])]; [key (CDiv "" [])];
   [CQuote [key p]]; [CDiv "" [key p]]; [CList LKBullet Tight [[key p]]];
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
    Key (@render_djot _ keyed_bconfig (blocks_of_cblocks cbs)) = blocks_of_cblocks cbs.
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
A delimiter against the colon is not settled
--------------------------------------------

`.project/keyed-blocks.md` 9.1.  `iscan_closed` resolves the state as
if the line ended, and a delimiter run settles there as literal text;
with a byte following it opens instead.  The split asks
`iscan_settled`, which resolves with the colon known to follow, so
these decline.
*)

Example delimiter_against_colon_declines :
  (key_split "a*: b*", key_split "a_: b_", key_split "a^: b^",
   key_split "a~: b~", key_split "a"": b""")
  = (None, None, None, None, None).
Proof. vm_compute. reflexivity. Qed.

(* the two readings that would make a split wrong: one text run alone,
   an opener in place *)
Example delimiter_label_reads_two_ways :
  (para_inlines ["a*"], para_inlines ["a*: b*"])
  = ([mk (Str "a*")], [mk (Str "a"); mk (Strong [mk (Str ": b")])]).
Proof. vm_compute. reflexivity. Qed.

(* so the line is a paragraph under either setting, and the keys-on and
   keys-off readings agree *)
Example delimiter_line_is_not_a_key :
  Key "a*: b*" = Djot "a*: b*".
Proof. vm_compute. reflexivity. Qed.

(* a run that *closes* consults no following byte, so 3.1's row 9 is
   unaffected, and neither is a canonical label ending in an escape *)
Example closing_delimiter_still_splits :
  (key_split """foo"": bar", key_split "`code`: a description",
   key_split "it's: bar", key_split "a -- b: c")
  = (Some ("""foo""", "bar"), Some ("`code`", "a description"),
     Some ("it's", "bar"), Some ("a -- b", "c")).
Proof. vm_compute. reflexivity. Qed.

(* the canonical spelling escapes the delimiter either way *)
Example delimiter_label_is_escaped_canonically :
  (ci_line [CIStr "a*"], @cb_ok _ keyed_bconfig (CKey (CIStr "a*") (cpara ["b*"])))
  = ("a\*", true).
Proof. vm_compute. reflexivity. Qed.

(*
Claiming a block out of column
------------------------------

Section 5, and the worked examples that turn on it.  Line 2 sits at
the marker's own column, so ordinarily the list ends there; the open key
holds it open and takes the fence, and the fence's closing line ends the
key, which ends the override.  Line 5 is then a marker the list sees.
*)

Example out_of_column_is_claimed :
  Key "- foo:
```
bar
```
- baz"
  = [mk (BulletList "-" Tight
           [mk [mk (Ext_keyed [mk (Str "foo")] (mk (CodeBlock "" "bar
")))];
            mk [para "baz"]])].
Proof. vm_compute. reflexivity. Qed.

(* A footnote ends by column as a list item does, so an open key holds
   it open the same way.  Line 2 is not indented into the note and still
   reaches the fence; line 5, with the key finished, ends the note. *)
Example out_of_column_is_claimed_in_a_footnote :
  Key "[^n]: foo:
```
bar
```
baz"
  = [mk (FootnoteDef "n"
           [mk (Ext_keyed [mk (Str "foo")] (mk (CodeBlock "" "bar
")))]);
     para "baz"].
Proof. vm_compute. reflexivity. Qed.

(* 7.5, the same discipline two levels deep.  Line 3 passes through both
   lists that the open key is holding open and reaches the fence.  Line
   5, at column 2 with the key finished, is content to the outer list
   and a marker to the inner one, so `baz` is `foo`'s sibling. *)
Example out_of_column_returns_to_a_nested_list :
  KeySub "- tt
  - foo:
```
bar
```
  - baz"
  = [mk (BulletList "-" Tight
           [mk [para "tt";
             mk (BulletList "-" Tight
                   [mk [mk (Ext_keyed [mk (Str "foo")] (mk (CodeBlock "" "bar
")))];
                    mk [para "baz"]])]])].
Proof. vm_compute. reflexivity. Qed.

(* Without the second setting there is no inner list for `foo` to be an
   item of: line 2 is lazy text of `tt`, so its colon is never tested. *)
Example a_nested_key_needs_the_sublist_setting :
  Key "- tt
  - foo:
```
bar
```
  - baz"
  = [mk (BulletList "-" Tight
           [mk [mk (Para [mk (Str "tt"); mk SoftBreak; mk (Str "- foo:")])]]);
     mk (CodeBlock "" "bar
");
     mk (BulletList "-" Tight [mk [para "baz"]])].
Proof. vm_compute. reflexivity. Qed.

(* A thematic break emits immediately, so the same claim closes the key
   in the step that opens it; there is no live announced-end state. *)
Example thematic_out_of_column_is_claimed :
  Key "- foo:
* * * *
- baz"
  = [mk (BulletList "-" Tight
           [mk [mk (Ext_keyed [mk (Str "foo")] (mk ThematicBreak))];
            mk [para "baz"]])].
Proof. vm_compute. reflexivity. Qed.

(* 5.2: a list is not a block whose end is announced, so it is never
   claimed.  `foo:` is not a key here and the colon is literal text --
   the same document a writer gets from typing two bullets. *)
Example a_list_is_not_claimed :
  Key "- foo:
- bar"
  = [mk (BulletList "-" Tight [mk [para "foo:"]; mk [para "bar"]])].
Proof. vm_compute. reflexivity. Qed.

(* 5.1: the override is about column only.  A quote keeps its prefix... *)
Example quote_prefix_survives_the_override :
  Key "> foo:
> ```
> bar
> ```"
  = [mk (BlockQuote
           [mk (Ext_keyed [mk (Str "foo")] (mk (CodeBlock "" "bar
")))])].
Proof. vm_compute. reflexivity. Qed.

(* ...and a div's closing fence still closes it. *)
Example div_closer_survives_the_override :
  Key ":::
- foo:
```
bar
```
:::"
  = [mk (Div "" [mk (BulletList "-" Tight
                    [mk [mk (Ext_keyed [mk (Str "foo")] (mk (CodeBlock "" "bar
")))]])])].
Proof. vm_compute. reflexivity. Qed.

(* With keys off nothing above changes: the list ends at line 2, the
   fence is read outside it, and the second marker opens a new list. *)
Example out_of_column_needs_the_setting :
  Djot "- foo:
```
bar
```
- baz"
  = [mk (BulletList "-" Tight [mk [para "foo:"]]);
     mk (CodeBlock "" "bar
");
     mk (BulletList "-" Tight [mk [para "baz"]])].
Proof. vm_compute. reflexivity. Qed.

(* ...and the tree it would produce is already reachable, by indenting
   the fence into the item.  Section 5 adds a spelling, not a document,
   which is why the canonical renderer can decline it and
   `ListUniformity.v` stays out of section 5's price. *)
Example out_of_column_tree_is_reachable :
  Key "- foo:
  ```
  bar
  ```
- baz"
  = [mk (BulletList "-" Tight
           [mk [mk (Ext_keyed [mk (Str "foo")] (mk (CodeBlock "" "bar
")))];
            mk [para "baz"]])].
Proof. vm_compute. reflexivity. Qed.

(* A div survives a blank and keeps the claim until its own closing
   fence.  The blank belongs to the div and the closing fence is not a
   blank, so the list stays tight when the following marker resumes it. *)
Example div_out_of_column_is_claimed :
  Key "- foo:
  :::

next
:::
- baz"
  = [mk (BulletList "-" Tight
           [mk [mk (Ext_keyed [mk (Str "foo")] (mk (Div "" [para "next"])))];
            mk [para "baz"]])].
Proof. vm_compute. reflexivity. Qed.

(* The ordinary div remains blank-safe, but a key holding it is not:
   after the blank the key still owns lines through the div closer. *)
Example key_over_div_is_not_blank_safe :
  blank_safe (match snd (@run_lines _ keyed_bconfig ["- foo:"; "  :::"] (PPara []))
              with PList _ _ inner => inner | st => st end) = false.
Proof. vm_compute. reflexivity. Qed.
