(* ai-disclosure: autonomous *)

(* Baseline and header syntax for `.project/callouts.md`, sections 1 and 3.
   These default-profile examples must keep passing after callouts are enabled
   only through an explicit block setting. *)
From Stdlib Require Import String List Ascii.
From DjotV Require Import Ast Strings Line Parser Render Document Html InlineTable Site.
Import ListNotations.
Open Scope string_scope.

Local Notation Djot := (@parse_blocks _ djot_bconfig _ _).
Local Notation S := (fun s => mk (Str s)).
Local Notation P := (fun xs => mk (Para xs)).
Local Notation Q := (fun xs => mk (BlockQuote xs)).

Example baseline_title_and_body :
  Djot "> [!note] Title
> body" = [Q [P [S "[!note] Title"; mk SoftBreak; S "body"]]].
Proof. vm_compute. reflexivity. Qed.

Example baseline_empty_title :
  Djot "> [!note]
> body" = [Q [P [S "[!note]"; mk SoftBreak; S "body"]]].
Proof. vm_compute. reflexivity. Qed.

Example baseline_uppercase :
  Djot "> [!NOTE]" = [Q [P [S "[!NOTE]"]]].
Proof. vm_compute. reflexivity. Qed.

Example baseline_fold_marker :
  Djot "> [!note]- T
> b" = [Q [P [S "[!note]- T"; mk SoftBreak; S "b"]]].
Proof. vm_compute. reflexivity. Qed.

Example baseline_bad_suffix_and_kind :
  Djot "> [!note]x" = [Q [P [S "[!note]x"]]] /\
  Djot "> [!no te] T" = [Q [P [S "[!no te] T"]]].
Proof. split; vm_compute; reflexivity. Qed.

Example baseline_lazy_continuation :
  Djot "> [!note] T
lazy" = [Q [P [S "[!note] T"; mk SoftBreak; S "lazy"]]].
Proof. vm_compute. reflexivity. Qed.

Example baseline_blank_closes_quote :
  Djot "> [!note] T

> b" = [Q [P [S "[!note] T"]]; Q [P [S "b"]]].
Proof. vm_compute. reflexivity. Qed.

Example baseline_nested_quote :
  Djot "> > [!note] T" = [Q [Q [P [S "[!note] T"]]]].
Proof. vm_compute. reflexivity. Qed.

Example baseline_link :
  Djot "> [!note](x)" = [Q [P [mk (Link [S "!note"] (Direct "x"))]]].
Proof. vm_compute. reflexivity. Qed.

Example baseline_span :
  Djot "> [!note]{.a}" =
  [Q [P [Node NoPos [("class", "a")] (Span [S "!note"])]]].
Proof. vm_compute. reflexivity. Qed.

Example baseline_reference_link :
  Djot "> [!note][r]

[r]: u" =
  [Q [P [mk (Link [S "!note"] (Reference "r"))]]; mk (RefDef "r" "u")].
Proof. vm_compute. reflexivity. Qed.

Example baseline_reference_definition :
  Djot "> [!note]: u" = [Q [mk (RefDef "!note" "u")]].
Proof. vm_compute. reflexivity. Qed.

Example baseline_quote_needs_space :
  Djot ">[!note] T" = [P [S ">[!note] T"]].
Proof. vm_compute. reflexivity. Qed.

(* The recognizer sees the content after the quote prefix, before inline
   parsing. *)
Example header_forms :
  callout_header "[!note] Backlinks" = Some ("note", None, "Backlinks") /\
  callout_header "[!NOTE]" = Some ("NOTE", None, "") /\
  callout_header "[!note]- T" = Some ("note", Some FoldCollapsed, "T") /\
  callout_header "[!a_2-b]+   Title  " = Some ("a_2-b", Some FoldExpanded, "Title  ").
Proof. repeat split; vm_compute; reflexivity. Qed.

Example header_title_trims_at_inline_parse :
  match callout_header "[!a_2-b]+   Title  " with
  | Some (_, _, source) => strip_trailing_ws source
  | None => ""
  end = "Title".
Proof. vm_compute. reflexivity. Qed.

Example header_rejects_djot_suffixes :
  callout_header "[!note](x)" = None /\
  callout_header "[!note]{.a}" = None /\
  callout_header "[!note][r]" = None /\
  callout_header "[!note]: u" = None /\
  callout_header "[!note]x" = None /\
  callout_header "[!note]-x" = None /\
  callout_header ("[!note]" ++ String "013" "T") = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

Example header_rejects_bad_kind :
  callout_header "[!no te] T" = None /\
  callout_header "[!] T" = None /\
  callout_header "[![a](b)](c)" = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* Section 6's escape claim, sampled on each inline family that can
   render a leading opening bracket.  The universal proof belongs with
   the canonical constructor and roundtrip work. *)
Definition rendered_quote_header (il : node inline)
  : option (string * option callout_fold * string) :=
  match split_lines (render_djot [Q [P [il]]]) with
  | line :: _ =>
      match quote_prefix line with
      | Some content => callout_header content
      | None => None
      end
  | [] => None
  end.

Example canonical_quote_prefix_probe :
  map rendered_quote_header
    [S "[!note] T";
     mk (Link [S "!note"] (Direct "x"));
     Node NoPos [("class", "a")] (Span [S "!note"]);
     mk (Link [S "!note"] (Reference "r"));
     mk (FootnoteReference "n");
     mk (Ext_wikilink false "note" None)]
  = [None; None; None; None; None; None].
Proof. vm_compute. reflexivity. Qed.

Local Notation Callouts :=
  (@parse_blocks _ (with_callouts true djot_bconfig) _ _).
Local Notation C := (fun kind fold title body =>
  mk (Ext_callout kind fold title body)).

Example enabled_title_and_body :
  Callouts "> [!note] Backlinks
> body" =
  [C "note" None [S "Backlinks"] [P [S "body"]]].
Proof. vm_compute. reflexivity. Qed.

Example enabled_folded_empty_title :
  Callouts "> [!tip]-
> body" =
  [C "tip" (Some FoldCollapsed) [] [P [S "body"]]].
Proof. vm_compute. reflexivity. Qed.

Example enabled_empty_body :
  Callouts "> [!tip] T" = [C "tip" None [S "T"] []].
Proof. vm_compute. reflexivity. Qed.

Example enabled_nested :
  Callouts "> [!note] Outer
> > [!note] Inner
> > text" =
  [C "note" None [S "Outer"]
    [C "note" None [S "Inner"] [P [S "text"]]]].
Proof. vm_compute. reflexivity. Qed.

Example enabled_header_only_on_opener :
  Callouts "> quoted
> [!note] T" =
  [Q [P [S "quoted"; mk SoftBreak; S "[!note] T"]]].
Proof. vm_compute. reflexivity. Qed.

Example enabled_invalid_suffix_stays_quote :
  Callouts "> [!note](x)" =
    [Q [P [mk (Link [S "!note"] (Direct "x"))]]].
Proof. vm_compute. reflexivity. Qed.

Example enabled_lazy_body :
  Callouts "> [!note] T
> body
lazy" =
  [C "note" None [S "T"]
    [P [S "body"; mk SoftBreak; S "lazy"]]].
Proof. vm_compute. reflexivity. Qed.

Example enabled_blank_closes_callout :
  Callouts "> [!note] T

> body" =
  [C "note" None [S "T"] []; Q [P [S "body"]]].
Proof. vm_compute. reflexivity. Qed.

Example enabled_inline_title :
  Callouts "> [!note] _T_" =
  [C "note" None [mk (Emph [S "T"])] []].
Proof. vm_compute. reflexivity. Qed.

Example enabled_callout_in_list :
  Callouts "- > [!note] T
  > body" =
  [mk (BulletList Tight [[C "note" None [S "T"] [P [S "body"]]]])].
Proof. vm_compute. reflexivity. Qed.

Example enabled_block_attribute :
  Callouts "{.warn}
> [!note] T" =
  [Node NoPos [("class", "warn")]
    (Ext_callout "note" None [S "T"] [])].
Proof. vm_compute. reflexivity. Qed.

Local Notation KeyCallouts :=
  (@parse_blocks _ (with_callouts true keyed_bconfig) _ _).

Example enabled_callout_after_key :
  KeyCallouts "foo:
> [!note] T
> body" =
  [mk (Ext_keyed [S "foo"]
    (C "note" None [S "T"] [P [S "body"]]))].
Proof. vm_compute. reflexivity. Qed.

Definition wiki_callout_table : dtable :=
  DTable (with_wikilinks true djot_config) eq_refl.
Local Notation WikiCallouts :=
  (@parse_blocks wiki_callout_table (with_callouts true djot_bconfig) _ _).

Example worked_warning_with_list :
  WikiCallouts "> [!warning]- Do not rename
> Renaming breaks the backlinks below.
>
> - [[a]]
> - [[b]]" =
  [C "warning" (Some FoldCollapsed) [S "Do not rename"]
    [P [S "Renaming breaks the backlinks below."];
     mk (BulletList Tight
       [[P [mk (Ext_wikilink false "a" None)]];
        [P [mk (Ext_wikilink false "b" None)]]])]].
Proof. vm_compute. reflexivity. Qed.

Definition callout_doc (source : string) : doc :=
  @parse_doc (DTable djot_config eq_refl)
    (with_callouts true djot_bconfig) semantic_pos source.

Example expanded_html_is_open :
  render_html (callout_doc "> [!note]+ T
> body") =
    "<details class=""callout"" data-callout=""note"" open="""">
<summary class=""callout-title"">T</summary>
<div class=""callout-content"">
<p>body</p>
</div>
</details>
".
Proof. vm_compute. reflexivity. Qed.

Example empty_plain_title_has_no_title_element :
  render_html (callout_doc "> [!note]") =
    "<div class=""callout"" data-callout=""note"">
<div class=""callout-content"">
</div>
</div>
".
Proof. vm_compute. reflexivity. Qed.

Example title_destination_can_be_renamed :
  cb_dests (CCallout "note" None [CIWiki false "old" None] []) = ["old"] /\
  cb_map_dest (fun _ => "new")
    (CCallout "note" None [CIWiki false "old" None] []) =
    CCallout "note" None [CIWiki false "new" None] [].
Proof. split; vm_compute; reflexivity. Qed.
