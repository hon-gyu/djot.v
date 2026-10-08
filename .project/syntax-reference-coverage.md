---
ai-disclosure: ai-generated
author: anthropic/claude-opus-5-5
---
# Syntax reference coverage

For each rule the djot syntax reference states, what in this repository
fails if the parser breaks it.  The plan behind this file is
`260928.plan.syntax-reference-audit.md`.

**Audited version:** jgm/djot `doc/syntax.md` at `d77f8a0` (2026-07-01),
the latest commit to touch it.  Rules are cited by that version's
section.  When the reference moves, the diff between versions lists the
rows to revisit.

## Levels

| Level | Meaning |
| --- | --- |
| T | A theorem states the rule over all inputs it applies to, written from the reference. |
| T~ | A theorem states the rule for a restricted shape only.  The notes name the shape. |
| E | A kernel-checked `Example` pins the reference's own example, or a case its prose states, with djot.js's output. |
| D | Only the djot.js comparison exercises it. |
| none | Nothing. |
| n/a | Not a parsing rule: rendering, intent, or advice.  Listed so the table is complete. |

Examples are in `dev/check/Reference.v` unless another file is named.
"Unit" in the notes points to further pinned cases that are not the
reference's (`dev/InlineExamples.v`, `dev/ParserExamples.v`, `Line.v`,
`Document.v`); they do not change the level.  Lemmas that are equations
of `step` in the parser's own predicates (`step_quote_close`,
`step_fence_close`, `step_list_close`, ...) describe the code and are not
counted: `step_foot_close` was one of those and it proved the bug.

## Summary

| Section | T | T~ | E | D | none | n/a |
| --- | --- | --- | --- | --- | --- | --- |
| Inline | 11 | 9 | 32 | 0 | 0 | 5 |
| Block: introduction and paragraph | 5 | 1 | 1 | 0 | 0 | 1 |
| Block: heading, quote, list item, list | 17 | 2 | 0 | 0 | 0 | 1 |
| Block: leaf blocks and tables | 13 | 0 | 3 | 0 | 0 | 2 |
| Block: references, footnotes, attributes, ids | 8 | 2 | 4 | 0 | 0 | 0 |
| Nesting limits, security | 0 | 0 | 0 | 0 | 0 | 2 |

Every rule with a parse outcome is at least E: the 76 code examples and
61 prose cases in `Reference.v` all match djot.js except
`table_caption_alone` (adjudicated 2026-08-22, see the log) and the
list tightness cases of LS4 (djot.js bugs, fixed here 2026-09-29, and a
spec gap, 2026-09-30).  The T rows
are the container rules, the line-level spellings and block-level
determinism.  Inline syntax has eleven T: link locality, which holds by
construction, the emphasis flanking and nonempty rules (M2, M3) over
every document, escapes (O2), verbatim spans (V1) and dash runs (Q5)
from any point where the scan is reading text, and the attribute
language (AT2 to AT5, C1) as a grammar the machine accepts exactly.  It
has nine T~: precedence and nesting over a restricted alphabet (P1 to
P5), backslash escapes over the same alphabet (O3 to O5), and line
breaks in a spec (AT6).  The other 32 inline rules are at E.

## Inline syntax

| # | Section | Rule | Level | Checks | Notes |
| --- | --- | --- | --- | --- | --- |
| P1 | Precedence | "the first opener that gets closed takes precedence ... any potential openers between the opener and the closer get marked as regular text" | T~ | `para_inlines_valid` (InlinePrecedence.v), `valid_unique`, `valid_nested` (Precedence.v); `precedence_first_closed_emph`, `precedence_first_closed_strong`, `precedence_link_closes_first`, `precedence_strong_closes_first` | The rule is `valid` (Precedence.v): an opener inside a pair that closed earlier is no longer live.  At most one reading is valid, and the paragraph is its tree.  Shape: a paragraph of delimiters of the rows whose unmatched token is its own text (`_ * ^ ~` bare or braced, `= +` braced, in djot's table), of any width, brackets with a destination `](...)` or a reference label `][...]`, and bytes no other syntax claims (`over_alphabet`, Precedence.v).  So the reference's two bracket examples are instances.  Backslash escapes are in the alphabet (O3 to O5).  Left out: `{` except as a marker, `[^`, `[[`, `]{`, images and smart quotes. |
| P2 | Precedence | "*nested* containers are fine" | T~ | `para_inlines_valid` (InlinePrecedence.v), `valid_nested` (Precedence.v), `para_inlines_ci_para` (InlineInvert.v); `precedence_nesting`, `emphasis_nested` | `valid` lets a pair open and close inside another, and `valid_nested` says that is the only way two pairs meet.  Shape as P1.  `para_inlines_ci_para` adds the trees the inline renderer writes, whatever their constructs. |
| P3 | Precedence | "`{_` ... can *only* open emphasis, while `_}` ... can *only* close" | T~ | `para_inlines_valid`; `precedence_braces`, `emphasis_braces` | `lex` (Precedence.v) makes `{_` an opener that cannot close and `_}` a closer that cannot open.  Shape as P1.  Unit: InlineExamples.v, "The delimiter family". |
| P4 | Precedence | "Explicitly marked closers can only match explicitly marked openers, and non-marked closers can only match non-marked openers" | T~ | `para_inlines_valid`; `marked_closer_needs_marked_opener` | `valid` pairs tokens of the same style and marking (`dkey`).  Shape as P1. |
| P5 | Precedence | "When there are multiple openers ... the closest one is used" | T~ | `para_inlines_valid` (InlinePrecedence.v), `valid_unique` (Precedence.v); `precedence_closest_opener` | `closest_live` in `valid`.  Shape as P1. |
| P6 | Precedence | "Verbatim syntax ... doesn't allow nested markup" | E | `precedence_verbatim` | |
| O1 | Ordinary text | "Anything that isn't given a special meaning is parsed as literal text" | n/a | | The default case of every other row. |
| O2 | Ordinary text | "All ASCII punctuation characters ... may be backslash-escaped" | T | `escape_in_text` (InlineScan.v), `escape_every_punct` (InlineExamples.v); `escape_punctuation` | From the scan reading text with nothing pending, after any prefix and before any rest: the two bytes add the punctuation byte to the text and change nothing else.  Not followed: a candidate still undecided (a symbol alias, an attribute spec, a destination), which reads the same bytes in its ordinary-reading shadow.  Unit: InlineExamples.v, "Escapes". |
| O3 | Ordinary text | "Backslashes before characters other than ASCII punctuation ... are just treated as literal backslashes" | T~ | `para_inlines_valid` (InlinePrecedence.v), `TEsc`, `TEscWs`, `THard` in `lex` (Precedence.v); `escape_other_is_literal` | `esc_text`: the byte if punctuation, the backslash and the byte otherwise.  Shape as P1: a paragraph over the precedence alphabet, where a backslash may escape any byte.  Inside a destination an escape is decoded the same way, inside a reference label it is kept as written (`tok_region`). |
| O4 | Ordinary text | "Backslash before a newline (or before spaces or tabs followed by a newline) is parsed as a hard line break.  Spaces and tab characters before the backslash are ignored" | T~ | `para_inlines_valid` (InlinePrecedence.v), `TEsc`, `TEscWs`, `THard` in `lex` (Precedence.v); `escape_newline_hard_break`, `escape_newline_after_spaces`, `line_break` | `THard`: a backslash and whitespace to the line's end; the tree trims the text before it (`str_trim`) and the break after it is the hard one (`after_hard`).  A backslash that ends the paragraph is a hard break too, as in djot.js.  Shape as P1. |
| O5 | Ordinary text | "Backslash before a space is parsed as a nonbreaking space" | T~ | `para_inlines_valid` (InlinePrecedence.v), `TEsc`, `TEscWs`, `THard` in `lex` (Precedence.v); `escape_space_nbsp` | `TEscWs`: a backslash and a whitespace run with more on the line; a run that begins with a space is a non-breaking space and the rest of the run, one that begins with a tab is text with its backslash (`nbsp_rest`).  Shape as P1. |
| L1 | Link | inline link: text in `[...]`, then the destination in parentheses, "no space between the `]` ... and the open `(`" | E | `link_inline`, `link_no_space_before_destination` | Unit: InlineExamples.v, "Direct links". |
| L2 | Link | "link text (which may contain arbitrary inline formatting)" | E | `precedence_link_closes_first` | |
| L3 | Link | "The URL may be split over multiple lines; ... the line breaks and any leading and trailing space is ignored, and the lines are concatenated" | E | `link_url_split` | |
| L4 | Link | reference link: the label "must come immediately after the link text" | E | `link_reference`, `link_no_space_before_label` | |
| L5 | Link | "the parsing of the link is 'local' and does not depend on whether the label is defined" | T | `classify_inlines_locality`, `html_tree_reference_shape`; `link_reference_local` | Locality holds by construction: the inline scan never sees the definitions. |
| L6 | Link | "If the label is empty, then the link text will be taken to be the reference label" | E | `link_empty_label` | |
| I1 | Image | "Images work just like links, but have a `!` prefixed", inline and reference | E | `image` | |
| A1 | Autolink | "A URL or email address that is enclosed in `<`...`>` will be hyperlinked" | E | `autolink` | Unit: InlineExamples.v, "Autolinks". |
| A2 | Autolink | "The content between pointy braces is treated literally (backslash-escapes may not be used)" | E | `autolink_literal` | |
| A3 | Autolink | "The URL or email address may not contain a newline" | E | `autolink_no_newline` | |
| V1 | Verbatim | begins with a run of backticks, "ends with an equal-lengthed string" | T | `verbatim_in_text`, `verbatim_at_end` (InlineScan.v); `verbatim_backticks` | From the scan reading text, as O2: a run of any length opens, and the next run of that length closes, for a body that holds no run of that length (`verb_safe`) and neither starts nor ends with a backtick, so that the runs are the delimiters.  The node's text is `trim_verb` of the body (V3).  A `{` after the closer is R1's.  Unit: InlineExamples.v, "Canonical verbatim". |
| V2 | Verbatim | "backslash escapes don't work there" | E | `verbatim_no_escapes` | |
| V3 | Verbatim | "If the content starts or ends with a backtick character, a single space is removed" | E | `verbatim_space_stripped` | `trim_verb_pad` is the renderer's inverse, not this rule. |
| V4 | Verbatim | "If the text ... ends before a closing backtick string ..., the verbatim text extends to the end" | E | `verbatim_unclosed` | |
| M1 | Emphasis/strong | `_` delimits emphasis, `*` strong | E | `emphasis` | |
| M2 | Emphasis/strong | "can open emphasis only if it is not directly followed by whitespace.  It can close ... only if it is not directly preceded by whitespace" | T | `parse_blocks_located_spans` (StoredLines.v), from `para_inlines_spans`, `cell_inlines_spans` (InlineSpans.v); `emphasis_not_opened`, `emphasis_opener_before_space`, `emphasis_closer_after_space` | Every delimiter node of the located parse of any document, in any inline sequence at any depth and for every row: a bare opener is followed by a byte that is not whitespace, a bare closer preceded by one, both read in the source lines.  Whitespace is space, tab, CR and LF (`nonspace_at`); a line break counts as whitespace.  The bytes read are inline content, never a container prefix: at the start of a stored line the scanner sees a break.  Keys are off: a key with no block retracts to a paragraph read by the semantic scan, whose nodes carry no position. |
| M3 | Emphasis/strong | closes "only if there are some characters besides the delimiter character between the opener and the closer" | T | `para_inlines_spans`, `cell_inlines_spans`; `emphasis_not_opened` (`___`) | As M2: at least one byte or line break lies between the opener's end and the closer's start.  The wording read literally would exclude `{___}`, which is emphasis around `_` in the model, the parser and djot.js; the theorem states what all three do. |
| M4 | Emphasis/strong | "Emphasis can be nested" | E | `emphasis_nested` | See P2. |
| M5 | Emphasis/strong | "Curly braces may be used to force interpretation ... as an opener or as a closer" | E | `emphasis_braces` | |
| H1 | Highlighted | `{=` ... `=}`; "the `{` and `}` are mandatory" | E | `highlighted`, `highlight_needs_braces` | |
| S1 | Super/subscript | `^` superscript, `~` subscript; braces "may be used, but are not required" | E | `super_subscript`, `super_subscript_braces` | |
| D1 | Insert/delete | `{+` ... `+}`, `{-` ... `-}`; "The `{` and `}` are mandatory" | E | `insert_delete`, `insert_needs_braces` | |
| Q1 | Smart punctuation | straight quotes "are parsed as curly quotes"; "Djot is pretty good about figuring out from context which direction" | E | `smart_quotes` | The heuristic itself is not stated.  Unit: InlineExamples.v, "Smart quotes". |
| Q2 | Smart punctuation | "using curly braces to mark a quote as an opener `{"` or a closer `"}`" | E | `smart_quotes_braces` | |
| Q3 | Smart punctuation | "If you want a straight quote, use a backslash-escape" | E | `smart_quotes_escaped` | |
| Q4 | Smart punctuation | three periods: ellipsis; three hyphens: em dash; two: en dash | E | `smart_dashes_ellipsis` | |
| Q5 | Smart punctuation | longer hyphen runs divided "uniformly, if possible, and preferring em-dashes" | T | `dashes_divide`, `dash_run_in_text`, `dash_run_at_end` (InlineScan.v); `smart_dash_runs` | `dashes_divide` is the cut, for every length.  The other two say the scan hands it the whole run: from the scan reading text, as O2, a run ended by any byte but `}`, or by the end of the line.  A `}` takes the last hyphen back for a delete closer.  Unit: `dashes_1` ... `dashes_13`. |
| MA1 | Math | verbatim prefixed with `$` (inline) or `$$` (display) | E | `math`, `math_display` | Unit: InlineExamples.v, "Math". |
| F1 | Footnote reference | "`^` + the reference label in square brackets" | E | `footnote_reference` | Unit: InlineExamples.v, "Footnote references". |
| B1 | Line break | "Line breaks in inline content are treated as 'soft' breaks" | E | `line_break` | |
| B2 | Line break | "may be rendered as spaces, or ... as newlines" | n/a | | Rendering. |
| C1 | Comment | "Material between two `%` characters in an attribute will be ignored" | T | `machine_accepts`, `machine_sound` (AttrAgree.v); `comment_in_attribute` | `CComment` and `BOpenComment` in the grammar (`AttrSyntax.v`) add nothing to the attributes.  As AT2. |
| C2 | Comment | "an attribute specifier that contains only a comment" as a general comment | E | `comment_alone` | |
| Y1 | Symbols | "Surrounding a word with `:` signs creates a 'symbol'", "rendered literally" by default | E | `symbols`, `symbol` | |
| Y2 | Symbols | "may be treated specially by a filter" | n/a | | |
| R1 | Raw inline | "a verbatim span followed by `{=FORMAT}`" | E | `raw_inline` | Unit: InlineExamples.v, "Raw inline". |
| R2 | Raw inline | "passed through verbatim when rendering the designated format, but ignored otherwise" | n/a | | Rendering. |
| N1 | Span | "Text in square brackets that is not a link or image and is followed immediately by an attribute" | E | `span`, `span_needs_attributes` | |
| AT1 | Inline attributes | "must *immediately follow* the inline element ... (with no intervening whitespace)" | E | `inline_attrs_need_adjacency` | Unit: InlineExamples.v, "Inline attributes". |
| AT2 | Inline attributes | "`.foo` specifies `foo` as a class.  Multiple classes ... will be combined" | T | `machine_accepts`, `machine_sound` (AttrAgree.v); `inline_attrs_classes_combine` | The attribute language as a grammar written without the machine (`body`, `attrs_of` in `AttrSyntax.v`): the machine is done after a body and its `}` exactly when the grammar reads that body, with the grammar's attributes.  Every spec, block or inline, is read by this machine (`attr_open`, `iattr_feed`, `ispan_feed`); the inline scan's use of it is by the code, not restated.  Where the reference is silent the grammar follows djot.js: `SPEC-GAP`, 2026-10-07. |
| AT3 | Inline attributes | "if multiple identifiers are given, the last one is used" | T | `machine_accepts`, `machine_sound` (AttrAgree.v); `inline_attrs_last_id` | `add_item` on `IId`.  As AT2. |
| AT4 | Inline attributes | `key="value"` or `key=value`; bare values of ASCII alphanumerics, `_`, `:`, `-`; "Backslash escapes may be used inside quoted values" | T | `machine_accepts`, `machine_sound` (AttrAgree.v); `inline_attrs_bare_value`, `inline_attrs_quoted_escape` | `OBare`, `CQuoted`, `quoted`.  As AT2.  Which bytes escape and how whitespace in a value is stored: `SPEC-GAP`, 2026-10-07. |
| AT5 | Inline attributes | "`%` begins a comment, which ends with the next `%` or the end of the attribute" | T | `machine_accepts`, `machine_sound` (AttrAgree.v); `comment_in_attribute` | `CComment` and `BOpenComment`.  As AT2. |
| AT6 | Inline attributes | "Attribute specifiers may contain line breaks" | T~ | `machine_accepts`, `machine_sound` (AttrAgree.v), `attr_continuation`; `inline_attributes` | The grammar's whitespace includes the line feed, inside a quoted value too, and block specs over several lines are BA2.  Shape: the inline scan feeds a line break to the machine as a line feed (`nl_char` in the `IAttr` arms), which no theorem states. |
| AT7 | Inline attributes | stacked specifiers "will be combined" | E | `inline_attributes_stacked`, `inline_attributes_merged` | |
| — | Highlighted | "(in HTML, `<mark>`)" | n/a | | Rendering. |

Inline: T 11, T~ 9, E 32, n/a 5.

## Block syntax

### Introduction and paragraph

| # | Section | Rule | Level | Checks | Notes |
| --- | --- | --- | --- | --- | --- |
| BI1 | Block syntax | "block structure can be discerned prior to inline parsing and takes priority over inline structure" | T | `block_shape_independent` (BlockShape.v) | The block tree with every inline erased, table captions included, is the same under any two inline delimiter tables.  A caption is inlines, empty meaning none, as in djot.js's AST, so whether a table has one is not a block-level fact (divergences, closed 2026-10-02).  Keyed blocks, an extension, are off: finding a key's label asks the inline scanner, which breaks the rule on purpose (`key_split_contract`). |
| BI2 | Block syntax | "blocks can be parsed line by line with no backtracking.  The contribution a line makes to block-level structure never depends on a future line" | T | `prefix_determinism`, `no_future_line_dependence`, `prefix_state_suffices` | |
| BI3 | Block syntax | "Indentation is only significant for list item or footnote nesting" | T~ | `indent_uniformity`, `classify_ws_prefix`, `quote_uniformity_pad` | Shape: every line indented by the same blanks; then the parse is unchanged, for every document, lists and footnotes included.  Indentation that differs from line to line is read by code blocks and by nesting, so no statement covers it. |
| BI4 | Block syntax | "a thematic break or fenced code block can be directly followed by a paragraph" | E | `code_block_longer_closer` | |
| BI5 | Block syntax | "Paragraphs can never be interrupted by other block-level elements" | T | `hard_wrap_one_para` (with `djot_wrap_neutral`) | Inside containers, by composition with the uniformity theorems. |
| BI6 | Block syntax | paragraphs "must always end with a blank line (or the end of the document or containing element)" | T | `hard_wrap_para_then_rest`, `hard_wrap_one_para`; `quote_uniformity`, `div_uniformity` for the containing element | |
| BI7 | Block syntax | "we recommend *always* separating block-level elements by blank lines" | n/a | | Advice. |
| PA1 | Paragraph | "a sequence of nonblank lines that does not meet the condition for being one of the other block-level elements ... parsed as a sequence of inline elements.  Newlines are treated as soft breaks" | T | `hard_wrap_one_para` | |

Introduction and paragraph: T 5, T~ 1, E 1, n/a 1.

### Heading, block quote, list item, list

| # | Section | Rule | Level | Checks | Notes |
| --- | --- | --- | --- | --- | --- |
| HE1 | Heading | "one or more `#` characters, followed by whitespace.  The number of `#` characters defines the heading level" | T | `classify_heading_ws`, `classify_heading_level`; `heading`, `heading_needs_space` | Line level: any indentation, any whitespace character.  A bare `#` is an empty heading in both engines although the rule asks for whitespace after it. |
| HE2 | Heading | "The heading text may spill over onto following lines, which may also be preceded by the same number of `#` characters (but these can also be left off)" | T | `heading_ends_at` (Uniformity.v), `heading_text_wrap_then_rest`, `heading_marker_wrap_then_rest`; `heading_marked_continuation`, `heading_lazy_continuation` | Stated from an open heading state.  `heading_ends_at` takes the following lines marked or not in any mix (`heading_keeps`); the other two are the all-unmarked and the all-marked run. |
| HE3 | Heading | "The heading ends when a blank line (or the end of the document or enclosing container) is encountered" | T | `heading_ends_at`, `heading_ends_with_lines`; `heading_other_marker_count`, `heading_ends_with_container` | The heading ends at the first line it does not keep, which is then parsed as if no heading were open, or with the lines.  A blank is such a line.  The enclosing-container half as for CB2: each container theorem parses the contents as a document that ends with the container.  Any line that is neither text nor a `#` line of the same level ends it too, a list marker or a quote as well as a `#` line of another level, and a heading continues lazily inside a quote: `SPEC-GAP`, 2026-09-28 and 2026-10-05. |
| BQ1 | Block quote | "each of which begins with `>`, followed either by a space or by the end of the line" | T | `classify_quote_marker`, `step_quote_bare`; `block_quote`, `quote_needs_space`, `quote_bare_marker` | Line level, both directions: any indentation, `>` then the end of the line or one whitespace character.  Tab and CR after `>`: `SPEC-GAP`, 2026-09-30. |
| BQ2 | Block quote | "The contents of the block quote (minus initial `>`) are parsed as block-level content" | T | `quote_uniformity`, `quote_uniformity_pad`, `quote_uniformity_bare`, `quote_uniformity_tail`, `parse_lines_quote` | A bare `>` first line opens the same quote but is not stated (it records a different source range). |
| BQ3 | Block quote | "it is possible to 'lazily' omit the `>` prefixes from regular paragraph lines ... except in front of the first line of a paragraph" | T | `lazy_stack_line`, `step_lazy_spelling`, `quote_lazy_line`; `block_quote_lazy`, `quote_no_lazy_first_line` | The exception has only the example. |
| LI1 | List item | "a list marker followed by a space (or a newline) followed by one or more lines, indented relative to the list marker" | T | `list_item_owns`; `list_uniformity`, `list_uniformity_tail`, `ck_uniformity`; `list_item`, `list_marker_then_newline` | `list_item_owns`: every line indented past the marker's column, and every blank, goes to the open item.  The uniformity theorems add what the item means when its lines are indented by exactly the marker's width; at other widths the contents read the extra or missing indentation (`- - a` then `    - b`), so uniformity is not the rule there. |
| LI2 | List item | "Indentation may be 'lazily' omitted on paragraph lines following the first line of a paragraph" | T | `lazy_stack_line`, `step_lazy_spelling`, `list_lazy_line`; `list_item_lazy` | `step_lazy_spelling` takes any indentation past the marker. |
| LI3 | List item | "an indented list marker on the line directly after paragraph text does not begin a sublist; it is taken as lazy continuation of the paragraph" | T | `list_uniformity` with `hard_wrap_one_para`; `list_item_no_sublist` | By composition: the item's lines parse as a top-level document, where BI5 holds. |
| LI4 | List item | "A blank line ends the paragraph, after which the indented marker begins a sublist" | T | `list_uniformity` twice; `list_item_sublist_after_blank` | By composition, as LI3. |
| LI5 | List item | the marker table: `-` `+` `*` bullets; `1.` `1)` `(1)` and the alpha and roman variants ordered; `:` definition; `- [ ]` task | T | `classify_list_marker` (Line.v), `styles_of_core_numeral` (Marker.v); `ck_uniformity`, `star_uniformity`, `plus_uniformity`, `definition_list_uniformity`, `nsc_uniformity` | Line level, both directions: a line is a list marker exactly when it is not a thematic break and, after any indentation, spells one (`marker_spelling`): a bullet, a bullet with a checkbox, or a numeral in one of the three delimiter shapes, then the end of the line or one whitespace character.  `styles_of_core_numeral` is the table's right column: the candidate styles are the enumerations the numeral reads in (`numeral_ok`).  Any run of roman digits is a roman numeral (`iiii`, `vx`), as in djot.js.  A tab or CR counts as the space: `SPEC-GAP`, 2026-10-05.  The uniformity theorems say what list the canonical spellings build. |
| LI6 | List item | "Ordered list markers can use any number in the series: thus, `(xix)` and `v)` are both valid" | T | `ordered_decimal_uniformity`, `ordered_roman_uniformity_any`, `ordered_alpha_uniformity_any`; `ordered_roman_wide` | Decimal cores are capped at 18 digits, 2026-09-26 entry. |
| LI7 | List item | "`v)` is *also* a valid lower-alpha-enumerated marker" | T | `alpha_from_nine_uniformity`, `list_uniformity_narrow`; `ordered_v_paren` | A lone ambiguous marker reads as roman: `SPEC-GAP`, 2026-09-28. |
| TK1 | Task list item | "A bullet list item that begins with `[ ]`, `[X]`, or `[x]` followed by a space is a task list item" | T | `classify_list_marker` (`SpellTask`, `checkbox_ok`), `ck_uniformity` (`LKTask`); `task_items`, `task_tab_after_bullet` | Line level, both directions: a `-`, `+` or `*`, one whitespace character, the box, then the end of the line or one whitespace character; and a bullet in front of such a box is never a plain bullet.  A tab between the bullet and the box makes a task item here and a plain bullet in djot.js (divergences, 2026-10-05).  Unit: `marker_task_*` in Line.v. |
| DL1 | Definition list item | "the first line or lines after the `:` marker is parsed as inline content and taken to be the *term*.  Any further blocks ... are ... the *definition*" | T~ | `definition_list_uniformity`; `definition_list_item`, `definition_term_lines` | The term split is `def_items`, Ast.v's own function, not a statement of the rule. |
| LS1 | List | "A list is simply a sequence of list items of the same type ... changing ordered list style or bullet will stop one list and start a new one" | T | `list_same_type_joins`, `list_different_types_split` (Uniformity.v), `list_uniformity_same`; `list_style_change` | Both halves from an open list and a next marker, in any spelling, at the list's column (`list_takes` false).  A marker that shares a style with the list's surviving styles starts its next item: nothing is emitted, and the item so far joins the finished ones.  One whose styles are disjoint ends the list, which is emitted before the new list opens.  `list_uniformity_same` is the whole list for a repeated canonical marker. |
| LS2 | List | "the ambiguity will be resolved in such a way as to continue the list, if possible" | T | `list_uniformity_narrow`, `list_uniformity_narrow2`, `roman_from_one_uniformity`, `alpha_from_nine_uniformity`; `list_ambiguous_marker` | |
| LS3 | List | "The start number ... will be determined by the number of its first item.  The numbers of subsequent items are irrelevant" | T | `list_uniformity` (`items_ok` admits any number of the same style); `list_start_number` | |
| LS4 | List | "*tight* if it does not contain blank lines between items, or between blocks inside an item.  Blank lines at the start or end of a list do not count" | T~ | `item_loose_separates`, `separator_separates`, `list_spacing_separates`, `separates_item_loose`, `separates_loosens`, `separates_after_loosens` (Tightness.v); `list_tight`, `list_loose`; `list_blank_before_nested_list_item`, `list_blank_before_empty_last_item`, `list_div_closer_not_blank`, `list_blank_after_footnote_in_item`, `list_blank_after_footnote_between_items`, `list_blank_inside_footnote`, `list_blank_before_caption`, `list_blank_after_table`, `list_blank_after_open_div`, `list_blank_in_open_code` | Both directions.  The parser loosens a list only at a blank the rule counts (`separates`, `separates_after`), for items whose first line is nonblank and that pass `run_safe` (no block attribute spec open at a line boundary before the last line).  Every such blank loosens: between items (`separates_after_loosens`), and inside an item (`separates_item_loose`) when the lines before the blank leave no code block open.  A blank inside an open code block is not covered by the converse; the parser does not count it.  `separates` says "between two blocks" with the next nonblank line: written after the blank it starts a block of its own, and so does a paragraph line at its indentation.  Five shapes where djot.js breaks the rule are fixed to follow it (entries 2026-09-29): a div's closing fence no longer loosens (jgm/djot.js#157); a blank before an item that opens with a list marker, or before an empty last item, now does (jgm/djot.js#45); so does a blank that ends a footnote in an item; and a blank before a table's caption does not.  A div left open at the end of an item ends before the blank after it, so that blank loosens; a code block left open takes it as text, and does not (`SPEC-GAP`, 2026-09-30).  `run_safe` is not only a proof condition: without it the first theorem is false, for a spec that attaches to nothing between a nested list and two blanks (divergences, 2026-10-05, open). |
| LS5 | List | "tight lists should be rendered with less space between items" | n/a | | Rendering. |

Heading, block quote, list item, list: T 17, T~ 2, n/a 1.

### Leaf blocks and tables

| # | Section | Rule | Level | Checks | Notes |
| --- | --- | --- | --- | --- | --- |
| CB1 | Code block | "starts with a line of three or more consecutive backticks, optionally followed by a language specifier, but nothing else" (whitespace around it allowed) | T | `classify_backtick_fences`; `code_block_info_only`, `code_block_info_spaces` | Line level: any indentation, any run of three or more, whitespace or none before the info string, trailing whitespace.  Tilde fences: `SPEC-GAP`, 2026-08-02. |
| CB2 | Code block | "ends with a line of backticks equal or greater in length to the opening backtick 'fence,' or the end of the document or enclosing block" | T | `fence_close_backticks`, `fenced_code_closed`, `fenced_code_unclosed`, `parse_lines_quote`, `quote_uniformity_tail`, `div_uniformity`, `list_uniformity`, `footnote_content_uniformity`; `code_block_longer_fence`, `code_block_longer_closer`, `code_block_unclosed`, `code_block_closed_by_parent` | `fence_close_backticks` says which lines close a backtick fence of any length; `fenced_code_closed` and `fenced_code_unclosed` say the block runs to the first of them or the end of the document.  The enclosing-block half: each container theorem parses the contents as a document that ends with the container. |
| CB3 | Code block | "Its contents are interpreted as verbatim text" | T | `fenced_code_closed`, `fenced_code_unclosed` | The block's text is the lines between the fences joined by newlines, each less the opener's indentation and otherwise as written, whatever they hold. |
| TB1 | Thematic break | "three or more `*` or `-` characters, and nothing else (except spaces or tabs)"; "may be indented" | T | `classify_thematic`; `thematic_break_indented`, `thematic_dashes`, `thematic_mixed_ws` | Line level.  `*` and `-` may be mixed on one line, in both engines. |
| TB2 | Thematic break | "(`<hr>` in HTML)" | n/a | | Rendering. |
| RB1 | Raw block | "A code block with `=FORMAT` where the language specification would normally go is interpreted as raw content" | T | `raw_block_closed`; `raw_block` | |
| RB2 | Raw block | "passed through verbatim to output in that format" | n/a | | Rendering. |
| DV1 | Div | "a line of three or more consecutive colons, optionally followed by white space and a class name (but nothing else)" | T | `classify_div_fences`; `div`, `div_class_only` | Both directions.  Class token: 2026-08-09 entry.  No whitespace before the class (`:::foo`): `SPEC-GAP`, 2026-09-30. |
| DV2 | Div | "ends with a line of consecutive colons at least as long as the opening fence, or with the end of the document or containing block" | T | `div_close_colons`, `fenced_div_closed`, `fenced_div_unclosed`, `div_uniformity_tail`; `div_longer_closer`, `div_unclosed` | Any opener and closer, for contents that leave the div open (`run_div_open`).  The closer's `3 <= m` follows from `len <= m`, since every opener has three. |
| DV3 | Div | "The contents of a div are interpreted as block-level content" | T | `div_uniformity`, `div_uniformity_tail` | For contents that leave the div open (`div_content_ok`), which is every content the rule applies to. |
| PT1 | Pipe table | "Each row starts and ends with a pipe character (`\|`) and contains one or more *cells* separated by pipe characters" | T | `table_row_shape`, `table_row_cells`; `table_row`, `table_row_needs_closing_pipe` | Only if: every row has a bar at each end, after any indentation and before any trailing whitespace, and at least one cell.  If: for plain cells (no bar, backslash or backtick; no whitespace at either end), written as the renderer writes them.  Unit: `row_*` in Line.v, ParserExamples.v "Tables". |
| PT2 | Pipe table | a separator line: "every cell consists of a sequence of one of more `-` characters, optionally prefixed and/or suffixed by a `:`" | T | `table_row_separator`; `table_header` | Both directions, with the whitespace the scan admits: before each bar, and between cells but not before the first.  Unit: `row_sep_*`.  Cell trimming: `SPEC-GAP`, 2026-08-02. |
| PT3 | Pipe table | "the previous row is treated as a header, and alignments on that row and any subsequent rows are determined by the separator line (until a new header is found).  The separator line itself does not contribute a row" | T | `table_separator_regime`; `table_header`, `table_alignment_changes`, `table_header_resets` | Arbitrary earlier rows and prior alignments; every body row through the next separator.  Located table output erases to this fold (`of_table_fold_located`). |
| PT4 | Pipe table | the four alignment cases from leading and trailing `:` | T | `separator_cell_alignment`, `separator_row_alignments`; `table_alignment_changes` | Every positive dash width and every mix of colon patterns across separator cells; `table_separator_regime` carries the resulting alignments to table rows.  Unit: `row_sep_default_right`. |
| PT5 | Pipe table | "A table need not have a header: just omit any separator lines, or ... *begin* with a separator line" | E | `table_no_header`, `table_separator_first` | |
| PT6 | Pipe table | "Contents of table cells are parsed as inlines" | E | `table_header` | |
| PT7 | Pipe table | "backslash-escaped pipes and pipes in verbatim spans ... do not count as cell separators" | T | `table_row_escaped_bar`, `table_row_verbatim_bar`; `table_escaped_pipes` | One cell holding `\|` between plain text, and one holding a single-backtick span with any bar-bearing, backtick-free content.  Unit: `row_escaped_bar`, `row_verbatim_bar` and neighbours. |
| PT8 | Pipe table | caption: `^` lines "indented relative to the `^`"; "directly after the table, or there can be an intervening blank line" | E | `table_caption_after_table`, `table_caption_after_blank`, `table_caption_alone` | The reference's snippet on its own differs from djot.js: ours, 2026-08-22. |

Leaf blocks and tables: T 13, E 3, n/a 2.

### References, footnotes, attributes, identifiers

| # | Section | Rule | Level | Checks | Notes |
| --- | --- | --- | --- | --- | --- |
| RD1 | Reference link definition | "the reference label in square brackets, followed by a colon, followed by whitespace (or a newline) and the URL" | T | `classify_ref_whitespace`; `reference_definition` | Line level: any indentation, then after the colon either whitespace and a whitespace-free URL chunk, or nothing (the URL starts on the next line, RD2).  Whitespace after the URL makes the line text, in both engines. |
| RD2 | Reference link definition | "The URL may be split over multiple lines (... concatenated, with any leading or trailing space removed).  None of the chunks of the URL may contain internal whitespace" | T | `ref_url_chunks`, `ref_url_chunks_end` (Uniformity.v), `ref_open_value_no_ws`; `reference_definition`, `reference_url_lines` | Any number of lines after the opener, each indented past it and holding one whitespace-free run (`ref_chunk`): the URL is the first chunk and those runs joined.  The first line that is not one ends the definition and is parsed as if none were open, so a chunk with whitespace inside or after it is not part of the URL.  Unit: ParserExamples.v, "Reference definitions". |
| RD3 | Reference link definition | "No case normalization is done on reference labels" | E | `reference_case_sensitive` | |
| RD4 | Reference link definition | "Attributes on reference definitions get transferred to the link ... the attribute on the link overrides the one on the reference definition" | E | `reference_attributes`, `reference_attributes_link_overrides` | `html_tree_reference_shape` bounds what a definition can change (attributes only), not this rule. |
| FN1 | Footnote | "a footnote reference followed by a colon followed by the contents of the note, indented to any column beyond the column in which the reference starts.  The contents ... are parsed as block-level content" | T | `footnote_content_uniformity`, `footnote_open_uniformity_tail`, `footnote_text_uniformity`, `footnote_blank_uniformity`, `footnote_unshifted_uniformity` (and `_tail`s); `footnote`, `footnote_indent_past_reference`, `footnote_indent_not_past` | Except a note whose first line opens a list: `footnote_list_shift_counterexample`. |
| FN2 | Footnote | "subsequent lines in paragraphs can 'lazily' omit the indentation" | T | `lazy_stack_line`, `step_lazy_spelling`, `footnote_lazy_line`; `footnote_lazy` | |
| FN3 | Footnote | a new paragraph "must be indented, at least in the first line" | T | `footnote_content_uniformity_tail` | A nonblank line that the note does not take (`foot_takes`: not indented past the opener, and with keyed blocks on not claimed by an open key) and that is not lazy ends the note. |
| BA1 | Block attributes | "put the attributes on the line immediately before the block" | T | `attr_uniformity`; `block_attributes` | |
| BA2 | Block attributes | "if they don't fit on one line, subsequent lines must be indented" | T | `attr_continuation`, `attr_unindented`; `block_attributes_multiline`, `block_attributes_multiline_unindented` | A spec over lines indented past its opener parses as the same spec on one line, for continuation lines with content.  The "must": an unindented second line makes the two lines a paragraph (two-line case).  Unit: ParserExamples.v, "Block attributes". |
| BA3 | Block attributes | "Repeated attribute specifiers can be used, and the attributes will accumulate" | T | `attr_accumulate`; `block_attributes` | Any run of complete specs, one per line, merged in order by `Attr.merge`.  `attr_uniformity` is the one-spec case. |
| LH1 | Links to headings | "Identifiers are added automatically to any headings that do not have explicit identifiers" | T~ | `assign_heading_id_spec`; `heading_identifier` | Stated through `id_base` and `unique_id`, the pass's own functions.  Unit: `section_*`, `explicit_id_displaces_auto_id` in Document.v. |
| LH2 | Links to headings | the identifier: plain text "excluding non-textual elements such as footnote references and symbols, removing punctuation (other than `_` and `-`), replacing spaces with `-`, and ... a numerical suffix" | T~ | `is_id_sep_punct`, `is_id_sep_other`, `id_base_sep_free`, `id_base_word`, `id_base_sep`, `id_base_word_sep`, `unique_id_first`, `unique_id_fresh` (Document.v); `heading_identifier`, `heading_identifier_footnote`, `heading_identifier_symbol`, `heading_identifier_unique`, `heading_identifier_punctuation` | Shape: from the heading's plain text on, over every text and every set of taken identifiers.  Which bytes are dropped, that none reaches the identifier, that the rest is kept, and that runs of dropped bytes become one `-` between words.  The suffix gives the first candidate that is nonempty and not taken.  The plain text itself (`inlines_text`, the "excluding" clause) has only the examples.  Which punctuation is dropped follows djot.js, not the wording: `SPEC-GAP`, 2026-10-04. |
| LH3 | Links to headings | "implicit link references are created for all headings" | E | `heading_implicit_reference` | Unit: `implicit_heading_reference` in Document.v. |
| LH4 | Links to headings | `# Introduction[^1]` "generates the identifier `Introduction`, not `Introduction1`" | E | `heading_identifier_footnote` | |
| — | Reference link definition | "The reference label should be defined somewhere in the document" | T~ | see L5 | Advice to the author; what happens when it is not defined is L5. |

References, footnotes, attributes, identifiers: T 8, T~ 2, E 4 (the
last row is counted under L5).

### Nesting limits and security

| # | Section | Rule | Level | Notes |
| --- | --- | --- | --- | --- |
| NL1 | Nesting limits | "Conforming implementations can impose reasonable limits on nesting" | n/a | A permission. |
| SE1 | Security | the whole section | n/a | Out of scope by the plan. |

## Triage

Every row below T with a parse outcome, sorted into the plan's three
outcomes, and the T~ rows that stay as they are.

### Prove it, ranked

Ranked by how much of the parser a violation could hide in.  Each needs
a `dev/check/Probe.v` run over reachable states before the proof.

Container and continuation rules:

1. Done: **BQ3, LI2, FN2 joined with BQ2, LI1, FN1**.  `quote_lazy_line`,
   `list_lazy_line`, `footnote_lazy_line` (`260928.plan.lazy-lines.md`).
2. Done: **LI1 at any indentation**, as ownership (`list_item_owns`).
   Uniformity at other widths is false: a differential run over the
   reference's examples as item contents found 110 of 1400 cases where
   continuation lines at 1 to width-1 spaces parse differently from the
   same lines at the marker's width (code block contents, nested
   markers).
3. Done: **BQ2, CB2 "or enclosing container"**.  `quote_uniformity_tail`
   (a quote ended by any line that is neither a quote line nor lazy) and
   `quote_uniformity_bare` (empty lines written `>`).  The reference's
   `code_block_closed_by_parent` was already `parse_lines_quote`, a quote
   followed by a blank line.
4. Done: **BI3 over documents**, `indent_uniformity`, with no side
   condition.  An open attribute spec reads a line past its leading
   whitespace, so the padded run is a shift of the plain one there too
   (`step_fuel_pad`).

List and table structure:

5. Done: **LS4 tightness**, `item_loose_separates` and
   `separator_separates` (Tightness.v): a loose verdict always has a
   blank the rule counts.  The converse, that every such blank loosens,
   holds between items (`separates_after_loosens`) and inside an item
   (`separates_item_loose`), there for a blank outside any open code
   block (`260929.plan.list-tightness.md`, step 3).
6. Done: **LS1 the split half**, `list_different_types_split`.
7. Done: **PT3 header regime**, `table_separator_regime`, and **PT4
   alignment cases**, `separator_cell_alignment` and
   `separator_row_alignments`.

Inline structure:

8. Done: **P1 to P5 precedence**, `para_inlines_valid`: on a
   paragraph of delimiters, bare or marked with braces, and brackets
   with destinations or reference labels, the paragraph is the tree of
   the unique reading the rules allow
   (`260930.plan.inline-precedence.md`).  Smart quotes, spans and images
   are outside its alphabet.
9. Done: **M2, M3 flanking**, `parse_blocks_located_spans`
   (StoredLines.v): on the located parse's spans, over every document
   without keys (`261002.plan.inline-flanking.md` for the inline level,
   `261002.plan.stored-line-suffixes.md` for the lift).
10. Done: **BI1** `block_shape_independent`: the block tree, inlines
    erased, does not depend on the inline delimiter table, for
    configurations without keyed blocks.

Single constructs, each a small theorem over a finite or simple domain:

11. Done: **Q5** `dashes_divide`.
12. Done: **O2** `escape_every_punct`.
13. Done: **HE1, CB1, TB1, RD1** at the line level over all spellings:
    `classify_heading_ws`, `classify_backtick_fences`,
    `classify_thematic`, `classify_ref_whitespace`.
14. Done: **LH2**, `id_base` by cases on the text (`id_base_word`,
    `id_base_sep`, `id_base_word_sep`) over the bytes it drops
    (`is_id_sep_punct`, `is_id_sep_other`), and `unique_id_first` for the
    suffix.  The cases rest on the same four equations for `words`
    (Strings.v), which `normalize_label` is also built on.

Moved here from "An example is enough" on 2026-09-30, each with a plan:

15. Done: **CB2 the fence-length half, RB1, DV1, DV2**,
    `fence_close_backticks`, `fenced_code_closed`, `raw_block_closed`,
    `classify_div_fences`, `div_close_colons`, `fenced_div_closed`
    (`260930.plan.fences.md`).
16. Done: **PT1, PT2, PT7**, `table_row_shape`, `table_row_cells`,
    `table_row_separator`, `table_row_escaped_bar`,
    `table_row_verbatim_bar` (`260930.plan.pipe-table-rows.md`).
17. Done: **BA2, BA3**, `attr_continuation`, `attr_unindented`,
    `attr_accumulate` (`260930.plan.block-attributes.md`).
18. Done: **BQ1 over every spelling**, `classify_quote_marker`
    (`260930.plan.quote-marker.md`).

Added 2026-10-05, from the rows still below T:

19. Done: **LI5, TK1 over every spelling**, `classify_list_marker` and
    `styles_of_core_numeral`.  `classify_marker_open`, the canonical
    opener, is now a corollary.
20. Done: **HE3 every ending, HE2 in any mix**, `heading_ends_at` and
    `heading_ends_with_lines`.
21. Done: **LS1 the joining half**, `list_same_type_joins`.

Added 2026-10-05, from the T~ rows and the four the lists above had
missed (P2, V1, CB3, LH1):

22. Done: **O2, V1, Q5 from text mode**, `escape_in_text`,
    `verbatim_in_text`, `verbatim_at_end`, `dash_run_in_text`,
    `dash_run_at_end`.
23. Done: **RD2 every chunk**, `ref_url_chunks`, `ref_url_chunks_end`.
24. Done: **CB3**.  `fenced_code_closed` already said it; the row cited
    the roundtrip.

Added 2026-10-07, the first step from coverage to specification:

25. Done: **AT2 to AT5, C1, AT6 in part**, the attribute language as a
    grammar independent of the machine (`AttrSyntax.v`), with
    `machine_accepts` and `machine_sound` (`AttrAgree.v`,
    `261007.plan.attribute-grammar.md`).

26. Done: **O3 to O5**, stage 1 of the inline specification: backslash
    escapes in the precedence alphabet, `para_inlines_valid` unchanged in
    statement (2026-10-08).

Open: **LS4 without `run_safe`**.  The theorem is false there until the
2026-10-05 entry on a spec between a nested list and a blank is decided.

### Stays restricted

T~ rows where the restriction is not a gap to close now.

- **P1 to P5, O3 to O5**: the alphabet leaves out `{` except as a marker,
  `[^`, `[[`, `]{`, images and smart quotes; the inline specification
  widens it stage by stage (`261007.plan.inline-specification.md`).  Each is a new token
  kind in `lex` and a new case through the simulation in
  InlinePrecedence.v.  That is a plan of its own, not a row to sweep.
- **BI3**: the rule as worded is false for indentation that differs from
  line to line, which code block contents and nesting read.  Uniform
  indentation is all there is to state.
- **DL1**: the canonical marker; the term split is under "An example is
  enough".
- **LH1**: `assign_heading_id_spec` is the rule at one heading.  That
  the pass reaches every heading at every depth needs a predicate over
  each container, a further copy of the traversal
  `261003.plan.traversal-pilot.md` is meant to remove.  After that plan.
- **LH2**: the "excluding" clause is `inline_text`'s arms for footnote
  references and symbols.  A theorem would repeat the definition; the
  examples pin it.

### An example is enough

P6, L1, L2, L3, L4, L6, I1, A1, A2, A3, V2, V3, V4,
M1, M4, M5, H1, S1, D1, Q1, Q2, Q3, Q4, MA1, F1, B1, C2, Y1, R1,
N1, AT1, AT7, BI4, PT5, PT6, PT8, RD3,
RD4, LH3, LH4, and what the T~ theorem leaves of DL1.

Each is one case, or a list of cases with no quantifier worth stating,
and its examples say what the reference says.  DL1 is T~ for the
canonical marker (`definition_list_uniformity`); the rest stays at
examples.  DL1's term split is an AST function stated
once (`def_split`); proving it would restate it.

This list is why inline syntax is mostly E.  It records a choice, not a
limit: a formal statement of inline syntax beyond precedence would
reopen it.

### Spec gaps

Logged in `djotjs-divergences.md` with the `SPEC-GAP` verdict:

- HE3: a `#` line of another level ends a heading; a heading continues
  lazily inside a quote (2026-09-28).  Any block opener ends a heading
  (2026-10-05).
- LI7: a lone ambiguous marker reads as roman (2026-09-28).
- LS4: a div left open at the end of an item ends before the blank
  after it (2026-09-30).
- BQ1: a tab or CR after `>` counts as the space (2026-09-30).
- LI1, LI5, TK1: a tab or CR after a list marker or a checkbox counts as
  the space (2026-10-05).
- CB1: tilde fences (2026-08-02).
- DV1: no whitespace needed before a div's class (2026-09-30).
- PT2: separator cells are not trimmed (2026-08-02).
- LH2: punctuation in a heading separates the identifier's words, and
  `"` `'` `:` `;` are kept (2026-10-04).
- AT2 to AT7: identifier and class characters, escapable bytes and
  whitespace in values, separation between items, and a `class` key in
  one spec against stacked specs (2026-10-07).
