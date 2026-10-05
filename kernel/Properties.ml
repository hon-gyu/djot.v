open InlineTable
open Profile
open ProfileChecks

type status =
| Proved
| Conditional of string
| Broken of string * string
| Conjectured
| Unknown
| Inapplicable of string

(** val status_name : status -> string **)

let status_name = function
| Proved -> "proved"
| Conditional _ -> "conditional"
| Broken (_, _) -> "broken"
| Conjectured -> "conjectured"
| Unknown -> "unknown"
| Inapplicable _ -> "inapplicable"

(** val claimed : status -> bool **)

let claimed = function
| Proved -> true
| Conditional _ -> true
| _ -> false

type property = { p_id : string; p_group : string; p_statement : string;
                  p_implication : string; p_theorems : string list;
                  p_status : (options -> status) }

(** val always : status -> options -> status **)

let always s _ =
  s

(** val no_backtracking : string **)

let no_backtracking =
  "No backtracking"

(** val uniformity : string **)

let uniformity =
  "Container uniformity"

(** val local : string **)

let local =
  "Local interpretation"

(** val wrapping : string **)

let wrapping =
  "Safe hard-wrapping"

(** val structure : string **)

let structure =
  "Block structure first"

(** val precedence : string **)

let precedence =
  "Inline precedence"

(** val p_block_no_backtracking : property **)

let p_block_no_backtracking =
  { p_id = "block-no-backtracking"; p_group = no_backtracking; p_statement =
    "A later line never changes a block already parsed."; p_implication =
    "Blocks can be emitted as lines arrive."; p_theorems =
    ("prefix_determinism" :: ("no_future_line_dependence" :: [])); p_status =
    (always Proved) }

(** val p_inline_no_backtracking : property **)

let p_inline_no_backtracking =
  { p_id = "inline-no-backtracking"; p_group = no_backtracking; p_statement =
    "Each byte of a paragraph is read once."; p_implication =
    "An unclosed * or [ never forces a rescan."; p_theorems =
    ("iscan_str_no_reread" :: []); p_status = (always Proved) }

(** val p_incremental_reparse : property **)

let p_incremental_reparse =
  { p_id = "incremental-reparse"; p_group = no_backtracking; p_statement =
    "After an edit, reparsing can stop once the parser is back in the state it had before the edit.";
    p_implication =
    "An editor reparses the changed region and reuses the rest.";
    p_theorems = ("prefix_state_suffices" :: ("reparse_only_new" :: []));
    p_status = (always Proved) }

(** val p_block_replace : property **)

let p_block_replace =
  { p_id = "block-replace"; p_group = no_backtracking; p_statement =
    "Replacing one block leaves the parse of every other block unchanged.";
    p_implication = "An edit's effect stays within the block it touches.";
    p_theorems = ("block_replace" :: ("replace_at_id_parse" :: []));
    p_status = (always Proved) }

(** val p_positions : property **)

let p_positions =
  { p_id = "positions"; p_group = no_backtracking; p_statement =
    "Recording source positions does not change the parse."; p_implication =
    "A tool that needs positions gets the same tree as everyone else.";
    p_theorems =
    ("parse_blocks_located_erase" :: ("parse_doc_located_erase" :: []));
    p_status = (always Proved) }

(** val p_linear_time : property **)

let p_linear_time =
  { p_id = "linear-time"; p_group = no_backtracking; p_statement =
    "Parsing takes linear time."; p_implication =
    "Reading each byte once does not give this: one byte can do work proportional to the number of open delimiters.";
    p_theorems = []; p_status = (always Conjectured) }

(** val p_quote_uniformity : property **)

let p_quote_uniformity =
  { p_id = "quote-uniformity"; p_group = uniformity; p_statement =
    "Text inside a block quote parses as it would at top level.";
    p_implication =
    "Moving text into or out of a quote does not change its meaning.";
    p_theorems = ("quote_uniformity" :: ("quote_uniform_sound" :: []));
    p_status = (fun o ->
    if quote_uniform o
    then Proved
    else Broken
           ("A quote whose first line is a callout header is a callout, and the header is not part of its content.",
           "> [!note] Title\n> body\n")) }

(** val p_list_uniformity : property **)

let p_list_uniformity =
  { p_id = "list-uniformity"; p_group = uniformity; p_statement =
    "Text inside an item of a bullet or ordered list parses as it would at top level, when indented the way the formatter writes it.";
    p_implication =
    "Moving text into or out of a list item does not change its meaning.";
    p_theorems = ("list_uniformity" :: ("ordered_uniformity" :: []));
    p_status = (always Proved) }

(** val p_definition_list_uniformity : property **)

let p_definition_list_uniformity =
  { p_id = "definition-list-uniformity"; p_group = uniformity; p_statement =
    "The same, for the items of a definition list."; p_implication =
    "Moving text into or out of a definition does not change its meaning.";
    p_theorems = ("definition_list_uniformity" :: []); p_status = (fun o ->
    if o.o_deflists then Proved else Inapplicable "Definition lists are off") }

(** val p_div_uniformity : property **)

let p_div_uniformity =
  { p_id = "div-uniformity"; p_group = uniformity; p_statement =
    "Text inside a fenced div parses as it would at top level, unless it contains the div's own closing fence.";
    p_implication =
    "Moving text into or out of a div does not change its meaning.";
    p_theorems = ("div_uniformity" :: ("div_uniformity_tail" :: []));
    p_status = (fun o ->
    if o.o_divs then Proved else Inapplicable "Divs are off") }

(** val p_footnote_uniformity : property **)

let p_footnote_uniformity =
  { p_id = "footnote-uniformity"; p_group = uniformity; p_statement =
    "Lines indented under a footnote belong to it, cannot affect anything outside it, and parse as they would at top level.";
    p_implication =
    "Moving text into a footnote does not change its meaning."; p_theorems =
    ("footnote_content_uniformity" :: ("footnote_text_uniformity" :: ("footnote_list_shift_counterexample" :: [])));
    p_status = (fun o ->
    if o.o_inline.dc_footnotes
    then Conditional
           "Not when the footnote's first line starts a list: the indentation of the following items is measured from the footnote marker."
    else Inapplicable "Footnotes are off") }

(** val p_lazy_lines : property **)

let p_lazy_lines =
  { p_id = "lazy-lines"; p_group = uniformity; p_statement =
    "A text line that continues a paragraph may leave out the prefixes of the quotes, list items and footnotes around it, and parses as it would with them written.";
    p_implication =
    "Leaving out a prefix on such a line does not change the document.";
    p_theorems =
    ("lazy_stack_line" :: ("step_lazy" :: ("lazy_line_restore" :: ("lazy_uniform_sound" :: []))));
    p_status = (fun o ->
    if lazy_uniform o
    then Proved
    else Conditional
           "Not for a line that underlines the paragraph: it makes a setext heading.") }

(** val p_list_tightness : property **)

let p_list_tightness =
  { p_id = "list-tightness"; p_group = uniformity; p_statement =
    "A list is loose exactly where a blank line separates two of its items, or two blocks inside one item.";
    p_implication =
    "Whether a list renders with space between its items follows from where its blank lines are.";
    p_theorems =
    ("list_spacing_separates" :: ("separates_loosens" :: ("blank_between_items_loosens" :: [])));
    p_status =
    (always (Conditional
      "For items in which no block attribute spans several lines. A blank line inside a code block does not count.")) }

(** val p_indent_uniformity : property **)

let p_indent_uniformity =
  { p_id = "indent-uniformity"; p_group = uniformity; p_statement =
    "Indenting every line of a document by the same amount does not change its parse.";
    p_implication =
    "A document pasted at some indentation means the same thing.";
    p_theorems = ("indent_uniformity" :: []); p_status = (always Proved) }

(** val p_reference_locality : property **)

let p_reference_locality =
  { p_id = "reference-locality"; p_group = local; p_statement =
    "Whether [foo][bar] is a link does not depend on whether bar is defined.";
    p_implication = "Inline syntax can be read from the paragraph alone.";
    p_theorems = ("classify_inlines_locality" :: []); p_status =
    (always Proved) }

(** val p_reference_shape : property **)

let p_reference_shape =
  { p_id = "reference-shape"; p_group = local; p_statement =
    "Adding, removing or changing a reference definition changes only link and image attributes in the HTML.";
    p_implication = "Resolving references never restructures the document.";
    p_theorems = ("render_blocks_reference_shape" :: []); p_status =
    (always Proved) }

(** val p_hard_wrap_paragraph : property **)

let p_hard_wrap_paragraph =
  { p_id = "hard-wrap-paragraph"; p_group = wrapping; p_statement =
    "A line inside a paragraph never starts a new block."; p_implication =
    "Hard-wrapping a paragraph cannot create a list, heading or quote by accident.";
    p_theorems =
    ("hard_wrap_one_para" :: ("hard_wrap_para_then_rest" :: ("wrap_safe_iff" :: ("wrap_cut_list" :: ("wrap_cut_setext" :: [])))));
    p_status = (fun o ->
    if wrap_safe o
    then Proved
    else if o.o_list_interrupts
         then Broken ("A line that begins with a list marker starts a list.",
                "A paragraph wrapped so that the next line starts with\n- a hyphen.\n")
         else if o.o_setext
              then Broken
                     ("A line of = or - under a paragraph makes it a heading.",
                     "A paragraph wrapped before\n===\n")
              else Conjectured) }

(** val p_hard_wrap_heading : property **)

let p_hard_wrap_heading =
  { p_id = "hard-wrap-heading"; p_group = wrapping; p_statement =
    "A heading continues on the following lines until a blank line.";
    p_implication = "Hard-wrapping a long heading keeps it one heading.";
    p_theorems =
    ("heading_text_wrap_then_rest" :: ("heading_marker_wrap_then_rest" :: []));
    p_status = (fun o ->
    if heading_wrap_safe o
    then Proved
    else Broken ("A heading is one line.",
           "# A heading wrapped\nonto a second line\n")) }

(** val p_block_structure_first : property **)

let p_block_structure_first =
  { p_id = "block-structure-first"; p_group = structure; p_statement =
    "Which blocks a document has, and how they nest, is decided without reading inline syntax.";
    p_implication =
    "A tool can find the blocks of a document without an inline parser, and a bug in inline parsing cannot move a block boundary.";
    p_theorems = ("block_shape_independent" :: []); p_status = (fun o ->
    if shape_first o
    then Conditional
           "Except a table caption, which disappears when its inline content is empty."
    else Unknown) }

(** val p_inline_precedence : property **)

let p_inline_precedence =
  { p_id = "inline-precedence"; p_group = precedence; p_statement =
    "When delimiters overlap, the first opener that gets closed wins, and a closer takes the closest open opener. Exactly one reading follows these rules, and the parser gives it.";
    p_implication =
    "Overlapping delimiters have one meaning, which can be worked out by hand.";
    p_theorems = ("para_inlines_valid" :: ("valid_unique" :: [])); p_status =
    (always (Conditional
      "For emphasis-like delimiters, links and plain text. Smart quotes, spans and images are not covered.")) }

(** val all : property list **)

let all =
  p_block_no_backtracking :: (p_inline_no_backtracking :: (p_incremental_reparse :: (p_block_replace :: (p_positions :: (p_linear_time :: (p_quote_uniformity :: (p_list_uniformity :: (p_definition_list_uniformity :: (p_div_uniformity :: (p_footnote_uniformity :: (p_lazy_lines :: (p_list_tightness :: (p_indent_uniformity :: (p_reference_locality :: (p_reference_shape :: (p_hard_wrap_paragraph :: (p_hard_wrap_heading :: (p_block_structure_first :: (p_inline_precedence :: [])))))))))))))))))))
