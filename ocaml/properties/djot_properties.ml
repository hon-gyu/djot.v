(* ai-disclosure: ai-generated *)

open Djot
module Checks = Kernel.ProfileChecks

type status =
  | Proved
  | Proved_with_caveat of string
  | Broken of
      { reason : string
      ; example : string
      }
  | Expected
  | Unknown
  | Not_applicable of string

type t =
  { id : string
  ; group : string
  ; statement : string
  ; implication : string
  ; theorems : (string * string) list
  ; status : Profile.t -> status
  }

let id p = p.id
let group p = p.group
let statement p = p.statement
let implication p = p.implication
let theorems p = p.theorems
let status p = p.status
let always s _ = s
let options (p : Profile.t) = (p :> Kernel.Profile.options)

(* Proved where the switch is on, and about nothing where it is off. *)
let needs (switch : bool -> Profile.t -> Profile.t) what on p =
  if Profile.equal p (switch true p) then on else Not_applicable (what ^ " are off")
;;

let no_backtracking = "No backtracking"
let uniformity = "Container uniformity"
let local = "Local interpretation"
let wrapping = "Safe hard-wrapping"
let structure = "Block structure first"
let precedence = "Inline precedence"

let all =
  [ { id = "block-no-backtracking"
    ; group = no_backtracking
    ; statement = "A later line never changes a block already parsed."
    ; implication = "Blocks can be emitted as lines arrive."
    ; theorems =
        [ "prefix_determinism", "Uniformity.v"
        ; "no_future_line_dependence", "Uniformity.v"
        ]
    ; status = always Proved
    }
  ; { id = "inline-no-backtracking"
    ; group = no_backtracking
    ; statement = "Each byte of a paragraph is read once."
    ; implication = "An unclosed * or [ never forces a rescan."
    ; theorems = [ "iscan_str_no_reread", "InlineScan.v" ]
    ; status = always Proved
    }
  ; { id = "incremental-reparse"
    ; group = no_backtracking
    ; statement =
        "After an edit, reparsing can stop once the parser is back in the state it had \
         before the edit."
    ; implication = "An editor reparses the changed region and reuses the rest."
    ; theorems =
        [ "prefix_state_suffices", "Uniformity.v"; "reparse_only_new", "Uniformity.v" ]
    ; status = always Proved
    }
  ; { id = "block-replace"
    ; group = no_backtracking
    ; statement = "Replacing one block leaves the parse of every other block unchanged."
    ; implication = "An edit's effect stays within the block it touches."
    ; theorems = [ "block_replace", "Roundtrip.v"; "replace_at_id_parse", "Address.v" ]
    ; status = always Proved
    }
  ; { id = "positions"
    ; group = no_backtracking
    ; statement = "Recording source positions does not change the parse."
    ; implication = "A tool that needs positions gets the same tree as everyone else."
    ; theorems =
        [ "parse_blocks_located_erase", "Reparse.v"
        ; "parse_doc_located_erase", "Document.v"
        ]
    ; status = always Proved
    }
  ; { id = "linear-time"
    ; group = no_backtracking
    ; statement = "Parsing takes linear time."
    ; implication =
        "Reading each byte once does not give this: one byte can do work proportional to \
         the number of open delimiters."
    ; theorems = []
    ; status = always Expected
    }
  ; { id = "quote-uniformity"
    ; group = uniformity
    ; statement = "Text inside a block quote parses as it would at top level."
    ; implication = "Moving text into or out of a quote does not change its meaning."
    ; theorems = [ "quote_uniformity", "Uniformity.v" ]
    ; status =
        (fun p ->
          if Checks.quote_uniform (options p)
          then Proved
          else
            Broken
              { reason =
                  "A quote whose first line is a callout header is a callout, and the \
                   header is not part of its content."
              ; example = "> [!note] Title\n> body\n"
              })
    }
  ; { id = "list-uniformity"
    ; group = uniformity
    ; statement =
        "Text inside an item of a bullet or ordered list parses as it would at top \
         level, when indented the way the formatter writes it."
    ; implication = "Moving text into or out of a list item does not change its meaning."
    ; theorems = [ "list_uniformity", "ListUniformity.v"; "ordered_uniformity", "OrderedList.v" ]
    ; status = always Proved
    }
  ; { id = "definition-list-uniformity"
    ; group = uniformity
    ; statement = "The same, for the items of a definition list."
    ; implication = "Moving text into or out of a definition does not change its meaning."
    ; theorems = [ "definition_list_uniformity", "OrderedList.v" ]
    ; status = needs Profile.with_deflists "Definition lists" Proved
    }
  ; { id = "div-uniformity"
    ; group = uniformity
    ; statement =
        "Text inside a fenced div parses as it would at top level, unless it contains \
         the div's own closing fence."
    ; implication = "Moving text into or out of a div does not change its meaning."
    ; theorems = [ "div_uniformity", "Uniformity.v"; "div_uniformity_tail", "Uniformity.v" ]
    ; status = needs Profile.with_divs "Divs" Proved
    }
  ; { id = "footnote-uniformity"
    ; group = uniformity
    ; statement =
        "Lines indented under a footnote belong to it, cannot affect anything outside \
         it, and parse as they would at top level."
    ; implication = "Moving text into a footnote does not change its meaning."
    ; theorems =
        [ "footnote_content_uniformity", "Uniformity.v"
        ; "footnote_text_uniformity", "Uniformity.v"
        ; "footnote_list_shift_counterexample", "Uniformity.v"
        ]
    ; status =
        needs
          Profile.with_footnotes
          "Footnotes"
          (Proved_with_caveat
             "Not when the footnote's first line starts a list: the indentation of the \
              following items is measured from the footnote marker.")
    }
  ; { id = "lazy-lines"
    ; group = uniformity
    ; statement =
        "A text line that continues a paragraph may leave out the prefixes of the quotes, \
         list items and footnotes around it, and parses as it would with them written."
    ; implication = "Leaving out a prefix on such a line does not change the document."
    ; theorems =
        [ "lazy_stack_line", "Uniformity.v"
        ; "step_lazy", "Uniformity.v"
        ; "lazy_line_restore", "Uniformity.v"
        ]
    ; status =
        (fun p ->
          if Checks.lazy_uniform (options p)
          then Proved
          else
            Proved_with_caveat
              "Not for a line that underlines the paragraph: it makes a setext heading.")
    }
  ; { id = "list-tightness"
    ; group = uniformity
    ; statement =
        "A list is loose only where a blank line separates two of its items, or two \
         blocks inside one item."
    ; implication =
        "Whether a list renders with space between its items follows from where its \
         blank lines are."
    ; theorems = [ "list_spacing_separates", "Tightness.v" ]
    ; status =
        always
          (Proved_with_caveat
             "One direction: a list the parser calls loose has such a blank line.")
    }
  ; { id = "indent-uniformity"
    ; group = uniformity
    ; statement =
        "Indenting every line of a document by the same amount does not change its parse."
    ; implication = "A document pasted at some indentation means the same thing."
    ; theorems = [ "indent_uniformity", "ListUniformity.v" ]
    ; status =
        always (Proved_with_caveat "As long as no block attribute spans several lines.")
    }
  ; { id = "reference-locality"
    ; group = local
    ; statement = "Whether [foo][bar] is a link does not depend on whether bar is defined."
    ; implication = "Inline syntax can be read from the paragraph alone."
    ; theorems = [ "classify_inlines_locality", "InlineScan.v" ]
    ; status = always Proved
    }
  ; { id = "reference-shape"
    ; group = local
    ; statement =
        "Adding, removing or changing a reference definition changes only link and image \
         attributes in the HTML."
    ; implication = "Resolving references never restructures the document."
    ; theorems = [ "render_blocks_reference_shape", "Html.v" ]
    ; status = always Proved
    }
  ; { id = "hard-wrap-paragraph"
    ; group = wrapping
    ; statement = "A line inside a paragraph never starts a new block."
    ; implication =
        "Hard-wrapping a paragraph cannot create a list, heading or quote by accident."
    ; theorems =
        [ "hard_wrap_one_para", "Invariants.v"
        ; "hard_wrap_para_then_rest", "Invariants.v"
        ; "wrap_safe_iff", "ProfileChecks.v"
        ; "wrap_cut_list", "ProfileChecks.v"
        ; "wrap_cut_setext", "ProfileChecks.v"
        ]
    ; status =
        (fun p ->
          let o = options p in
          if Checks.wrap_safe o
          then Proved
          else if o.o_list_interrupts
          then
            Broken
              { reason = "A line that begins with a list marker starts a list."
              ; example = "A paragraph wrapped so that the next line starts with\n- a hyphen.\n"
              }
          else if o.o_setext
          then
            Broken
              { reason = "A line of = or - under a paragraph makes it a heading."
              ; example = "A paragraph wrapped before\n===\n"
              }
          else
            Broken
              { reason = "A text line with a key is a keyed block, not a paragraph."
              ; example = "note: a paragraph\nthat goes on\n"
              })
    }
  ; { id = "hard-wrap-heading"
    ; group = wrapping
    ; statement = "A heading continues on the following lines until a blank line."
    ; implication = "Hard-wrapping a long heading keeps it one heading."
    ; theorems =
        [ "heading_text_wrap_then_rest", "Uniformity.v"
        ; "heading_marker_wrap_then_rest", "Uniformity.v"
        ]
    ; status =
        (fun p ->
          if Checks.heading_wrap_safe (options p)
          then Proved
          else
            Broken
              { reason = "A heading is one line."
              ; example = "# A heading wrapped\nonto a second line\n"
              })
    }
  ; { id = "block-structure-first"
    ; group = structure
    ; statement =
        "Which blocks a document has, and how they nest, is decided without reading \
         inline syntax."
    ; implication =
        "A tool can find the blocks of a document without an inline parser, and a bug in \
         inline parsing cannot move a block boundary."
    ; theorems = [ "block_shape_independent", "BlockShape.v" ]
    ; status =
        (fun p ->
          if Checks.shape_first (options p)
          then
            Proved_with_caveat
              "Except a table caption, which disappears when its inline content is empty."
          else Unknown)
    }
  ; { id = "inline-precedence"
    ; group = precedence
    ; statement =
        "When delimiters overlap, the first opener that gets closed wins, and a closer \
         takes the closest open opener. Exactly one reading follows these rules, and the \
         parser gives it."
    ; implication = "Overlapping delimiters have one meaning, which can be worked out by hand."
    ; theorems = [ "para_inlines_valid", "InlinePrecedence.v"; "valid_unique", "Precedence.v" ]
    ; status =
        always
          (Proved_with_caveat
             "For emphasis-like delimiters, links and plain text. Smart quotes, spans and \
              images are not covered.")
    }
  ]
;;
