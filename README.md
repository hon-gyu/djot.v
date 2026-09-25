<!-- ai-disclosure: ai-assisted -->
# djot.v

djot.v is a [djot](https://djot.net) parser written and verified in Rocq, with an extracted OCaml parser, a AST-to-djot renderer and an AST-to-HTML renderer. 

It is _verified_ in the sense that the goals behind djot's design are stated as theorems about the parser and proved. The main ones:

- **No backtracking.** Blocks are parsed line by line, and a later line never changes an earlier block. Inline text is scanned once, byte by byte. This is what makes streaming and incremental parsing possible: after an edit, a parser can resume from a saved state instead of starting over.
- **Container uniformity.** Text placed in a block quote or a list item parses as it would on its own, so moving content in or out of a container does not change its meaning.
- **Local interpretation.** Whether `[foo][bar]` is a link does not depend on whether `bar` is defined elsewhere in the document, so a highlighter can classify it without reading the rest of the document.
- **Safe rewrapping.** A line inside a paragraph never starts a list, heading or quote, whatever it begins with. Rewrapping a paragraph cannot create one by accident.
- **No expressive blind spots.** Every document the renderer accepts can be written as djot that parses back to exactly that document.

The first four are goals from [djot's rationale](https://github.com/jgm/djot#rationale) and [Beyond Markdown](https://johnmacfarlane.net/beyond-markdown.html); the fifth is djot's goal 4, stated as a roundtrip. [Properties](#properties) lists everything proved, what each proof assumes, and what is planned.

It is _generalized_ in the sense that djot is one setting of a configurable parser, and the theorems are proved for every setting, or state which settings can break them. A new syntax option therefore comes with an answer to which of the properties above it keeps. For example, a Markdown-like profile writes strong emphasis as `**` rather than `*`, allows sublists without a blank line, and allows setext (underlined) headings. The proofs show that it keeps no backtracking, uniformity and the roundtrip, and that sublists without a blank line and setext headings are what cost it safe rewrapping. Beyond that, syntax extensions can added, and two of them are supported: wikilinks (Obsidian-style) and keyed blocks (`label: content`, pairing an inline label with a block). 

> Gen-AI disclosure: most of the proofs were written by LLMs, mainly Claude Opus 5, with some use of OpenAI Sol 5 and Deepseek Flash 4.1.

## Properties

The theorems are checked by Rocq, with no axioms and no admitted proofs.

Status is **proved**, **planned**, or **planned (long-term)**.

| Property | Implication | Status |
| --- | --- | --- |
| Blocks are committed line by line; a later line never changes an earlier block. Holds for every configuration. | Block parsing does not backtrack, and no extension can make it. | proved: `prefix_determinism`, `no_future_line_dependence`; every configuration: `block_incremental_holds` |
| The inline scanner reads each byte once. Where djot.js replays a failed attribute or link candidate, this scanner carries the ordinary reading alongside. Holds for every set of inline delimiters. | Inline parsing does not backtrack. | proved: `iscan_str_no_reread`; every configuration: `inline_structural_holds` |
| Parsing takes linear time. | Reading each byte once is not a time bound: a byte can do work proportional to the number of open delimiters. Needs a cost model. | planned (long-term) |
| Prefixing every line with `> ` wraps the parse in a quote, for any content. | Content moved into a quote keeps its meaning. | proved: `quote_uniformity` |
| A list item's contents parse as they would at top level, for bullet and ordered lists (including roman and alphabetic), for items the renderer can produce (`items_ok`). | Content moved into a list item keeps its meaning. | proved: `list_uniformity`, `ordered_uniformity` |
| A fenced div's contents parse as at top level when the div is enabled, no content line closes it, and no code fence remains open. Definition-list item contents do the same when definition lists are enabled and every item satisfies `item_ok colon`. | Moving qualifying content into either container keeps its block parse before definition terms are paired with definitions. | proved: `div_uniformity`, `div_uniformity_tail`, `definition_list_uniformity` |
| A footnote definition's contents parse as they would at top level. | Moving content into a footnote preserves its block parse. | planned |
| Whether `[foo][bar]` is a link does not depend on whether `bar` is defined. | An editor can highlight links without document-wide information. | proved, but only because classification is never given the definitions: `classify_inlines_locality` |
| Changing reference definitions leaves inline HTML element nesting and text unchanged; it can change link and image attributes. | Inline structure does not depend on reference lookup. | proved: `render_inline_reference_shape`, `render_inlines_reference_shape` |
| Changing reference definitions leaves the whole document tree's structure unchanged. | Reference resolution changes attributes without restructuring the document. | planned |
| A paragraph's continuation line never starts a block, even if it begins with `- `, `# `, `> `, `1. ` or `***`. | Rewrapping a paragraph cannot turn part of it into a list, heading or quote. Inline content can still change when a break moves into verbatim, after a backslash, or past trailing spaces (`wrap_moves_*`). | proved: `hard_wrap_one_para`, `hard_wrap_para_then_rest` |
| With heading continuation enabled, ordinary text lines and repeated same-level heading markers remain in the open heading until a blank line. | Rewrapping within either kind of continuation keeps one heading; other block openers can end it. | proved: `heading_text_wrap_then_rest`, `heading_marker_wrap_then_rest` |
| Every input parses, and the output is always well-formed. | No syntax errors. Consumers need not handle malformed trees. | proved: `wf_parse`, `wf_parse_doc` |
| `parse (render d) = d` for every canonical document, that is, every document the renderer can write. | djot-to-djot conversion loses nothing. | proved: `roundtrip_blocks`, `roundtrip_doc` |
| `parse (render (parse s)) = parse s` for every input. | A formatter never changes a document's meaning. Needs every parse result to be canonical. | planned |
| The parser state is all a prefix passes forward. | An editor can reparse after an edit only until the state matches the old one, and reuse the rest. | proved: `prefix_state_suffices`, `reparse_only_new` |
| Replacing one block, directly or by its id, leaves every other block's parse unchanged. | | proved: `block_replace`, `replace_at_id_parse` |
| The located parse is the plain parse with positions attached. | Source positions do not affect the parse. | proved: `parse_blocks_located_erase`, `parse_doc_located_erase` |
| Without raw content, every `<` in the HTML output belongs to a tag. | Source text cannot inject HTML. | proved: `serialize_lt_tags` |
| HTML output is well-nested. | | planned (long-term) |
| Roundtrip, well-formedness and uniformity hold for every profile, over that profile's constructs. | An extension or profile gets these properties without new proofs. | proved: the theorems are stated over the configuration |
| Each block setting is read at one decision point: switching tables on changes what a table row opens and nothing else. | | proved: `with_*_opens_only_*`, `with_*_finishes_nothing` |
| Turning a construct off (tables, say) does not change the parse of a document that never uses it. Proved per decision point; the whole-document statement must account for the construct appearing at any nesting depth. | | planned |
| Two settings that each preserve an invariant preserve it together. | Extensions that are each safe stay safe when combined. | proved: `preserves_compose` |
| Only three settings can break rewrap safety: list interruption, setext underlines, and the keyed-block extension. Each has a precondition under which it does not. The Markdown-like profile breaks it deliberately. | An extension author knows whether a setting affects rewrapping, and under what condition it does not. | proved: `with_*_preserves_wrap_neutral`, `markdown_wrap_splits` |
| A list may interrupt a paragraph when its marker cannot occur in prose. The condition is necessary and sufficient; `1865.` at the start of a line refutes a looser one. | A policy more permissive than djot's with the same guarantee against accidental lists. | proved: `with_marker_interrupts_accidental_list_immune_iff`, `prose_safe_markers_is_immune` |
| Changing the character of one inline delimiter (emphasis, strong, highlight, ...) keeps the configuration valid when the new character differs from every other enabled delimiter's. | Only the changed delimiter needs checking. | proved: `update_drow_preserves_admissible` |
| If strong emphasis is respelled from `*` to `+`, a document with `*` and `+` swapped parses to the old tree with `*` and `+` swapped in its text. Likewise for any delimiter. The precondition is known. | A profile can respell a delimiter without changing what documents mean. | planned |
| For a directory of notes published as a site: URLs are unique once one decidable check passes; editing a note leaves other pages' output unchanged unless its title, ids or links changed; backlinks are exact; renaming a note equals rewriting its URL in the built site. | A site generator can rebuild and rename incrementally. | proved: `routes_injective`, `build_local`, `backlinks_sound`, `backlinks_complete`, `rename_correct` |
| After a rename, every note is still canonical. | | partly proved: only notes linking to the renamed one need checking (`rename_canonical_local`); the rest planned |
| The renderer is proved as a relation over all valid spellings, not one canonical spelling. | Needed only if a construct has no single obvious spelling; none has so far. | planned (long-term) |

## Conformance

The parser is compared with [djot.js](https://github.com/jgm/djot.js): it matches the expected HTML on all 287 cases of djot.js's test suite, and agrees with djot.js on generated canonical documents. Agreement is tested, not proved.

To run the comparison, build djot.js once with `make build-djotjs`, then
`make diff`. 

## Extraction

Rocq supports extraction to OCaml, Haskell and Scheme. We tested extraction to OCaml only.

With [js_of_ocaml](https://github.com/ocsigen/js_of_ocaml), a JavaScript or WebAssembly parser can be built in theory.

Performance: long lines are still quadratic. There's ongoing work to improve this.

## Development Requirements

- opam switch with Rocq 9.x, dune ≥ 3.20

## References

- [djot](https://github.com/jgm/djot)
- [djot.js](https://github.com/jgm/djot.js)
- [djoths](https://github.com/jgm/djoths)
- [cmarkit](https://github.com/dbuenzli/cmarkit)
