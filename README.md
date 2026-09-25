# djot.v

djot.v is a [djot](https://djot.net) parser written and verified in Rocq, with an extracted OCaml parser, an AST-to-djot renderer and an AST-to-HTML renderer.

It is _verified_ in the sense that the goals behind djot's design are stated as theorems about the parser and proved. The main ones:

- **No backtracking.** Blocks are parsed line by line, and a later line never changes an earlier block. Inline text is scanned once, byte by byte. This is what makes streaming and incremental parsing possible: after an edit, a parser can resume from a saved state instead of starting over.
- **Container uniformity.** Text placed in a block quote or a list item parses as it would on its own, so moving content in or out of a container does not change its meaning.
- **Local interpretation.** Whether `[foo][bar]` is a link does not depend on whether `bar` is defined elsewhere in the document, so a highlighter can classify it without reading the rest of the document.
- **Safe rewrapping.** A line inside a paragraph never starts a list, heading or quote, whatever it begins with. Rewrapping a paragraph cannot create one by accident.
- **No expressive blind spots.** Every document the renderer accepts can be written as djot that parses back to exactly that document.

See [djot's rationale](https://github.com/jgm/djot#rationale) and [Beyond Markdown](https://johnmacfarlane.net/beyond-markdown.html) for where these goals come from. [Properties](#properties) lists everything proved, what each proof assumes, and what is still to be done.

It is _generalized_ in the sense that djot is one setting of a configurable parser. The theorems are proved for every combination of the settings below, or state which settings break them, so each setting comes with an answer to which of the properties above it keeps. For example, a Markdown-like profile writes strong emphasis as `**` rather than `*`, allows sublists without a blank line, and allows setext (underlined) headings. The proofs show that it keeps no backtracking, uniformity and the roundtrip, and that sublists without a blank line and setext headings are what cost it safe rewrapping. This syntax profile feels familiar to Markdown users, and most of djot's guarantees still hold.

> Gen-AI disclosure: most of the proofs were written by LLMs, mainly Claude Opus 5, with some use of OpenAI Sol 5 and Deepseek Flash 4.1.

## Djot Properties

The theorems are checked by Rocq, with no axioms and no admitted proofs.

Status is **proved**, **planned**, or **planned (long-term)**.

### No backtracking

| Property | Implication | Status |
| --- | --- | --- |
| Block parsing does not backtrack: a later line never changes a block already parsed. | Blocks can be emitted as lines arrive. | proved: `prefix_determinism`, `no_future_line_dependence` |
| Inline parsing does not backtrack: each byte of a paragraph is read once. | An unclosed `*` or `[` never forces a rescan. | proved: `iscan_str_no_reread` |
| After an edit, reparsing can stop as soon as the parser is back in the state it had before the edit. | An editor reparses only the changed region and reuses the rest of the old parse. | proved: `prefix_state_suffices`, `reparse_only_new` |
| Replacing one block leaves the parse of every other block unchanged. | An edit's effect stays within the block it touches. | proved: `block_replace`, `replace_at_id_parse` |
| Recording source positions does not change the parse. | Tools that need positions, such as editors, get the same tree as everyone else. | proved: `parse_blocks_located_erase`, `parse_doc_located_erase` |
| Parsing takes linear time. | Reading each byte once is not enough for this: one byte can do work proportional to the number of open delimiters. | planned (long-term) |

### Container uniformity

| Property | Implication | Status |
| --- | --- | --- |
| Text inside a block quote, list item, fenced div or definition-list item parses as it would at top level. For list items, the text must be indented the way the formatter writes it; for divs, it must not contain the div's own closing fence. | Moving text into or out of a container does not change its meaning. | proved: `quote_uniformity`, `list_uniformity`, `ordered_uniformity`, `div_uniformity`, `div_uniformity_tail`, `definition_list_uniformity` |
| Lines indented under a footnote belong to it and cannot affect anything outside it. They parse as they would at top level, unless the footnote's first line starts a list. | Moving text into a footnote does not change its meaning, with one exception: in `[^a]: - x` followed by `  - y`, the indentation of `- y` is measured from `[^a]:`, so it becomes a second item, while the same two lines at top level make one item. | proved: `footnote_content_uniformity`, `footnote_content_uniformity_tail`, `footnote_open_uniformity_tail`, `footnote_unshifted_uniformity`, `footnote_text_uniformity`, `footnote_blank_uniformity` (and tail variants); the exception: `footnote_list_shift_counterexample` |

### Local interpretation

| Property | Implication | Status |
| --- | --- | --- |
| Whether `[foo][bar]` is a link does not depend on whether `bar` is defined. | Inline syntax can be read from the paragraph alone, without the rest of the document. | proved, and true by construction, since link recognition never sees the definitions: `classify_inlines_locality` |
| Adding, removing or changing a reference definition changes only link and image attributes in the HTML, such as the URL,, never its structure or text. | Resolving references never restructures the document. | proved: `render_inline_reference_shape`, `render_inlines_reference_shape`, `html_tree_reference_shape`, `render_document_foot_reference_shape`, `render_blocks_reference_shape` |

### Safe rewrapping

| Property | Implication | Status |
| --- | --- | --- |
| A line inside a paragraph never starts a new block, even if it begins with `- `, `# `, `> `, `1. ` or `***`. | Rewrapping a paragraph cannot accidentally create a list, heading or quote. It can still change inline content when a line break moves into verbatim, after a backslash, or past trailing spaces (`wrap_moves_*`). | proved: `hard_wrap_one_para`, `hard_wrap_para_then_rest` |
| A heading continues on the following lines, with or without a repeated `#` marker, until a blank line. | Rewrapping a long heading keeps it one heading. | proved: `heading_text_wrap_then_rest`, `heading_marker_wrap_then_rest` |

### Well-formedness and roundtrip

| Property | Implication | Status |
| --- | --- | --- |
| Every input parses to a well-formed tree. | There are no syntax errors, and consumers never see a malformed tree. | proved: `wf_parse`, `wf_parse_doc` |
| Rendering a document to djot and parsing it back gives the same document, for every document the renderer can write. | djot-to-djot conversion loses nothing. | proved: `roundtrip_blocks`, `roundtrip_doc` |
| Formatting any input (parse, render, parse again) gives the same document as parsing it. | A formatter never changes a document's meaning. | planned. Not true yet: the renderer always fences code with three backticks, which breaks a code block containing a line of three backticks (`normalization_code_fence_counterexample`) |

### HTML output

| Property | Implication | Status |
| --- | --- | --- |
| Without raw HTML in the source, every `<` in the output belongs to a tag. | Document text cannot inject HTML. | proved: `serialize_lt_tags` |
| HTML output is well-nested. | | planned (long-term) |

## Properties of the Generalized Parser

Current supported extensions and parser configs are:
- Character and width of each inline delimiter (emphasis, strong, superscript, ...): breaks none
- Opt out of smart typography, raw inline, math, inline attributes, tables, fenced divs, task lists, raw blocks, definition lists, block attributes, footnotes, heading continuation: breaks none
- List interruption (a list marker can end a paragraph): breaks safe rewrapping
- Setext (underlined) headings: breaks safe rewrapping
- Wikilinks (Obsidian-style `[[target\|alias]]`): breaks none
- Keyed blocks (`label: content`, pairing an inline label with a block): breaks safe rewrapping; also changes the tree structure of existing documents
- ... more to come

Some additional properties for the generalized parser:
- Changing one inline delimiter's character is valid when the new character differs from every other delimiter's. ==> Only the changed delimiter needs checking.
- Respelling a delimiter (strong as `+` instead of `*`, say) parses every document to the same tree once the two characters are swapped in the source. ==> A profile can respell a delimiter without changing what documents mean.
- [ ] Turning a construct off does not change the parse of a document that never uses it.

## Conformance

The parser is compared with [djot.js](https://github.com/jgm/djot.js): it matches the expected HTML on all 287 cases of djot.js's test suite at (8a529fe00b52adf0ba14708195c42e0b6712520f).

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
