# djot.v

djot.v is a verified and generalized [djot](https://djot.net) implementation in Rocq, with an optimized extraction to OCaml.

It is **verified** in the sense that the goals behind djot's design[^design-rationale] are stated as theorems about the parser and proved. The main ones:

- No backtracking[^no-backtracking]: 
    - blocks are parsed line by line, and a later line never changes an earlier block. 
    - Inline text is scanned once, byte by byte. 
    - This makes streaming and incremental parsing possible: after an edit, a parser can resume from a saved state instead of starting over.
    - $\mathrm{parse}(L \mathbin{+\!\!+} R) = \mathrm{done}(L) \mathbin{+\!\!+} \mathrm{parse}_{\mathrm{state}(L)}(R)$

- Container uniformity[^container-uniformity]: 
    - if a chunk of text has a certain meaning, it will continue to have the same meaning when put into a container block (such as a list item or blockquote).
    - Blockquote: $\mathrm{parse}(\mathtt{>}\,L) = \mathrm{Quote}(\mathrm{parse}(L))$
    - List: $\mathrm{parse}(\mathtt{-}\,L_1, \dots, \mathtt{-}\,L_n) = \mathrm{List}(\mathrm{parse}(L_1), \dots, \mathrm{parse}(L_n))$

- Local interpretation[^local-interpretation]: 
    - parsing of inline elements is local
    - whether `[foo][bar]` is a link does not depend on whether `bar` is defined elsewhere in the document
    - $\mathrm{parse}([foo][bar]) = \mathrm{parse}([foo][bar'])$

- Safe hard-wrapping[^safe-hard-wrapping]: 
    - Block-level elements can't interrupt paragraphs (or headings)
    - hard-wrapping a paragraph should not lead to different interpretations.
    - $\mathrm{parse}(l_1, \dots, l_n) = \mathrm{Para}(l_1, \dots, l_n)$ when $l_1$ is text and no $l_i$ is blank

It is **generalized** in the sense that djot is one setting of a configurable parser family. 
- Extensions and dialects are developed in a safe way.
    - The theorems are proved for a given setting, or it's stated which setting breaks them. So each setting comes with an answer to which of the properties above it keeps. In such framing, 
- Possibility of Markdown-like syntax that still keeps most of djot's guarantees.
    - we have a Markdown-like profile that writes strong emphasis as `**` rather than `*`, allows sublists without a blank line, and allows setext (underlined) headings. 
    - The proofs show that it keeps no backtracking and uniformity, and that sublists without a blank line and setext headings are what cost it safe hard-wrapping. 

> ai-disclosure: most of the Rocq proofs were done by a Gen-AI tool. "ai-disclosure" tags are attached in this repository wherever possible.

[^design-rationale]: See [djot's rationale](https://github.com/jgm/djot#rationale) and [Beyond Markdown](https://johnmacfarlane.net/beyond-markdown.html) for the main reference of djot's design.
[^no-backtracking]: Goal 1 of [djot's rationale](https://github.com/jgm/djot#rationale)
[^local-interpretation]: Goal 2 of [djot's rationale](https://github.com/jgm/djot#rationale)
[^container-uniformity]: <https://spec.commonmark.org/0.31.2/#principle-of-uniformity>
[^safe-hard-wrapping]: Goal 7 of [djot's rationale](https://github.com/jgm/djot#rationale)

## Djot Properties

This section lists everything proved, what each proof assumes, and what is still to be done.

The theorems are checked by Rocq, with no axioms and no admitted proofs.

> ai-disclosure: this section is ai-generated

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
| A text line that continues an open paragraph may leave out the prefixes of the block quotes, list items and footnotes around it, and it parses as it would with them written out. Where setext headings are on, a line that underlines the paragraph is the exception. | Leaving out a prefix on such a line does not change what the document means. Together with the uniformity rows, this gives the meaning of a document with lazy lines: `> a` then `b` is a quote holding the paragraph `a b`, and likewise for a list item and a footnote. | proved: `lazy_stack_line` (the three containers, as the syntax reference lists them), `step_lazy`, `step_lazy_spelling` (any indentation the containers accept), `lazy_line_restore`; per container: `quote_lazy_line`, `list_lazy_line`, `footnote_lazy_line` |
| A list is loose only where a blank line separates two of its items, or two blocks inside one item. A blank line directly before a nested list, or right after one ends, does not count, and neither does a blank line inside a nested block such as a div, a footnote, or a table before its caption. | Whether a list renders with space between its items follows from where its blank lines are, as the syntax reference states it. | proved in one direction: `list_spacing_separates` (a list the parser calls loose has such a blank line); the converse is planned |
| Indenting every line of a document by the same amount does not change its parse, as long as no block attribute `{...}` spans several lines. | Indentation matters only relative to a list marker or footnote, as the syntax reference says: a document pasted at some indentation means the same thing. | proved: `indent_uniformity` |

### Local interpretation

| Property | Implication | Status |
| --- | --- | --- |
| Whether `[foo][bar]` is a link does not depend on whether `bar` is defined. | Inline syntax can be read from the paragraph alone, without the rest of the document. | proved, and true by construction, since link recognition never sees the definitions: `classify_inlines_locality` |
| Adding, removing or changing a reference definition changes only link and image attributes in the HTML, such as the URL, never its structure or text. | Resolving references never restructures the document. | proved: `render_inline_reference_shape`, `render_inlines_reference_shape`, `html_tree_reference_shape`, `render_document_foot_reference_shape`, `render_blocks_reference_shape` |

### Safe hard-wrapping

| Property | Implication | Status |
| --- | --- | --- |
| A line inside a paragraph never starts a new block, even if it begins with `- `, `# `, `> `, `1. ` or `***`. | Hard-wrapping a paragraph cannot accidentally create a list, heading or quote. It can still change inline content when a line break moves into verbatim, after a backslash (where it becomes a hard line break), or past trailing spaces (`wrap_moves_*`). | proved: `hard_wrap_one_para`, `hard_wrap_para_then_rest` |
| A heading continues on the following lines, with or without a repeated `#` marker, until a blank line. | Hard-wrapping a long heading keeps it one heading. | proved: `heading_text_wrap_then_rest`, `heading_marker_wrap_then_rest` |

### Block structure first

| Property | Implication | Status |
| --- | --- | --- |
| Which blocks a document has, and how they nest, is decided without reading inline syntax: the same blocks come out however emphasis, links and other inline constructs parse. The one exception is a table caption, which disappears when its inline content comes out empty. | A tool can find the blocks of a document, such as for folding or an outline, without an inline parser, and a bug in inline parsing cannot move a block boundary. | proved: `block_shape_independent` |

### Inline precedence

| Property | Implication | Status |
| --- | --- | --- |
| When emphasis delimiters overlap, the first opener that gets closed wins, and a closer takes the closest open opener: `_a *b_ c*` is emphasis around `a *b`, with the `*`s as text. There is exactly one reading that follows these rules, and the parser gives it. | Overlapping delimiters have one meaning, the one the syntax reference gives, and it can be worked out by hand. | proved for a paragraph of `_`, `*`, `^`, `~` (bare or in braces), `{= =}`, `{+ +}`, links `[..](..)` and `[..][..]`, and plain text: `para_inlines_valid`, `valid_unique`; smart quotes, spans and images are not covered |

### Roundtrip

| Property | Implication | Status |
| --- | --- | --- |
| Rendering a document to djot and parsing it back gives the same document. | djot-to-djot conversion loses nothing. | planned (long-term); a restricted version is proved in `theories/Roundtrip.v` |

## Properties of the Generalized Parser

Current supported extensions and parser configs are:
- Character and width of each inline delimiter (emphasis, strong, superscript, ...): breaks none
- Opt out of smart typography, raw inline, math, inline attributes, tables, fenced divs, task lists, raw blocks, definition lists, block attributes, footnotes, heading continuation: breaks none
- List interruption (a list marker can end a paragraph): breaks safe hard-wrapping (`hard_wrap_cut_not_one_para`)
- Setext (underlined) headings: breaks safe hard-wrapping (`hard_wrap_cut_not_one_para`)
- Wikilinks (Obsidian-style `[[target\|alias]]`): breaks none
- Dollar math (`$x$`, `$$x$$` and GitHub's ``$`x`$``): breaks none
- Keyed blocks (`label: content`, pairing an inline label with a block): breaks safe hard-wrapping; also changes the tree structure of existing documents
- Callouts (`> [!kind]` on a quote opener): breaks block quote container uniformity for matching headers; also changes the tree structure of those quotes
- Custom tag names (`::: details` names a div, `:kbd[Ctrl+C]` names a span): breaks none; changes how existing documents with `::: word` or `:word[` parse
- ... more to come

Some additional properties for the generalized parser:
- Changing one inline delimiter's character is valid when the new character differs from every other delimiter's. ==> Only the changed delimiter needs checking.
- Respelling a delimiter (strong as `+` instead of `*`, say) parses every document to the same tree once the two characters are swapped in the source. ==> A profile can respell a delimiter without changing what documents mean.
- Changing the inline delimiters, or turning inline constructs on or off, never changes block structure: the same blocks, nested the same way, with the same list items and table cells. The one exception is a table caption, which disappears when its inline content comes out empty. Keyed blocks must be off. ==> Blocks can be found before inline syntax is read, as the syntax reference requires.
- [ ] Turning a construct off does not change the parse of a document that never uses it.

## Conformance

The parser is compared with [djot.js](https://github.com/jgm/djot.js): it matches the expected HTML on all 287 HTML cases of djot.js's test suite (8a529fe00b52adf0ba14708195c42e0b6712520f).

To run the comparison, build djot.js once with `make build-djotjs`, then
`make diff`. 

## Extracted Programs

The OCaml extraction is packaged in [`ocaml/`](ocaml) as the `djot` library, which builds without Rocq. It parses a document, lets you walk or rewrite the tree, and renders it to HTML or back to djot. Its API is modeled on [cmarkit](https://github.com/dbuenzli/cmarkit)'s; see [ocaml/README.md](ocaml/README.md).

The extraction itself is trusted, not proved: the theorems are about the Rocq definitions, and the OCaml is what Rocq's extraction produces from them.

On ordinary documents the library is about 2x slower than `djot.js` and about 3x slower than `cmarkit` (measured on `djot.js`'s `bench/readme.dj`; `cmarkit` parses it as CommonMark). Parse time is linear in document size. A few unusual inputs are still superlinear, such as very deep nesting on one line or thousands of reference definitions.

A Haskell extraction exists in [extraction/haskell](extraction/haskell). It has none of the OCaml extraction's performance work and is not packaged. With strings as Haskell `String` it is about 7x slower than [djoths](https://github.com/jgm/djoths) on large documents; with `ByteString`, about 3x, but quadratic on long lines. 

Rocq can also extract to Scheme, which is untested.

## Development Requirements

- opam switch with Rocq 9.x, dune ≥ 3.20

## References

- [djot](https://github.com/jgm/djot)
- [djot.js](https://github.com/jgm/djot.js)
- [djoths](https://github.com/jgm/djoths)
- [cmarkit](https://github.com/dbuenzli/cmarkit)

## License

MIT, see [LICENSE](LICENSE).

The module types of the `djot` package in `ocaml/` are modeled on cmarkit's, which is under the ISC license; its notice is in [ocaml/LICENSE-cmarkit](ocaml/LICENSE-cmarkit). The package is licensed MIT AND ISC.
