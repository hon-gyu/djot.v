# djot.v

djot.v is a verified and generalized [djot](https://djot.net) implementation in Rocq, with an optimized extraction to OCaml.

> [!NOTE]
> The [site](https://hon-gyu.github.io/djot.v/) has a playground, the reference for the extensions, and the OCaml API.

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

This section lists what is proved of the djot profile. The site's [playground](https://hon-gyu.github.io/djot.v/playground/) shows the same for any profile.

The theorems are checked by Rocq, with no axioms and no admitted proofs.

> ai-disclosure: this section is ai-generated

<!-- properties: generated from theories/Properties.v -->

### No backtracking

| Property | Implication | Status |
| --- | --- | --- |
| A later line never changes a block already parsed. | Blocks can be emitted as lines arrive. | proved: `prefix_determinism`, `no_future_line_dependence` |
| Each byte of a paragraph is read once. | An unclosed * or [ never forces a rescan. | proved: `iscan_str_no_reread` |
| After an edit, reparsing can stop once the parser is back in the state it had before the edit. | An editor reparses the changed region and reuses the rest. | proved: `prefix_state_suffices`, `reparse_only_new` |
| Replacing one block leaves the parse of every other block unchanged. | An edit's effect stays within the block it touches. | proved: `block_replace`, `replace_at_id_parse` |
| Recording source positions does not change the parse. | A tool that needs positions gets the same tree as everyone else. | proved: `parse_blocks_located_erase`, `parse_doc_located_erase` |
| Parsing takes linear time. | Reading each byte once does not give this: one byte can do work proportional to the number of open delimiters. | conjectured |

### Container uniformity

| Property | Implication | Status |
| --- | --- | --- |
| Text inside a block quote parses as it would at top level. | Moving text into or out of a quote does not change its meaning. | proved: `quote_uniformity`, `quote_uniform_sound` |
| Text inside an item of a bullet or ordered list parses as it would at top level, when indented the way the formatter writes it. | Moving text into or out of a list item does not change its meaning. | proved: `list_uniformity`, `ordered_uniformity` |
| The same, for the items of a definition list. | Moving text into or out of a definition does not change its meaning. | proved: `definition_list_uniformity` |
| Text inside a fenced div parses as it would at top level, unless it contains the div's own closing fence. | Moving text into or out of a div does not change its meaning. | proved: `div_uniformity`, `div_uniformity_tail` |
| Lines indented under a footnote belong to it, cannot affect anything outside it, and parse as they would at top level. | Moving text into a footnote does not change its meaning. | conditional: `footnote_content_uniformity`, `footnote_text_uniformity`, `footnote_list_shift_counterexample`. Not when the footnote's first line starts a list: the indentation of the following items is measured from the footnote marker. |
| A text line that continues a paragraph may leave out the prefixes of the quotes, list items and footnotes around it, and parses as it would with them written. | Leaving out a prefix on such a line does not change the document. | proved: `lazy_stack_line`, `step_lazy`, `lazy_line_restore`, `lazy_uniform_sound` |
| A list is loose exactly where a blank line separates two of its items, or two blocks inside one item. | Whether a list renders with space between its items follows from where its blank lines are. | conditional: `list_spacing_separates`, `separates_loosens`, `separates_after_loosens`. For items in which no block attribute spans several lines. A blank line inside a code block does not count. |
| Indenting every line of a document by the same amount does not change its parse. | A document pasted at some indentation means the same thing. | proved: `indent_uniformity` |

### Local interpretation

| Property | Implication | Status |
| --- | --- | --- |
| Whether [foo][bar] is a link does not depend on whether bar is defined. | Inline syntax can be read from the paragraph alone. | proved: `classify_inlines_locality` |
| Adding, removing or changing a reference definition changes only link and image attributes in the HTML. | Resolving references never restructures the document. | proved: `render_blocks_reference_shape` |

### Safe hard-wrapping

| Property | Implication | Status |
| --- | --- | --- |
| A line inside a paragraph never starts a new block. | Hard-wrapping a paragraph cannot create a list, heading or quote by accident. | proved: `hard_wrap_one_para`, `hard_wrap_para_then_rest`, `wrap_safe_iff`, `wrap_cut_list`, `wrap_cut_setext` |
| A heading continues on the following lines until a blank line. | Hard-wrapping a long heading keeps it one heading. | proved: `heading_text_wrap_then_rest`, `heading_marker_wrap_then_rest` |

### Block structure first

| Property | Implication | Status |
| --- | --- | --- |
| Which blocks a document has, and how they nest, is decided without reading inline syntax. | A tool can find the blocks of a document without an inline parser, and a bug in inline parsing cannot move a block boundary. | conditional: `block_shape_independent`. Except a table caption, which disappears when its inline content is empty. |

### Inline precedence

| Property | Implication | Status |
| --- | --- | --- |
| When delimiters overlap, the first opener that gets closed wins, and a closer takes the closest open opener. Exactly one reading follows these rules, and the parser gives it. | Overlapping delimiters have one meaning, which can be worked out by hand. | conditional: `para_inlines_valid`, `valid_unique`. For emphasis-like delimiters, links and plain text. Smart quotes, spans and images are not covered. |

<!-- /properties -->

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
