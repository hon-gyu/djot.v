---
ai-disclosure: autonomous
---

# Pandoc and PyMarkdown extensions against the configuration family

The question: can the current configuration family (`dconfig`/`dtable`
for inlines, `bconfig` for blocks, composed by `Profile`) express the
syntax extensions of pandoc's Markdown and of PyMarkdown, and where it
cannot, what generalization would let it while keeping the theorems.

The catalog is kept current in place: when a verdict changes, its row is
edited. The generalization plan at the end is dated, because it reads the
tree at one commit.

Sources: pandoc `MANUAL.txt` at `jgm/pandoc` main, fetched 2026-09-10,
every `### Extension:` heading that changes Markdown input; PyMarkdown's
extension page (pymarkdown.readthedocs.io, stable). Python-Markdown is a
different project with a similar name; its list is at the end in case it
was the one meant.

## Short answer

Of 71 pandoc syntax extensions, 26 are already expressible (most are
djot features pandoc also has, and a few are a new value of an existing
setting), 16 need an existing setting's type widened, 21 are new
constructs, and 8 are excluded by decisions already made (raw HTML,
indentation as code). PyMarkdown's 7 are 4, 1, 2, and 0 of the same.

The family is a menu of switches over a fixed set of constructs plus a
respellable delimiter table. It is good at "turn off" and "respell". It
cannot add a construct by configuration: every block construct is a
`pstate` constructor, a `cblock` constructor and a case in the standing
theorems, and every inline container is a `dstyle` constructor wired to
one AST constructor by `dnode`.

## Pandoc, extension by extension

Columns: **have** = expressible now (djot already does it, or a value of
an existing setting); **widen** = an existing setting's type has to grow;
**new** = a new construct or scanner mode; **out** = excluded by a
recorded decision. Writer-side and non-Markdown extensions
(`literate_haskell`, `native_numbering`, `xrefs_*`, `styles`, `amuse`,
`gutenberg`, `sourcepos`, `rebase_relative_paths`, the org/docx/typst
variants) are left out of the count.

### Blocks

| extension | verdict | notes |
| --- | --- | --- |
| `blank_before_header` | have | djot's default: nothing interrupts a paragraph. Turning it *off* is widen (see the generalization plan) |
| `blank_before_blockquote` | have | same; `from-markdown.md` already notes quotes were never given the list-marker treatment |
| `space_in_atx_header` | have | `KHeading` requires the space. Turning it off is a classifier change |
| `lists_without_preceding_blankline` | have | `sublist_bconfig`. Pandoc's "ordered sublists must start with 1" is the same line as `prose_safe_markers` |
| setext headings (base pandoc) | have | `setext_bconfig`; input-only, renders ATX |
| `fenced_code_blocks`, `backtick_code_blocks` | have | |
| `fancy_lists` | have, mostly | letters, roman, `.`/`)`/`(x)` exist. `#.` as a marker and the two-space rule after a capital letter are classifier changes |
| `startnum`, `task_lists`, `footnotes` | have | |
| `fenced_divs` | have | djot's `::: class`. Pandoc's `::: {#id .c} :::` opener spelling is an opener-recognizer change. With custom tag names on (`custom-tags.md`) the word is the div's name, not a class |
| `header_attributes` | widen | trailing `{#id}` on the heading line. Djot drops an attribute after a space, so this is non-conservative. A rule at heading finish; input-only, since the renderer writes attributes on the preceding line and escapes `{` in heading text |
| `mmd_header_identifiers` | widen | same place, `[id]` spelling |
| `fenced_code_attributes` | widen | `{.lang #id}` after the fence; the attribute parser exists, the info-string reader does not call it |
| `pipe_tables` | widen | djot rows need both outer pipes. GFM/pandoc rows without them are a paragraph until the delimiter row arrives, which is the setext shape (open paragraph + one line decides) |
| `table_captions`, `table_attributes` | widen | djot has `^ caption` after the table. `Table: x` / `: x` after the table is a respelling. Before the table it is a pending block that falls back to a paragraph, the `PAttr` shape |
| `alerts` | widen | `> [!TIP]` becomes a `Div` with a class at quote finish. Roundtrips through `::: tip` while divs are on; needs its own spelling when they are off |
| `definition_lists` | new | pandoc's term is a plain paragraph followed by `: def`. The tight form is setext-shaped. The form with a blank line between term and definition needs a *closed* paragraph to stay revisable across the blank (see the conflicts in the generalization plan) |
| `line_blocks` | new | a leading `\|` and a space, lines of inlines. Collides with a djot table row that ends in `\|`; needs a disjointness rule like the lone dash |
| `example_lists` | new | `(@)` markers, numbered across the document; `(@label)` references resolve at document level |
| `simple_tables`, `multiline_tables` | new | column positions from a dashed line. Simple tables with a header are setext-shaped; multiline tables span blank lines |
| `grid_tables` | new | cells contain blocks, known only when a row's lower border arrives: buffered lines parsed per cell. A container that is not a descent |
| `pandoc_title_block`, `yaml_metadata_block`, `mmd_title_block` | new | document-start metadata. Cheapest as a split in `parse_doc` before `parse_lines`, identity when absent. `---` at line 1 is a thematic break in djot, so off in djot's profile |
| `abbreviations` | new | pandoc parses and discards them; discarding is not injective, so the canonical view would have to exclude them |

### Inlines

| extension | verdict | notes |
| --- | --- | --- |
| `smart`, `escaped_line_breaks`, `all_symbols_escapable`, `angle_brackets_escapable` | have | |
| `inline_code_attributes`, `link_attributes`, `bracketed_spans`, `raw_attribute`, `attributes` | have | djot's attribute model is the general one pandoc's `attributes` imitates |
| `superscript`, `subscript` | have | pandoc forbids unescaped spaces inside; djot allows them. The restriction is a content rule, not expressible now |
| `strikeout` | have | `~~`, width 2 (probe, in the generalization plan). Not jointly with `~` subscript |
| `mark` | have | `==`, width 2, bare (probe, in the generalization plan) |
| `emoji` | have in djot | `:smile:` is core Djot symbol syntax, now parsed as `Ast.Symbol`. djot.js renders it as source; emoji substitution requires a filter |
| `auto_identifiers` | have | the document pass |
| `ascii_identifiers`, `gfm_auto_identifiers` | widen | the id function becomes a parameter of the document pass |
| `intraword_underscores` | widen | a neighbour test on the bare spelling; free for roundtrip (braced canonical form) |
| `old_dashes` | widen | a second smart-typography rule set |
| `hard_line_breaks`, `ignore_line_breaks`, `east_asian_line_breaks` | widen | what a source newline in a paragraph becomes: soft, hard, or nothing (the last conditional on the neighbouring bytes being wide characters, a bounded UTF-8 lookup) |
| `tex_math_gfm` | widen | ``$`x`$`` is djot's ``$`x` `` plus one trailing `$`; ```` ```math ```` is an info-string mapping like `braw_blocks` |
| `inline_notes` | new | `^[...]`, a note body inline. Either a new node or desugared by the document pass into a reference and a definition |
| `citations` | new | `[@key, p. 3; @k2]` and `@key`. New node; the locator heuristics depend on CSL locale data |
| `shortcut_reference_links`, `implicit_header_references` | new | whether `[foo]` is a link depends on definitions that may come later. Parse is fine (djot keeps `[foo]` as bracketed text); the decision moves to the document pass, which then has to be undoable |
| `spaced_reference_links` | new | `[foo] [bar]`: after `]`, a run of spaces is held until the next byte decides. Bounded, but a new scanner state |
| `implicit_figures` | new | a lone image in a paragraph becomes a figure. A normalizing pass, and `Para [Image]` then needs a spelling that is not a figure |
| `tex_math_dollars` | new | `$x$` with flanking and "closing `$` not followed by a digit". The content is verbatim and the opener can fail after it, so a single pass has to carry both readings (product state, per `no-backtracking.md`) |
| `tex_math_single_backslash`, `tex_math_double_backslash` | new | same shape, and `\(` stops being an escape of `(` |
| `autolink_bare_uris` | new | recognizing a URL without `<>`; GFM's trailing-punctuation rule needs the whole word first |
| `short_subsuperscripts` | new | `x^2`, a prefix operator over an alphanumeric run |
| `mmd_link_attributes` | new | key/value tail on a reference definition |
| `wikilinks_title_after_pipe` | have | `dc_wikilinks`, specified in `wikilinks.md` |
| `wikilinks_title_before_pipe` | widen | the same construct with the split read the other way round |

### Out

`raw_html`, `markdown_in_html_blocks`, `native_divs`, `native_spans`,
`markdown_attribute` (HTML in the source, `beyond-djot.md`), `raw_tex`
and `latex_macros` (same argument as HTML), `four_space_rule` and
indented code (indentation means nesting). Pandoc's base emphasis (`*`
and `_` both, `**`/`__`, delimiter runs and flanking) is also out under
the E1 decision in `extension-decisions.md`; see the character-width
widening below for what reopening it would involve.

## PyMarkdown

| identifier | verdict | notes |
| --- | --- | --- |
| `markdown-task-list-items` | have | `btasks` |
| `markdown-strikethrough` | have | `~~` as above. GFM also accepts a single `~`, which is one row at two widths (see the character-width widening) |
| `markdown-disallow-raw-html` | have | vacuous: there is no raw HTML to disallow |
| `linter-pragmas` | have, vacuously | HTML comments that steer the linter, not syntax |
| `markdown-tables` | widen | GFM pipe tables, as `pipe_tables` above |
| `front-matter` | new | as the metadata blocks above |
| `markdown-extended-autolinks` | new | as `autolink_bare_uris` |

## Composition caveat

Individually expressible is not jointly expressible. The `~` case from
the probe in the generalization plan is one example; `line_blocks`
against djot tables and pandoc's `: definition` against djot's `: term`
are others. A profile is checked
as a whole (`dconfig_ok`, `block_prefix_ok`); per-extension "have"
verdicts above assume the extension's characters are otherwise free.

## Python-Markdown, briefly

If "pymarkdown" meant Python-Markdown: `attr_list`, `fenced_code`,
`footnotes`, `smarty`, `sane_lists`, `tables` (partially) and `toc`
(ids) map as above; `nl2br` is the newline policy; `def_list` is
pandoc's definition list; `wikilinks` is `dc_wikilinks`; `abbr`, `meta`
(front matter) and `admonition` (`!!! note` with an indented body, a
prefixed-container instance) are new; `md_in_html`, `legacy_attrs` and `legacy_em` are out;
`codehilite` is renderer-side.

## Generalization plan (2026-09-10, `c2ac8f4`)

Everything in this section is read off the tree at the commit above
and will drift as the configuration family grows. The catalog above
is kept current in place; this section is not.

### Why widening is cheaper than it looks

1. The theorems carry no hypothesis on block settings. `roundtrip_blocks`,
   `wf_parse`, `list_uniformity` and `block_incremental_holds` sit in
   `Section`s over `{T : dtable} {K : bconfig}` with nothing assumed of
   `K`. Only the inline table carries an admissibility proof
   (`dconfig_ok`, decidable). So a user configuration, once it passes a
   decidable check, inherits every headline theorem with no proof work.
2. The canonical renderer spells every delimiter in its braced form
   (`marked_open k = "{" ++ dtoken k`). Any rule that constrains only the
   *bare* spelling (neighbour tests, intraword rules) is invisible to the
   roundtrip. That is why `DBareAfterBreak` cost little, and it is what
   makes the neighbour-test widening below cheap.

### Probe

`PandocProbe.v` (scratchpad, not kept) built two tables.

| table | `dconfig_ok` |
| --- | --- |
| markdown's `**`/`_`, plus `==` for highlight (width 2, bare), `~~` for delete (width 2, bare), subscript off | `true` |
| the same, but subscript kept on `~` | `false` |

Under the first, `a ==b== ~~c~~ **d** _e_` parses to highlight, delete,
strong, emphasis, and `H~2~O` is literal. The canonical spelling of the
highlight is `{==b==}`, which parses back to the same node. So pandoc's
`mark` and `strikeout` are configuration today, but not together with
pandoc's `subscript`, because `~` would have to belong to two rows at two
widths.

### Where the family stops

Four limits account for every "widen" and most "new" entries.

1. **A row is one character at one width, and a row is an AST
   constructor.** `dc_char : dstyle -> ascii` is a function, so two
   spellings of one container (`*` and `_` both emphasis) cannot be
   written; `dconfig_distinct` keys rows by character, so one character
   at two widths (`~` and `~~`) is rejected; and `dstyle` is a closed
   enum mapped by `dnode`, so a user cannot add an underline row.
2. **Only list markers interrupt a paragraph.** `binterrupt` matches
   `KList` and answers `false` for every other kind by construction.
3. **The classifier is fixed.** `Line.classify` is profile-independent
   by design. New line shapes arrive as queries beside it
   (`underline_of`) and each needs its own conflict rule (the lone-dash
   check in `block_prefix_ok`).
4. **Inline constructs whose opener can fail after verbatim content.**
   Delimiter rows are safe because their content is inline-parsed
   either way and a failed opener decays to text. `$x$`, `\(x\)` and
   bare URLs are not: the content is read differently depending on
   whether a closer arrives.

### The widenings, cheapest first

Each keeps djot as the instance whose new fields reproduce today's
behaviour definitionally, which is what `beyond-djot.md` requires and
what keeps every existing `Example` unchanged.

#### Paragraph interruption by any line kind

`bmarker_interrupts` becomes a question about any `line_kind`, not only
`KList`. Unlocks `blank_before_header` and `blank_before_blockquote`
off, and CommonMark's rule that a fence or thematic break interrupts.

Why the theorems survive: E2 already established that a rule stated over
the open paragraph, without reference to the container, leaves
`list_uniformity` true. `bcuts` is the one query both `step`'s paragraph
branch and `para_ok` ask, so the change concentrates there. The canonical
side needs continuation lines that could interrupt to be escaped; `-`
already is (the hyphen is always escaped), `#` and `>` are not, so this
adds a line-initial escape.

Probe first: whether lazy continuation (`is_lazy`, `feed_lazy`) consults
the interrupt test before or after deciding laziness, for `> a` / `# b`.

#### Neighbour tests on bare delimiters

`dsyntax`'s bare variants take a test on the previous and next byte
(either a closed set of named tests or a function with no laws). Unlocks
`intraword_underscores` and GFM's word rules for `~`, and generalizes
`DBareAfterBreak` rather than adding a sibling.

Why it is cheap: the canonical view uses the braced form, so no
canonical obligation changes. The braced form survives every dialect,
since `DBare` means "braces optional" and turning attributes off does not
turn off braced rows. The cost is in the scanner's productivity and
well-formedness lemmas where `DBareAfterBreak` is already case-split.

#### Document-pass parameters

The id function becomes a parameter of the document pass
(`ascii_identifiers`, `gfm_auto_identifiers`). `pass_erase` holds for
pristine input, where the pass only adds ids, so how an id is computed
should not enter the proof. Check that `undo_pass` never compares an id
against the generated one before relying on that.

The same place hosts rewrites that happen once a block is known:
alerts (quote to div), `inline_notes` desugaring, and later
`implicit_figures`. Each is a normalizing pass, so
[[project-engineering-lessons#Probe the equations a new pass must
preserve, not only the invariant it establishes]] applies: list the
lemmas whose conclusion is an equation about the rewritten construct,
and make the pass the identity on the canonical fragment where possible.

#### Newline policy

What a newline inside a paragraph becomes: `SoftBreak`, `HardBreak`, or
nothing. Unlocks the three line-break extensions and Python-Markdown's
`nl2br`. The canonical view excludes `SoftBreak` at settings that
cannot spell it. Cost is in the line-by-line decomposition
(`ibreak_closed`, `iscan_closed`), which already had to be kept in
agreement with the whole-paragraph reading once.

#### Delimiter entries instead of delimiter rows

Two separate steps, and only the first is a widening.

**Entries mapped to spans.** The table gains user entries whose meaning
is a `Span` with a class instead of one of the nine constructors, so
`++x++` or `!!x!!` can mean `[x]{.underline}`. The canonical view does
not need a new constructor: the node is an ordinary `Span`, which already
has a spelling while inline attributes are on, so the entry is input
sugar like setext. `dstyles` and `dstyle_eq` become table-dependent. The
census is encouraging: `dstyle` is mentioned 115 times in `Inline.v` but
case-split in about 12 proofs there and 6 in `Wf.v`, and `dnode` is the
single place a style becomes a node.

**One character at several widths.** Keying rows by `(character, width)`
lets `~` be subscript and `~~` delete, and `*` emphasis and `**` strong.
This reopens E1, which settled that a character has one width precisely
to keep run arithmetic out. With djot's stacking rule (only the top
opener can close) a cheap deterministic rule exists: a closing run closes
the top opener at that opener's width and continues with the rest.
`***a***` would read as strong around emphasis, where CommonMark reads
emphasis around strong. It is a decision to make, not a knob to add; the
scanner's token-counting states (`IDelim`) would have to consult the
stack before a token's width is known.

#### Block construct schemas

This is the change that would make most of the "new" block entries into
configuration. Today each block construct pays separately for the
standing theorems (`step_fuel_shift`, `step_fuel_pad`,
`step_blank_finish`, `finish_wf`, `finish_supported` over states;
`render_cb_lines`, `cb_ok_lines_ok`, `cb_lines_first_line_ok`,
`nonlist_cblock_first`, `cb_ast_pristine` over cblocks). Keyed blocks are
the most recent measure of that cost.

A schema is a generic construct with a decidable side condition, proved
once, the way `dtable` is for delimiters:

| schema | existing instances | would host |
| --- | --- | --- |
| verbatim fence: opener recognizer, closer test, verbatim lines, AST from payload | code, raw blocks | `$$` display math, ```` ```math ````, front matter (plus a first-line flag), mmd/pandoc title blocks |
| prefixed container: strip a line prefix and descend | block quote | alerts, admonition-like constructs |
| prefixed leaf: strip a prefix, lines become inlines | none | `line_blocks` |
| fenced container | div | pandoc's attribute-opener divs |
| pending block with paragraph fallback | block attributes (`PAttr`/`PParaOff`) | caption before a table, `Table:` captions |

The side condition is where conflict-freeness goes: an instance's opener
must not claim a line another enabled recognizer claims, generalizing the
single lone-dash check in `block_prefix_ok` to a check over all
recognizers in force. And
[[project-engineering-lessons#Probe the definitions a theorem already
constrains, too]] says what a schema's state must obey: any column it
records is absolute.

This is a large refactor of `Step.v` and `Render.v` and it has not been
probed. The smallest informative probe is the verbatim fence schema with
two instances (code fence and front matter) and `step_fuel_shift` stated
for the schema.

#### Scanner modes that carry two readings

`tex_math_dollars`, the backslash math delimiters, bare URLs and spaced
reference links each need a scanner state that carries the reading
"this opener will close" alongside the reading "it will not" until the
next byte settles it. `no-backtracking.md` allows this. Each is its own
piece of scanner work rather than an instance of something shared, so
these stay out of the knob story. `tex_math_gfm` covers the same need
with djot's existing verbatim machinery.

### Conflicts with the properties

Two pandoc behaviours cannot be had without giving something up.

- A definition whose term is separated from it by a blank line, and in
  general any rule where a line changes the type of a paragraph a blank
  line already closed. Setext and pipe-table headers delay one line
  while the paragraph is still open, which `step` handles today. Here
  the delay crosses the blank, so the blank must no longer finish the
  paragraph: `step_blank_finish` changes, and every paragraph stays
  revisable until the next nonblank line. The tight form
  (`Term` / `: def`) has no such cost.
- Pandoc's "footnotes may not appear inside other blocks" and the
  four-space rule for example-list continuations are container-sensitive
  rules. Stated as pandoc states them, they falsify the uniformity
  theorems. E2's approach (restate the rule without reference to the
  container) has to be tried for each.

### Suggested order

1. Interrupts over any line kind, and neighbour tests on bare
   delimiters. Both small, both keep the canonical view nearly still,
   and together they cover most of what a pandoc or CommonMark user
   notices first.
2. Document-pass parameters (ids first), then the newline policy.
3. Entries mapped to spans, after a census of the proofs that split on
   `dstyle`.
4. Probe the verbatim fence schema. If `step_fuel_shift` goes through
   for the schema, front matter and display math become instances, and
   the other schemas follow the same pattern.
5. Decide separately whether to reopen E1 (one character at several
   widths). It is the only route to pandoc's own emphasis and to `~`
   with `~~`.
