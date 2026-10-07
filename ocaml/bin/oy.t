  $ export DJOT_SYNTAX="markdown-like ext-wikilinks ext-callouts ext-callouts ext-tags"
  $ export NO_COLOR=1

  $ djot profile
  emph: _ bare
  strong: ** bare
  superscript: ^ bare
  subscript: ~ bare
  highlight: = braced
  insert: + braced
  delete: - braced
  single_quote: ' bare after a break
  double_quote: " bare
  footnotes: on
  smart_typography: on
  raw_inline: on
  math: on
  inline_attrs: on
  tables: on
  divs: on
  tasks: on
  raw_blocks: on
  deflists: on
  block_attrs: on
  heading_continuation: off
  ext_wikilinks: on
  ext_dollar_math: on
  ext_keyed: off
  ext_callouts: on
  ext_tags: on
  ext_setext_headings: on
  ext_list_interrupts: on

  $ cat > tt.md << 'END'
  > # Hi
  > 
  > *not-strong*
  > **strong**
  > _italic_
  > [[w]]
  > END

  $ djot ast tt.md
  doc
    section
      heading level=1 plain="Hi"
        str text="Hi"
      para
        str text="*not-strong*"
        soft_break
        strong
          str text="strong"
        soft_break
        emph
          str text="italic"
        soft_break
        ext_wikilink embed=false target="w"
