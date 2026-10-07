# ai-disclosure: ai-generated

The djot command, one test per option. Frontmatter is in cli_frontmatter.t,
which needs the yaml package.

  $ unset DJOT_SYNTAX
  $ export NO_COLOR=1

  $ cat > doc.dj <<'END'
  > # Hi
  > 
  > *strong* and [[w]]
  > END

Subcommands
===========

  $ djot html doc.dj
  <section id="Hi">
  <h1>Hi</h1>
  <p><strong>strong</strong> and [[w]]</p>
  </section>

  $ djot djot doc.dj
  # Hi
  
  *strong* and [[w]]

  $ djot djot doc.dj --style safe
  # Hi
  
  {*strong*} and \[\[w\]\]

  $ djot ast doc.dj
  doc
    section
      heading level=1 plain="Hi"
        str text="Hi"
      para
        strong
          str text="strong"
        str text=" and [[w]]"

  $ djot ast --locs doc.dj | grep strong
        strong (3:1:6-3:8:13)
          str (3:2:7-3:7:12) text="strong"

  $ echo x | djot json
  {
    "tag": "doc",
    "references": {},
    "autoReferences": {},
    "footnotes": {},
    "children": [
      {
        "tag": "para",
        "children": [
          {
            "tag": "str",
            "text": "x"
          }
        ]
      }
    ]
  }

  $ echo x | djot json --compact
  {"tag":"doc","references":{},"autoReferences":{},"footnotes":{},"children":[{"tag":"para","children":[{"tag":"str","text":"x"}]}]}

  $ echo x | djot json --compact --locs | grep -c '"pos"'
  1

The bare command prints the manual.

  $ djot --help=plain > help
  $ TERM=dumb djot | diff help -

Input
=====

  $ djot json doc.dj | djot html --from json
  <section id="Hi">
  <h1>Hi</h1>
  <p><strong>strong</strong> and [[w]]</p>
  </section>

  $ djot html - < doc.dj | head -1
  <section id="Hi">

  $ djot html doc.dj --time 2>&1 > /dev/null | sed 's/[0-9.]* ms/N ms/'
  parse: N ms
  render: N ms

Syntax options
==============

  $ djot html doc.dj --ext-wikilinks | grep '<p>'
  <p><strong>strong</strong> and <a href="w">w</a></p>

  $ echo 'a -- b' | djot html
  <p>a – b</p>

  $ echo 'a -- b' | djot html --no-smart-typography
  <p>a -- b</p>

  $ cat > md.dj <<'END'
  > Title
  > =====
  > 
  > **b**
  > END

  $ djot html md.dj
  <p>Title
  =====</p>
  <p><strong><strong>b</strong></strong></p>

  $ djot html md.dj --profile markdown-like
  <section id="Title">
  <h1>Title</h1>
  <p><strong>b</strong></p>
  </section>

An option naming a construct overrides the profile.

  $ djot html md.dj --profile markdown-like --no-ext-setext-headings
  <p>Title
  =====</p>
  <p><strong>b</strong></p>

The profile command prints the syntax the options select.

  $ djot profile > djot.profile
  $ cat djot.profile
  emph: _ bare
  strong: * bare
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
  heading_continuation: on
  ext_wikilinks: off
  ext_dollar_math: off
  ext_keyed: off
  ext_callouts: off
  ext_tags: off
  ext_setext_headings: off
  ext_list_interrupts: off

  $ djot profile --profile markdown-like --no-tables | diff djot.profile -
  2c2
  < strong: * bare
  ---
  > strong: ** bare
  15c15
  < tables: on
  ---
  > tables: off
  21c21
  < heading_continuation: on
  ---
  > heading_continuation: off
  23c23
  < ext_dollar_math: off
  ---
  > ext_dollar_math: on
  27,28c27,28
  < ext_setext_headings: off
  < ext_list_interrupts: off
  ---
  > ext_setext_headings: on
  > ext_list_interrupts: on
  [1]

An option naming a delimiter respells it: bare, braced only, or off.

  $ echo '**b** ==h== {==h==}' | djot html --strong '**' --highlight '=='
  <p><strong>b</strong> <mark>h</mark> <mark>h</mark></p>

  $ djot profile --superscript '{^}' --delete off | grep -e superscript -e delete
  superscript: ^ braced
  delete: off

  $ djot profile --strong _
  Usage: djot profile [--help] [OPTION]…
  djot: strong=_: '_' is already the emph delimiter
  [124]

  $ djot profile --strong ab 2>&1 | grep -c expected
  1

DJOT_SYNTAX gives the syntax the options start from.

  $ export DJOT_SYNTAX='markdown-like ext-wikilinks no-tables highlight==='
  $ djot profile | diff djot.profile -
  2c2
  < strong: * bare
  ---
  > strong: ** bare
  5c5
  < highlight: = braced
  ---
  > highlight: == bare
  15c15
  < tables: on
  ---
  > tables: off
  21,23c21,23
  < heading_continuation: on
  < ext_wikilinks: off
  < ext_dollar_math: off
  ---
  > heading_continuation: off
  > ext_wikilinks: on
  > ext_dollar_math: on
  27,28c27,28
  < ext_setext_headings: off
  < ext_list_interrupts: off
  ---
  > ext_setext_headings: on
  > ext_list_interrupts: on
  [1]

  $ echo '[[w]]' | djot html
  <p><a href="w">w</a></p>

An option overrides it, and --profile ignores it.

  $ djot profile --tables | grep -e tables -e wikilinks
  tables: on
  ext_wikilinks: on

  $ djot profile --profile djot | diff djot.profile -

  $ DJOT_SYNTAX='tables markdown-like' djot profile 2>&1 | grep -c 'DJOT_SYNTAX: markdown-like: expected'
  1

  $ DJOT_SYNTAX='strong=_' djot profile
  Usage: djot profile [--help] [OPTION]…
  djot: DJOT_SYNTAX: strong=_: '_' is already the emph delimiter
  [124]

  $ unset DJOT_SYNTAX

HTML page
=========

  $ djot html --doc doc.dj --css s.css
  <!DOCTYPE html>
  <html lang="en">
  <head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Doc</title>
  <link rel="stylesheet" href="s.css">
  </head>
  <body>
  <section id="Hi">
  <h1>Hi</h1>
  <p><strong>strong</strong> and [[w]]</p>
  </section>
  </body>
  </html>

  $ djot html -c doc.dj --title 'A & B' --lang fr | grep -e '<html' -e '<title'
  <html lang="fr">
  <title>A &amp; B</title>

  $ echo x | djot html -c | grep title
  <title>Untitled</title>

The built-in stylesheet is used unless a stylesheet is given.

  $ djot html -c doc.dj | grep -c '<style>'
  1

  $ echo 'p { color: red }' > a.css
  $ djot html -c doc.dj --inline-css a.css | grep -A2 '<style>'
  <style>
  p { color: red }
  </style>

Errors
======

  $ djot html missing.dj
  djot: missing.dj: No such file or directory
  [1]

  $ djot html --from json doc.dj 2>&1 | head -1
  djot: doc.dj: Expected JSON value but found #

  $ djot html --from json doc.dj 2> /dev/null
  [1]

  $ djot html --from yaml doc.dj 2> /dev/null
  [124]
