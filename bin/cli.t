# ai-disclosure: ai-generated

  $ cat > doc.dj <<'END'
  > ---
  > title: A page
  > ---
  > # Hi
  > 
  > *strong* and [[w]]
  > END

  $ djot html doc.dj --frontmatter
  <section id="Hi">
  <h1>Hi</h1>
  <p><strong>strong</strong> and [[w]]</p>
  </section>

  $ djot html doc.dj --frontmatter --ext-wikilinks
  <section id="Hi">
  <h1>Hi</h1>
  <p><strong>strong</strong> and <a href="w">w</a></p>
  </section>

  $ djot ast --locs doc.dj --frontmatter
  doc frontmatter={"title":"A page"}
    section (4:1:22-6:18:45)
      heading (4:1:22-4:4:25) level=1 plain="Hi"
        str (4:3:24-4:4:25) text="Hi"
      para (6:1:28-6:18:45)
        strong (6:1:28-6:8:35)
          str (6:2:29-6:7:34) text="strong"
        str (6:9:36-6:18:45) text=" and [[w]]"

  $ djot djot doc.dj --frontmatter --style safe
  ---
  title: A page
  ---
  
  # Hi
  
  {*strong*} and \[\[w\]\]

  $ djot json doc.dj --frontmatter | djot html --from json
  <section id="Hi">
  <h1>Hi</h1>
  <p><strong>strong</strong> and [[w]]</p>
  </section>

  $ djot html -c doc.dj --frontmatter --css s.css | grep -v '^<meta'
  <!DOCTYPE html>
  <html lang="en">
  <head>
  <title>A page</title>
  <link rel="stylesheet" href="s.css">
  </head>
  <body>
  <section id="Hi">
  <h1>Hi</h1>
  <p><strong>strong</strong> and [[w]]</p>
  </section>
  </body>
  </html>

  $ echo x | djot html -c | grep title
  <title>Untitled</title>

  $ djot html missing.dj
  djot: missing.dj: No such file or directory
  [1]

  $ djot html --from json doc.dj
  djot: doc.dj: Expected doc object but found number
  File "-", line 1, characters 0-1:
  [1]
