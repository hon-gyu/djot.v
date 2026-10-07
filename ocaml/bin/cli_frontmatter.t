# ai-disclosure: ai-generated

The --frontmatter option. Runs only when the library is built with yaml.

  $ cat > doc.dj <<'END'
  > ---
  > title: A page
  > ---
  > # Hi
  > END

  $ djot html doc.dj --frontmatter
  <section id="Hi">
  <h1>Hi</h1>
  </section>

Locations count the frontmatter's lines.

  $ djot ast --locs doc.dj --frontmatter
  doc frontmatter={"title":"A page"}
    section (4:1:22-4:4:25)
      heading (4:1:22-4:4:25) level=1 plain="Hi"
        str (4:3:24-4:4:25) text="Hi"

  $ djot djot doc.dj --frontmatter
  ---
  title: A page
  ---
  
  # Hi

  $ djot json doc.dj --frontmatter | djot html --from json --doc | grep title
  <title>A page</title>

The page title is the frontmatter's unless --title is given.

  $ djot html --doc doc.dj --frontmatter | grep title
  <title>A page</title>

  $ djot html --doc doc.dj --frontmatter --title Other | grep title
  <title>Other</title>
