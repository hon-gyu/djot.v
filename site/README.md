<!-- ai-disclosure: ai-generated -->
# site

The project's static site: a home page, a playground, the extension
reference, and the OCaml API documentation. There is no CI: the site is
built and published by hand.

## Building

```
make site          # into _build/site
make site-serve    # the same, then serve it on localhost:8000
make site-publish  # the same, then push it to the gh-pages branch of origin
```

`site-publish` refuses to run with uncommitted changes, or from a commit
that is not on origin, since the site states the commit it is built from
and links to the source at that commit. It adds one commit to the `gh-pages`
branch on the remote and touches nothing in the working tree. GitHub Pages
has to be set to serve that branch.

Both need an opam switch with the `ocaml/` package's dependencies (jsont,
bytesrw, odoc) plus brr and js_of_ocaml-compiler. Neither needs Rocq: the
site is built from the extracted code checked in under `ocaml/kernel`.

`site/` is a dune project of its own, so that brr and js_of_ocaml are not
dependencies of the package. It sees the package through the symlink
`site/djot`, which points at `ocaml/`. The root `dune` file excludes
`site/` from the Rocq build.

## Layout

| Path | What it is |
| --- | --- |
| `lib/profiles.ml` | A profile as a short string, for URLs: what differs from djot. Used by the playground and by the playground links on the pages. |
| `lib/links.ml` | The repository's address, and the link to a theorem's statement. |
| `lib/theorems.sh` | Writes `theorems.ml` at build time: every theorem of `theories/` and `dev/` with its file and line. |
| `lib/versions.sh` | Writes `versions.ml` at build time: what the `VERSION` file at the root states, and the commit being built. |
| `gen/gen.ml` | Writes the static pages from `pages/`. |
| `playground/playground.ml` | The playground's interface, with brr. |
| `playground/worker.ml` | The playground's parser, as a web worker. |
| `pages/*.dj` | The pages, in djot. |
| `pages/theme.css` | Colours and fonts, shared by the two below. |
| `pages/style.css`, `pages/preview.css` | The site's stylesheet, and the one inside the playground's preview frame. |

## Pages

A page is a djot file rendered by the parser. `gen.ml` fills in four code
block languages:

- `example`: a source, a line with a period, and its HTML, shown side by
  side with a link that opens the source in the playground;
- `changes`: the properties whose status a profile changes, against djot;
- `properties`: a table of every property under the profiles named in the
  block, one per line;
- `versions`: the commits the site was built from.

The extensions page is `pages/extensions.dj` followed by the files of
`theories/spec/`, the extension reference, which is part of the
Rocq development (`theories/Spec.v` says how it is checked).
`gen.ml` moves their headings one level down and appends a Properties
section to each.

## What follows the code, and what does not

These come from the Rocq development or the package and cannot be wrong on
the site:

- the switches and delimiters the playground offers (`Djot.Profile.switches`,
  `Djot.Profile.delimiters`);
- the property list, with its words and the status of each property
  under a profile (`theories/Properties.v`, where every status that claims
  a property carries a proof of it for that profile). The README's
  property tables are written from the same file;
- the output of every example of the extension reference: it is written
  in the reference, and the Rocq build proves the parser renders it;
- the version, the syntax reference commit and the built commit in the
  footer and on the home page (`VERSION`, and git);
- the link from a theorem's name to its statement. A property that names
  a theorem the development does not have fails the build;
- the word a status is shown as (`status_name`, in the same file).

These are written by hand and go stale without any build failing:

1. **The prose of the extension reference** (`theories/spec/`). Its
   examples are proved; the sentences around them are not. A parser
   change that alters an example fails the build at that example, which
   is the moment to reread the prose around it.
2. **The words of the property list** (`theories/Properties.v`): each
   row's statement and implication in English, beside its formal
   statement. The theorem names listed for a row are names only; one that
   does not exist fails the site build.
3. **The home page and the API page** (`pages/home.dj`, `pages/api.dj`):
   what they say about the Markdown-like profile, and the code sample,
   which is not compiled. The meaning of each status word is written in
   `gen/gen.ml`.
4. **Switch descriptions.** The one-line `doc` of each switch in
   `ocaml/src/djot.ml` repeats the doc comment in `djot.mli`.
5. **The extracted code.** The site runs `ocaml/kernel`, which is a copy of
   the extraction. `make check-rocq` says whether it is behind
   `theories/`. Run it before publishing.
6. **Styles.** `preview.css` styles the classes the HTML renderer writes
   (`callout`, `keyed`). A new rendered class needs a rule there.
7. **`VERSION`.** The version number and the syntax reference commit are
   edited by hand.
