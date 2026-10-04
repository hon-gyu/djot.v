<!-- ai-disclosure: ai-generated -->
# site

The project's static site: a home page, a playground, the extension
reference, and the OCaml API documentation. Published to GitHub Pages by
`.github/workflows/site.yml` on every push to `main`.

## Building

```
make site         # into _build/site
make site-serve   # the same, then serve it on localhost:8000
```

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
| `lib/spec.ml` | A profile as a short string, for URLs: what differs from djot. Used by the playground and by the playground links on the pages. |
| `lib/links.ml` | The repository's address, and the link to a theorem's statement. |
| `lib/theorems.sh` | Writes `theorems.ml` at build time: every theorem of `theories/` and `dev/` with its file and line. |
| `lib/versions.sh` | Writes `versions.ml` at build time from git: this repository's commit and the commit of the `djot` submodule. |
| `gen/gen.ml` | Writes the static pages from `pages/`. |
| `playground/playground.ml` | The playground's interface, with brr. |
| `playground/worker.ml` | The playground's parser, as a web worker. |
| `pages/*.dj` | The pages, in djot. |
| `pages/extensions/*.dj` | One file per extension; together they make the extensions page. |
| `pages/theme.css` | Colours and fonts, shared by the two below. |
| `pages/style.css`, `pages/preview.css` | The site's stylesheet, and the one inside the playground's preview frame. |

## Pages

A page is a djot file rendered by the parser. `gen.ml` fills in four code
block languages:

- `example`: shows the source and the HTML it renders to, with a link that
  opens it in the playground;
- `changes`: the properties whose status a profile changes, against djot;
- `properties`: a table of every property under the profiles named in the
  block, one per line;
- `versions`: the commits the site was built from.

To add an extension, add a file to `pages/extensions/`. Its first line is
`profile: ...` in the form `Spec.of_string` reads, for example
`profile: ext_wikilinks=on`. That profile is used for the file's `example`
blocks. Write the headings as for a page of its own, starting at `#`:
`gen.ml` moves them one level down, and appends a Properties section. The
files are joined in the order of their names.

## What follows the code, and what does not

These come from the Rocq development or the package and cannot be wrong on
the site:

- the switches and delimiters the playground offers (`Djot.Profile.switches`,
  `Djot.Profile.delimiters`);
- the status of a property under a profile, where it depends on the
  profile (the checks of `theories/ProfileChecks.v`);
- the rendered output of every `example` block;
- the commits in the footer and on the home page;
- the link from a theorem's name to its statement. A property that names
  a theorem the development does not have fails the build;
- the word a status is shown as (`Djot_properties.status_name`).

These are written by hand and go stale without any build failing:

1. **The prose of the extension pages.** An example's output is
   regenerated, so it stays true, but the sentence above it is not checked
   against it. After a change to an extension's parsing, reread its page.
2. **The property list** (`ocaml/properties/djot_properties.ml`):
   - a row with a fixed status (`always Proved`, a fixed condition) is a
     claim about every profile that nothing recomputes. If a theorem gains
     a hypothesis about the profile, the row needs a check in
     `ProfileChecks.v`;
   - the statements repeat the README's property tables.
3. **The home page and the API page** (`pages/home.dj`, `pages/api.dj`):
   what they say about the Markdown-like profile, and the code sample,
   which is not compiled. The meaning of each status word is written in
   `gen/gen.ml`.
4. **Switch descriptions.** The one-line `doc` of each switch in
   `ocaml/src/djot.ml` repeats the doc comment in `djot.mli`.
5. **The extracted code.** The site runs `ocaml/kernel`, which is a copy of
   the extraction. `make ocaml-pkg-check-current` says whether it is behind
   `theories/`; the workflow does not run it, since it needs Rocq.
6. **The syntax reference.** The site states the commit of the `djot`
   submodule. Moving the submodule does not redo the audit in
   `.project/syntax-reference-coverage.md`, which names its commit
   separately.
7. **Styles.** `preview.css` styles the classes the HTML renderer writes
   (`callout`, `keyed`). A new rendered class needs a rule there.
8. **The workflow.** Its `opam install` line lists the dependencies by
   hand, and its OCaml version is fixed.
