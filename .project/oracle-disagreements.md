# Oracle disagreements

Append-only adjudication log: cases where djoths's output differs from
djot.js's expected corpus output (djot.js passes its own corpus 287/287, so
"expected" and "djot.js" coincide on this corpus).

Baseline established 2026-08-02 with `make baseline`
(djot.js @ v0.3.2 submodule, djoths @ 0.1.4.1 submodule; 287 cases run,
6 skipped for `p`/`a` options, filter cases dropped).
Full diffs: `.project/baseline-report.txt` (regenerate with `make baseline`).

Verdict legend: `djotjs-bug` / `djoths-bug` / `spec-gap` / `unadjudicated`.

| Case | Verdict | Notes |
|---|---|---|
| attributes.test:145 | unadjudicated | |
| attributes.test:253 | unadjudicated | |
| attributes.test:327 | unadjudicated | |
| attributes.test:346 | unadjudicated | |
| attributes.test:362 | unadjudicated | |
| block_quote.test:117 | unadjudicated | |
| code_blocks.test:1 | unadjudicated | `~~~` fence |
| definition_lists.test:6 | unadjudicated | |
| definition_lists.test:113 | unadjudicated | |
| escapes.test:30 | unadjudicated | |
| footnotes.test:1 | unadjudicated | |
| footnotes.test:74 | unadjudicated | |
| headings.test:36 | unadjudicated | |
| headings.test:59 | unadjudicated | |
| headings.test:138 | unadjudicated | |
| headings.test:163 | unadjudicated | |
| links_and_images.test:183 | unadjudicated | |
| links_and_images.test:192 | unadjudicated | |
| spans.test:21 | unadjudicated | |
| spans.test:27 | unadjudicated | |
| spans.test:33 | unadjudicated | |
| tables.test:111 | unadjudicated | |
| task_lists.test:1 | unadjudicated | |
| task_lists.test:17 | unadjudicated | |
| task_lists.test:38 | unadjudicated | |
