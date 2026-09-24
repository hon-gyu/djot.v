// djot.js: djot on stdin, HTML on stdout.
// Requires the submodule to be built (make build-djotjs).
//
// Two modes:
//   (default)  one document on stdin, its HTML on stdout.
//   --batch    many documents, length-delimited both ways:
//                in:   for each document, "<byte-length>\n" then that many bytes
//                out:  for each document, "<byte-length>\n" then that many bytes
//              End of input ends the batch; outputs come back in order.
//
// `--parse-only` parses and discards, printing nothing: it exists so a
// timing run can compare parse against parse without `renderHTML` in the
// number.
//
// Batch exists because node startup (~70ms) dominates: the generated
// corpus is hundreds of documents, and one process per document turns a
// two-second run into a minute.  Framing is by byte length rather than a
// separator because a djot document may contain any bytes, newlines and
// would-be sentinels included.
import fs from "node:fs";
import { parse, renderHTML } from "../../djot.js/lib/index.js";

const warn = () => {};

// djot.js keeps the smart-quote defaults in a closure variable that
// `betweenMatched` assigns to (`inline.ts:118-136`), and the variable is the
// enclosing call's parameter rather than the per-scan one, so it is shared by
// every parse in the process.  A `{"` or a `"}` therefore flips the default
// for the documents after it, and a batch stops agreeing with the same
// documents run one per process.
//
// The two spellings below restore each row's default: `{"` is an open marker,
// which turns the double quote back to `left_double_quote`, and `'}` is a
// close marker, which turns the single quote back to `right_single_quote`.
// Neither changes a default that is already the row's own, so the pair is
// idempotent, and running it before each document is what makes a batch mean
// what it says.  Upstream's own behaviour within one document is left alone;
// see `.project/djotjs-divergences.md`.
const resetQuoteDefaults = () => {
  parse('{"', { warn });
  parse("'}", { warn });
};

const parseOnly = process.argv.includes("--parse-only");

const convert = (s) => {
  resetQuoteDefaults();
  const doc = parse(s, { warn });
  return parseOnly ? "" : renderHTML(doc, { warn });
};

if (!process.argv.includes("--batch")) {
  process.stdout.write(convert(fs.readFileSync(0, "utf8")));
} else {
  const input = fs.readFileSync(0);
  const out = [];
  let at = 0;
  for (;;) {
    const nl = input.indexOf(0x0a, at);
    if (nl < 0) break;
    const len = parseInt(input.toString("utf8", at, nl), 10);
    if (!Number.isInteger(len) || len < 0) break;
    const start = nl + 1;
    const doc = input.toString("utf8", start, start + len);
    at = start + len;
    const html = Buffer.from(convert(doc), "utf8");
    out.push(Buffer.from(`${html.length}\n`, "utf8"), html);
  }
  process.stdout.write(Buffer.concat(out));
}
