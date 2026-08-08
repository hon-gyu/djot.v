// djot.js oracle: djot on stdin, HTML on stdout.
// Requires the submodule to be built (make oracles).
//
// Two modes:
//   (default)  one document on stdin, its HTML on stdout.
//   --batch    many documents, length-delimited both ways:
//                in:   for each document, "<byte-length>\n" then that many bytes
//                out:  for each document, "<byte-length>\n" then that many bytes
//              End of input ends the batch; outputs come back in order.
//
// Batch exists because node startup (~70ms) dominates: the generated
// corpus is hundreds of documents, and one process per document turns a
// two-second run into a minute.  Framing is by byte length rather than a
// separator because a djot document may contain any bytes, newlines and
// would-be sentinels included.
import fs from "node:fs";
import { parse, renderHTML } from "../../djot.js/lib/index.js";

const warn = () => {};
const convert = (s) => renderHTML(parse(s, { warn }), { warn });

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
