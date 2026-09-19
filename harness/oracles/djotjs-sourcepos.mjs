// ai-disclosure: ai-generated
//
// djot.js source positions, restated in the convention of
// .project/260916.plan.source-locations.md: 0-based half-open *byte*
// ranges.  One document on stdin; one line per positioned node on stdout:
//
//   <indent><tag> [<start>,<stop>) <JSON of the source bytes in range>
//
// djot.js reports `line:col:offset` with an inclusive end, and its offsets
// and columns count UTF-16 code units, not bytes (`é` is one unit, two
// bytes).  Both are converted here.  A block's inclusive end usually lands
// on its own trailing newline, and at end of input without one it points
// one past the last byte; `--trim` drops a trailing "\n" (or "\r\n") from
// every block range so spans compare against a rule that excludes it.
// Breaks are left alone: their range *is* the line ending.
//
// Nodes without `pos` (djot.js gives none to `doc`) are printed without a
// range.  The `references` and `footnotes` maps are printed after the tree.
import fs from "node:fs";
import { parse } from "../../djot.js/lib/index.js";

const trim = process.argv.includes("--trim");
const src = fs.readFileSync(0, "utf8");
const bytes = Buffer.from(src, "utf8");

// byteAt[u] = byte offset of UTF-16 unit u; byteAt[src.length] = total.
const byteAt = new Array(src.length + 1);
{
  let b = 0;
  for (let u = 0; u < src.length; u++) {
    byteAt[u] = b;
    const c = src.charCodeAt(u);
    if (c >= 0xd800 && c <= 0xdbff) { byteAt[++u] = b; b += 4; }
    else b += c < 0x80 ? 1 : c < 0x800 ? 2 : 3;
  }
  byteAt[src.length] = b;
}

const range = (pos, isBreak) => {
  const start = byteAt[Math.min(pos.start.offset, src.length)];
  let endUnit = pos.end.offset + 1;
  const c = src.charCodeAt(pos.end.offset);
  if (c >= 0xd800 && c <= 0xdbff) endUnit++;
  let stop = byteAt[Math.min(endUnit, src.length)];
  if (trim && !isBreak && stop > start && bytes[stop - 1] === 0x0a) {
    stop--;
    if (stop > start && bytes[stop - 1] === 0x0d) stop--;
  }
  return [start, Math.max(start, stop)];
};

const out = [];
const show = (node, depth) => {
  let line = "  ".repeat(depth) + node.tag;
  if (node.pos) {
    const [a, b] = range(node.pos, node.tag.endsWith("_break"));
    line += ` [${a},${b}) ${JSON.stringify(bytes.subarray(a, b).toString("utf8"))}`;
  }
  if (node.attributes) line += " " + JSON.stringify(node.attributes);
  out.push(line);
  for (const k of ["children", "caption"]) {
    const v = node[k];
    if (Array.isArray(v)) v.forEach((n) => show(n, depth + 1));
    else if (v && typeof v === "object") show(v, depth + 1);
  }
};

const doc = parse(src, { sourcePositions: true, warn: () => {} });
show(doc, 0);
for (const k of ["references", "footnotes"]) {
  for (const [label, n] of Object.entries(doc[k] || {})) {
    out.push(`${k}[${JSON.stringify(label)}]`);
    show(n, 1);
  }
}
process.stdout.write(out.join("\n") + "\n");
