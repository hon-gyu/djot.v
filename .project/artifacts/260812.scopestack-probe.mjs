// Throwaway probe for 260811.inline-parser.md §2.2: is the scope-stack
// formulation equivalent to djot.js's splice-based match list?  Kept as
// evidence for the decision recorded there; not maintained, not wired into
// any make target, and expected to rot when djot.js changes.
//
// Method.  djot.js's own matchers run unmodified; only `this.matches` is
// replaced, by an array that mirrors every mutation into a scope stack of
// open openers, each frame carrying its accumulated content.  At
// getMatches() the flattened stack is compared against the flat array
// djot.js actually built, element by element and by object identity.  A
// divergence is either an anomaly (a mutation the stack cannot mirror) or
// an order mismatch.
//
// Usage:
//   node 260812.scopestack-probe.mjs --corpus
//   node 260812.scopestack-probe.mjs "<alphabet>" <maxlen>
// The second form runs every string up to <maxlen> over <alphabet>: the
// corpus is a regression suite, not a systematic exploration of the
// delimiter grammar.

import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)),
                          "../..");
const require_ = createRequire(import.meta.url);
const lib = path.join(root, "djot.js/lib");
const inlineMod = require_(path.join(lib, "inline.js"));
const Base = inlineMod.InlineParser;

let anomalies = [];
const note = (kind, detail) => anomalies.push({ kind, detail });

class Frame {
  constructor(placeholder) { this.placeholder = placeholder; this.content = []; }
}

function flatten(frames) {
  let acc = frames[frames.length - 1].content.slice();
  for (let i = frames.length - 1; i >= 1; i--) {
    acc = frames[i - 1].content.concat([frames[i].placeholder], acc);
  }
  return acc;
}

class MatchList extends Array {
  static get [Symbol.species]() { return Array; }
  attach(self) { this.self = self; return this; }
  top() { return this.self.frames[this.self.frames.length - 1]; }
  locate(obj) {
    const frames = this.self.frames;
    for (let i = frames.length - 1; i >= 0; i--) {
      if (i > 0 && frames[i].placeholder === obj) return { kind: "placeholder", depth: i };
      const j = frames[i].content.indexOf(obj);
      if (j >= 0) return { kind: "content", depth: i, index: j };
    }
    return null;
  }
  push(...ms) { for (const m of ms) this.top().content.push(m); return super.push(...ms); }
  pop() {
    const frames = this.self.frames;
    const t = frames[frames.length - 1];
    if (t.content.length > 0) t.content.pop();
    else if (frames.length > 1) { note("discard-frame", this.length); frames.pop(); }
    else note("pop-into-empty-root", this.length);
    return super.pop();
  }
  splice(start, deleteCount, ...items) {
    const frames = this.self.frames;
    if (deleteCount === 1 && items.length === 1) {
      const loc = this.locate(this[start]);
      if (loc === null) note("replace-target-missing", items[0].annot);
      else if (loc.kind === "placeholder") {
        if (loc.depth !== frames.length - 1) {
          note("close-below-top", items[0].annot);
          while (frames.length - 1 > loc.depth) this.self.abandonTop();
        }
        const f = frames.pop();
        frames[frames.length - 1].content.push(items[0], ...f.content);
      } else frames[loc.depth].content[loc.index] = items[0];
    } else if (deleteCount === 0 && items.length === 1) {
      const anchor = this[start];
      const loc = anchor === undefined ? null : this.locate(anchor);
      if (loc === null) note("insert-anchor-missing", start);
      else if (loc.kind === "placeholder") {
        // inserting just before an open frame's placeholder = appending to
        // that frame's parent, which owns the flat region ending there
        frames[loc.depth - 1].content.push(items[0]);
      } else frames[loc.depth].content.splice(loc.index, 0, items[0]);
    } else note("unexpected-splice", `${start}/${deleteCount}/${items.length}`);
    return super.splice(start, deleteCount, ...items);
  }
}

class DualInlineParser extends Base {
  constructor(subject, options) {
    super(subject, options);
    this.frames = [new Frame(null)];
    this.matches = new MatchList().attach(this);
  }
  abandonTop() {
    const f = this.frames.pop();
    this.frames[this.frames.length - 1].content.push(f.placeholder, ...f.content);
  }
  addOpener(name, startpos, endpos, defaultAnnot) {
    if (!this.openers[name]) this.openers[name] = [];
    this.openers[name].push({
      matchIndex: this.matches.length, startpos, endpos, annot: null,
      subMatchIndex: this.matches.length, substartpos: null, subendpos: null,
    });
    const placeholder = { startpos, endpos, annot: defaultAnnot };
    Array.prototype.push.call(this.matches, placeholder);
    this.frames.push(new Frame(placeholder));
  }
  clearOpeners(startpos, endpos) {
    super.clearOpeners(startpos, endpos);
    while (this.frames.length > 1) {
      const p = this.frames[this.frames.length - 1].placeholder;
      if (p.startpos >= startpos && p.endpos <= endpos) this.abandonTop();
      else break;
    }
  }
  getMatches() {
    const ms = super.getMatches();
    const flat = flatten(this.frames);
    if (flat.length !== ms.length) {
      note("order-mismatch", `length ${flat.length} vs ${ms.length}`);
    } else {
      for (let i = 0; i < ms.length; i++) {
        if (flat[i] !== ms[i]) {
          note("order-mismatch",
            `at ${i}: ${JSON.stringify(flat[i])} vs ${JSON.stringify(ms[i])}`);
          break;
        }
      }
    }
    return ms;
  }
}

// Reporting
// ----------

let total = 0;
const byKind = {};
const samples = {};
function record(label) {
  for (const a of anomalies) {
    byKind[a.kind] = (byKind[a.kind] || 0) + 1;
    (samples[a.kind] ||= []).length < 5 &&
      samples[a.kind].push([label, a.detail]);
  }
}

function runInline(s) {
  total++;
  anomalies = [];
  try {
    const p = new DualInlineParser(s, { warn: () => {} });
    p.feed(0, s.length - 1);
    p.getMatches();
  } catch (e) {
    note("throw", String(e).slice(0, 80));
  }
  record(JSON.stringify(s));
}

// Corpus mode
// -----------

function parseTests(file) {
  const lines = fs.readFileSync(file, "utf8").split("\n");
  const cases = [];
  let i = 0;
  while (i < lines.length) {
    const m = /^(`{3,})\s*(.*)$/.exec(lines[i]);
    if (!m) { i++; continue; }
    const fence = m[1];
    const linenum = i + 1;
    i++;
    const input = [];
    while (i < lines.length && lines[i] !== "." && lines[i] !== "!") {
      input.push(lines[i]); i++;
    }
    const filtered = lines[i] === "!";
    i++;
    while (i < lines.length && lines[i] !== fence) i++;
    i++;
    if (!filtered) {
      cases.push({ label: `${path.basename(file)}:${linenum}`,
                   input: input.join("\n") + "\n" });
    }
  }
  return cases;
}

function runCorpus() {
  inlineMod.InlineParser = DualInlineParser; // block.ts constructs it by name
  const { parse } = require_(path.join(lib, "index.js"));
  const dir = path.join(root, "djot.js/test");
  for (const f of fs.readdirSync(dir).filter((x) => x.endsWith(".test"))) {
    for (const c of parseTests(path.join(dir, f))) {
      total++;
      anomalies = [];
      try {
        parse(c.input, { warn: () => {} });
      } catch (e) {
        note("throw", String(e).slice(0, 80));
      }
      record(c.label);
    }
  }
  console.log(`corpus documents: ${total}`);
}

function runGenerated(alphabet, maxlen) {
  const buf = [];
  const gen = (len) => {
    if (buf.length === len) { runInline(buf.join("")); return; }
    for (const c of alphabet) { buf.push(c); gen(len); buf.pop(); }
  };
  for (let n = 0; n <= maxlen; n++) gen(n);
  console.log(`alphabet ${JSON.stringify(alphabet.join(""))}, ` +
              `length <= ${maxlen}: ${total} strings`);
}

if (process.argv[2] === "--corpus") {
  runCorpus();
} else {
  runGenerated((process.argv[2] || "_*a{} ").split(""),
               parseInt(process.argv[3] || "5", 10));
}

console.log("anomalies:", JSON.stringify(byKind));
for (const k in samples) {
  console.log(`-- ${k}`);
  for (const [s, d] of samples[k]) console.log(`   ${s}  ${d}`);
}
