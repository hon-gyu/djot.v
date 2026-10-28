// ai-disclosure: ai-generated

const test = require("node:test");
const assert = require("node:assert/strict");
const djotv = require("../djotv.js");

// A text with the main kinds of node.
const TEXT = `{#top .a key="v"}
# Heading _emph_ *strong*

A {=mark=} x^sup^ \`verb\` [link](http://e.x) [ref][r] note[^n] 'single'

> quote

\`\`\` py
code
\`\`\`

1. one
2. two

- [ ] todo

| h | i |
|---|---|
| 1 | 2 |

[r]: http://r.ef

[^n]: The note.
`;

test("the tree is Djot_json's", () => {
  const doc = djotv.parse("*hi*");
  assert.equal(doc.tag, "doc");
  assert.deepEqual(doc.children, [
    { tag: "para", children: [{ tag: "strong", children: [{ tag: "str", text: "hi" }] }] },
  ]);
});

test("locs gives positions", () => {
  assert.equal(djotv.parse("x").children[0].pos, undefined);
  assert.deepEqual(djotv.parse("a\n\nb", { locs: true }).children[1].pos.start.line, 3);
});

test("html", () => {
  assert.equal(djotv.toHtml("*hi*"), "<p><strong>hi</strong></p>\n");
});

test("the html of a tree is the html of its text", () => {
  assert.equal(djotv.toHtml(djotv.parse(TEXT)), djotv.toHtml(TEXT));
});

test("djot of a tree parses back, in every style but naive", () => {
  const doc = djotv.parse(TEXT);
  for (const style of [undefined, "irredundant", "checked", "safe"]) {
    assert.deepEqual(djotv.parse(djotv.toDjot(doc, { style })), doc, style);
  }
  assert.equal(typeof djotv.toDjot(doc, { style: "naive" }), "string");
});

test("irredundant is the default style", () => {
  const doc = djotv.parse("a \\* b");
  assert.equal(djotv.toDjot(doc), djotv.toDjot(doc, { style: "irredundant" }));
});

test("a built tree", () => {
  const doc = {
    tag: "doc",
    children: [{ tag: "heading", level: 2, children: [{ tag: "str", text: "T" }] }],
  };
  assert.equal(djotv.toDjot(doc), "## T");
});

test("profile", () => {
  const wikilinks = { switches: { ext_wikilinks: true } };
  assert.equal(djotv.parse("[[w]]", { profile: wikilinks }).children[0].children[0].tag, "ext_wikilink");
  assert.match(djotv.toHtml("**x**", { profile: { base: "markdown_like" } }), /<strong>/);
  assert.doesNotMatch(djotv.toHtml("| a |\n", { profile: { switches: { tables: false } } }), /<table>/);
});

test("errors", () => {
  assert.throws(() => djotv.toHtml("x", { profile: { switches: { nope: true } } }), /unknown switch/);
  assert.throws(() => djotv.toHtml("x", { profile: { base: "commonmark" } }), /unknown profile/);
  assert.throws(() => djotv.toHtml("x", { profile: { base: 1 } }), /must be a string/);
  assert.throws(() => djotv.toDjot(djotv.parse("x"), { style: "pretty" }), /unknown style/);
  assert.throws(() => djotv.toHtml({ tag: "doc" }), /Missing member children/);
  assert.throws(() => djotv.toHtml("> ".repeat(5000) + "x"), /nested too deeply/);
});
