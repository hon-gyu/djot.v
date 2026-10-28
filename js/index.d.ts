// ai-disclosure: ai-generated

/**
 * The syntax a parse accepts: a named profile with constructs switched.
 *
 * `djot` is djot as specified. `markdown_like` adds Markdown spellings:
 * strong as `**`, dollar math, setext headings, sublists without a blank
 * line. It is not CommonMark.
 *
 * A switch has the name of its `Djot.Profile.with_` function in the OCaml
 * library: `tables`, `footnotes`, `ext_wikilinks`, `ext_callouts`. The
 * extensions are off in both profiles.
 */
export interface Profile {
  base?: "djot" | "markdown_like";
  switches?: Record<string, boolean>;
}

/**
 * How `toDjot` writes a tree.
 *
 * - `irredundant`: every backslash and brace the parse needs, and no other.
 *   About 0.8 s for a 140 KB document.
 * - `checked`: what a person would type, falling back to the fully escaped
 *   form for a top-level block that would read back differently. About 0.15 s
 *   for the same document.
 * - `safe`: escaped by fixed rules. The fastest.
 * - `naive`: what a person would type; it need not read back as the tree.
 *
 * The OCaml library's `Djot.style` documents each in full.
 */
export type Style = "irredundant" | "checked" | "safe" | "naive";

/** A node of the tree: djot.js's AST, with a few additions. */
export interface Node {
  tag: string;
  [member: string]: unknown;
}

/**
 * The tree of a document, as the OCaml library's `Djot_json` writes it:
 * the blocks under `children`, and `references`, `autoReferences` and
 * `footnotes` by label.
 */
export interface Doc extends Node {
  tag: "doc";
  children: Node[];
}

/** The tree of a djot text. With `locs`, every node has the `pos` it was read from. */
export function parse(text: string, options?: { profile?: Profile; locs?: boolean }): Doc;

/** The HTML of a djot text, or of a tree. */
export function toHtml(source: string | Doc, options?: { profile?: Profile }): string;

/**
 * A tree as djot text, in the syntax of `profile`.
 *
 * Except with `naive`, parsing the result with that profile gives the same
 * tree, up to positions and the exceptions `Djot.Doc.to_string` lists in the
 * OCaml library. `style` defaults to `irredundant`.
 */
export function toDjot(doc: Doc, options?: { profile?: Profile; style?: Style }): string;
