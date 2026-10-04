(* ai-disclosure: ai-generated *)

(** Djot trees as JSON, in the format of djot.js's AST.

    A node is an object with its ["tag"], the members of that tag, ["attributes"] when it
    has any and ["pos"] when it has a position. Tags and members are the ones djot.js
    writes, so its [ast.ts] is the reference for them.

    Members and tags djot.js does not have:
    - ["plain"] on a heading and on a keyed block: the text of the heading or of the
      label, as {!Djot.Inline.to_plain_text} gives it;
    - ["tight"] on a definition list;
    - ["name"] on a div or span that has one;
    - ["ext_wikilink"], ["ext_keyed"] and ["ext_callout"], with the members of
      {!Djot.Inline.Ext_wikilink}, {!Djot.Block.Ext_keyed} and {!Djot.Block.Ext_callout}.

    Where the tree does not hold what djot.js writes:
    - dashes, ellipses and unmatched quotes are part of a ["str"], as the character they
      render to; there is no ["smart_punctuation"] node;
    - ["pos"] has the range of {!Djot.Doc.textloc}, and its columns and offsets count
      bytes where djot.js counts UTF-16 code units. *)

(** {1 Trees} *)

(** A {!Djot.Block.FootnoteDef} is a ["footnote"] and a {!Djot.Block.RefDef} a
    ["reference"], each where it is in the tree.

    An identifier is in ["attributes"] whether it was written or derived: a tree does not
    say which. Only {!of_doc} writes ["autoAttributes"].

    Decoding skips unknown members. It reads ["plain"], ["pos"] and a row's ["head"] and
    drops them, and puts an identifier under ["autoAttributes"] first among the
    attributes. So a decoded node has no position, and decoding what was encoded gives
    the same tree up to positions. *)
val block : Djot.Block.t Djot.node Jsont.t

val inline : Djot.Inline.t Djot.node Jsont.t

(** {1 Documents} *)

(** The ["doc"] object: [references], [autoReferences] and [footnotes] by label, then the
    blocks, with the definitions left out as djot.js does. A footnote has the attributes
    of its definition. An identifier in {!Djot.Doc.auto_identifiers} is under
    ["autoAttributes"], as in djot.js. Nodes have a ["pos"] when the document was parsed with
    [~locs:true].

    There is no decoder for documents, since a {!Djot.Doc.t} is not built from blocks. *)
val of_doc : Djot.Doc.t -> Jsont.json

(** {!of_doc} as JSON text.
    @param format default [Jsont.Minify] *)
val to_string : ?format:Jsont.format -> Djot.Doc.t -> string
