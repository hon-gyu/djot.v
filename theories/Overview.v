(* ai-disclosure: autonomous *)

From DjotV Require Import Ast Profile Invariants Render Roundtrip.

(** * DjotV: a verified Djot parser

    DjotV is an executable Djot parser written in Gallina. The same
    definitions are compiled by Rocq, extracted to OCaml for differential
    testing, and used in the statements of the machine-checked guarantees.
    The project treats [djot.js] and [djoths] as executable oracles; it does
    not attempt to verify either implementation.

    This page is the reader's map to the development. It emphasizes what has
    been delivered and points to the modules containing the executable
    definitions and theorems.

    - {{DjotV.Ast.html}Ast} defines the document, block, and inline syntax trees.
    - {{DjotV.Step.html}Step} implements block parsing as a fold over classified
      lines with an explicit container state. {{DjotV.Inline.html}Inline}
      implements the single-pass inline scanner.
      {{DjotV.Document.html}Document} performs whole-document resolution after
      parsing.
    - {{DjotV.Render.html}Render} defines the canonical Djot renderer and the
      canonical fragment on which rendering is invertible.
    - {{DjotV.Roundtrip.html#roundtrip_blocks}roundtrip_blocks} and
      {{DjotV.Roundtrip.html#roundtrip_doc}roundtrip_doc} prove that
      parsing canonical rendered output recovers the original value.
    - {{DjotV.Address.html}Address} names a block by its explicit
      [{#id}] and resolves that name to a split of the document, so an
      edit can be applied where the roundtrip theorems already talk.
    - {{DjotV.Site.html}Site} routes a directory of notes to URLs and
      proves the build local: an edit that preserves a note's summary
      leaves every other page's rendering identical.
    - {{DjotV.Uniformity.html}Uniformity} and
      {{DjotV.ListUniformity.html}ListUniformity} prove that container contents
      parse by the same rules as top-level input.
    - {{DjotV.Invariants.html}Invariants} collects the exported structural
      guarantees and compatibility conditions for configuration changes.
    - {{DjotV.Profile.html}Profile} exposes reviewed Djot and Markdown-like
      profiles while keeping their inline and block capabilities independently
      composable.

    ** Main guarantees

    The block parser is prefix deterministic: once a prefix has committed
    blocks, later lines cannot revise those blocks. Its explicit state is
    sufficient to continue parsing, so the parser carries no hidden history.
    See {{DjotV.Invariants.html#incremental_invariants}incremental_invariants}.

    Inline scanning consumes one unit of fuel per source byte and structural
    classification is independent of reference and footnote resolution
    environments. See
    {{DjotV.Invariants.html#inline_invariants}inline_invariants}.

    The central roundtrip theorem is exact equality, not equivalence modulo a
    normalization relation. Its domain is the canonical view accepted by
    {{DjotV.Render.html#cb_ok}cb_ok} and
    {{DjotV.Inline.html#ci_ok}ci_ok}. This boundary states which AST values
    have a canonical source spelling for a selected profile.

    ** Configurable language profiles

    {{DjotV.Profile.html#djot_profile}djot_profile} preserves Djot behavior.
    The independently constructed
    {{DjotV.Profile.html#markdown_like_profile}markdown_like_profile} changes
    delimiter spelling,
    paragraph interruption, setext headings, typography, heading
    continuation, and Djot-specific capabilities. It is deliberately called
    Markdown-like rather than CommonMark: a GFM table grammar and CommonMark's
    delimiter-run rules are not implemented.

    A profile is an open pairing, not an enumeration. Callers may start from
    a named value, apply field-local inline or block updates, and retain the
    generic parser theorems.
    {{DjotV.Config.html#preserves_compose}preserves_compose} is the small frame
    lemma used to combine independently proved invariant-preserving updates.

    ** Verification boundary

    The project proves properties of the Gallina parser and canonical
    renderer. HTML fidelity is checked differentially but is not the subject
    of the roundtrip theorem. Source positions, command-line behavior, and
    the oracle implementations themselves are outside the verified boundary.
    The extracted exhaustive checks complement the proofs; they do not replace
    them.

    ** Suggested reading order

    Start with {{DjotV.Ast.html}Ast}, then read
    {{DjotV.Profile.html}Profile} for the user-facing entry points.
    {{DjotV.Step.html}Step} and {{DjotV.Inline.html}Inline} explain the two
    parsing layers. {{DjotV.Invariants.html}Invariants} states the main
    structural results, while {{DjotV.Render.html}Render} and
    {{DjotV.Roundtrip.html}Roundtrip} define and prove the canonical roundtrip
    contract.
*)
