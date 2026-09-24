(* ai-disclosure: autonomous *)

(** * Single-pass inline parsing

   The inline layer: the parser's pass over a paragraph's text, and the
   canonical (renderable) view it inverts.  As in the block layer,
   `para_inlines` is the pass, `cinline` is the image, and the two meet
   in `para_inlines_ci_para`.

   The scan threads through line breaks rather than restarting at each
   one, because a span may cross a break.  The canonical view stays
   line-local, `cblock` describing a paragraph as a list of lines, and
   `iscan_cis_closed` reconciles the two: a canonical line leaves the scan
   owing nothing to the next. *)

(* The inline layer is split across the files re-exported here, in
   dependency order; this file adds the delimiter table instances. *)

From Stdlib Require Import String.
From DjotV Require Export InlineTable InlineView InlineScan InlineLocated InlineInvert.

Local Open Scope string_scope.

(*
Djot's instance
---------------

The table in force for everything downstream.  A second one lives in
`dev/check/Markdown.v`, named explicitly rather than put in scope: two
instances of one class in one scope is how the wrong table gets
inferred.
*)

#[export] Instance djot_table : dtable :=
  DTable djot_config eq_refl.

(* The Markdown-like table, as an instance but deliberately *not* an
   `Instance`: it is named where it is wanted (`dev/check/Markdown.v`) so
   that inference in this development always means djot's. *)
Definition markdown_table : dtable :=
  DTable markdown_config eq_refl.

(* The narrower profile keeps Markdown spelling and switches off every
   djot-only delimiter container. *)
Definition markdown_like_table : dtable :=
  DTable markdown_like_config eq_refl.
