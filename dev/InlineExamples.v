(* ai-disclosure: autonomous *)

(* Examples pinning the inline scanner at djot's table, each
   checked against djot.js.  Nothing requires this file. *)

From Stdlib Require Import String Ascii List Bool Lia Arith.
From DjotV Require Import Config Strings Ast Attributes Inline.
Import ListNotations.

Local Open Scope string_scope.

(*
Escapes, pinned
===============

The examples from here on pin the scanner's behaviour, each checked
against djot.js.
*)

(* The scanner accepts any punctuation after a backslash... *)
Example escaped_punct_literal : parse_inline_line "\*" = [mk (Str "*")].
Proof. reflexivity. Qed.

(* ...and leaves a backslash before anything else alone. *)
Example escaped_nonpunct_literal : parse_inline_line "\a" = [mk (Str "\a")].
Proof. reflexivity. Qed.

(* Whitespace is the exception to that: a space becomes a non-breaking
   one, and the end of the line becomes a hard break. *)
Example escaped_space_is_nbsp :
  parse_inline_line "a\ b"
  = [mk (Str "a"); mk NonBreakingSpace; mk (Str "b")].
Proof. vm_compute. reflexivity. Qed.

(* Only the first byte of the run is claimed; the rest is text. *)
Example escaped_space_claims_one :
  parse_inline_line "a\  b"
  = [mk (Str "a"); mk NonBreakingSpace; mk (Str " b")].
Proof. vm_compute. reflexivity. Qed.

(* A tab is not a space, so the backslash stays literal. *)
Example escaped_tab_is_literal :
  parse_inline_line (String "\"%char (String "009"%char "b"))
  = [mk (Str (String "\"%char (String "009"%char "b")))].
Proof. vm_compute. reflexivity. Qed.

Example escaped_eol_is_hard_break :
  parse_inline_line "para\" = [mk (Str "para"); mk HardBreak].
Proof. vm_compute. reflexivity. Qed.

(* The hard break replaces the soft one, and the whitespace on either
   side of the backslash goes with it. *)
Example escaped_eol_replaces_soft_break :
  para_inlines ["ab \  "; "c"]
  = [mk (Str "ab"); mk HardBreak; mk (Str "c")].
Proof. vm_compute. reflexivity. Qed.

(* A backtick in a `Str` is escaped, so it does not open a verbatim... *)
Example escaped_tick_literal : parse_inline_line "\`a\`" = [mk (Str "`a`")].
Proof. reflexivity. Qed.

(* ...while a bare one does, and a run of the wrong width is content. *)
Example verbatim_basic : parse_inline_line "`a`" = [mk (Verbatim "a")].
Proof. reflexivity. Qed.

Example verbatim_wrong_width_is_content :
  parse_inline_line "` `` `" = [mk (Verbatim "``")].
Proof. reflexivity. Qed.

Example verbatim_unclosed_closes_at_eol :
  parse_inline_line "`a" = [mk (Verbatim "a")].
Proof. reflexivity. Qed.

(* The encoder emits only what `needs_escape` names, which is why a
   comma renders bare where a backslash does not. *)
Example escape_backslash : escape_str "a\b" = "a\\b".
Proof. reflexivity. Qed.

Example escape_leaves_punct : escape_str "a,b" = "a,b".
Proof. reflexivity. Qed.

(* ...but a delimiter the table claims is escaped, like the backtick. *)
Example escape_delims : escape_str "a*b_c{d}" = "a\*b\_c\{d\}".
Proof. reflexivity. Qed.

(*
Canonical verbatim, pinned
==========================
*)

Example verb_ticks_examples :
  (verb_ticks "a", verb_ticks "`", verb_ticks "``", verb_ticks "` ``")
  = (1, 2, 1, 3).
Proof. vm_compute. reflexivity. Qed.

Example verbatim_render_tick : ci_line [CIVerb "`"] = "`` ` ``".
Proof. vm_compute. reflexivity. Qed.

Example verbatim_mixed_roundtrip :
  parse_inline_line (ci_line [CIStr "a"; CIVerb "`"; CIStr "*"])
  = ci_inlines [CIStr "a"; CIVerb "`"; CIStr "*"].
Proof. vm_compute. reflexivity. Qed.

(* The byte after a delayed closer is dispatched normally: here it is
   the backslash that protects a literal backtick. *)
Example verbatim_then_escaped_tick :
  parse_inline_line (ci_line [CIVerb "v"; CIStr "`"])
  = ci_inlines [CIVerb "v"; CIStr "`"].
Proof. vm_compute. reflexivity. Qed.

(* The empty verbatim is outside the view: its two runs are separated by
   nothing, so only the end of the paragraph closes it. *)
Example empty_verbatim_not_canonical : ci_ok (CIVerb EmptyString) = false.
Proof. reflexivity. Qed.

(*
Spans cross a line break
========================
*)

(* A verbatim opened on one line closes on the next, with the break as
   content. *)
Example verbatim_crosses_break :
  para_inlines ["`a"; "b`"] = [mk (Verbatim "a
b")].
Proof. vm_compute. reflexivity. Qed.

(* And the ordinary case still splits at the break. *)
Example text_breaks_at_line_end :
  para_inlines ["a"; "b"] = [mk (Str "a"); mk SoftBreak; mk (Str "b")].
Proof. vm_compute. reflexivity. Qed.

(* The block-attribute recovery, which is what `para_inlines_off` is for.
   With attributes on, a `{%` on the first line opens a comment that the
   `%}` closes, and the spec attaches to nothing and is dropped, so the
   whole paragraph vanishes.  With the first line off, nothing opens. *)
Example para_off_comment_spans_paragraph :
  para_inlines ["{%"; "c"; "%}"] = [].
Proof. vm_compute. reflexivity. Qed.

Example para_off_one_frozen_line :
  para_inlines_off 1 ["{%"; "c"; "%}"]
  = [mk (Str "{%"); mk SoftBreak; mk (Str "c");
     mk SoftBreak; mk (Str "%}")].
Proof. vm_compute. reflexivity. Qed.

(* Two of them, which is what an indented continuation line gives. *)
Example para_off_two_frozen_lines :
  para_inlines_off 2 ["{%"; "c"; "%}"]
  = [mk (Str "{%"); mk SoftBreak; mk (Str "c");
     mk SoftBreak; mk (Str "%}")].
Proof. vm_compute. reflexivity. Qed.

(* An id spec is the same story with a different machine state. *)
Example para_off_id_spec :
  para_inlines_off 1 ["{#i"; "%}"]
  = [mk (Str "{#i"); mk SoftBreak; mk (Str "%}")].
Proof. vm_compute. reflexivity. Qed.

(* A delimiter span crosses one too. *)
Example emph_crosses_break :
  para_inlines ["_a"; "b_"]
  = [mk (Emph [mk (Str "a"); mk SoftBreak; mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

(*
The delimiter family, pinned
============================
*)

Example canonical_emph_source :
  ci_line [CIDelim DEmph [CIStr "a"]] = "{_a_}".
Proof. reflexivity. Qed.

Example canonical_nested_delimiter_roundtrip :
  parse_inline_line
    (ci_line [CIDelim DEmph
      [CIStr "a"; CIDelim DStrong [CIStr "b"]]])
  = ci_inlines [CIDelim DEmph
      [CIStr "a"; CIDelim DStrong [CIStr "b"]]].
Proof. vm_compute. reflexivity. Qed.

(* Bare and braced spell the same span... *)
Example emph_bare : parse_inline_line "_a_" = [mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example emph_braced : parse_inline_line "{_a_}" = [mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

(* ...but the marking is part of the key, so a braced opener is not
   closed by a bare delimiter, and the whole thing decays to text. *)
Example emph_marked_needs_marked_closer :
  parse_inline_line "{_a_" = [mk (Str "{_a_")].
Proof. vm_compute. reflexivity. Qed.

(* `can_open` is a nonspace to the right, `can_close` a nonspace to the
   left, so a delimiter against a space is literal. *)
Example emph_open_needs_nonspace :
  parse_inline_line "_ a_" = [mk (Str "_ a_")].
Proof. vm_compute. reflexivity. Qed.

(* ...and the brace overrides both, which is the point of the marker. *)
Example braced_keeps_the_space :
  parse_inline_line "{_ a_}" = [mk (Emph [mk (Str " a")])].
Proof. vm_compute. reflexivity. Qed.

(* Doubling is nesting, not a second construct.  This is the fact that
   makes `__` for strong a *different table*, not an extension of this
   one (`.project/260811.inline-parser.md` §0.1). *)
Example doubled_is_nested :
  parse_inline_line "__a__" = [mk (Emph [mk (Emph [mk (Str "a")])])].
Proof. vm_compute. reflexivity. Qed.

(* An opener the closer spans is abandoned: its source becomes text, and
   its content splices into the scope that closed. *)
Example abandoned_opener_becomes_text :
  parse_inline_line "_a*b_" = [mk (Emph [mk (Str "a*b")])].
Proof. vm_compute. reflexivity. Qed.

(* An opener that never closes decays the same way, merging with the text
   on both sides so no two `Str` nodes end up adjacent. *)
Example unclosed_opener_merges :
  parse_inline_line "a*b" = [mk (Str "a*b")].
Proof. vm_compute. reflexivity. Qed.

(* The three rows that only exist braced: a bare `=`, `+` or `-` is
   text.  The hyphen is the one that has to be braced for a reason
   beyond frequency -- an unbraced `-` is where smart dashes live. *)
Example mark_needs_braces :
  (parse_inline_line "=a=", parse_inline_line "{=a=}")
  = ([mk (Str "=a=")], [mk (Highlight [mk (Str "a")])]).
Proof. vm_compute. reflexivity. Qed.

Example delete_needs_braces :
  (parse_inline_line "-a-", parse_inline_line "{-a-}")
  = ([mk (Str "-a-")], [mk (Delete [mk (Str "a")])]).
Proof. vm_compute. reflexivity. Qed.

(* Its content is scanned like any other row's, and the braces belong to
   the delimiter rather than to the text. *)
Example delete_nests :
  parse_inline_line "{-a _b_-}"
  = [mk (Delete [mk (Str "a "); mk (Emph [mk (Str "b")])])].
Proof. vm_compute. reflexivity. Qed.

(* And the row round-trips through the canonical view like the others.
   `-` is a delimiter character, so a canonical `Str` holding one spells
   it escaped, which keeps `{-a-}` from reappearing out of text that only
   looked like it. *)
Example delete_ci_roundtrip :
  (ci_src (CIDelim DDelete [CIStr "a"]),
   parse_inline_line (ci_src (CIDelim DDelete [CIStr "a"])))
  = ("{-a-}", [ci_ast (CIDelim DDelete [CIStr "a"])]).
Proof. vm_compute. reflexivity. Qed.

Example hyphen_in_str_is_escaped :
  (ci_src (CIStr "a-b"), parse_inline_line (ci_src (CIStr "a-b")))
  = ("a\-b", [mk (Str "a-b")]).
Proof. vm_compute. reflexivity. Qed.

(* An empty span is not a span: a closer immediately after its opener
   does not close it. *)
Example empty_span_is_text :
  parse_inline_line "{__}" = [mk (Str "{__}")].
Proof. vm_compute. reflexivity. Qed.

(* Smart punctuation on the two characters that are not delimiters.
   Three periods are one ellipsis and a fourth is itself; a run of
   hyphens is cut by `dashes`; and both are text, so they merge with the
   text around them rather than becoming nodes. *)
Example ellipsis_and_remainder :
  (parse_inline_line "a...b", parse_inline_line "a....b")
  = ([mk (Str ("a" ++ ellipsis ++ "b"))],
     [mk (Str ("a" ++ ellipsis ++ ".b"))]).
Proof. vm_compute. reflexivity. Qed.

Example two_periods_are_text :
  parse_inline_line "a..b" = [mk (Str "a..b")].
Proof. vm_compute. reflexivity. Qed.

Example dash_runs :
  (parse_inline_line "a-b", parse_inline_line "a--b", parse_inline_line "a---b")
  = ([mk (Str "a-b")],
     [mk (Str ("a" ++ endash ++ "b"))],
     [mk (Str ("a" ++ emdash ++ "b"))]).
Proof. vm_compute. reflexivity. Qed.

(* Where the run meets the delete row, which is the one place the two
   rules interact: the closer takes the last hyphen back and the rest of
   the run is cut. *)
Example dash_run_gives_back_its_closer :
  parse_inline_line "{-a---}"
  = [mk (Delete [mk (Str ("a" ++ endash))])].
Proof. vm_compute. reflexivity. Qed.

(* With nothing open, `-}` is what is left over: two literal characters,
   and the run before them cut. *)
Example dash_run_without_an_opener :
  parse_inline_line "a---}" = [mk (Str ("a" ++ endash ++ "-}"))].
Proof. vm_compute. reflexivity. Qed.

(* Escaping is what keeps canonical text out of both rules. *)
Example escaped_runs_are_literal :
  (parse_inline_line (escape_str "a---b"), parse_inline_line (escape_str "a...b"))
  = ([mk (Str "a---b")], [mk (Str "a...b")]).
Proof. vm_compute. reflexivity. Qed.

(* Verbatim is a mode, not a row: while one is open the table is
   suppressed entirely. *)
Example verbatim_suppresses_delimiters :
  parse_inline_line "`_a_`" = [mk (Verbatim "_a_")].
Proof. vm_compute. reflexivity. Qed.

(*
Math
----

`$` and `$$` before a backtick run make the span math instead of
verbatim.
*)

Example math_inline :
  parse_inline_line "$`x`" = [mk (Math InlineMath "x")].
Proof. vm_compute. reflexivity. Qed.

Example math_display :
  parse_inline_line "$$`x`" = [mk (Math DisplayMath "x")].
Proof. vm_compute. reflexivity. Qed.

(* An unclosed run still closes at the end of the line, and it is still
   math. *)
Example math_unclosed :
  parse_inline_line "$`x" = [mk (Math InlineMath "x")].
Proof. vm_compute. reflexivity. Qed.

(* A third dollar is text: the prefix is the last two, and the extra one
   is flushed. *)
Example math_three_dollars :
  parse_inline_line "$$$`x`" = [mk (Str "$"); mk (Math DisplayMath "x")].
Proof. vm_compute. reflexivity. Qed.

(* The prefix has to be adjacent, and an escaped dollar is not a prefix
   at all -- which is why `IDollar` is a state rather than a look back
   into the text buffer, where the two would be indistinguishable. *)
Example math_needs_adjacency :
  parse_inline_line "$ `x`" = [mk (Str "$ "); mk (Verbatim "x")].
Proof. vm_compute. reflexivity. Qed.

Example math_escaped_dollar_is_verbatim :
  parse_inline_line "\$`x`" = [mk (Str "$"); mk (Verbatim "x")].
Proof. vm_compute. reflexivity. Qed.

(* Inside a run the dollar is content, as every other character is. *)
Example math_dollar_inside_verbatim :
  parse_inline_line "`$x`" = [mk (Verbatim "$x")].
Proof. vm_compute. reflexivity. Qed.

(* A dollar with no run after it is text, and canonical text escapes it,
   since `dreserved` claims it. *)
Example math_lone_dollar : parse_inline_line "$" = [mk (Str "$")].
Proof. vm_compute. reflexivity. Qed.

Example math_dollar_escapes : ci_line [CIStr "a$b"] = "a\$b".
Proof. vm_compute. reflexivity. Qed.

(*
Smart quotes
------------

Two more table rows.  What they need beyond a character and a width is
the decay: an unmatched quote is a curly character rather than its own
source, and the markers choose the side.
*)

Example squote_pair :
  parse_inline_line "'a'" = [mk (Quoted SingleQuotes [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example dquote_pair :
  parse_inline_line """a""" = [mk (Quoted DoubleQuotes [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

(* An apostrophe cannot open, so it decays: this is `DBareAfterBreak`. *)
Example apostrophe_is_not_an_opener :
  parse_inline_line "can't" = [mk (Str ("can" ++ rsquo ++ "t"))].
Proof. vm_compute. reflexivity. Qed.

Example decade_is_an_apostrophe :
  parse_inline_line "the '70s" = [mk (Str ("the " ++ rsquo ++ "70s"))].
Proof. vm_compute. reflexivity. Qed.

(* An unmatched opener decays too: to the *right* form for the single
   quote and the *left* for the double one.  The side is a property of
   the row, not of the position. *)
Example unmatched_squote_is_right :
  parse_inline_line "'a" = [mk (Str (rsquo ++ "a"))].
Proof. vm_compute. reflexivity. Qed.

Example unmatched_dquote_is_left :
  parse_inline_line "a""" = [mk (Str ("a" ++ ldquo))].
Proof. vm_compute. reflexivity. Qed.

(* And the byte a decay leaves in the buffer is not the byte the next
   quote's open rule reads.  A quote that decays writes `rsquo`; the
   source said `'`, and `dopens_after` accepts a quote and not a curly
   one, so the second `'` here opens and the third closes it.  `ilead`
   takes the source byte from `prev` for exactly this. *)
Example decay_does_not_hide_the_source_byte :
  parse_inline_line "a''b'"
  = [mk (Str ("a" ++ rsquo)); mk (Quoted SingleQuotes [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

(* The dashes rewrite the buffer the same way, and cost the same. *)
Example dash_does_not_hide_the_source_byte :
  parse_inline_line "a--'b'"
  = [mk (Str ("a" ++ endash)); mk (Quoted SingleQuotes [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

(* A marker overrides both the open rule and the side: a braced opener
   opens where an apostrophe would otherwise be meant, and an abandoned
   one decays to the left form. *)
Example marked_squote_opens :
  parse_inline_line "{'a'}" = [mk (Quoted SingleQuotes [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example marked_squote_abandoned_is_left :
  parse_inline_line "{'a" = [mk (Str (lsquo ++ "a"))].
Proof. vm_compute. reflexivity. Qed.

(* Both markers at once, the one token whose two flips compete.  The
   row's own default decides: the single quote defaults right, so the
   open marker is the flip that applies and the `}` changes nothing,
   while the double quote defaults left and the close marker wins.  The
   `}` is not consumed either way, since the token has an open marker, so
   the token still opens a scope and the brace is text after it. *)
Example marked_squote_with_close_marker_is_left :
  parse_inline_line "{'}a" = [mk (Str (lsquo ++ "}a"))].
Proof. vm_compute. reflexivity. Qed.

Example marked_dquote_with_close_marker_is_right :
  parse_inline_line "{""}a" = [mk (Str (rdquo ++ "}a"))].
Proof. vm_compute. reflexivity. Qed.

(* And it is still an opener, so a closer later in the line reaches it
   and the decay is never asked for. *)
Example marked_dquote_with_close_marker_still_opens :
  parse_inline_line "{""}a""}"
  = [mk (Quoted DoubleQuotes [mk (Str "}a")])].
Proof. vm_compute. reflexivity. Qed.

(* An ordinary row's decay is its source, and there the `}` is the one
   the token did not take: `{*}` is three characters of text, not four. *)
Example marked_strong_with_close_marker_keeps_one_brace :
  parse_inline_line "{*}" = [mk (Str "{*}")].
Proof. vm_compute. reflexivity. Qed.

(* And an escape still wins, which keeps a canonical `Str` containing a
   quote round-tripping: the quote rows are in `is_delim`, so
   `needs_escape` covers them. *)
Example escaped_quotes_are_literal :
  parse_inline_line "\'a\'" = [mk (Str "'a'")].
Proof. vm_compute. reflexivity. Qed.

Example quotes_escape_in_canonical_text :
  ci_line [CIStr "it's a ""quote"""] = "it\'s a \""quote\""".
Proof. vm_compute. reflexivity. Qed.

Example canonical_squote_source :
  ci_line [CIDelim DSQuote [CIStr "a"]] = "{'a'}".
Proof. vm_compute. reflexivity. Qed.

Example canonical_squote_roundtrip :
  parse_inline_line (ci_line [CIDelim DSQuote [CIStr "a"]])
  = ci_inlines [CIDelim DSQuote [CIStr "a"]].
Proof. vm_compute. reflexivity. Qed.

(*
Direct links
------------
*)

Definition bkids : inlines := [mk (Str "a")].

Example link_basic : parse_inline_line "[a](b)" = [mk (Link bkids (Direct "b"))].
Proof. vm_compute. reflexivity. Qed.

Example link_balanced_parens :
  parse_inline_line "[a](b(c)d)" = [mk (Link bkids (Direct "b(c)d"))].
Proof. vm_compute. reflexivity. Qed.

Example link_escaped_paren :
  parse_inline_line "[a](b\)c)" = [mk (Link bkids (Direct "b)c"))].
Proof. vm_compute. reflexivity. Qed.

(* Without a destination the brackets are text, and they merge with the
   text on both sides: `opop_str` takes back what the `[` had flushed. *)
Example bracket_literal_merges :
  parse_inline_line "z[a]x" = [mk (Str "z[a]x")].
Proof. vm_compute. reflexivity. Qed.

(* A label's non-text children stay classified when the brackets do not
   become a link, which is why the fallback cannot work from source. *)
Example bracket_literal_keeps_children :
  parse_inline_line "[_a_]x"
  = [mk (Str "["); mk (Emph [mk (Str "a")]); mk (Str "]x")].
Proof. vm_compute. reflexivity. Qed.

(* An unterminated destination is not literal source: the region turns
   literal only at the balanced `)`, so a region that never gets one
   keeps what the ordinary scan made of it.  The `[` and the `](` come
   back out of the `FKDest` scope the state opened. *)
Example dest_unterminated_is_scanned :
  para_inlines ["[unclosed](hello *a"; "b*"]
  = [mk (Str "[unclosed](hello ");
     mk (Strong [mk (Str "a"); mk SoftBreak; mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

(* The scope is a barrier as well as a container: a closer inside a
   destination may not reach an opener from before the `[`
   (`fr_barrier`). *)
Example dest_bars_an_outer_opener :
  parse_inline_line "*x [u](a* b" = [mk (Str "*x [u](a* b")].
Proof. vm_compute. reflexivity. Qed.

(* ...and only that: a delimiter opened *inside* the region closes there,
   around a link that closed inside it. *)
Example dest_inner_matching_is_ordinary :
  parse_inline_line "[u](a *b* c"
  = [mk (Str "[u](a "); mk (Strong [mk (Str "b")]); mk (Str " c")].
Proof. vm_compute. reflexivity. Qed.

(* A delimiter opened inside a label is abandoned by the close, since the
   label is a scope and the delimiter did not close inside it. *)
Example link_label_abandons_opener :
  parse_inline_line "[_a](b)_"
  = [mk (Link [mk (Str "_a")] (Direct "b")); mk (Str "_")].
Proof. vm_compute. reflexivity. Qed.

(* ...but only a `]` that *closes* abandons anything.  One whose next
   byte makes no construct is text, and its opener is still on the stack
   for a later `]` to close -- so the label runs to the second one and
   the delimiter opened before the first still closes inside it. *)
Example rbrack_without_a_construct_keeps_the_opener :
  parse_inline_line "[u]b](c)" = [mk (Link [mk (Str "u]b")] (Direct "c"))].
Proof. vm_compute. reflexivity. Qed.

Example rbrack_without_a_construct_keeps_the_scope :
  parse_inline_line "[_u]b_](c)"
  = [mk (Link [mk (Emph [mk (Str "u]b")])] (Direct "c"))].
Proof. vm_compute. reflexivity. Qed.

(* A destination crosses a line break and drops it; an unterminated one
   keeps it, since the break is then an ordinary soft break.  A `]` at a
   break is already literal: the `(` has to be the very next byte. *)
Example dest_crosses_break :
  para_inlines ["[a](b"; "c)"] = [mk (Link bkids (Direct "bc"))].
Proof. vm_compute. reflexivity. Qed.

Example dest_unterminated_keeps_break :
  para_inlines ["[a](b"; "c"]
  = [mk (Str "[a](b"); mk SoftBreak; mk (Str "c")].
Proof. vm_compute. reflexivity. Qed.

Example bracket_needs_paren_on_the_same_line :
  para_inlines ["[a]"; "(b)"]
  = [mk (Str "[a]"); mk SoftBreak; mk (Str "(b)")].
Proof. vm_compute. reflexivity. Qed.

(* The canonical spelling, and what it excludes.  An empty label is
   canonical, which is the one place a link differs from a delimiter. *)
(* Images.  The `!` is a state of its own (`IBang`), and the frame
   records the answer. *)
Example image_basic :
  parse_inline_line "![a](u)" = [mk (Image bkids (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

Example image_escaped_bang_is_a_link :
  parse_inline_line "\![a](u)" = [mk (Str "!"); mk (Link bkids (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

Example image_needs_the_bracket :
  parse_inline_line "!x" = [mk (Str "!x")].
Proof. vm_compute. reflexivity. Qed.

Example image_bang_before_image :
  parse_inline_line "!![a](u)"
  = [mk (Str "!"); mk (Image bkids (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

Example image_without_destination_is_text :
  parse_inline_line "![a]" = [mk (Str "![a]")].
Proof. vm_compute. reflexivity. Qed.

Example canonical_link_source :
  ci_line [CIStr "x"; CILink false [CIStr "a"] "b"; CIStr "y"] = "x[a](b)y".
Proof. vm_compute. reflexivity. Qed.

Example canonical_image_source :
  ci_line [CILink true [CIStr "a"] "u"] = "![a](u)".
Proof. vm_compute. reflexivity. Qed.

Example canonical_link_empty_label : ci_line [CILink false [] "u"] = "[](u)".
Proof. vm_compute. reflexivity. Qed.

Example reference_link_explicit :
  parse_inline_line "[foobar][1]" =
  [mk (Link [mk (Str "foobar")] (Reference "1"))].
Proof. vm_compute. reflexivity. Qed.

Example reference_link_collapsed :
  parse_inline_line "[link][]" =
  [mk (Link [mk (Str "link")] (Reference "link"))].
Proof. vm_compute. reflexivity. Qed.

Example reference_link_multiline_label :
  para_inlines ["[link][a and"; "b]"] =
  [mk (Link [mk (Str "link")] (Reference "a and b"))].
Proof. vm_compute. reflexivity. Qed.

Example reference_image :
  parse_inline_line "![alt][img]" =
  [mk (Image [mk (Str "alt")] (Reference "img"))].
Proof. vm_compute. reflexivity. Qed.

Example unclosed_reference_is_literal :
  parse_inline_line "[link][open" = [mk (Str "[link][open")].
Proof. vm_compute. reflexivity. Qed.

Example canonical_link_escapes_destination :
  ci_line [CILink false [CIDelim DEmph [CIStr "a"]] "u(v)\"]
  = "[{_a_}](u\(v\)\\)".
Proof. vm_compute. reflexivity. Qed.

Example canonical_link_roundtrip :
  parse_inline_line (ci_line [CILink false [CIDelim DEmph [CIStr "a"]] "u(v)\"])
  = ci_inlines [CILink false [CIDelim DEmph [CIStr "a"]] "u(v)\"].
Proof. vm_compute. reflexivity. Qed.

(* A `!` before a link is escaped, so both parsers read the rendering as
   a link rather than one of them reading an image. *)
Example bang_before_link_escaped :
  ci_line [CIStr "a!"; CILink false [CIStr "b"] "u"] = "a\![b](u)".
Proof. vm_compute. reflexivity. Qed.

Example bang_before_link_roundtrip :
  parse_inline_line (ci_line [CIStr "a!"; CILink false [CIStr "b"] "u"])
  = ci_inlines [CIStr "a!"; CILink false [CIStr "b"] "u"].
Proof. vm_compute. reflexivity. Qed.

(* Excluded: a destination that spans a line cannot come back. *)
Example link_destination_with_break_not_canonical :
  ci_ok (CILink false [CIStr "a"] "u
v") = false.
Proof. vm_compute. reflexivity. Qed.

(* The canonical reference spelling is the explicit one, and it survives
   a nested delimiter in the text exactly as a direct link does. *)
Example canonical_reference_source :
  ci_line [CIStr "x"; CIRef false [CIStr "a"] "lab"] = "x[a][lab]".
Proof. vm_compute. reflexivity. Qed.

Example canonical_reference_image_source :
  ci_line [CIRef true [CIStr "a"] "lab"] = "![a][lab]".
Proof. vm_compute. reflexivity. Qed.

Example canonical_reference_roundtrip :
  parse_inline_line (ci_line [CIRef false [CIDelim DEmph [CIStr "a"]] "lab"])
  = ci_inlines [CIRef false [CIDelim DEmph [CIStr "a"]] "lab"].
Proof. vm_compute. reflexivity. Qed.

(* Excluded, and each for its own reason: an empty label is the collapsed
   spelling, whose label comes from the text rather than the source; a
   `]` would end the label early; and a label the parser would normalize
   comes back as something else. *)
Example reference_empty_label_not_canonical :
  ci_ok (CIRef false [CIStr "a"] "") = false.
Proof. vm_compute. reflexivity. Qed.

Example reference_bracket_label_not_canonical :
  ci_ok (CIRef false [CIStr "a"] "a]b") = false.
Proof. vm_compute. reflexivity. Qed.

Example reference_unnormalized_label_not_canonical :
  ci_ok (CIRef false [CIStr "a"] "a  b") = false.
Proof. vm_compute. reflexivity. Qed.

(*
Spans
=====

`[...]` followed immediately by an attribute spec.
*)

Example span_simple :
  parse_inline_line "[s]{.a}"
  = [Node NoPos [("class", "a")] (Span [mk (Str "s")])].
Proof. vm_compute. reflexivity. Qed.

(* An empty spec still builds the node, and so does an empty label --
   `wf_inline` exempts a span from `nonempty` for exactly this reason. *)
Example span_empty_spec :
  parse_inline_line "[s]{}" = [mk (Span [mk (Str "s")])].
Proof. vm_compute. reflexivity. Qed.

Example span_empty_label :
  parse_inline_line "[]{.a}" = [Node NoPos [("class", "a")] (Span [])].
Proof. vm_compute. reflexivity. Qed.

(* The brace must be adjacent: a space between it and the `]` leaves an
   ordinary bracket, and the spec then has nothing to attach to -- the
   pending text ends in whitespace -- so it is dropped. *)
Example span_needs_adjacent_brace :
  parse_inline_line "[s] {.a}" = [mk (Str "[s] ")].
Proof. vm_compute. reflexivity. Qed.

(* A failed spec puts the region back as text and resumes the scan at the
   byte that failed, so the `*` still opens a delimiter run. *)
Example span_failed_spec_resumes :
  parse_inline_line "[s]{bad*x*y"
  = [mk (Str "[s]{bad"); mk (Strong [mk (Str "x")]); mk (Str "y")].
Proof. vm_compute. reflexivity. Qed.

(* `!` is not part of a span: the image opener decays to text. *)
Example span_ignores_image_marker :
  parse_inline_line "![x]{.a}"
  = [mk (Str "!"); Node NoPos [("class", "a")] (Span [mk (Str "x")])].
Proof. vm_compute. reflexivity. Qed.

(* And it merges with the text before it rather than leaving two
   adjacent `Str` nodes, which `wf_inlines` forbids. *)
Example span_image_marker_merges :
  parse_inline_line "a![x]{.a}"
  = [mk (Str "a!"); Node NoPos [("class", "a")] (Span [mk (Str "x")])].
Proof. vm_compute. reflexivity. Qed.

(* A second spec belongs to the span too, and classes accumulate where
   other keys overwrite: `Attr.merge` is the same rule the block layer
   uses.  There is no pending text when the second `{` arrives, so
   `oattach_list` finds the span node itself. *)
Example span_stacked_specs :
  parse_inline_line "[s]{.a}{.b}"
  = [Node NoPos [("class", "a b")] (Span [mk (Str "s")])].
Proof. vm_compute. reflexivity. Qed.

(*
Footnote references
===================

The label is source, trimmed and whitespace-collapsed by
`normalize_label`, and everything the brackets would have held is
discarded.
*)

Example note_basic :
  parse_inline_line "[^a]" = [mk (FootnoteReference "a")].
Proof. vm_compute. reflexivity. Qed.

(* The discard disposition: `*x*` is destroyed, not flattened. *)
Example note_label_is_source :
  parse_inline_line "[^*x*]" = [mk (FootnoteReference "*x*")].
Proof. vm_compute. reflexivity. Qed.

Example note_label_normalized :
  parse_inline_line "[^ a  b ]" = [mk (FootnoteReference "a b")].
Proof. vm_compute. reflexivity. Qed.

(* A label crosses a line break, and the newline is whitespace. *)
Example note_label_crosses_break :
  para_inlines ["[^a"; "b]"] = [mk (FootnoteReference "a b")].
Proof. vm_compute. reflexivity. Qed.

Example note_empty_label : parse_inline_line "[^]" = [mk (FootnoteReference "")].
Proof. vm_compute. reflexivity. Qed.

(* The verdict is final at the `]`: no destination, reference or span
   mode follows, so what comes after is ordinary text.  This is where a
   footnote reference differs from every other bracket. *)
Example note_beats_destination :
  parse_inline_line "[^a](url)"
  = [mk (FootnoteReference "a"); mk (Str "(url)")].
Proof. vm_compute. reflexivity. Qed.

Example note_beats_reference :
  parse_inline_line "[^a][b]"
  = [mk (FootnoteReference "a"); mk (Str "[b]")].
Proof. vm_compute. reflexivity. Qed.

(* A spec still attaches, because the reference is a node and
   `oattach_list` takes the last one resolved. *)
Example note_takes_attributes :
  parse_inline_line "[^a]{.c}"
  = [Node NoPos [("class", "c")] (FootnoteReference "a")].
Proof. vm_compute. reflexivity. Qed.

(* The image marker decays: `!` is text and the note is its own node. *)
Example note_after_bang :
  parse_inline_line "![^a]" = [mk (Str "!"); mk (FootnoteReference "a")].
Proof. vm_compute. reflexivity. Qed.

(* Only a `^` *immediately* inside the bracket marks one. *)
Example note_marker_must_be_first :
  parse_inline_line "[x^a]" = [mk (Str "[x^a]")].
Proof. vm_compute. reflexivity. Qed.

Example note_escaped_bracket_is_text :
  parse_inline_line "\[^a]" = [mk (Str "[^a]")].
Proof. vm_compute. reflexivity. Qed.

(* An escape defers the `]` without being decoded: the label is source. *)
Example note_escaped_close :
  parse_inline_line "[^a\]b]" = [mk (FootnoteReference "a\]b")].
Proof. vm_compute. reflexivity. Qed.

(* Unclosed, the whole region is its own source. *)
Example note_unclosed_is_text :
  parse_inline_line "[^a" = [mk (Str "[^a")].
Proof. vm_compute. reflexivity. Qed.

Example note_unclosed_after_bang_is_text :
  parse_inline_line "x![^a" = [mk (Str "x![^a")].
Proof. vm_compute. reflexivity. Qed.

(* The innermost bracket wins, as it does for links. *)
Example note_inside_brackets :
  parse_inline_line "x[y[^a]z]w"
  = [mk (Str "x[y"); mk (FootnoteReference "a"); mk (Str "z]w")].
Proof. vm_compute. reflexivity. Qed.

(* ...and a note inside a link label survives into the link. *)
Example note_inside_link :
  parse_inline_line "[a[^b]c](u)"
  = [mk (Link [mk (Str "a"); mk (FootnoteReference "b"); mk (Str "c")]
          (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

(* Canonical text escapes the marker, so a `Str` can never spell one. *)
Example note_marker_escaped_in_canonical_text :
  ci_line [CIStr "[^a]"] = "\[\^a\]".
Proof. vm_compute. reflexivity. Qed.

(* The canonical leaf is the converse direction: its source deliberately
   leaves the marker structural and its AST is the reference node. *)
Example note_canonical_leaf :
  ci_line [CINote "a"] = "[^a]" /\
  ci_inlines [CINote "a"] = [mk (FootnoteReference "a")].
Proof. vm_compute. split; reflexivity. Qed.

Example note_canonical_empty_label : ci_ok (CINote "") = true.
Proof. vm_compute. reflexivity. Qed.

(* One trailing backslash protects the would-be closer; two are consumed
   as a pair and leave the closer structural. *)
Example note_canonical_backslash_boundary :
  ci_ok (CINote "a\") = false /\ ci_ok (CINote "a\\") = true.
Proof. vm_compute. split; reflexivity. Qed.

Example note_canonical_escaped_close :
  ci_ok (CINote "a\]b") = true /\
  parse_inline_line (ci_line [CINote "a\]b"])
    = ci_inlines [CINote "a\]b"].
Proof. vm_compute. split; reflexivity. Qed.

Example note_canonical_normalized_only : ci_ok (CINote " a  b ") = false.
Proof. vm_compute. reflexivity. Qed.

Example note_canonical_roundtrip_nested :
  parse_inline_line
    (ci_line [CILink false [CIStr "a"; CINote "b"; CIStr "c"] "u"])
  = ci_inlines [CILink false [CIStr "a"; CINote "b"; CIStr "c"] "u"].
Proof. apply parse_inline_line_ci; vm_compute; reflexivity. Qed.

(*
Autolinks
=========

`<...>` with no whitespace inside: a link to its own text.  One example
below is a divergence, logged in `.project/oracle-disagreements.md`.
*)

Example auto_url :
  parse_inline_line "<http://x.com>" = [mk (UrlLink "http://x.com")].
Proof. vm_compute. reflexivity. Qed.

Example auto_email_addr :
  parse_inline_line "<me@example.com>" = [mk (EmailLink "me@example.com")].
Proof. vm_compute. reflexivity. Qed.

(* The two tests are searches, not shapes: any letter-colon anywhere is a
   url, and the email test wins when both match. *)
Example auto_scheme_is_a_search :
  parse_inline_line "<a:b>" = [mk (UrlLink "a:b")].
Proof. vm_compute. reflexivity. Qed.

Example auto_email_beats_url :
  parse_inline_line "<a:b@c>" = [mk (EmailLink "a:b@c")].
Proof. vm_compute. reflexivity. Qed.

(* An `@` in the leading position has no character before it, so
   `/[^:]@/` cannot match and the region fails both tests. *)
Example auto_leading_at_is_not_email :
  parse_inline_line "<@x>" = [mk (Str "<@x>")].
Proof. vm_compute. reflexivity. Qed.

(* Neither test matches, so the brackets are literal -- as they are for
   an empty region, which the `+` in the pattern excludes. *)
Example auto_no_scheme_is_text :
  parse_inline_line "<div>" = [mk (Str "<div>")].
Proof. vm_compute. reflexivity. Qed.

Example auto_empty_is_text :
  parse_inline_line "<>" = [mk (Str "<>")].
Proof. vm_compute. reflexivity. Qed.

(* Whitespace ends the candidate where it stands, and a second `<` starts
   a new one. *)
Example auto_space_is_text :
  parse_inline_line "<a b>" = [mk (Str "<a b>")].
Proof. vm_compute. reflexivity. Qed.

Example auto_second_bracket_restarts :
  parse_inline_line "<a<b:c>" = [mk (Str "<a"); mk (UrlLink "b:c")].
Proof. vm_compute. reflexivity. Qed.

(* Nothing in the region is dispatched, which is what makes a backtick
   inside a *successful* autolink content rather than a verbatim opener. *)
Example auto_region_is_literal :
  parse_inline_line "<a:b`c>" = [mk (UrlLink "a:b`c")].
Proof. vm_compute. reflexivity. Qed.

(* A candidate that never closes decays to the text it ate, and the scan
   resumes -- so the `<` is not a mode the rest of the line is stuck in. *)
Example auto_unclosed_decays :
  parse_inline_line "x <a:b" = [mk (Str "x <a:b")].
Proof. vm_compute. reflexivity. Qed.

(* The open divergence.  djot.js decides with a regex lookahead and, when
   it fails, scans the region as ordinary inline content: `<_a_>` is
   `&lt;<em>a</em>&gt;` there and `&lt;_a_&gt;` here.  The current state
   does not keep that interpretation, but a shadow can do so
   without replay.  The canonical view cannot produce the shape because
   `escape_str` claims the `<`; see `.project/no-backtracking.md`. *)
Example auto_failed_region_is_flat :
  parse_inline_line "<_a_>" = [mk (Str "<_a_>")].
Proof. vm_compute. reflexivity. Qed.

Example auto_failed_region_keeps_escapes :
  parse_inline_line "<a\*b>" = [mk (Str "<a\*b>")].
Proof. vm_compute. reflexivity. Qed.

(* Canonical text escapes the `<`, so a `Str` can never spell one. *)
Example auto_bracket_escaped_in_canonical_text :
  ci_line [CIStr "<a:b>"] = "\<a\:b>".
Proof. vm_compute. reflexivity. Qed.

(* The canonical leaf: one constructor for both kinds, since the kind is
   computed from the region by the same function the scanner uses. *)
Example auto_canonical_leaf :
  ci_line [CIAuto "a:b"] = "<a:b>" /\
  ci_inlines [CIAuto "a:b"] = [mk (UrlLink "a:b")] /\
  ci_inlines [CIAuto "a@b"] = [mk (EmailLink "a@b")].
Proof. vm_compute. repeat split; reflexivity. Qed.

Example auto_canonical_needs_a_kind :
  ci_ok (CIAuto "div") = false /\ ci_ok (CIAuto "a:b") = true.
Proof. vm_compute. split; reflexivity. Qed.

Example auto_canonical_excludes_region_bytes :
  ci_ok (CIAuto "") = false /\ ci_ok (CIAuto "a: b") = false /\
  ci_ok (CIAuto "a:>b") = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example auto_canonical_roundtrip_nested :
  parse_inline_line
    (ci_line [CIDelim DEmph [CIStr "a"; CIAuto "u:v"; CIStr "b"]])
  = ci_inlines [CIDelim DEmph [CIStr "a"; CIAuto "u:v"; CIStr "b"]].
Proof. apply parse_inline_line_ci; vm_compute; reflexivity. Qed.

(*
Raw inline
==========

A verbatim whose closer is followed immediately by `{=format}`.
*)

Example raw_simple :
  parse_inline_line "`<a>`{=html}" = [mk (RawInline "html" "<a>")].
Proof. vm_compute. reflexivity. Qed.

(* The run length is the verbatim's business, not the spec's. *)
Example raw_wide_fence :
  parse_inline_line "``x``{=html}" = [mk (RawInline "html" "x")].
Proof. vm_compute. reflexivity. Qed.

(* The spec preempts the delimiter row spelled with the same character:
   `{=a=}` is a highlight anywhere else, and raw content in format `a=`
   here.  This is the one place the two constructs meet, and it is why
   `ci_pair_ok` excludes the pair. *)
Example raw_beats_the_row :
  parse_inline_line "`x`{=a=}" = [mk (RawInline "a=" "x")] /\
  parse_inline_line "{=a=}" = [mk (Highlight [mk (Str "a")])].
Proof. vm_compute. split; reflexivity. Qed.

(* Only a verbatim takes one: math keeps its node and the spec is
   text. *)
Example raw_not_after_math :
  parse_inline_line "$`x`{=html}"
  = [mk (Math InlineMath "x"); mk (Str "{=html}")].
Proof. vm_compute. reflexivity. Qed.

(* The `{` must be adjacent, and the format nonempty. *)
Example raw_needs_adjacency :
  parse_inline_line "`x` {=html}"
  = [mk (Verbatim "x"); mk (Str " {=html}")].
Proof. vm_compute. reflexivity. Qed.

Example raw_needs_a_format :
  parse_inline_line "`x`{=}" = [mk (Verbatim "x"); mk (Str "{=}")].
Proof. vm_compute. reflexivity. Qed.

(* A spec that is not a candidate at all leaves the `{` to the ordinary
   attribute path, which is what every canonical delimiter after a
   verbatim depends on. *)
Example raw_non_candidate_is_a_delimiter :
  parse_inline_line "`x`{_a_}"
  = [mk (Verbatim "x"); mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example raw_non_candidate_is_an_attribute :
  parse_inline_line "`x`{.c}"
  = [Node NoPos [("class", "c")] (Verbatim "x")].
Proof. vm_compute. reflexivity. Qed.

(* A candidate that fails puts back what it read and dispatches the byte
   that failed it, so a construct inside the region still parses. *)
Example raw_failed_spec_resumes_the_scan :
  parse_inline_line "`x`{=a`b`}"
  = [mk (Verbatim "x"); mk (Str "{=a"); mk (Verbatim "b"); mk (Str "}")].
Proof. vm_compute. reflexivity. Qed.

(* A spec the line ends inside never closes; so does a bare `{`, which is
   the state the mode stands in for. *)
Example raw_unclosed_is_text :
  parse_inline_line "`x`{=htm" = [mk (Verbatim "x"); mk (Str "{=htm")] /\
  parse_inline_line "`x`{" = [mk (Verbatim "x"); mk (Str "{")].
Proof. vm_compute. split; reflexivity. Qed.

(* The exclusion the construct costs the canonical view: a verbatim may
   not be followed by the row spelled `=`, because that source is raw.
   Every other row is unaffected. *)
Example raw_pair_exclusion :
  ci_sep_ok [CIVerb "x"; CIDelim DMark [CIStr "a"]] = false /\
  ci_sep_ok [CIVerb "x"; CIDelim DEmph [CIStr "a"]] = true.
Proof. vm_compute. split; reflexivity. Qed.

(* The canonical leaf.  Unlike the autolink's, the format is a field: the
   scanner reads it as source rather than computing it from the
   content. *)
Example raw_canonical_leaf :
  ci_line [CIRaw "html" "<br>"] = "`<br>`{=html}" /\
  ci_inlines [CIRaw "html" "<br>"] = [mk (RawInline "html" "<br>")].
Proof. vm_compute. split; reflexivity. Qed.

(* The verbatim half is spelled by the verbatim machinery, so content
   that would close its own fence widens it -- and the spec still lands
   on the closing run. *)
Example raw_canonical_widens_its_fence :
  ci_line [CIRaw "html" "a`b"] = "``a`b``{=html}" /\
  parse_inline_line (ci_line [CIRaw "html" "a`b"])
    = ci_inlines [CIRaw "html" "a`b"].
Proof. vm_compute. split; reflexivity. Qed.

(* The format is read raw, so what it may not hold it may not escape
   either. *)
Example raw_canonical_format_conditions :
  ci_ok (CIRaw "" "x") = false /\
  ci_ok (CIRaw "a b" "x") = false /\
  ci_ok (CIRaw "a}b" "x") = false /\
  ci_ok (CIRaw "a`b" "x") = false /\
  ci_ok (CIRaw "html" "x") = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* And it merges with a verbatim before it exactly as a second verbatim
   would, which is the second pair the construct costs. *)
Example raw_pair_after_verbatim :
  ci_sep_ok [CIVerb "x"; CIRaw "html" "y"] = false /\
  ci_sep_ok [CIRaw "html" "y"; CIVerb "x"] = true.
Proof. vm_compute. split; reflexivity. Qed.

Example raw_canonical_roundtrip_nested :
  parse_inline_line
    (ci_line [CIDelim DEmph [CIStr "a"; CIRaw "html" "<br>"]])
  = ci_inlines [CIDelim DEmph [CIStr "a"; CIRaw "html" "<br>"]].
Proof. apply parse_inline_line_ci; vm_compute; reflexivity. Qed.

(*
The empty-span exclusion
========================

A closer looks only at the innermost matching opener.  When that opener
is empty it declines to close and becomes an opener itself, so a run of
n identical delimiters around content nests n deep, and a bare run is
literal.  These are the rows of the baseline table in
`.project/extension-decisions.md`, which the configurable delimiter table
has to keep reproducing.
*)

Example emph_run_two : parse_inline_line "__a__"
  = [mk (Emph [mk (Emph [mk (Str "a")])])].
Proof. vm_compute. reflexivity. Qed.

Example emph_run_three : parse_inline_line "___a___"
  = [mk (Emph [mk (Emph [mk (Emph [mk (Str "a")])])])].
Proof. vm_compute. reflexivity. Qed.

(* A fourth level is still nesting, so the exclusion generalizes to
   longer runs of one character. *)
Example emph_run_four : parse_inline_line "____a____"
  = [mk (Emph [mk (Emph [mk (Emph [mk (Emph [mk (Str "a")])])])])].
Proof. vm_compute. reflexivity. Qed.

(* Bare runs are literal, at every length: each closer finds an empty
   opener on top, declines, and becomes an opener that is never closed. *)
Example emph_run_bare_two : parse_inline_line "__" = [mk (Str "__")].
Proof. vm_compute. reflexivity. Qed.

Example emph_run_bare_four : parse_inline_line "____" = [mk (Str "____")].
Proof. vm_compute. reflexivity. Qed.

(* Unbalanced runs: the surplus stays literal on the side that has it. *)
Example emph_run_unbalanced_left : parse_inline_line "__a_"
  = [mk (Str "_"); mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example emph_run_unbalanced_right : parse_inline_line "_a__"
  = [mk (Emph [mk (Str "a")]); mk (Str "_")].
Proof. vm_compute. reflexivity. Qed.

(*
Inline attributes
=================

A spec attaches to the run of text before it.  The table in
.project/260811.inline-parser.md is the measured source for these.
*)

Example attr_on_word :
  parse_inline_line "foo{.a}"
  = [Node NoPos [("class", "a")] (Str "foo")].
Proof. vm_compute. reflexivity. Qed.

(* The split is at the last whitespace, so only the final word takes the
   spec -- and an attributed `Str` therefore never contains a space. *)
Example attr_splits_at_last_space :
  parse_inline_line "foo bar{.a}"
  = [mk (Str "foo "); Node NoPos [("class", "a")] (Str "bar")].
Proof. vm_compute. reflexivity. Qed.

Example attr_punctuation_does_not_split :
  parse_inline_line "a-b{.a}"
  = [Node NoPos [("class", "a")] (Str "a-b")].
Proof. vm_compute. reflexivity. Qed.

(* Parentheses are not a span: the spec still lands on the last word. *)
Example attr_parens_are_not_a_span :
  parse_inline_line "(some text){.attr}"
  = [mk (Str "(some "); Node NoPos [("class", "attr")] (Str "text)")].
Proof. vm_compute. reflexivity. Qed.

(* Adjacency: a space before the brace means there is no last word, and
   the spec is dropped. *)
Example attr_needs_adjacency :
  parse_inline_line "foo {.a}" = [mk (Str "foo ")].
Proof. vm_compute. reflexivity. Qed.

(* An empty spec attaches nothing, and the text stays one run. *)
Example attr_empty_spec :
  parse_inline_line "foo{}bar" = [mk (Str "foobar")].
Proof. vm_compute. reflexivity. Qed.

(* `{` before a delimiter character is a braced delimiter, never a spec,
   even when the contents would have parsed as attributes. *)
Example attr_brace_delimiter_wins :
  parse_inline_line "a{_x=y_}"
  = [mk (Str "a"); mk (Emph [mk (Str "x=y")])].
Proof. vm_compute. reflexivity. Qed.

(* A failed spec resumes the scan at the byte that failed, as a span
   does. *)
Example attr_failed_spec_resumes :
  parse_inline_line "x{bad*y*z"
  = [mk (Str "x{bad"); mk (Strong [mk (Str "y")]); mk (Str "z")].
Proof. vm_compute. reflexivity. Qed.

(* With no pending text the spec decorates the node just emitted. *)
Example attr_on_node :
  parse_inline_line "*e*{.a}"
  = [Node NoPos [("class", "a")] (Strong [mk (Str "e")])].
Proof. vm_compute. reflexivity. Qed.

(* The immediately preceding *node*, not the innermost one: a byte of
   text after the close puts the word back in the way. *)
Example attr_on_node_loses_to_text :
  parse_inline_line "*e*w{.a}"
  = [mk (Strong [mk (Str "e")]); Node NoPos [("class", "a")] (Str "w")].
Proof. vm_compute. reflexivity. Qed.

(* An empty spec builds no wrapper but still vanishes, which is what
   `[l](u){}` needs. *)
Example attr_empty_spec_on_node :
  parse_inline_line "[l](u){}"
  = [mk (Link [mk (Str "l")] (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

(* Nothing at all before it and the spec is gone, source included.  A
   line that is nothing else resolves to no inlines. *)
Example attr_with_nothing_before_vanishes :
  parse_inline_line "{#i} x"
  = [mk (Str " x")].
Proof. vm_compute. reflexivity. Qed.

Example attr_alone_leaves_nothing :
  parse_inline_line "{#i}" = [].
Proof. vm_compute. reflexivity. Qed.

(* A scope holding nothing else closes onto nothing
   (`<strong></strong>`): the empty-scope test runs on the items, before
   attachment. *)
Example attr_alone_in_scope_closes_empty :
  parse_inline_line "*{#i}*" = [mk (Strong [])].
Proof. vm_compute. reflexivity. Qed.

(* An opener that never closed is text by the time the spec attaches, so
   the last word reaches back over it.  This is the whole point of
   deferring: at the `}` the `*` is still an open scope and the answer is
   not yet available. *)
Example attr_reaches_over_an_unclosed_opener :
  parse_inline_line "a *b{.c}o"
  = [mk (Str "a "); Node NoPos [("class", "c")] (Str "*b"); mk (Str "o")].
Proof. vm_compute. reflexivity. Qed.

(* And over text flushed before that opener was even pushed, which is
   what rules out repairing this locally when the scope is abandoned. *)
Example attr_reaches_past_the_scope :
  parse_inline_line "az*b{.c}o"
  = [Node NoPos [("class", "c")] (Str "az*b"); mk (Str "o")].
Proof. vm_compute. reflexivity. Qed.

(* Two of them, and a bracket, decay the same way. *)
Example attr_reaches_over_nested_openers :
  parse_inline_line "a *_b{.c}o"
  = [mk (Str "a "); Node NoPos [("class", "c")] (Str "*_b"); mk (Str "o")].
Proof. vm_compute. reflexivity. Qed.

Example attr_reaches_over_a_bracket :
  parse_inline_line "a [x{.c}o"
  = [mk (Str "a "); Node NoPos [("class", "c")] (Str "[x"); mk (Str "o")].
Proof. vm_compute. reflexivity. Qed.

(* When the opener does close it is a node, and the spec stops there. *)
Example attr_stops_at_a_closed_opener :
  parse_inline_line "a b*c*d{.e}f"
  = [mk (Str "a b"); mk (Strong [mk (Str "c")]);
     Node NoPos [("class", "e")] (Str "d"); mk (Str "f")].
Proof. vm_compute. reflexivity. Qed.

Example attr_inside_a_closed_opener :
  parse_inline_line "a *b{.c}o*"
  = [mk (Str "a ");
     mk (Strong [Node NoPos [("class", "c")] (Str "b"); mk (Str "o")])].
Proof. vm_compute. reflexivity. Qed.

(* An empty spec still resolves to nothing, and the run it sat between is
   rejoined: `oresolve_go`'s flag is what stops the two halves ending up
   adjacent. *)
Example attr_empty_spec_rejoins :
  parse_inline_line "foo{}bar" = [mk (Str "foobar")].
Proof. vm_compute. reflexivity. Qed.

(* A spec first inside a scope that closes: the scope's tip is empty, the
   spec goes, and the scope keeps the rest. *)
Example attr_first_in_a_closing_scope :
  parse_inline_line "a *{.c}b*"
  = [mk (Str "a "); mk (Strong [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

Example attr_alone_in_a_closing_scope :
  parse_inline_line "a *{.c}*"
  = [mk (Str "a "); mk (Strong [])].
Proof. vm_compute. reflexivity. Qed.

(* A spec inside a bracket that decays.  Nothing resolves at the `]`
   here: the byte after it is not one of the three that close a bracket,
   so the scope stays open and `oflatten` abandons it at the end of the
   paragraph, merging the opener's `[` into the `Str` the spec then
   attaches to. *)
Example attr_inside_a_decaying_bracket :
  parse_inline_line "[a{.c}b] c"
  = [Node NoPos [("class", "c")] (Str "[a"); mk (Str "b] c")].
Proof. vm_compute. reflexivity. Qed.

(* The break is a byte of the spec, so the machine is fed it and the
   spec closes on the next line.  Nothing separates the two lines in the
   output: the break was inside the spec's source. *)
Example attr_spec_crosses_a_break :
  para_inlines ["hi{#id .class"; "key=""value""}"]
  = [Node NoPos [("id", "id"); ("class", "class"); ("key", "value")]
       (Str "hi")].
Proof. vm_compute. reflexivity. Qed.

(* A comment is a spec that commits nothing, so a multi-line one is a
   spec that attaches nothing -- and the text before it ends in a space,
   which is where a spec is dropped rather than attached. *)
Example attr_comment_crosses_a_break :
  para_inlines ["Foo bar {% This is a comment, spanning"; "multiple lines %} baz."]
  = [mk (Str "Foo bar  baz.")].
Proof. vm_compute. reflexivity. Qed.

(* A spec the paragraph ended inside is its own source, and the breaks it
   spanned come back as `SoftBreak`s: a `Str` holding a newline renders
   the same but does not survive a reparse, so the buffer cannot go back
   whole.  This is `bsplit_nl`, the destination's rule. *)
Example attr_unclosed_spec_keeps_its_breaks :
  para_inlines ["{a=x"; "hello"]
  = [mk (Str "{a=x"); mk SoftBreak; mk (Str "hello")].
Proof. vm_compute. reflexivity. Qed.

(* A failed attribute candidate keeps an ordinary-inline interpretation
   current beside the spec, with attribute recognition disabled there.
   Choosing that interpretation at the end makes the quote smart and lets
   the delimiter pair interact normally, without replaying any source. *)
Example attr_unclosed_spec_keeps_ordinary_scan :
  parse_inline_line "x{a=""*b*"""
  = [mk (Str "x{a=");
     mk (Quoted DoubleQuotes [mk (Strong [mk (Str "b")])])].
Proof. vm_compute. reflexivity. Qed.

(* And it is cut at slice boundaries (`islice_end`), so a run inside the
   candidate never grows into one token: `-` and `-` are two hyphens
   rather than an en dash, where the same two bytes outside a candidate
   are one. *)
Example attr_failed_spec_cuts_a_run :
  parse_inline_line "x{a--" = [mk (Str "x{a--")].
Proof. vm_compute. reflexivity. Qed.

(*
The key connective, pinned
==========================

The three tables of `.project/keyed-blocks.md` section 3, one example
per row.  `key_point` is the split rule of 3.1, `key_label_ok` the
one-inline rule of 3.2, and `key_split` the two together, which is what
the block layer asks.
*)

(* 3.1, the split rule *)

Example key_first_colon : key_point "foo: bar" = Some ("foo", "bar").
Proof. vm_compute. reflexivity. Qed.

(* Nothing is decided by whether the run closes: an unclosed one runs to
   the end of the line, so the colon is inside the span either way. *)
Example key_inside_verbatim :
  key_point "`a: b` is how you write it" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_after_verbatim :
  key_point "`code`: a description" = Some ("`code`", "a description").
Proof. vm_compute. reflexivity. Qed.

Example key_inside_link : key_point "[see: here](x) is the reference" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_after_link :
  key_point "[see](x): the reference" = Some ("[see](x)", "the reference").
Proof. vm_compute. reflexivity. Qed.

Example key_after_brace :
  key_point "foo{#my-foo}: bar" = Some ("foo{#my-foo}", "bar").
Proof. vm_compute. reflexivity. Qed.

(* The first colon reads as part of a title, so the scan goes on. *)
Example key_after_quoted_value :
  key_point "x{title=""a: b""}y: z" = Some ("x{title=""a: b""}y", "z").
Proof. vm_compute. reflexivity. Qed.

(* A quotation mark pairs like any other delimiter, so these two are the
   same construct open and closed. *)
Example key_inside_quotation : key_point """foo: bar"" and more" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_after_quotation :
  key_point """foo"": bar" = Some ("""foo""", "bar").
Proof. vm_compute. reflexivity. Qed.

(* Declined although splitting would have been harmless: the `_` is
   unmatched, but at the colon the scan cannot know that yet. *)
Example key_inside_emphasis : key_point "_a: b_" = None.
Proof. vm_compute. reflexivity. Qed.

(* 9.1.  A delimiter run against the colon is undecided rather than
   open: settling it needs the byte the colon occupies, and it settles
   as an opener there and as literal text at a line's end.  Alone the
   label would be `a*`; in place the `*` opens the span that swallows
   the colon.  A run that *closes* consults no following byte, which is
   why `key_after_quotation` is unaffected. *)
Example key_pending_delimiter :
  (key_point "a*: b*", key_point "a_: b_", key_point "a^: b^",
   key_point "a~: b~", key_point "a"": b""")
  = (None, None, None, None, None).
Proof. vm_compute. reflexivity. Qed.

Example key_needs_adjacency : key_point "foo : bar" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_needs_space_after : key_point "foo:bar" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_tab_is_not_a_space : key_point "foo:	bar" = None.
Proof. vm_compute. reflexivity. Qed.

(* The value may be empty, which is the two-line spelling's key line. *)
Example key_line_final : key_point "foo:" = Some ("foo", "").
Proof. vm_compute. reflexivity. Qed.

(* One split per line: what follows is the value's text, colons and all. *)
Example key_one_per_line : key_point "foo: bar: baz" = Some ("foo", "bar: baz").
Proof. vm_compute. reflexivity. Qed.

(* An escaped colon is text, and a pending backslash is not a closed
   state, so the rule needs no case for it. *)
Example key_escaped_colon : key_point "foo\: bar:" = Some ("foo\: bar", "").
Proof. vm_compute. reflexivity. Qed.

Example key_empty_label : key_point ":" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_leading_colon : key_point ": term" = None.
Proof. vm_compute. reflexivity. Qed.

(* The line is normalised, so a container prefix's indentation cannot
   change the answer. *)
Example key_ignores_indentation : key_point "    foo: bar" = key_point "foo: bar".
Proof. vm_compute. reflexivity. Qed.

(* 3.2, the one-inline rule.  The counts are of the resolved list, which
   is why the first five are one node and not two or three. *)

Example key_label_run : key_label_ok "foo" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_phrase : key_label_ok "foo bar baz" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_apostrophe : key_label_ok "it's" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_dash : key_label_ok "a -- b" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_escape : key_label_ok "foo\: bar" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_verbatim : key_label_ok "`code`" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_link : key_label_ok "[see](x)" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_quotation : key_label_ok """foo""" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_strong : key_label_ok "*bold*" = true.
Proof. vm_compute. reflexivity. Qed.

(* An attribute is not a second element: it rides on the element in
   front of it. *)
Example key_label_attributed : key_label_ok "x{title=""a""}" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_two_kinds : key_label_ok "x`y`" = false.
Proof. vm_compute. reflexivity. Qed.

(* Two runs, and they cannot merge: only one carries the title. *)
Example key_label_split_attribute : key_label_ok "x{title=""a: b""}y" = false.
Proof. vm_compute. reflexivity. Qed.

Example key_label_embedded_markup : key_label_ok "the `--flag` option" = false.
Proof. vm_compute. reflexivity. Qed.

(* An attribute spec that finds nothing to decorate vanishes, and its
   neighbours merge, so the label is the one run they make. *)
Example key_label_vanished_spec : key_label_ok "a {#i}b" = true.
Proof. vm_compute. reflexivity. Qed.

(* 3.6, where a line does not read as it looks *)

Example key_prose_colon :
  key_split "Note: this matters." = Some ("Note", "this matters.").
Proof. vm_compute. reflexivity. Qed.

Example key_declines_embedded_markup :
  key_split "the `--flag` option: what it does" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_declines_split_attribute :
  key_split "x{title=""a: b""}y: z" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_second_colon_splits :
  key_split "see http://x: it works" = Some ("see http://x", "it works").
Proof. vm_compute. reflexivity. Qed.

(* A spec with nothing before it leaves no inline at all, so a label that
   is nothing else is not one inline and the line is not a key.  This is
   `key_label_ok` at work: 3.2's advice, to put an attribute meant for
   the keyed node on its own line above, follows from it. *)
Example key_leading_brace_is_no_key :
  key_split "{#i}: bar" = None.
Proof. vm_compute. reflexivity. Qed.

(* With something after it the spec attaches and the label is that. *)
Example key_leading_brace_attaches :
  key_split "{#i}foo: bar" = Some ("{#i}foo", "bar").
Proof. vm_compute. reflexivity. Qed.
