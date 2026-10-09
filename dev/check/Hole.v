(* ai-disclosure: ai-generated *)

(* Holes, `` %`e` `` (`.project/261009.plan.backtick-holes.md`): each
   decision, read with the setting on and off. *)

From Stdlib Require Import String List.
From DjotV Require Import Ast Inline Profile Strings Line Parser Config Reparse
  Render Step Document.
Import ListNotations.
Open Scope string_scope.

Definition hole_table : dtable :=
  DTable (with_holes true djot_config) eq_refl.
Local Notation Parse := (@InlineScan.parse_inline_line hole_table).
Local Notation Lines := (@InlineScan.para_inlines hole_table).

(* Off in djot: a `%` before a code span is text, and the span code. *)
Example off_in_djot :
  (parse_inline_line "a %`x` b", parse_inline_line "a %{.c} b")
  = ([mk (Str "a %"); mk (Verbatim "x"); mk (Str " b")],
     [mk (Str "a "); Node NoPos [("class", "c")] (Str "%"); mk (Str " b")]).
Proof. vm_compute. reflexivity. Qed.

(* E1: a `%` directly before a code span makes it a hole, and the
   payload is the span's, longer runs and trimming included. *)
Example a_hole :
  (Parse "a %`x` b", Parse "%``f `A``", Parse "%`` `A` ``")
  = ([mk (Str "a "); mk (Hole "x"); mk (Str " b")],
     [mk (Hole "f `A")],
     [mk (Hole "`A`")]).
Proof. vm_compute. reflexivity. Qed.

(* E3: the payload is verbatim, braces and backslashes included. *)
Example verbatim_payload :
  (Parse "%`{r with x = 1}`", Parse "%`print_string ""\n""`", Parse "%`a\`")
  = ([mk (Hole "{r with x = 1}")], [mk (Hole "print_string ""\n""")],
     [mk (Hole "a\")]).
Proof. vm_compute. reflexivity. Qed.

(* E2: an unclosed hole runs to the end of its paragraph, as an unclosed
   code span does, and crosses a soft break, which is in its payload. *)
Example unclosed_runs_on :
  (Parse "a %`x and y", Lines ["Total: %`f"; "x"], Lines ["a %`f"; "x` b"])
  = ([mk (Str "a "); mk (Hole "x and y")],
     [mk (Str "Total: "); mk (Hole "f
x")],
     [mk (Str "a "); mk (Hole "f
x"); mk (Str " b")]).
Proof. vm_compute. reflexivity. Qed.

(* E4: an empty payload is a hole, for the consumer to reject. *)
Example empty_holes :
  (Parse "%``", Parse "%`` ``")
  = ([mk (Hole "")], [mk (Hole " ")]).
Proof. vm_compute. reflexivity. Qed.

(* E5: a raw format after a hole is text, as after math. *)
Example raw_suffix_is_text :
  Parse "%`x`{=html}" = [mk (Hole "x"); mk (Str "{=html}")].
Proof. vm_compute. reflexivity. Qed.

(* E6: attributes after a hole are the hole's. *)
Example hole_attributes :
  Parse "%`x`{.c}" = [Node NoPos [("class", "c")] (Hole "x")].
Proof. vm_compute. reflexivity. Qed.

(* E7: only a bare `%` right before the backticks is a prefix; `%{` is
   what it is with the setting off. *)
Example not_a_prefix :
  (Parse "a % `x`", Parse "\%`x`", Parse "a %{.c} b")
  = ([mk (Str "a % "); mk (Verbatim "x")],
     [mk (Str "%"); mk (Verbatim "x")],
     [mk (Str "a "); Node NoPos [("class", "c")] (Str "%"); mk (Str " b")]).
Proof. vm_compute. reflexivity. Qed.

(* Places a `%` is not read at all. *)
Example not_an_opener :
  (Parse "``%`x``", Parse "[a](%`u`)", Parse "<http://a/%`b`>")
  = ([mk (Verbatim "%`x")],
     [mk (Link [mk (Str "a")] (Direct "%`u`"))],
     [mk (UrlLink "http://a/%`b`")]).
Proof. vm_compute. reflexivity. Qed.

(* E8: no kinds: `%*` and `%?` read as they do with the setting off. *)
Example no_kinds :
  (Parse "%*`x`", Parse "%?`x`", Parse "%*`x`*")
  = ([mk (Str "%*"); mk (Verbatim "x")],
     [mk (Str "%?"); mk (Verbatim "x")],
     [mk (Str "%"); mk (Strong [mk (Verbatim "x")])]).
Proof. vm_compute. reflexivity. Qed.

(* A hole has a code span's priority: what opens first wins. *)
Example code_span_priority :
  (Parse "*a %`b* c`", Parse "`d %`e` f`")
  = ([mk (Str "*a "); mk (Hole "b* c")],
     [mk (Verbatim "d %"); mk (Str "e"); mk (Verbatim " f")]).
Proof. vm_compute. reflexivity. Qed.

(* A `%` inside a failed attribute spec still prefixes the code span
   after it, as a `$` does. *)
Example prefix_in_failed_spec :
  (Parse "a{%`x`", Parse "a{$`x`")
  = ([mk (Str "a{"); mk (Hole "x")],
     [mk (Str "a{"); mk (Math InlineMath "x")]).
Proof. vm_compute. reflexivity. Qed.

(* E13: a hole's text is its expression, as math's is its formula. *)
Example hole_text :
  (inlines_text (Parse "Total %`n`"), inlines_text (Parse "a$`x`"))
  = ("Total n", "ax").
Proof. vm_compute. reflexivity. Qed.

(* The located scan's range covers the sigil and both backtick runs. *)
Definition hole_range (s : string) : option (nat * nat) :=
  let lines := line_table s in
  match @parse_blocks_located hole_table djot_bconfig s with
  | [Node _ _ (Para [_; i])] | [Node _ _ (Para [i])] =>
      match node_provenance i with
      | Some p =>
          match resolve_spot lines (span_start (node_span p)),
                resolve_spot lines (span_stop (node_span p)) with
          | Some lo, Some hi => Some (source_byte lo, source_byte hi)
          | _, _ => None
          end
      | None => None
      end
  | _ => None
  end.

Example hole_located_ranges :
  (hole_range "%`x`", hole_range "ab %``x``")
  = (Some (0, 4), Some (3, 9)).
Proof. vm_compute. reflexivity. Qed.

(* A hole is outside the canonical view, as math is, so its own spelling
   is checked here: rendering a parsed document and parsing it again gives
   the same blocks. *)
Definition hole_blocks (s : string) : blocks :=
  Profile.parse_profile_blocks (Profile hole_table djot_bconfig) s.

Definition hole_again (s : string) : blocks :=
  hole_blocks (@Render.render_djot hole_table djot_bconfig (hole_blocks s)).

Definition hole_samples : list string :=
  ["a %`x` b"; "%`{r with x = 1}`"; "%`a\`"; "%``f `A``"; "%`` `A` ``";
   "a %`f
x` b"; "50\% and %`x`{.c}"; "*a %`b* c`"; "a %`unclosed";
   "a % `x` and \%`y`"; "%``"].

Example holes_render_back :
  map hole_again hole_samples = map hole_blocks hole_samples.
Proof. vm_compute. reflexivity. Qed.
