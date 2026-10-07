(* ai-disclosure: ai-generated *)

(* Holes, `%{e}` (`.project/261007.plan.holes.md`): every row of the
   spec's examples, read with the setting on and off. *)

From Stdlib Require Import String List.
From DjotV Require Import Ast Inline Profile Strings Line Parser Config Reparse
  Render Step.
Import ListNotations.
Open Scope string_scope.

Definition hole_table : dtable :=
  DTable (with_holes true djot_config) eq_refl.
Local Notation Parse := (@InlineScan.parse_inline_line hole_table).
Local Notation Lines := (@InlineScan.para_inlines hole_table).

(* Off in djot: the bytes read as they always have. *)
Example off_in_djot :
  (parse_inline_line "a %{x} b", parse_inline_line "a %{.c} b")
  = ([mk (Str "a %{x} b")],
     [mk (Str "a "); Node NoPos [("class", "c")] (Str "%"); mk (Str " b")]).
Proof. vm_compute. reflexivity. Qed.

Example a_hole :
  (Parse "a %{x} b", Parse "%{ f x }", Parse "%{x}")
  = ([mk (Str "a "); mk (Hole "x"); mk (Str " b")],
     [mk (Hole " f x ")],
     [mk (Hole "x")]).
Proof. vm_compute. reflexivity. Qed.

(* D2: the closer is the brace that returns the depth to zero. *)
Example brace_depth :
  (Parse "%{ {r with x = 1} }", Parse "%{a{b{c}}d}")
  = ([mk (Hole " {r with x = 1} ")], [mk (Hole "a{b{c}}d")]).
Proof. vm_compute. reflexivity. Qed.

(* D3: `%{` wins over an attribute block. *)
Example hole_not_attributes :
  (Parse "a %{.c} b", Parse "foo%{#id}")
  = ([mk (Str "a "); mk (Hole ".c"); mk (Str " b")],
     [mk (Str "foo"); mk (Hole "#id")]).
Proof. vm_compute. reflexivity. Qed.

(* D6: an empty or blank payload is a hole, for the consumer to reject.
   Escaped, the `%` is text and `{}` an empty attribute block, which djot
   drops. *)
Example empty_holes :
  (Parse "%{}", Parse "%{  }", Parse "\%{}")
  = ([mk (Hole "")], [mk (Hole "  ")], [mk (Str "%")]).
Proof. vm_compute. reflexivity. Qed.

(* D7: `\{`, `\}` and `\\` are escapes and do not count; any other
   backslash is kept. *)
Example escapes :
  (Parse "%{ print_string ""\}"" }", Parse "%{a\{b}", Parse "%{""\n""}",
   Parse "%{a\\}")
  = ([mk (Hole " print_string ""}"" ")], [mk (Hole "a{b")],
     [mk (Hole """\n""")], [mk (Hole "a\")]).
Proof. vm_compute. reflexivity. Qed.

(* D8: places a `%{` does not open. *)
Example not_an_opener :
  (Parse "\%{x}", Parse "`%{x}`", Parse "[a](%{u})", Parse "<http://a/%{b}>")
  = ([mk (Str "%{x}")], [mk (Verbatim "%{x}")],
     [mk (Link [mk (Str "a")] (Direct "%{u}"))],
     [mk (UrlLink "http://a/%{b}")]).
Proof. vm_compute. reflexivity. Qed.

(* D9: a hole is always closed, and a closed one wins over what it
   overlaps.  With verbatim, whichever opens first wins. *)
Example unclosed_is_text :
  (Parse "a %{x", Lines ["Total: %{ f"], Parse "%{ a `b")
  = ([mk (Str "a %{x")], [mk (Str "Total: %{ f")],
     [mk (Str "%{ a "); mk (Verbatim "b")]).
Proof. vm_compute. reflexivity. Qed.

Example closed_hole_wins :
  (Parse "*a %{b* c}", Parse "[a %{b](u) c}")
  = ([mk (Str "*a "); mk (Hole "b* c")],
     [mk (Str "[a "); mk (Hole "b](u) c")]).
Proof. vm_compute. reflexivity. Qed.

Example holes_and_verbatim :
  (Parse "`a %{b` c}", Parse "%{ f ""`"" }", Parse "%{ a `b } c")
  = ([mk (Verbatim "a %{b"); mk (Str " c}")],
     [mk (Hole " f ""`"" ")],
     [mk (Hole " a `b "); mk (Str " c")]).
Proof. vm_compute. reflexivity. Qed.

(* D4: a hole crosses a soft break, which is part of its payload. *)
Example across_lines :
  Lines ["a %{ x"; "y } b"]
  = [mk (Str "a "); mk (Hole " x
y "); mk (Str " b")].
Proof. vm_compute. reflexivity. Qed.

(* A hole takes attributes like any inline. *)
Example hole_attributes :
  Parse "%{x}{.c}" = [Node NoPos [("class", "c")] (Hole "x")].
Proof. vm_compute. reflexivity. Qed.

(* The located scan's range covers the sigil and both braces. *)
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
  (hole_range "%{x}", hole_range "ab %{\}}")
  = (Some (0, 4), Some (3, 8)).
Proof. vm_compute. reflexivity. Qed.

(* A hole is outside the canonical view, as math is, so its own spelling
   is checked here: rendering a parsed document and parsing it again gives
   the same blocks. *)
Definition hole_blocks (s : string) : blocks :=
  Profile.parse_profile_blocks (Profile hole_table djot_bconfig) s.

Definition hole_again (s : string) : blocks :=
  hole_blocks (@Render.render_djot hole_table djot_bconfig (hole_blocks s)).

Definition hole_samples : list string :=
  ["a %{x} b"; "%{ {r with x = 1} }"; "%{a\\}"; "%{ print ""\}"" }";
   "a %{ x
y } b"; "50\% and %{x}{.c}"; "*a %{b* c}"; "%{\{}"].

Example holes_render_back :
  map hole_again hole_samples = map hole_blocks hole_samples.
Proof. vm_compute. reflexivity. Qed.
