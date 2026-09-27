(* ai-disclosure: autonomous *)

From Stdlib Require Import String List.
From DjotV Require Import Ast Inline Profile Strings Line Parser Config Reparse.
Import ListNotations.
Open Scope string_scope.

Definition dollar_only_table : dtable :=
  DTable (with_dollar_math true (with_math false djot_config)) eq_refl.
Local Notation Parse := (@InlineScan.parse_inline_line dollar_only_table).

Example inline_and_display_dollars :
  (Parse "$x+1$", Parse "x $$y$$ z")
  = ([mk (Math InlineMath "x+1")],
     [mk (Str "x "); mk (Math DisplayMath "y"); mk (Str " z")]).
Proof. vm_compute. reflexivity. Qed.

Example whitespace_and_digit_limits :
  (Parse "$ x $", Parse "$x $", Parse "It costs $5 and $10.",
   Parse "To split $100 in half, we calculate $100/2$")
  = ([mk (Str "$ x $")], [mk (Str "$x $")],
     [mk (Str "It costs $5 and $10.")],
     [mk (Str "To split $100 in half, we calculate ");
      mk (Math InlineMath "100/2")]).
Proof. vm_compute. reflexivity. Qed.

Example failed_closer_restarts_at_the_same_dollar :
  (Parse "x$y$z", Parse "$a$1b$", Parse "$a$$b$")
  = ([mk (Str "x"); mk (Math InlineMath "y"); mk (Str "z")],
     [mk (Str "$a"); mk (Math InlineMath "1b")],
     [mk (Math InlineMath "a"); mk (Math InlineMath "b")]).
Proof. vm_compute. reflexivity. Qed.

Example verbatim_math_content_and_escapes :
  (Parse "$a*b*c$", Parse "$a\$b$", Parse "$\{x\}$", Parse "\$x$")
  = ([mk (Math InlineMath "a*b*c")],
     [mk (Math InlineMath "a\$b")],
     [mk (Math InlineMath "\{x\}")],
     [mk (Str "$x$")]).
Proof. vm_compute. reflexivity. Qed.

Example display_runs_and_empty_content :
  (Parse "$$a$$b$$", Parse "$$x$", Parse "$$$x$$$", Parse "$$$$",
   Parse "$$x$$$", Parse "$$x$$$y$$")
  = ([mk (Math DisplayMath "a"); mk (Str "b$$")],
     [mk (Str "$$x$")], [mk (Str "$$$x$$$")],
     [mk (Str "$$$$")], [mk (Str "$$x$$$")],
     [mk (Math DisplayMath "x$$$y")]).
Proof. vm_compute. reflexivity. Qed.

Example math_overlaps_other_inline_constructs :
  (Parse "*a $b* c$", Parse "[a $b](u) c$", Parse "`a $b` c$",
   Parse "$a `b$", Parse "$a *b* c")
  = ([mk (Str "*a "); mk (Math InlineMath "b* c")],
     [mk (Str "[a "); mk (Math InlineMath "b](u) c")],
     [mk (Verbatim "a $b"); mk (Str " c$")],
     [mk (Math InlineMath "a `b")],
     [mk (Str "$a "); mk (Strong [mk (Str "b")]); mk (Str " c")]).
Proof. vm_compute. reflexivity. Qed.

Example github_backtick_form_and_fallback :
  (Parse "$`x`$", Parse "$``a`b``$", Parse "$`x` y")
  = ([mk (Math InlineMath "x")], [mk (Math InlineMath "a`b")],
     [mk (Str "$"); mk (Verbatim "x"); mk (Str " y")]).
Proof. vm_compute. reflexivity. Qed.

Example djot_math_consumes_optional_trailing_dollar :
  @InlineScan.parse_inline_line markdown_like_table "$`x`$"
  = [mk (Math InlineMath "x")].
Proof. vm_compute. reflexivity. Qed.

Example display_math_crosses_soft_breaks :
  @InlineScan.para_inlines dollar_only_table ["$$"; "x^2"; "$$"]
  = [mk (Math DisplayMath "
x^2
")].
Proof. vm_compute. reflexivity. Qed.

Example unclosed_math_stops_at_paragraph_boundary :
  (@InlineScan.para_inlines dollar_only_table ["$x"],
   @InlineScan.para_inlines dollar_only_table ["$$"; "x^2"])
  = ([mk (Str "$x")],
     [mk (Str "$$"); mk SoftBreak; mk (Str "x^2")]).
Proof. vm_compute. reflexivity. Qed.

Definition math_range (s : string) : option (nat * nat) :=
  let lines := line_table s in
  match @parse_blocks_located dollar_only_table djot_bconfig s with
  | [Node _ _ (Para [i])] =>
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

Example dollar_math_located_ranges_include_delimiters :
  (math_range "$x$", math_range "$$x$$", math_range "$`x`$")
  = (Some (0, 3), Some (0, 5), Some (0, 5)).
Proof. vm_compute. reflexivity. Qed.

Example multiline_display_math_range :
  math_range "$$
x^2
$$" = Some (0, 9).
Proof. vm_compute. reflexivity. Qed.
