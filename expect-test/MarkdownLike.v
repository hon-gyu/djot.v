(* ai-disclosure: autonomous *)

From Stdlib Require Import String.
From DjotV Require Import Profile Html.

Open Scope string_scope.

Compute render_html (parse_profile_doc markdown_like_profile
  "**strong** and _emphasis_").

Compute render_html (parse_profile_doc markdown_like_profile
  "# heading
continuation").

Compute render_html (parse_profile_doc markdown_like_profile
  "a---b and ...").

Compute render_html (parse_profile_doc markdown_like_profile
  "```=html
<b>x</b>
```").
