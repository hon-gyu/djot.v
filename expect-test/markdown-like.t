  $ ss () {
  >   {
  >     printf '%s\n' \
  >       '(* ai-disclosure: ai-generated *)' \
  >       'From Stdlib Require Import String.' \
  >       'From DjotV Require Import Profile Html.' \
  >       'Open Scope string_scope.'
  >     cat
  >   } > input.v
  >   rocq repl -q -batch -R ../theories DjotV -l input.v > output.raw || return
  >   awk '/^     = / { sub(/^     = /, "") } /^     : string$/ { next } { print }' output.raw
  > }

  $ ss <<'EOF'
  > Compute render_html (parse_profile_doc markdown_like_profile
  >   "**strong** and _emphasis_").
  > EOF
  "<p><strong>strong</strong> and <em>emphasis</em></p>
  "

  $ ss <<'EOF'
  > Compute render_html (parse_profile_doc markdown_like_profile
  >   "# heading
  > continuation").
  > EOF
  "<section id=""heading"">
  <h1>heading</h1>
  <p>continuation</p>
  </section>
  "

  $ ss <<'EOF'
  > Compute render_html (parse_profile_doc markdown_like_profile
  >   "a---b and ...").
  > EOF
  "<p>a—b and …</p>
  "

  $ ss <<'EOF'
  > Compute render_html (parse_profile_doc markdown_like_profile
  >   "```=html
  > <b>x</b>
  > ```").
  > EOF
  "<b>x</b>
  "
