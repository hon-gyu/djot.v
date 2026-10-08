#!/bin/sh
# ai-disclosure: ai-generated
# Fails unless the stated versions agree: ocaml/kernel/VERSION is VERSION,
# the syntax reference is the `djot` submodule's commit or an ancestor of
# it, and the changelog lists the kernel's and each package's version.
set -eu
cd "$(git rev-parse --show-toplevel)"

bad=0
err() { echo "check-versions: $*" >&2; bad=1; }

cmp -s VERSION ocaml/kernel/VERSION ||
  err "ocaml/kernel/VERSION differs from VERSION: run make ocaml-pkg-regen"

# The ancestor test needs the submodule checked out; the equality does not.
ref=$(sed -n 's/^syntax-reference-commit: *//p' VERSION)
pinned=$(git rev-parse HEAD:djot)
[ "$ref" = "$pinned" ] ||
  git -C djot merge-base --is-ancestor "$ref" "$pinned" 2>/dev/null ||
  err "syntax reference $ref is neither the djot submodule's commit nor an ancestor of it"

# released SECTION VERSION: the changelog has a [VERSION] heading under SECTION.
released() {
  awk -v s="## $1" -v v="[$2]" '
    /^## / { on = ($0 == s) }
    on && /^#+ \[/ && $2 == v { found = 1 }
    END { exit !found }' changelog ||
    err "changelog: no [$2] under \"$1\""
}
released "Kernel" "$(sed -n 's/^version: *//p' VERSION)"
released "OCaml package" "$(sed -n 's/^(version \(.*\))$/\1/p' ocaml/dune-project)"
released "Python package" "$(sed -n 's/^version = "\(.*\)"$/\1/p' py/pyproject.toml | head -1)"

[ $bad = 0 ] && echo "versions agree"
exit $bad
