#!/bin/sh
# ai-disclosure: ai-generated
# Writes versions.ml: what the VERSION file at the root of the repository
# states, and the commit the site is built from.
root=$(git rev-parse --show-toplevel)
field() { sed -n "s/^$1: *//p" "$root/VERSION"; }
echo "let version = \"$(field version)\""
echo "let spec_commit = \"$(field djot-commit)\""
echo "let spec_date = \"$(field djot-date)\""
echo "let commit = \"$(git -C "$root" rev-parse HEAD)\""
echo "let commit_date = \"$(git -C "$root" log -1 --format=%ad --date=short)\""
echo "let describe = \"$(git -C "$root" describe --always --tags --dirty)\""
