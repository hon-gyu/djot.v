#!/bin/sh
# ai-disclosure: ai-generated
# Writes versions.ml: this repository's commit and the commit of the djot
# syntax reference it pins as the `djot` submodule.
root=$(git rev-parse --show-toplevel)
spec=$(git -C "$root" ls-files -s djot | awk '{print $2}')
spec_date=$(git -C "$root/djot" log -1 --format=%ad --date=short "$spec" 2>/dev/null)
echo "let commit = \"$(git -C "$root" rev-parse HEAD)\""
echo "let describe = \"$(git -C "$root" describe --always --tags --dirty)\""
echo "let spec_commit = \"$spec\""
echo "let spec_date = \"$spec_date\""
