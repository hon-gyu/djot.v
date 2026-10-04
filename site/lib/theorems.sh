#!/bin/sh
# ai-disclosure: ai-generated
# Writes theorems.ml: every theorem of theories/ and dev/ with its file,
# as a path in the repository, and its line.
root=$(git rev-parse --show-toplevel)
cd "$root" || exit 1
echo "let all = ["
grep -nE '^(Theorem|Lemma|Corollary|Example) [A-Za-z0-9_]+' theories/*.v dev/*.v |
  sed -E 's|^([A-Za-z0-9_/]+\.v):([0-9]+):[A-Za-z]+ ([A-Za-z0-9_]+).*|  "\3", ("\1", \2);|'
echo "]"
