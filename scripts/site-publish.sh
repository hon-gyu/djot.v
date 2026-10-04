#!/bin/sh
# ai-disclosure: ai-generated
# Publishes the built site: one new commit on the gh-pages branch of
# origin, whose tree is the directory given, on top of the branch as it
# is on the remote.  Nothing is checked out and no local branch is made;
# the commit is built with a temporary index and pushed by its hash.
set -eu

site=${1:?usage: site-publish.sh SITE_DIR}
test -f "$site/index.html" || { echo "$site: not a built site"; exit 1; }
test -z "$(git status --porcelain)" || {
  echo "commit or stash first: the site states the commit it is built from"
  exit 1
}

index=$(mktemp)
trap 'rm -f "$index"' EXIT
rm -f "$index" # git wants to create it

# -f: the ignore rules are for the repository, not for the site's files.
GIT_INDEX_FILE=$index git --work-tree="$site" add -A -f .
tree=$(GIT_INDEX_FILE=$index git write-tree)

git fetch -q origin gh-pages 2>/dev/null || true
if parent=$(git rev-parse -q --verify refs/remotes/origin/gh-pages); then
  commit=$(git commit-tree "$tree" -p "$parent" -m "site at $(git rev-parse --short HEAD)")
else
  commit=$(git commit-tree "$tree" -m "site at $(git rev-parse --short HEAD)")
fi

git push origin "$commit:refs/heads/gh-pages"
