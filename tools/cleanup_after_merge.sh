#!/usr/bin/env bash
# Clean up after a merged branch:
#   1. remove its worktree when the worktree is clean (never --force);
#   2. delete the _build/agents/*/<item> run dirs that belong to the branch.
# A run dir belongs to the branch when its ITEM.json has {"branch": "<branch>"},
# or, without ITEM.json, when its name is the branch name, the branch name with
# "/" replaced by "-", or the last part of the branch name.
# The script keeps anything that a live process uses and everything under
# _build/agents/orch/. It does not delete the branch.
#
# usage: tools/cleanup_after_merge.sh [--dry-run] <branch>
set -euo pipefail

dry_run=0
if [ "${1:-}" = --dry-run ]; then dry_run=1; shift; fi
if [ "$#" -ne 1 ] || [ -z "$1" ]; then
  echo "usage: $0 [--dry-run] <branch>" >&2
  exit 2
fi
branch=${1#refs/heads/}
main_ref=${ZESU_MAIN_REF:-origin/main}
case "$branch" in
  main|master|HEAD|"${main_ref#origin/}")
    echo "cleanup_after_merge: refusing to clean up $branch" >&2; exit 2 ;;
esac

tools=$(dirname "$(realpath "$0")")
janitor=(python3 "$tools/build_janitor.py")
common=$(git rev-parse --path-format=absolute --git-common-dir)
root=$(dirname "$common")

tip=$(git -C "$root" rev-parse --verify -q "refs/heads/$branch^{commit}" || true)
if [ -z "$tip" ]; then
  echo "cleanup_after_merge: no local branch $branch" >&2; exit 2
fi
if ! git -C "$root" merge-base --is-ancestor "$tip" "$main_ref"; then
  echo "cleanup_after_merge: $branch ($tip) is not merged into $main_ref; nothing done." >&2
  echo "cleanup_after_merge: fetch $main_ref first if the merge is new." >&2
  exit 3
fi

worktree=$(git -C "$root" worktree list --porcelain | awk -v ref="refs/heads/$branch" '
  /^worktree / { path = substr($0, 10) }
  $0 == "branch " ref { print path; exit }')
if [ -z "$worktree" ]; then
  echo "no worktree has $branch checked out"
elif [ "$(realpath "$worktree")" = "$(realpath "$root")" ]; then
  echo "kept worktree $worktree: it is the base checkout"
elif "${janitor[@]}" --root "$root" in-use "$worktree"; then
  echo "kept worktree $worktree: a live process uses it"
elif [ -n "$(git -C "$worktree" status --porcelain --untracked-files=all)" ]; then
  echo "kept worktree $worktree: it has uncommitted or untracked files"
elif [ "$dry_run" = 1 ]; then
  echo "would remove worktree $worktree"
elif git -C "$root" worktree remove "$worktree"; then
  echo "removed worktree $worktree"
else
  echo "kept worktree $worktree: git worktree remove refused"
fi

if [ "$dry_run" = 1 ]; then
  "${janitor[@]}" --root "$root" branch-items "$branch"
else
  "${janitor[@]}" --root "$root" branch-items "$branch" --delete
fi
