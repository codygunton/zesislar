#!/usr/bin/env bash
# Clean up after a merged branch:
#   1. remove its worktree when the worktree is clean (never --force);
#   2. delete the _build/agents/*/<item> run dirs that belong to the branch.
# A run dir belongs to the branch when its ITEM.json has {"branch": "<branch>"},
# or, without ITEM.json, when its name is the branch name, the branch name with
# "/" replaced by "-", or the last part of the branch name.
# Before deleting a worktree build or run dir, it moves the saved goals in it
# (*Goal*.v, goals/**/*.v) into the store _build/goals/ and the closure records
# (CLOSURE.json, NOT-CLOSED.json) into _build/closures/<function>/<case>/<run>/
# (tools/goal_store.py); it never deletes either store. BENCH runs (tools/bench RUN.json +
# REPORT*.md, or anything under _build/agents/bench/) and gate cycle dirs
# (_build/agents/<lane>/gates-*) are reference data: they are kept and shrunk (build
# products dropped, BENCH logs gzip'd, a gate dir keeps its small files) instead of deleted,
# and a worktree's BENCH runs move to _build/agents/bench/ before the worktree goes
# (2026-11-18: cleanup of orch/finish-gate deleted the BENCH-v1 base run).
# The script keeps anything that a live process uses or that holds a release
# receipt named by the admission ledger, and everything under
# _build/agents/orch/. It does not delete the branch.
#
# usage: tools/cleanup_after_merge.sh [--dry-run] <branch>
set -euo pipefail

# The script may live in the worktree it removes; the janitor calls after
# `git worktree remove` then found no tools/build_janitor.py (2026-11-15).
# Run from a private copy of the script and the janitor, deleted on exit.
if [ -z "${ZESU_CLEANUP_TOOLS:-}" ]; then
  source_tools=$(dirname "$(realpath "$0")")
  copy=$(mktemp -d "${TMPDIR:-/tmp}/cleanup-after-merge.XXXXXX")
  cp -- "$source_tools/cleanup_after_merge.sh" "$source_tools/build_janitor.py" \
    "$source_tools/goal_store.py" "$copy/"
  ZESU_CLEANUP_TOOLS=$copy exec bash "$copy/cleanup_after_merge.sh" "$@"
fi
trap 'rm -f -- "$ZESU_CLEANUP_TOOLS/cleanup_after_merge.sh" "$ZESU_CLEANUP_TOOLS/build_janitor.py" \
  "$ZESU_CLEANUP_TOOLS/goal_store.py"; rmdir -- "$ZESU_CLEANUP_TOOLS"' EXIT

dry_run=0
if [ "${1:-}" = --dry-run ]; then dry_run=1; shift; fi
if [ "$#" -ne 1 ] || [ -z "$1" ]; then
  echo "usage: tools/cleanup_after_merge.sh [--dry-run] <branch>" >&2
  exit 2
fi
branch=${1#refs/heads/}
main_ref=${ZESU_MAIN_REF:-origin/main}
case "$branch" in
  main|master|HEAD|"${main_ref#origin/}")
    echo "cleanup_after_merge: refusing to clean up $branch" >&2; exit 2 ;;
esac

tools=$ZESU_CLEANUP_TOOLS
janitor=(python3 -B "$tools/build_janitor.py")
common=$(git rev-parse --path-format=absolute --git-common-dir)
root=$(dirname "$common")
# The current directory may be the worktree this run removes.
cd -- "$root"

tip=$(git -C "$root" rev-parse --verify -q "refs/heads/$branch^{commit}" || true)
if [ -z "$tip" ]; then
  echo "cleanup_after_merge: no local branch $branch" >&2; exit 2
fi
# A merge made on GitHub is invisible until origin is fetched; without the
# fetch the script reported "not merged" and did nothing (2026-11-16).
case "$main_ref" in
  origin/*)
    if ! git -C "$root" fetch --quiet origin \
      "+refs/heads/${main_ref#origin/}:refs/remotes/$main_ref"; then
      echo "cleanup_after_merge: git fetch origin failed; cannot tell whether $branch is merged." >&2
      exit 2
    fi ;;
esac
if ! git -C "$root" merge-base --is-ancestor "$tip" "$main_ref"; then
  echo "cleanup_after_merge: $branch ($tip) is not merged into $main_ref (fetched); nothing done." >&2
  exit 3
fi

# awk reads to the end: an early exit kills git with SIGPIPE, and pipefail stops the script.
worktree=$(git -C "$root" worktree list --porcelain | awk -v ref="refs/heads/$branch" '
  /^worktree / { path = substr($0, 10) }
  $0 == "branch " ref && found == "" { found = path }
  END { if (found != "") print found }')
if [ -z "$worktree" ]; then
  echo "no worktree has $branch checked out"
elif [ "$(realpath "$worktree")" = "$(realpath "$root")" ]; then
  echo "kept worktree $worktree: it is the base checkout"
elif "${janitor[@]}" --root "$root" in-use "$worktree"; then
  echo "kept worktree $worktree: a live process or an admission ledger receipt uses it"
elif [ -n "$(git -C "$worktree" status --porcelain --untracked-files=all)" ]; then
  echo "kept worktree $worktree: it has uncommitted or untracked files"
elif [ "$dry_run" = 1 ]; then
  if [ -d "$worktree/_build" ]; then
    "${janitor[@]}" --root "$root" --dry-run rescue-goals "$worktree/_build"
  fi
  echo "would remove worktree $worktree"
else
  if [ -d "$worktree/_build" ]; then
    "${janitor[@]}" --root "$root" rescue-goals --reason "cleanup_after_merge: $branch" \
      "$worktree/_build"
  fi
  if git -C "$root" worktree remove "$worktree"; then
    echo "removed worktree $worktree"
  else
    echo "kept worktree $worktree: git worktree remove refused"
  fi
fi

if [ "$dry_run" = 1 ]; then
  "${janitor[@]}" --root "$root" branch-items "$branch"
else
  "${janitor[@]}" --root "$root" branch-items "$branch" --delete
fi
