#!/usr/bin/env bash
set -euo pipefail

# Run one heavy non-coqc tool (generator passes, render, bank-args) in its
# own memory-fenced scope inside zesuworkloads.slice. On 2026-11-13 an
# unguarded generator pass grew to 110 GiB in a session scope and the
# account OOM killed the session. Inside its own scope the tool dies at its
# fence, and the kernel prefers it as an OOM victim (oom_score_adj 1000).
#
# Usage: tools/guarded_tool.sh [--memory GIB] [--] COMMAND [ARGS...]
#   --memory GIB   scope MemoryMax in GiB (default 16, ZESU_TOOL_MEMORY_GIB)

tools_dir=$(dirname "$(realpath "$0")")
guard=${ZESU_RESOURCE_GUARD:-$tools_dir/resource_guard.sh}
memory=${ZESU_TOOL_MEMORY_GIB:-16}
if [ "${1:-}" = --memory ]; then
  memory=${2:-}; shift 2 || { echo "guarded tool: --memory needs a value" >&2; exit 2; }
fi
[ "${1:-}" = -- ] && shift
if [[ ! "$memory" =~ ^[1-9][0-9]{0,2}$ ]]; then
  echo "guarded tool: memory must be a whole number of GiB" >&2
  exit 2
fi
if [ $# -eq 0 ]; then
  echo "usage: tools/guarded_tool.sh [--memory GIB] [--] COMMAND [ARGS...]" >&2
  exit 2
fi
name=$(basename -- "$1")
name=${name//[^a-zA-Z0-9_.-]/-}
"$guard" parent-setup
exec systemd-run --user --scope --quiet --collect --slice=zesuworkloads.slice \
  --unit="zesutool-${name}-$$-${RANDOM}" \
  -p "MemoryMax=${memory}G" -p MemorySwapMax=0 -- \
  "$guard" parent-exec -- "$@"
