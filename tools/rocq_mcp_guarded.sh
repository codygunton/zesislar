#!/usr/bin/env bash
set -euo pipefail

# Keep the persistent server outside the guard's transient job registry.
# Its pet children inherit this fence. Compiler jobs use registered scopes.
tools_dir=$(dirname "$(realpath "$0")")
mcp_binary=${ZESU_ROCQ_MCP_BINARY:-$(command -v rocq-mcp)}
# MCP clients can omit these variables from their subprocess environment.
export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$UID}
export DBUS_SESSION_BUS_ADDRESS=${DBUS_SESSION_BUS_ADDRESS:-unix:path=$XDG_RUNTIME_DIR/bus}
export ZESU_MODULE_LIMIT_GIB=${ZESU_GATE_MODULE_LIMIT_GIB-16}
if [[ ! "$ZESU_MODULE_LIMIT_GIB" =~ ^([6-9]|[12][0-9]|3[0-2])$ ]]; then
  echo "compiler gate memory limit must be an integer from 6 through 32 GiB" >&2
  exit 2
fi
export ZESU_HOLD_GIB=${ZESU_HOLD_GIB:-180}
export ROCQ_MAX_PET_RSS_MB=$((ZESU_MODULE_LIMIT_GIB * 1024))
export ROCQ_COQC_BINARY=${ZESU_ROCQ_COQC_WRAPPER:-$tools_dir/rocq_coqc_guarded.sh}
resource_guard=$(realpath "${ZESU_RESOURCE_GUARD:-$tools_dir/resource_guard.sh}")
export ZESU_RESOURCE_GUARD="$resource_guard"
slice=$("$resource_guard" parent-slice)
if [ "$slice" != zesuworkloads.slice ] &&
   [[ ! "$slice" =~ ^zesuworkloads-aggregate[0-9]+p[0-9]+r[0-9]+\.slice$ ]]; then
  echo "MCP guard: the selected guard lacks the shared memory parent" >&2
  exit 2
fi
export ZESU_MCP_SCOPE_UNIT="rocq-writer-${UID}-$$.scope"
exec systemd-run --user --scope --quiet --collect --slice="$slice" \
  --unit="rocq-writer-${UID}-$$" \
  -p "MemoryMax=${ZESU_MODULE_LIMIT_GIB}G" -p MemorySwapMax=0 -- \
  "$resource_guard" parent-exec -- "$mcp_binary" "$@"
