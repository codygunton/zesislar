#!/usr/bin/env bash
set -euo pipefail

# Keep the persistent server outside the guard's transient job registry.
# Its pet children inherit this fence. Compiler jobs use registered scopes.
tools_dir=$(dirname "$(realpath "$0")")
mcp_binary=${ZESU_ROCQ_MCP_BINARY:-$(command -v rocq-mcp)}
# MCP clients can omit these variables from their subprocess environment.
export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$UID}
export DBUS_SESSION_BUS_ADDRESS=${DBUS_SESSION_BUS_ADDRESS:-unix:path=$XDG_RUNTIME_DIR/bus}
export ZESU_MODULE_LIMIT_GIB=6 ZESU_HOLD_GIB=180
export ROCQ_MAX_PET_RSS_MB=6144
export ROCQ_COQC_BINARY="$tools_dir/rocq_coqc_guarded.sh"
exec systemd-run --user --scope --quiet --collect \
  --unit="rocq-writer-${UID}-$$" \
  -p MemoryMax=6G -p MemorySwapMax=0 -- "$mcp_binary" "$@"
