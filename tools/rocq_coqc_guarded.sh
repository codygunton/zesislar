#!/usr/bin/env bash
set -euo pipefail

tools_dir=$(dirname "$(realpath "$0")")
coqc_binary=${ZESU_ROCQ_COQC_BINARY:-${OPAM_SWITCH_PREFIX:?run under the pinned opam switch}/bin/coqc}
# Health probes do not compile a proof or need a compiler slot.
if [[ $# -eq 1 && $1 == --version ]]; then
  exec "$coqc_binary" "$@"
fi
export ZESU_MODULE_LIMIT_GIB=6 ZESU_HOLD_GIB=180
guard=${ZESU_RESOURCE_GUARD:-$tools_dir/resource_guard.sh}
"$guard" wait
exec "$guard" scope rocq-mcp-coqc -- "$coqc_binary" "$@"
