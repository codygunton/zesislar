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
exec python3 "$tools_dir/coqc_findlib.py" guarded --guard "$guard" -- "$coqc_binary" "$@"
