#!/usr/bin/env bash
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
tools_dir=$(dirname "$(realpath "$0")")
coqc_binary=${ZESU_ROCQ_COQC_BINARY:-${OPAM_SWITCH_PREFIX:?run under the pinned opam switch}/bin/coqc}
if [[ $# -eq 1 && ( $1 == --version || $1 == --print-version || $1 == --config || $1 == -config ) ]]; then
  exec "$coqc_binary" "$@"
fi
if [[ $# -eq 3 && $1 == --print-version && $2 == -boot && $3 == -noinit ]]; then
  exec "$coqc_binary" "$@"
fi
case "${ZESU_DIAGNOSTIC_PROBE:-1}" in
  1)
    memory_gib=64
    export ZESU_DIAGNOSTIC_PROBE=1 ZESU_PROBE_ISSUE=10
    ;;
  0)
    [[ ${ZESU_MEMORY_PHASE:-} == native ]] || { echo "measured compiler requires native phase" >&2; exit 2; }
    [[ ${ZESU_MODULE_LIMIT_GIB:-} =~ ^([6-9]|[12][0-9]|3[0-2])$ ]] || { echo "unsupported measured fence" >&2; exit 2; }
    [[ ${ZESU_GATE_MODULE_LIMIT_GIB:-} == "$ZESU_MODULE_LIMIT_GIB" && -z ${ZESU_PROBE_ISSUE:-} ]] || { echo "inconsistent measured compiler policy" >&2; exit 2; }
    memory_gib=$ZESU_MODULE_LIMIT_GIB
    export ZESU_DIAGNOSTIC_PROBE=0 ZESU_PROBE_ISSUE=
    ;;
  *) echo "unsupported compiler memory route" >&2; exit 2 ;;
esac
export ZESU_MODULE_LIMIT_GIB=$memory_gib ZESU_GATE_MODULE_LIMIT_GIB=$memory_gib
export ZESU_MODULE_CLAIM_BYTES=${ZESU_MODULE_CLAIM_BYTES:-$((memory_gib * 1073741824))}
export ZESU_PROOF_CPU_LIMIT=unlimited ZESU_SCOPE_CPU=unlimited
export ZESU_HOLD_GIB=${ZESU_HOLD_GIB:-180}
guard=${ZESU_RESOURCE_GUARD:-$tools_dir/resource_guard.sh}
exec /home/cody/.local/share/uv/tools/rocq-mcp/bin/python -B "$tools_dir/block/entry_chain_compiler.py" "$@"
