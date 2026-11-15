#!/usr/bin/env bash
set -euo pipefail

tools_dir=$(dirname "$(realpath "$0")")
coqc_binary=${ZESU_ROCQ_COQC_BINARY:-${OPAM_SWITCH_PREFIX:?run under the pinned opam switch}/bin/coqc}
# Health probes do not compile a proof or need a compiler slot.
if [[ $# -eq 1 && $1 == --version ]]; then
  exec "$coqc_binary" "$@"
fi
# Measured 18-25% lower peak RSS for +3-4% instructions (docs/ai/PROJECTS.md
# "Rocq GC setting"). Setting OCAMLRUNPARAM replaces Rocq's own GC policy, so
# keep its minor heap (s=32M) and best-fit allocator (a=2).
export OCAMLRUNPARAM=s=32M,a=2,o=40
export ZESU_MODULE_LIMIT_GIB=${ZESU_GATE_MODULE_LIMIT_GIB-16}
if [[ ! "$ZESU_MODULE_LIMIT_GIB" =~ ^([6-9]|[12][0-9]|3[0-2])$ ]]; then
  echo "compiler gate memory limit must be an integer from 6 through 32 GiB" >&2
  exit 2
fi
export ZESU_HOLD_GIB=${ZESU_HOLD_GIB:-180}
guard=${ZESU_RESOURCE_GUARD:-$tools_dir/resource_guard.sh}
exec python3 "$tools_dir/coqc_findlib.py" guarded --guard "$guard" -- "$coqc_binary" "$@"
