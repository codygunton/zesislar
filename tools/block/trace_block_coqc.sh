#!/usr/bin/env bash
# Diagnostic compiler admission for the native trace observer.
set -euo pipefail
tools_dir=$(dirname "$(dirname "$(realpath "$0")")")
coqc_binary=${OPAM_SWITCH_PREFIX:?run under the pinned opam switch}/bin/coqc
if [[ $# -eq 1 && $1 == --version ]]; then
  exec "$coqc_binary" "$@"
fi
# The existing guard validates the issue, memory fence, CPU, and gate state.
exec python3 "$tools_dir/coqc_findlib.py" guarded --guard "$tools_dir/resource_guard.sh" -- "$coqc_binary" "$@"
