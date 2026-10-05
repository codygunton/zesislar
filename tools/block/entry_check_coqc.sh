#!/usr/bin/env bash
set -euo pipefail

tools_dir=$(dirname "$(dirname "$(realpath "$0")")")
coqc_binary=${OPAM_SWITCH_PREFIX:?run under the pinned opam switch}/bin/coqc
if [[ $# -eq 1 && $1 == --version ]]; then
  exec "$coqc_binary" "$@"
fi
export ZESU_MODULE_LIMIT_GIB=2 ZESU_HOLD_GIB=180
"$tools_dir/resource_guard.sh" wait
exec "$tools_dir/resource_guard.sh" scope entry-application-check -- "$coqc_binary" "$@"
