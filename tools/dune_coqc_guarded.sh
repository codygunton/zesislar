#!/usr/bin/env bash
set -euo pipefail

# Dune copies this executable to tools/guard-bin/coqc in its build tree.
# Resolve the actual compiler from the active pinned opam switch.
# Cached scratch recipes can run outside opam exec and use the repository pin.
tools_dir=$(dirname "$(realpath "$0")")
if [[ "$(basename "$tools_dir")" == guard-bin ]]; then
  tools_dir=$(dirname "$tools_dir")
fi
export ZESU_MODULE_LIMIT_GIB=6
switch_prefix=${OPAM_SWITCH_PREFIX:-${ISLARIS_REPO:-$HOME/islaris}/_opam}
coqc_binary="$switch_prefix/bin/coqc"
if [[ "$(realpath "$coqc_binary")" == "$(realpath "$0")" ]]; then
  echo "refusing recursive compiler override" >&2
  exit 2
fi
guard=${ZESU_RESOURCE_GUARD:-$tools_dir/resource_guard.sh}

# Dune asks for configuration before any proof job. These queries do not
# consume a compiler slot. A source argument never uses this bypass.
case "$*" in
  -config|--config|--print-version|"--print-version -boot -noinit"|--version|-v)
    exec "$coqc_binary" "$@" ;;
esac

# The scope borrows an existing scratch token or owns one new token.
# A compiler already inside the same job scope does not create another scope.
"$guard" scope dune-coqc -- "$coqc_binary" "$@" &
scope_pid=$!
cleanup() {
  if [[ -n "$scope_pid" ]] && kill -0 "$scope_pid" 2>/dev/null; then
    kill "$scope_pid" 2>/dev/null || true
    wait "$scope_pid" 2>/dev/null || true
  fi
}
trap cleanup EXIT
trap 'exit 143' TERM
trap 'exit 130' INT
set +e
wait "$scope_pid"
status=$?
scope_pid=""
exit "$status"
