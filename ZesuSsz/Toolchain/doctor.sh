#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
switch=${OPAM_SWITCH:-/home/cody/islaris}
fail=0

check_command() {
  local name=$1
  shift
  if "$@" >/dev/null 2>&1; then
    printf 'ok: %s\n' "$name"
  else
    printf 'missing: %s\n' "$name" >&2
    fail=1
  fi
}

check_revision() {
  local name=$1
  local repository=$2
  local expected=$3
  local actual
  actual=$(git -C "$repository" rev-parse HEAD 2>/dev/null || true)
  if [[ "$actual" == "$expected" ]]; then
    printf 'ok: %s\n' "$name"
  else
    printf 'wrong revision: %s (%s)\n' "$name" "$actual" >&2
    fail=1
  fi
}

check_command nix nix --version
check_command opam opam --version
check_command zig zig version
check_command riscv64-objdump "$root/bin/riscv64-linux-gnu-objdump" --version
check_command rocq opam exec --switch="$switch" -- coqc --version
check_command dune opam exec --switch="$switch" -- dune --version
check_command islaris opam exec --switch="$switch" -- islaris --version
check_command isla-footprint test -x /home/cody/islaris/bin/isla-footprint
check_command z3 test -x "$root/bin/z3"
check_revision islaris-revision /home/cody/islaris c978e10f50db5c40f0fdf113f5f76a779782c6f9
check_revision isla-revision /home/cody/isla b8e614bda4a20e42c37d8b216853653133d04322

if nix store ping >/dev/null 2>&1; then
  printf 'ok: nix store\n'
else
  printf 'unavailable: nix store daemon\n' >&2
  fail=1
fi

exit "$fail"
