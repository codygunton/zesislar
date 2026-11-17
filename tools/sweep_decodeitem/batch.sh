#!/bin/bash
# batch.sh NAME CLAIM_GIB LIMIT_GIB JOBS.json : one guard batch running runjobs.py, under this checkout's guard.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
export PATH=${ISLARIS_REPO:-$HOME/islaris}/_opam/bin:$PATH
export OCAMLPATH=${BANK_OCAMLPATH:?set BANK_OCAMLPATH}
export TMPDIR=${TMPDIR:-/home/cody/.cache/orch-checkfast-tmp}
# PR #255 (2026-11-14): same GC setting as the repo compiler wrappers. Sweeps from gc32 on run ~+4% instructions
# and ~-28% peak vs earlier tags; compare against a baseline swept with this setting.
export OCAMLRUNPARAM=s=32M,a=2,o=40
unset ZESU_WRITER_ID
name=$1 claim=$2 limit=$3 jobs=$4
export ZESU_MODULE_CLAIM_BYTES=$((claim * 1073741824)) ZESU_MODULE_LIMIT_GIB=$limit ZESU_GATE_MODULE_LIMIT_GIB=$limit
export ZESU_PROOF_CPU_LIMIT=unlimited ZESU_SCOPE_CPU=unlimited
exec "$(python3 "$here/sweep_paths.py" guard)" batch "mq-$name" -- python3 -u "$here/runjobs.py" "$jobs"
