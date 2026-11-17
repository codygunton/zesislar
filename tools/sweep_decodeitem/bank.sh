#!/bin/bash
# bank.sh NAME BUILDDIR : build this checkout's decodeItem caller dependencies into BUILDDIR (one guard batch, this
# checkout's guard), then write BUILDDIR/bank/{ARGS.json,OCAMLPATH,BANK.json} for sweep.sh.
set -uo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
wt=$(python3 "$here/sweep_paths.py" repo) || exit 2
name=$1 b=$2
islaris=${ISLARIS_REPO:-$HOME/islaris}
export PATH=$wt/bin:$islaris/bin:$islaris/_opam/bin:$PATH
unset OCAMLPATH
export TMPDIR=${TMPDIR:-/home/cody/.cache/orch-checkfast-tmp}
mkdir -p "$b/bank"; b=$(readlink -f "$b")
cd "$wt" || exit 2
mapfile -t targets < <(grep -h '^Require Import ZesuSsz\.' tools/block/generated/fp301_callers/*.v | sed 's/Require Import //; s/\.$//' | sort -u | sed 's|\.|/|g; s|$|.vo|')
g() { env -u COORD_AGENT -u COORD_ROOT tools/resource_guard.sh batch "mq-bank-$name" -- \
  python3 tools/dune_trace_guard.py --canonical-build-dir -- \
  dune build --root . --build-dir "$b" --cache=enabled -j16 "$@"; }
make --no-print-directory stock-native-indexes AGENT_BUILD_DIR="$b" && g @install && g "${targets[@]}"
rc=$?
if [ $rc = 0 ]; then
  python3 tools/block/residual_scale.py bank-args --build-dir "$b" --out "$b/bank" || rc=$?
  echo "$b/install/default/lib" > "$b/bank/OCAMLPATH"
  printf '{"worktree": "%s", "head": "%s"}\n' "$wt" "$(git rev-parse HEAD)" > "$b/bank/BANK.json"
fi
echo "BANK-EXIT=$rc"
exit $rc
