#!/usr/bin/env bash
# Baseline arms at the pre-deletion root, on the re-frozen sets.
set -uo pipefail
SHA=${1:?usage: baseline_arms.sh <root-sha> <determinism-tools-dir>}
WT=$(cd "$(dirname "$0")/../../.." && pwd)
TOOLS=${2:?the tools/ directory of an export of origin/determinism}
GUARD=$WT/tools/resource_guard.sh
cd "$WT"
for arm in "refrozen-v1:benchmark_set.txt:" "refrozen-v1-rule15:benchmark_set_rule15.txt:" \
           "refrozen-v2:benchmark_set.txt:ZesuSsz.Automation.Sets.v2" \
           "refrozen-v2-rule15:benchmark_set_rule15.txt:ZesuSsz.Automation.Sets.v2"; do
  IFS=: read -r name set imp <<<"$arm"
  echo "=== $name $(date -Is)"
  "$GUARD" batch "$name" -- python3 "$TOOLS/residual/benchmark.py" --automation "$SHA" \
    --set "ZesuSsz/Evidence/residuals/$set" --name "$name" --jobs 32 --seconds 300 \
    ${imp:+--import $imp}
  echo "=== $name exit $? $(date -Is)"
done
ARM=$WT/_build/agents/bench/${SHA:0:12}
OUT=$WT/ZesuSsz/Evidence/det/refrozen-${SHA:0:8}
mkdir -p "$OUT"
for variant in v1 v2; do
  echo "=== segments-$variant $(date -Is)"
  rule=(); [ $variant = v2 ] && rule=(--rule "$WT/ZesuSsz/Evidence/det/rules/v2.v")
  (cd "$ARM" && "$GUARD" batch "segments-$variant" -- python3 "$TOOLS/det/infer_boundary.py" \
    --specs "$WT/ZesuSsz/Evidence/det/open_segments.json" --build-dir "$ARM/_build" \
    --seconds 900 "${rule[@]}" --out "$OUT/segments-$variant.jsonl")
  echo "=== segments-$variant exit $? $(date -Is)"
done
echo "=== done $(date -Is)"
