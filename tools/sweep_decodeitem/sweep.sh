#!/bin/bash
# sweep.sh TAG BANKDIR CALLERDIR [BLOCK,...] : decodeItem 24-block sweep, one guard batch per plan line.
# Uses the guard and fence of the checkout holding this script. Results: $OUT/sweep/TAG/ (see sweep_paths.py).
# Launch with tools/bg --heavy (it checks room at launch). Table: sweeptable.py BASETAG TAG.
set -uo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
tag=$1 bank=$2 cdir=$3
OUT=$(python3 "$here/sweep_paths.py" out) || exit 2
export SWEEP_ROOT=$OUT
export BANK_OCAMLPATH=$(cat "$bank/OCAMLPATH")
python3 "$here/mksweep.py" "$tag" "$bank" "$cdir" ${4:-} > "$OUT/sweep-$tag.plan" || exit 1
while read -r name claim limit blocks; do
  env -u COORD_AGENT -u COORD_ROOT "$here/batch.sh" "$tag-$name" "$claim" "$limit" "$OUT/sweep/$tag/jobs-$name.json" \
    > "$OUT/sweep/$tag/batch-$name.log" 2>&1 &
done < "$OUT/sweep-$tag.plan"
wait
echo "SWEEP-DONE $tag $(wc -l < "$OUT/sweep/$tag/results.jsonl")"
