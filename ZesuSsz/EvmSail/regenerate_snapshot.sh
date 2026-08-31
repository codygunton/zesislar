#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
evm_source=${EVM_SAIL_REPO:-/home/cody/evm-sail}
sail_source=${SAIL_REPO:-}

if [[ -z "$sail_source" ]]; then
  printf 'Set SAIL_REPO to Sail revision 25cc260d9940d65d2e5da427fe4b5d402809a50c.\n' >&2
  exit 2
fi

test "$(git -C "$evm_source" rev-parse HEAD)" = d0e4aabdde52f9158d191dbc8add444abffd9a6a
test "$(git -C "$sail_source" rev-parse HEAD)" = 25cc260d9940d65d2e5da427fe4b5d402809a50c

stage=$(mktemp -d)
output=$(mktemp -d)
cleanup() {
  rm -rf -- "$stage" "$output"
}
trap cleanup EXIT

rsync -a "$evm_source/sail/" "$stage/"
install -m644 "$root/ZesuSsz/EvmSail/decoder.sail_project" "$stage/"

export PATH="$root/bin:$PATH"
"$sail_source/sail" \
  --coq --coq-semantic-range-types --coq-undef-axioms \
  --coq-output-dir "$output" -o evm_decoder \
  --project "$stage/decoder.sail_project" --all-modules

sed -i 's/^Require Import evm_decoder_types\.$/Require Import EvmSail.evm_decoder_types./' \
  "$output/evm_decoder.v"

python3 "$root/ZesuSsz/EvmSail/check_snapshot.py" \
  --snapshot "$root/generated/evm-sail-coq" --generated "$output"
