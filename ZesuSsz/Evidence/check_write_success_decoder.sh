#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/../.." && pwd)
switch_path=${OPAM_SWITCH:-/home/cody/islaris}
build_dir=${AGENT_BUILD_DIR:-"$repo_root/_build/agents/push1"}
query_file=$(mktemp --suffix=.v)
output_file=$(mktemp)
trap 'rm -f "$query_file" "$output_file"' EXIT

cd "$repo_root"
python3 tools/build_record.py --build-dir "$build_dir" \
  --target WriteSuccessDecoderExamples -- \
  opam exec --switch="$switch_path" -- dune build --root . \
  --build-dir "$build_dir" --cache=enabled -j32 \
  ZesuSsz/Proofs/WriteSuccess/WriteSuccessDecoderExamples.vo

cat >"$query_file" <<'EOF'
From Coq Require Import Bool.Bool Lists.List ZArith.ZArith.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservationDecoder.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessDecoderExamples.
Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessCompleteExecutableCase : bool :=
  match writeSuccessDecodeObservation
    (writeSuccessEncodeObservation writeSuccessCp1Observation) with
  | Some _ => true
  | None => false
  end.

Definition writeSuccessDistinctBaseFeeExecutableCase : bool :=
  match
    writeSuccessDecodeObservation
      (writeSuccessEncodeObservation
        (writeSuccessCp1ObservationWithBaseFee 7)),
    writeSuccessDecodeObservation
      (writeSuccessEncodeObservation
        (writeSuccessCp1ObservationWithBaseFee 8))
  with
  | Some first, Some second =>
      negb (Z.eqb (observationBaseFee first) (observationBaseFee second))
  | _, _ => false
  end.

Definition writeSuccessVariablePublicKeysExecutableCase : bool :=
  match writeSuccessDecodeObservation
    (writeSuccessEncodeObservation writeSuccessCp1Observation) with
  | Some decoded =>
      match observationPublicKeys decoded with
      | first :: second :: [] =>
          Nat.eqb (length first) 2 && Nat.eqb (length second) 1
      | _ => false
      end
  | None => false
  end.

Definition writeSuccessTrailingByteExecutableCase : bool :=
  match writeSuccessDecodeObservation
    (writeSuccessEncodeObservation writeSuccessCp1Observation ++ [0]) with
  | Some _ => false
  | None => true
  end.

Eval vm_compute in
  forallb (fun result => result)
    [writeSuccessCompleteExecutableCase;
     writeSuccessDistinctBaseFeeExecutableCase;
     writeSuccessVariablePublicKeysExecutableCase;
     writeSuccessTrailingByteExecutableCase].
EOF

opam exec --switch="$switch_path" -- coqtop -quiet \
  -Q "$build_dir/default/InstrSpecs" InstrSpecs \
  -R "$build_dir/default/ZesuSsz" ZesuSsz -batch -l "$query_file" \
  >"$output_file"

if ! rg -q '^     = true$' "$output_file"; then
  cat "$output_file"
  exit 1
fi

echo "writeSuccess decoder executable cases: passed"
