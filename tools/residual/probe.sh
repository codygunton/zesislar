#!/usr/bin/env bash
# One-command residual capture, for a blocked report from a compliance agent.
#
#   tools/residual/probe.sh MODULE LEMMA [BUILD_DIR]
#
# MODULE is a path or a bare module name under ZesuSsz/Proofs/WriteSuccess.
# Prints the probe seconds, the outcome, the residual class and the first 30
# lines of the goal. It never edits the proof.
set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
  echo "usage: $0 MODULE LEMMA [BUILD_DIR]" >&2
  exit 2
fi

root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
exec python3 tools/residual/show_probe.py "$1" "$2" \
  --build-dir "${3:-$root/_build/agents/corpus}"
