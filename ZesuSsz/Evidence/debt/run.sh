#!/usr/bin/env bash
# Run the tech-debt sweep on the checkout that holds this script.
# Usage: run.sh <root-sha> <out-dir>
set -euo pipefail
sha=$1
out=$(realpath "$2")
here=$(cd "$(dirname "$0")" && pwd)
tree=$(cd "$here/../../.." && pwd)
base=$(git -C "$tree" rev-parse --path-format=absolute --git-common-dir | xargs dirname)
plans=$base/docs/ai/plan
mkdir -p "$out"
cd "$tree"
# The tree outside this directory must equal the root.
git diff --quiet "$sha" -- . ':!ZesuSsz/Evidence/debt' || {
  echo "checkout differs from $sha outside ZesuSsz/Evidence/debt" >&2; exit 2; }

find ZesuSsz -name '*.v' | sort > "$out/vfiles.txt"
coqdep=${COQDEP:-$HOME/islaris/_opam/bin/coqdep}
"$coqdep" -Q ZesuSsz ZesuSsz $(cat "$out/vfiles.txt") > "$out/coqdep.out" 2> "$out/coqdep.err"

python3 "$here/gate_cost.py" --roots "$base/_build" "$base/.worktrees" --out "$out/gate_cost.json"
python3 "$here/inventory.py" --tree . --coqdep "$out/coqdep.out" --cost "$out/gate_cost.json" \
  --plans "$plans/PLAN_ISLARIS_NATIVE_COMPLIANCE.md" "$plans/PLAN_BUILDER_BUILDOUT.md" \
          "$plans/PLAN_DETERMINISM.md" AGENTS.md \
  --out "$out/modules.json"
python3 "$here/answers.py" --modules "$out/modules.json" --coqdep "$out/coqdep.out" --out "$out/answers.json"
python3 "$here/script_refs.py" --tree . --base "$base" --out "$out/scripts.md"
python3 "$here/branches.py" --root "$sha" --out "$out/branches.md"
python3 "$here/closed_cleanup_gap.py" --root . --output "$out/closed_gap.md"
python3 "$here/render.py" --modules "$out/modules.json" --answers "$out/answers.json" \
  --branches "$out/branches.md" --scripts "$out/scripts.md" --closed "$out/closed_gap.md" \
  --sha "$sha" --out "$out/TECH_DEBT_INVENTORY.md"
if [ -f "$here/proposal.py" ]; then
  python3 "$here/proposal.py" --modules "$out/modules.json" --answers "$out/answers.json" \
    --branches "$out/branches.md" --scripts "$out/scripts.md" --sha "$sha" \
    --out "$out/TECH_DEBT_PROPOSAL.md"
fi
