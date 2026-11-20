#!/usr/bin/env bash
# Render one function's FP301 blocks: forward pass, loop heads, entries (with the profile's
# return-package design), loop-exit entries (profile `loop_exits`), callers (with the profile's
# `design_callers`) and, for a profile with `"entry_hist": "wrap"`, the history edge instances.
#
# Usage: tools/block/render_function.sh FUNCTION INPUTS RUNDIR BANK [EXTRA_COQC_FLAG...]
#   FUNCTION  profile name (tools/block/functions/FUNCTION.json)
#   INPUTS    source-pass inputs (SEED-MANIFEST.json, FUNCTION.json, ...; functions/entry_interface_inputs.py)
#   RUNDIR    new output directory: forward/, render/ (render/sources holds the entry modules),
#             callers/, EDGES.json; render/sources/<generated_directory>/Edges*.v in wrap mode
#   BANK      a kept bench bank (coqc_recipe.json, coqc-ocamlpath.json): the contradiction checks of
#             the entry render compile against it
#   EXTRA_COQC_FLAG  appended to the bank's coqc flags (development probes: `-Q DIR LOGICAL`)
# Each heavy step runs under tools/guarded_tool.sh. The loop heads of the new forward pass go to
# RUNDIR/loop-heads.json and the entry render reads them from there; the committed fixture is never
# written (the driver reports whether its rows differ: a committed re-render copies the file over).
# A step whose output exists is skipped, so a failed run resumes.
set -euo pipefail
[ $# -ge 4 ] || { sed -n '2,16p' "$0" >&2; exit 2; }
function_name=$1; inputs=$(realpath "$2"); run=$(realpath -m "$3"); bank=$(realpath "$4"); shift 4
worktree=$(realpath "$(dirname "$0")/../..")
cd "$worktree"
guard=tools/guarded_tool.sh
mkdir -p "$run"
sha() { sha256sum "$1" | cut -d' ' -f1; }
profile_value() {
  (cd tools/block && python3 -c "from function_profiles import load_profile; print(load_profile('$function_name').get('$1') or '')")
}

[ -f "$run/forward/RESULT.json" ] || $guard python3 tools/block/functions/run_source_pass.py \
  --inputs "$inputs" --output "$run/forward" --function "$function_name" > "$run/forward.log" 2>&1
echo "forward: $(tail -c 200 "$run/forward.log" | tr '\n' ' ')"

fixture=$(profile_value loop_head_fixture)
loop_heads=()
# A committed fixture whose rows carry no loop `design` (decodeItem's four-class heads) is an
# authenticated table that loop_design.py does not produce: the render reads it as committed.
designed=$( [ -f "$fixture" ] && python3 -c "import json,sys; print(int(all('design' in row for row in json.load(open(sys.argv[1]))['rows'])))" "$fixture" || echo 1)
if [ -n "$fixture" ] && [ "$designed" = 0 ]; then
  echo "loop heads: $fixture (committed authenticated table, not a loop_design output)"
elif [ -n "$fixture" ]; then
  [ -f "$run/loop-heads.json" ] || (cd tools/block && ../guarded_tool.sh python3 loop_design.py \
    --function "$function_name" --forward "$run/forward/FORWARD.json" --output "$run/loop-heads.json") \
    > "$run/loop-heads.log" 2>&1
  loop_heads=(--loop-heads "$run/loop-heads.json")
  same=$(python3 -c "import json,sys; r=lambda p: [{k: v for k, v in row.items() if k not in ('source', 'verification')} for row in json.load(open(p))['rows']]; print('same rows as' if r(sys.argv[1])==r(sys.argv[2]) else 'ROWS DIFFER from')" \
    "$run/loop-heads.json" "$fixture" 2>/dev/null || echo "no committed")
  echo "loop heads: $run/loop-heads.json ($same $fixture, provenance aside)"
fi

# The bank's coqc recipe with absolute load paths: its paths are relative to the bank's default/.
python3 - "$bank" "$run/coqc-args.json" "$@" <<'EOF'
import json, os, shutil, sys
bank, output, extra = sys.argv[1], sys.argv[2], sys.argv[3:]
command = json.load(open(os.path.join(bank, 'coqc_recipe.json')))['command'][:-1]
coqc = shutil.which('coqc')
if coqc is None:
    sys.exit('render_function: no coqc on PATH')
args = [coqc]
for position, value in enumerate(command[1:], 1):
    path = command[position - 1] in ('-I', '-Q', '-R') and not os.path.isabs(value)
    args.append(os.path.join(bank, 'default', value) if path else value)
json.dump(args + extra, open(output, 'w'), indent=1)
EOF
ocamlpath=$(python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['OCAMLPATH'])" "$bank/coqc-ocamlpath.json")
manifest=$inputs/SEED-MANIFEST.json
[ -f "$run/render/RESULT.json" ] || $guard env OCAMLPATH="$ocamlpath" python3 tools/block/render_fp301_entries.py \
  --output "$run/render" --input-receipt "$run/forward/INPUT-RECEIPT.json" \
  --input-receipt-sha256 "$(sha "$run/forward/INPUT-RECEIPT.json")" --seed-manifest "$manifest" \
  --seed-manifest-sha256 "$(sha "$manifest")" --coqc-args "$run/coqc-args.json" --function "$function_name" \
  "${loop_heads[@]}" --record-refusals > "$run/render.log" 2>&1
echo "render: $(head -c 300 "$run/render.log" | tr '\n' ' ')"

generated=$(profile_value generated_directory)
extra=()
if [ -n "$(profile_value loop_exits)" ]; then
  # The loop-exit entries derive from the run's own loop-head classes; they join the entry modules.
  [ -f "$run/loop-exits/RESULT.json" ] || $guard env OCAMLPATH="$ocamlpath" python3 tools/block/render_loop_exits.py \
    --function "$function_name" --coqc-args "$run/coqc-args.json" --output "$run/loop-exits" \
    --loop-heads-dir "$run/render/sources/$generated" > "$run/loop-exits.log" 2>&1
  cp "$run/loop-exits/sources/$generated"/*.v "$run/render/sources/$generated/"
  extra=(--extra-entries "$run/loop-exits/RESULT.json")
  echo "loop exits: $(tail -c 200 "$run/loop-exits.log" | tr '\n' ' ')"
fi

[ -d "$run/callers" ] || { $guard python3 tools/block/render_function_callers.py --function "$function_name" \
  --entries "$run/render/RESULT.json" "${extra[@]}" --cfg "$inputs/FUNCTION.json" --output "$run/callers" \
  > "$run/callers.log" 2>&1
  if [ -n "$(profile_value design_callers)" ]; then
    $guard python3 tools/block/render_design_callers.py --function "$function_name" --write \
      --output "$run/callers" >> "$run/callers.log" 2>&1
  fi; }
echo "callers: $(tail -c 200 "$run/callers.log" | tr '\n' ' ')"

[ -f "$run/EDGES.json" ] || $guard python3 tools/block/render_edges.py --function "$function_name" \
  --entries "$run/render/RESULT.json" --forward "$run/forward" --cfg "$inputs/FUNCTION.json" \
  --output "$run/EDGES.json" --rocq-dir "$run/render/sources/$generated" > "$run/edges.log" 2>&1
echo "edges: $(tail -c 300 "$run/edges.log")"
