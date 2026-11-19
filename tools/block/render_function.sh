#!/usr/bin/env bash
# Render one function's FP301 blocks: forward pass, loop heads, entries, callers and, for a profile
# with `"entry_hist": "wrap"`, the history edge instances.
#
# Usage: tools/block/render_function.sh FUNCTION INPUTS RUNDIR BANK [EXTRA_COQC_FLAG...]
#   FUNCTION  profile name (tools/block/functions/FUNCTION.json)
#   INPUTS    source-pass inputs (SEED-MANIFEST.json, FUNCTION.json, ...; functions/entry_interface_inputs.py)
#   RUNDIR    new output directory: forward/, render/ (render/sources holds the entry modules),
#             callers/, EDGES.json; render/sources/<generated_directory>/Edges*.v in wrap mode
#   BANK      a kept bench bank (coqc_recipe.json, coqc-ocamlpath.json): the contradiction checks of
#             the entry render compile against it
#   EXTRA_COQC_FLAG  appended to the bank's coqc flags (development probes: `-Q DIR LOGICAL`)
# Each heavy step runs under tools/guarded_tool.sh. The loop-head fixture of the profile is
# rewritten in this worktree (it is the loop design of the new forward pass). A step whose output
# exists is skipped, so a failed run resumes.
set -euo pipefail
[ $# -ge 4 ] || { sed -n '2,15p' "$0" >&2; exit 2; }
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
if [ -n "$fixture" ]; then
  (cd tools/block && ../guarded_tool.sh python3 loop_design.py --function "$function_name" \
    --forward "$run/forward/FORWARD.json" --output "$worktree/$fixture") > "$run/loop-heads.log" 2>&1
  echo "loop heads: $(tail -c 200 "$run/loop-heads.log")"
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
  --record-refusals > "$run/render.log" 2>&1
echo "render: $(head -c 300 "$run/render.log" | tr '\n' ' ')"

[ -d "$run/callers" ] || $guard python3 tools/block/render_function_callers.py --function "$function_name" \
  --entries "$run/render/RESULT.json" --cfg "$inputs/FUNCTION.json" --output "$run/callers" > "$run/callers.log" 2>&1
echo "callers: $(tail -c 200 "$run/callers.log" | tr '\n' ' ')"

if [ "$(profile_value entry_hist)" = wrap ]; then
  generated=$(profile_value generated_directory)
  [ -f "$run/EDGES.json" ] || $guard python3 tools/block/render_edges.py --function "$function_name" \
    --entries "$run/render/RESULT.json" --forward "$run/forward" --cfg "$inputs/FUNCTION.json" \
    --output "$run/EDGES.json" --rocq-dir "$run/render/sources/$generated" > "$run/edges.log" 2>&1
  echo "edges: $(tail -c 300 "$run/edges.log")"
fi
