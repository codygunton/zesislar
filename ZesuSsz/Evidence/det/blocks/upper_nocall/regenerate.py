"""Regenerate the four native no-call proofs from their captured records."""
import json
import sys
from pathlib import Path
stage = Path(__file__).resolve().parent
root = stage.parents[4]
sys.path[:0] = [str(root / "tools/block"), str(root / "tools/det")]
import gen_block
import gen_segment
for state in json.loads((stage / "entry_states.json").read_text()):
    leader = int(state["entry"], 16)
    (stage / "States" / f"State_{leader:x}.v").write_text(gen_block.state_source(leader, state))
for spec in json.loads((stage / "native_specs.json").read_text()):
    source, _ = gen_segment.from_spec(spec, ["ZesuSsz.Automation.Sets.call"], strict=True)
    name = "Block_" + spec["entry"][2:] + ".v"
    (stage / "Blocks" / name).write_text(gen_segment.REQUIRED + "\n" + source)
