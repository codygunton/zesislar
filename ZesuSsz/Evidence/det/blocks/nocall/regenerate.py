#!/usr/bin/env python3
"""Regenerate staged no-call states and blocks from captured records."""
import json
import sys
from pathlib import Path
stage = Path(__file__).resolve().parent
root = stage.parents[4]
sys.path[:0] = [str(root / "tools/block"), str(root / "tools/det"), str(root / "tools")]
import gen_block
entries = json.loads((stage / "nocall_entries.json").read_text())
for state in entries:
    target = stage / "States" / ("State_" + state["entry"][2:] + ".v")
    if target.exists():
        target.write_text(gen_block.state_source(int(state["entry"], 16), state))

successors = json.loads((stage / "successor_states.json").read_text())
for state in successors:
    target = stage / "States" / (state["name"] + ".v")
    target.write_text(gen_block.state_source(int(state["entry"], 16), state))
successors += json.loads((stage / "unreachable_successors.json").read_text())

cfg = json.loads((root / "build/endpoint-cfg/zesu-cfg.json").read_text())
blocks = {block["start"]: block for function in cfg["functions"]
          for block in function["blocks"]}
for entry in entries:
    leader = int(entry["entry"], 16)
    target = stage / "Blocks" / f"Block_{leader:x}.v"
    if not target.exists():
        continue
    states = {leader: entry}
    states.update({int(state["entry"], 16): state for state in successors
                   if state["source_predecessor"] == entry["entry"]})
    source, _ = gen_block.generate(blocks[leader], states)
    target.write_text(source)
