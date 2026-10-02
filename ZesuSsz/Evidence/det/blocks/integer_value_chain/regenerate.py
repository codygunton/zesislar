#!/usr/bin/env python3
"""Regenerate tail integer states and their complete native blocks."""
import json
import sys
from pathlib import Path

stage = Path(__file__).resolve().parent
root = stage.parents[4]
sys.path.insert(0, str(root / "tools/block"))
import gen_block

states = {}
entries = {}
for record_file in ("entry_states.json", "successor_states.json"):
    for state in json.loads((stage / record_file).read_text()):
        leader = int(state["entry"], 16)
        states[leader] = state
        if record_file == "entry_states.json":
            entries[leader] = state
        name = state.get("name", f"State_{leader:x}")
        target = stage / "States" / f"{name}.v"
        target.write_text(gen_block.state_source(leader, state))
for block in json.loads((stage / "blocks.json").read_text()):
    leader = int(block["start"], 16)
    source, _name = gen_block.generate(block, states | {leader: entries[leader]})
    leader = int(block["start"], 16)
    (stage / "Blocks" / f"Block_{leader:x}.v").write_text(source)
