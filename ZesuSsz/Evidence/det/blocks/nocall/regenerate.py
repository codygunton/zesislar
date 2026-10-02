#!/usr/bin/env python3
"""Regenerate staged no-call entry states from captured records."""
import json
import sys
from pathlib import Path
stage = Path(__file__).resolve().parent
root = stage.parents[4]
sys.path[:0] = [str(root / "tools/block"), str(root / "tools/det"), str(root / "tools")]
import gen_block
for state in json.loads((stage / "nocall_entries.json").read_text()):
    target = stage / "States" / ("State_" + state["entry"][2:] + ".v")
    if target.exists():
        target.write_text(gen_block.state_source(int(state["entry"], 16), state))
