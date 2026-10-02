"""Regenerate staged states and the root block with the existing generator.
Run from the repository root. This command does not promote modules.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
STAGE = Path(__file__).resolve().parent
sys.path[:0] = [str(ROOT / "tools/block"), str(ROOT / "tools/det")]
import call_sites
import gen_block

for state in json.loads((STAGE / "remaining_entries.json").read_text()):
    leader = int(state["entry"], 16)
    (STAGE / "States" / f"State_{leader:x}.v").write_text(
        gen_block.state_source(leader, state))

original_contracts = call_sites.contracts

def dispatched_contracts(*args, **kwargs):
    table = original_contracts(*args, **kwargs)
    table[0x10190] = {
        "name": "zesuWriteOutputCallSpec",
        "module": "ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls",
    }
    return table

call_sites.contracts = dispatched_contracts
sys.argv = ["gen_block.py", "--states", str(STAGE / "root_states.json"),
            "--leader", "0x1572c"]
raise SystemExit(gen_block.main())
