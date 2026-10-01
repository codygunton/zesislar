"""Regenerate the dispatched header blocks with the requested call contract.
Run from the repository root. This script uses the existing block generator.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
sys.path[:0] = [str(ROOT / "tools/block"), str(ROOT / "tools/det")]
import call_sites
import gen_block

original_contracts = call_sites.contracts

def dispatched_contracts(*args, **kwargs):
    table = original_contracts(*args, **kwargs)
    table[0x10190] = {
        "name": "zesuWriteOutputCallSpec",
        "module": "ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls",
    }
    return table

call_sites.contracts = dispatched_contracts
sys.argv = ["gen_block.py", "--states", str(Path(__file__).with_name("header_states.json"))]
for leader in ["0x14e28", "0x14e38", "0x14e48", "0x14e58", "0x14e68", "0x14e78"]:
    sys.argv += ["--leader", leader]
raise SystemExit(gen_block.main())
