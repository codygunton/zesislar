"""Check the approved C4 extern axiom names in each generated Sail root."""

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SNAPSHOT = ROOT / "generated/evm-sail-coq/transactions"
SCRATCH = (
    "host_scratch_reserve",
    "host_scratch_store_byte",
    "host_scratch_store_stateless_input",
    "host_scratch_store_word",
    "host_scratch_truncate",
)
APPROVED_BY_ROOT = {
    "decode_legacy_tx": (*SCRATCH, "scratch_keccak256"),
    "decode_access_list_tx": (*SCRATCH, "scratch_keccak256"),
    "decode_fee_market_tx": (*SCRATCH, "scratch_keccak256"),
    "decode_blob_tx": (*SCRATCH, "scratch_keccak256"),
    "decode_set_code_tx": (*SCRATCH, "scratch_keccak256"),
    "rlp_decode_tx": (*SCRATCH, "stateless_input_keccak256", "scratch_keccak256"),
}
AXIOM = re.compile(r"^Axiom\s+([A-Za-z_][A-Za-z_0-9]*)\s*:", re.MULTILINE)


def check() -> None:
    source = json.loads((SNAPSHOT / "SOURCE.json").read_text())
    if set(source["roots"]) != set(APPROVED_BY_ROOT):
        raise ValueError("C4 root set differs from the approved six roots")
    manifest = {entry["name"] for entry in source["c4PremiseCandidates"]}
    approved = set().union(*map(set, APPROVED_BY_ROOT.values()))
    if manifest != approved or len(source["c4PremiseCandidates"]) != 7:
        raise ValueError("C4 manifest differs from the seven approved host names")
    for root, expected in APPROVED_BY_ROOT.items():
        declared = tuple(AXIOM.findall((SNAPSHOT / f"evm_{root}.v").read_text()))
        reached = tuple(source["reachedExternsByRoot"][root])
        if declared != expected or set(reached) != set(expected):
            raise ValueError(
                f"{root}: declared {declared}, reached {reached}, expected {expected}"
            )
    print("C4 host axiom gate: six roots, seven approved names, no extra axioms")


if __name__ == "__main__":
    check()
