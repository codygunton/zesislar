"""Read CFG blocks and map their leaders to merged proof entries."""
import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/residual"))
from modules import parse_module

ADDRESS = re.compile(r"instr_(?:body|pre)\s+\(?\s*(0x[0-9a-fA-F]+|\d+)")


def scan(directory):
    entries = {}
    for path in sorted(directory.glob("*.v")):
        lines = path.read_text().splitlines()
        for proof in parse_module(path):
            statement = "\n".join(lines[proof.declaration_line:proof.proof_line])
            matches = list(ADDRESS.finditer(statement))
            if not matches:
                continue
            leader = hex(int(matches[-1].group(1), 0))
            entries.setdefault(leader, []).append(dict(module=path.stem, lemma=proof.name))
    return entries


def blocks(cfg, entries):
    functions = json.loads(cfg.read_text())["functions"]
    function = next(f for f in functions if f["name"].endswith(".writeSuccess"))
    result = []
    for block in function["blocks"]:
        tail = block["instructions"][-1]
        mnemonic = tail["mnemonic"]
        kind = "call:" + tail["operands"] if mnemonic in ("jal", "jalr") else (
            "ret" if mnemonic == "ret" else "jump" if mnemonic == "j" else
            "branch" if mnemonic.startswith("b") else "fall")
        entry = entries.get(block["id"])
        result.append(dict(leader=block["id"], last=hex(tail["pc"]), n=block["instructionCount"], kind=kind,
                           succ=block["successors"] or (["ret"] if mnemonic == "ret" else []),
                           instructions=block["instructions"],
                           pick=[entry["lemma"], entry["module"]] if entry else None))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cfg", type=Path, default=ROOT / "build/endpoint-cfg/zesu-cfg.json")
    parser.add_argument("--targets", action="store_true", help="Print selected Dune proof targets.")
    parser.add_argument("--output", type=Path, default=ROOT / "ZesuSsz/Evidence/det/block_entries.json")
    args = parser.parse_args()
    if args.targets:
        selected = json.loads(args.output.read_text())
        print(" ".join(f"ZesuSsz/Proofs/WriteSuccess/{module}.vo"
                       for module in sorted({entry["module"] for entry in selected.values()})))
        return
    found = scan(ROOT / "ZesuSsz/Proofs/WriteSuccess")
    existing = json.loads(args.output.read_text()) if args.output.exists() else {}
    leaders = {block["leader"] for block in blocks(args.cfg, {})}
    result = {}
    for leader in sorted((existing or found).keys() & leaders):
        candidates = found.get(leader, [])
        selected = existing.get(leader, candidates[0] if candidates else None)
        if selected not in candidates:
            raise ValueError(f"The selected entry for {leader} is absent.")
        result[leader] = selected
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
