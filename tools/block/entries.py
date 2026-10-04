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


def address(value):
    return int(value, 0) if isinstance(value, str) else value


def blocks(cfg, entries, function_name):
    functions = json.loads(cfg.read_text())["functions"]
    selected = [f for f in functions if f["name"] == function_name]
    if len(selected) != 1:
        raise ValueError(f"The CFG must contain exactly one function named {function_name}.")
    function = selected[0]
    result = []
    for block in function["blocks"]:
        instructions = block.get("instructions")
        if instructions is None:
            instructions = [row for row in function["rows"]
                            if address(block["start"]) <= row["pc"] < address(block["end"])]
        if not instructions:
            raise ValueError("The CFG contains an empty block.")
        tail = instructions[-1]
        mnemonic = tail["mnemonic"]
        kind = tail.get("kind")
        if kind is None:
            kind = ("call" if mnemonic in ("jal", "jalr") else
                    "return" if mnemonic == "ret" else "jump" if mnemonic == "j" else
                    "branch" if mnemonic.startswith("b") else "fall")
        leader = hex(address(block.get("id", block.get("start"))))
        picks = entries.get(leader)
        # scan() returns candidate lists, while persisted entries contain one pick.
        entry = picks[0] if isinstance(picks, list) and picks else picks
        result.append(dict(leader=leader, last=hex(address(tail["pc"])), n=len(instructions),
                           kind="ret" if kind == "return" else kind,
                           succ=[hex(address(pc)) for pc in block["successors"]] or
                                (["ret"] if kind == "return" else []),
                           instructions=instructions,
                           pick=[entry["lemma"], entry["module"]] if entry else None))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cfg", type=Path, default=ROOT / "build/stock-zisk/cfg.json")
    parser.add_argument("--targets", action="store_true", help="Print selected Dune proof targets.")
    parser.add_argument("--output", type=Path, default=ROOT / "build/stock-zisk/block_entries.json")
    parser.add_argument("--function", help="Select an exact CFG function name.")
    parser.add_argument("--proof-dir", type=Path, required=True)
    args = parser.parse_args()
    if not args.proof_dir.is_dir():
        parser.error(f"The proof directory is absent: {args.proof_dir}")
    if args.targets:
        selected = json.loads(args.output.read_text()) if args.output.exists() else {
            leader: candidates[0] for leader, candidates in scan(args.proof_dir).items()}
        print(" ".join(str(args.proof_dir / f"{module}.vo")
                       for module in sorted({entry["module"] for entry in selected.values()})))
        return
    if not args.function:
        parser.error("--function is required to select CFG blocks.")
    found = scan(args.proof_dir)
    existing = json.loads(args.output.read_text()) if args.output.exists() else {}
    leaders = {block["leader"] for block in blocks(args.cfg, {}, args.function)}
    result = {}
    for leader in sorted((existing or found).keys() & leaders):
        candidates = found.get(leader, [])
        selected = existing.get(leader, candidates[0] if candidates else None)
        if selected not in candidates:
            raise ValueError(f"The selected entry for {leader} is absent.")
        result[leader] = selected
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
