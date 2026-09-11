#!/usr/bin/env python3
"""Build the writeSuccess instruction-to-proof coverage matrix."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEVEL1 = ROOT / "ZesuSsz/Generated/Level1.v"
PROOFS = ROOT / "ZesuSsz/Proofs/WriteSuccess"
PROGRESS = ROOT / "contracts/viewer-progress.json"


@dataclass(frozen=True)
class Region:
    name: str
    start: int
    end: int


REGIONS = (
    Region("helper: write_output", 0x10190, 0x101C4),
    Region("helper: memcpy", 0x101D4, 0x101F8),
    Region("prologue", 0x14D30, 0x14E00),
    Region("header and value block", 0x14E00, 0x14F04),
    Region("transactions loop", 0x14F04, 0x151D0),
    Region("access lists", 0x151D0, 0x15228),
    Region("storage keys", 0x15228, 0x153B4),
    Region("access lists", 0x153B4, 0x153C0),
    Region("transactions loop", 0x153C0, 0x153D4),
    Region("blob hashes", 0x153D4, 0x15564),
    Region("transactions loop", 0x15564, 0x15590),
    Region("authorizations", 0x15590, 0x15620),
    Region("transactions loop", 0x15620, 0x15668),
    Region("post-transactions", 0x15668, 0x15694),
    Region("withdrawals", 0x15694, 0x156E8),
    Region("post-withdrawals", 0x156E8, 0x15744),
    Region("suffix hashes", 0x15744, 0x158E0),
    Region("tail", 0x158E0, 0x159D8),
    Region("epilogue", 0x159D8, 0x15A14),
    Region("Encoder.boolean", 0x15B9C, 0x15BC8),
    Region("Encoder.optional", 0x15BC8, 0x15C10),
    Region("Encoder.byte_lists", 0x15C10, 0x15C6C),
    Region("Encoder.bytes", 0x15C6C, 0x15CB0),
    Region("Encoder.u256", 0x15CB0, 0x15D10),
    Region("Encoder.int", 0x15D10, 0x15D38),
)


# Helper functions do not appear in viewer-progress.json proofRegions.
HELPER_COVERAGE = (
    (0x10190, 0x101C4, "zesu_write_output_call_correct"),
    (0x101D4, 0x101F8, "zesu_memcpy_call_correct"),
    (0x15B9C, 0x15BC8, "zesu_encoder_boolean_call_correct"),
    (0x15BC8, 0x15C10, "zesu_encoder_optional_u64_call_correct"),
    (0x15C10, 0x15C6C, "write_success_byte_lists"),
    (0x15C6C, 0x15CB0, "zesu_encoder_bytes_call_correct"),
    (0x15CB0, 0x15D10, "zesu_encoder_u256_call_correct"),
    (0x15D10, 0x15D38, "zesu_encoder_int_call_correct"),
    # The viewer file still uses five pre-composition theorem names here.
    (0x158E0, 0x15930, "write_success_native_suffix_bytes_158e0_to_15930"),
    (0x15680, 0x15694, "block_15680"),
    # These checked composition lemmas postdate the viewer coverage data.
    (0x156E8, 0x15700, "write_success_suffix_int_pair"),
    (0x15700, 0x15718, "block_15700"),
    (0x15718, 0x1571C, "block_15718"),
    (0x1571C, 0x15728, "block_1571c"),
    (0x15728, 0x1572C, "block_15728"),
    (0x1572C, 0x1573C, "write_success_suffix_root_output"),
    (0x1573C, 0x15740, "write_success_suffix_hashes_entry"),
    (0x15750, 0x15754, "write_success_suffix_hashes_entry_15750_handoff"),
    (0x159B8, 0x159C8, "write_success_suffix_optional_u64_159b8"),
    (0x159B0, 0x159B8, "block_159b0"),
    (0x159D4, 0x159D8, "write_success_post_159d4_byte_lists_call"),
)


def parse_int(value: str) -> int:
    return int(value, 0)


def execution_pcs() -> list[int]:
    text = LEVEL1.read_text()
    match = re.search(
        r"Definition writeSuccessExecutionPcRanges.*?:=\s*\[(.*?)\]\.\s*"
        r"Definition writeSuccessExitPcs",
        text,
        re.DOTALL,
    )
    if match is None:
        raise SystemExit(f"cannot find writeSuccessExecutionPcRanges in {LEVEL1}")
    ranges = [
        (parse_int(start), parse_int(end))
        for start, end in re.findall(r"\((0x[0-9a-fA-F]+),\s*(0x[0-9a-fA-F]+)\)", match.group(1))
    ]
    pcs = [pc for start, end in ranges for pc in range(start, end, 4)]
    if len(pcs) != len(set(pcs)):
        raise SystemExit("writeSuccessExecutionPcRanges overlap")
    return pcs


def theorem_index() -> dict[str, list[Path]]:
    declaration = re.compile(
        r"(?m)^(?:(?:Local|Global)\s+)?(?:Lemma|Theorem|Corollary)\s+([A-Za-z0-9_']+)"
    )
    result: dict[str, list[Path]] = {}
    for path in sorted(PROOFS.glob("*.v")):
        for name in declaration.findall(path.read_text()):
            result.setdefault(name, []).append(path.relative_to(ROOT))
    return result


def proof_spans() -> list[tuple[int, int, str, str]]:
    data = json.loads(PROGRESS.read_text())
    spans = list(HELPER_COVERAGE)
    result = [(start, end, theorem, "unconditionally_proven") for start, end, theorem in spans]
    for item in data["proofRegions"]:
        for theorem in (name.strip() for name in item["theorem"].split(";")):
            result.append(
                (
                    parse_int(item["startPc"]),
                    parse_int(item["endPc"]),
                    theorem,
                    item["status"],
                )
            )
    return result


def region_for(pc: int) -> str:
    names = [region.name for region in REGIONS if region.start <= pc < region.end]
    if len(names) != 1:
        raise SystemExit(f"address 0x{pc:x} belongs to {len(names)} regions: {names}")
    return names[0]


def render() -> str:
    pcs = execution_pcs()
    index = theorem_index()
    spans = proof_spans()
    rows: dict[str, list[tuple[int, str, str]]] = {}
    missing_theorems: set[str] = set()

    for pc in pcs:
        candidates = [span for span in spans if span[0] <= pc < span[1]]
        unconditional = [span for span in candidates if span[3] == "unconditionally_proven"]
        unconditional.sort(key=lambda span: (span[1] - span[0], span[2]))
        proof = "gap"
        note = ""
        unresolved = []
        for _start, _end, theorem, _status in unconditional:
            modules = index.get(theorem, [])
            if len(modules) == 1:
                proof = f"`{modules[0]}` / `{theorem}`"
                break
            unresolved.append(theorem)
        if proof == "gap":
            missing_theorems.update(unresolved)
            conditional = sorted(
                {span[2] for span in candidates if span[3] != "unconditionally_proven"}
            )
            if conditional:
                note = "conditional candidate: " + ", ".join(f"`{name}`" for name in conditional)
        rows.setdefault(region_for(pc), []).append((pc, proof, note))

    covered = sum(proof != "gap" for region_rows in rows.values() for _, proof, _ in region_rows)
    lines = [
        "# writeSuccess proof coverage",
        "",
        "Generated by `tools/coverage_matrix.py` from `writeSuccessExecutionPcRanges`,",
        "the checked theorem declarations, and `contracts/viewer-progress.json`.",
        "Only an unconditional proof region counts as coverage.",
        "",
        f"Total: {covered}/{len(pcs)} addresses covered; {len(pcs) - covered} gaps.",
        "",
        "| Region | Covered | Gaps |",
        "| --- | ---: | ---: |",
    ]
    for name, region_rows in rows.items():
        count = sum(proof != "gap" for _, proof, _ in region_rows)
        lines.append(f"| {name} | {count} | {len(region_rows) - count} |")
    for name, region_rows in rows.items():
        lines.extend(("", f"## {name}", "", "| Address | Covering module and lemma | Note |", "| --- | --- | --- |"))
        lines.extend(f"| `0x{pc:x}` | {proof} | {note} |" for pc, proof, note in region_rows)
    if missing_theorems:
        lines.extend(("", "## Unresolved coverage declarations", ""))
        lines.extend(f"- `{name}`" for name in sorted(missing_theorems))
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = render()
    if args.output is None:
        print(output, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)


if __name__ == "__main__":
    main()
