#!/usr/bin/env python3
"""Build a checked CFG certificate for the writeSuccess native region.

The certificate records the complete reachable block graph.  It does not
record one observed execution path.  Loop back edges therefore remain visible
in the certificate and cannot be removed by selecting a convenient path.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Iterable

from elf_identity import load_image_sha256


CONTRACT = "writeSuccess"
FUNCTION = "ssz_decode_observation.writeSuccess"
ENTRY_PC = 0x14D30
EXIT_PC = 0x14D10
INSTRUCTION_BOUND = 950

# This is the Level 1 execution region.  The exit PC is intentionally not in
# this set.  A return leaves the region through the separate exit edge.
LEVEL1_REGION = [
    (0x10190, 0x101C4),
    (0x101D4, 0x101F8),
    (0x14D30, 0x15A14),
    (0x15B9C, 0x15D38),
]

EXPECTED_BACK_EDGES = {
    (0x153B4, 0x151D4),
    (0x153A8, 0x15228),
    (0x15558, 0x153D4),
    (0x15614, 0x15590),
    (0x1565C, 0x14F00),
    (0x156DC, 0x15694),
    (0x158D4, 0x15754),
}

HEX = re.compile(r"^0x[0-9a-f]+$", re.IGNORECASE)


def _region_contains(pc: int, region: Iterable[tuple[int, int]]) -> bool:
    return any(start <= pc < stop for start, stop in region)


def _as_pc(value: object, *, field: str) -> int:
    if isinstance(value, int):
        return value
    if isinstance(value, str) and HEX.match(value):
        return int(value, 16)
    raise ValueError(f"{field} must be an integer or hexadecimal PC")


def _function(cfg: dict) -> dict:
    rows = [row for row in cfg.get("functions", []) if row.get("name") == FUNCTION]
    if len(rows) != 1:
        raise ValueError(f"expected one {FUNCTION} CFG function")
    return rows[0]


def _graph(cfg: dict) -> tuple[dict[int, dict], dict[int, list[int]]]:
    function = _function(cfg)
    blocks: dict[int, dict] = {}
    for block in function.get("blocks", []):
        start = _as_pc(block.get("start"), field="block start")
        if start in blocks:
            raise ValueError(f"duplicate CFG block at {start:#x}")
        instructions = block.get("instructions", [])
        if not instructions:
            raise ValueError(f"CFG block at {start:#x} has no instructions")
        blocks[start] = block
    if ENTRY_PC not in blocks:
        raise ValueError(f"missing writeSuccess entry block at {ENTRY_PC:#x}")
    edges: dict[int, list[int]] = {}
    for start, block in blocks.items():
        targets = [_as_pc(value, field="CFG successor")
                   for value in block.get("successors", [])]
        unknown = sorted(set(targets) - blocks.keys())
        if unknown:
            raise ValueError(
                f"unknown CFG edge {start:#x} -> {unknown[0]:#x}")
        edges[start] = list(dict.fromkeys(targets))
    return blocks, edges


def _reachable(edges: dict[int, list[int]]) -> set[int]:
    seen: set[int] = set()
    pending = [ENTRY_PC]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        pending.extend(edges[current])
    return seen


def _back_edges(edges: dict[int, list[int]], reachable: set[int]) -> set[tuple[int, int]]:
    """Return DFS back edges, which are exactly the seven loop edges here."""
    colour: dict[int, int] = {}
    result: set[tuple[int, int]] = set()

    def visit(node: int) -> None:
        colour[node] = 1
        for target in edges[node]:
            if target not in reachable:
                continue
            if colour.get(target) == 1:
                result.add((node, target))
            elif colour.get(target, 0) == 0:
                visit(target)
        colour[node] = 2

    visit(ENTRY_PC)
    return result


def _instruction_pcs(blocks: dict[int, dict], reachable: set[int]) -> list[int]:
    pcs = []
    for start in sorted(reachable):
        for instruction in blocks[start].get("instructions", []):
            pc = _as_pc(instruction.get("pc"), field="instruction PC")
            pcs.append(pc)
    if len(pcs) != len(set(pcs)):
        raise ValueError("reachable CFG contains duplicate instruction PCs")
    return sorted(pcs)


def _terminal_edges(blocks: dict[int, dict], reachable: set[int]) -> list[tuple[int, int]]:
    terminals: list[tuple[int, int]] = []
    for start in sorted(reachable):
        instructions = blocks[start].get("instructions", [])
        mnemonic = str(instructions[-1].get("mnemonic", "")).split(maxsplit=1)[0]
        if mnemonic in {"ret", "jr"}:
            terminals.append((_as_pc(instructions[-1]["pc"], field="return PC"), EXIT_PC))
    if not terminals:
        raise ValueError(f"missing return exit {EXIT_PC:#x}")
    if {target for _, target in terminals} != {EXIT_PC}:
        raise ValueError("CFG has an unexpected writeSuccess exit PC")
    return terminals


def _artifact(cfg: dict, elf: Path | None, expected_sha256: str | None) -> dict:
    artifact = cfg.get("artifact")
    if not isinstance(artifact, dict):
        raise ValueError("CFG has no artifact identity")
    identity_scope = artifact.get("identityScope")
    sha256 = artifact.get("sha256")
    if identity_scope != "ELF PT_LOAD memory image":
        raise ValueError("writeSuccess certificate requires ELF PT_LOAD identity")
    if not isinstance(sha256, str) or not re.fullmatch(r"[0-9a-f]{64}", sha256):
        raise ValueError("CFG artifact identity is not a SHA-256 digest")
    expected = expected_sha256.lower() if expected_sha256 else None
    if expected is not None and sha256 != expected:
        raise ValueError("CFG and pinned ELF identities differ")
    if elf is not None:
        actual = load_image_sha256(elf)
        if sha256 != actual:
            raise ValueError("CFG and ELF load-image identities differ")
    return {"identityScope": identity_scope, "sha256": sha256}


def generate(cfg: dict, *, elf: Path | None = None,
             expected_sha256: str | None = None) -> dict:
    """Return a certificate for every reachable CFG edge and instruction."""
    artifact = _artifact(cfg, elf, expected_sha256)
    blocks, edges = _graph(cfg)
    reachable = _reachable(edges)
    pcs = _instruction_pcs(blocks, reachable)
    outside = sorted(pc for pc in pcs if not _region_contains(pc, LEVEL1_REGION))
    if outside:
        raise ValueError(f"reachable PC {outside[0]:#x} is outside the Level 1 region")
    edge_rows = sorted((source, target) for source in reachable
                       for target in edges[source])
    back_edges = _back_edges(edges, reachable)
    if back_edges != EXPECTED_BACK_EDGES:
        missing = sorted(EXPECTED_BACK_EDGES - back_edges)
        unknown = sorted(back_edges - EXPECTED_BACK_EDGES)
        if missing:
            raise ValueError(f"missing CFG back edge {missing[0][0]:#x} -> {missing[0][1]:#x}")
        raise ValueError(f"unexpected CFG back edge {unknown[0][0]:#x} -> {unknown[0][1]:#x}")
    exits = _terminal_edges(blocks, reachable)
    return {
        "schemaVersion": 1,
        "contract": CONTRACT,
        "artifact": artifact,
        "entryPc": ENTRY_PC,
        "exitPcs": [EXIT_PC],
        "region": [{"start": start, "end": stop} for start, stop in LEVEL1_REGION],
        "reachablePcs": pcs,
        "edges": [{"from": source, "to": target} for source, target in edge_rows],
        "backEdges": [{"from": source, "to": target}
                      for source, target in sorted(back_edges)],
        "exitEdges": [{"from": source, "to": target} for source, target in exits],
        # Level 1 assigns 950 instructions to the complete writeSuccess
        # execution region.  This bound includes the proved call regions;
        # dynamic loop visits remain represented by the back edges above.
        "instructionCount": len(pcs),
        "instructionBound": INSTRUCTION_BOUND,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cfg", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--elf", type=Path)
    parser.add_argument("--expected-sha256")
    args = parser.parse_args()
    certificate = generate(json.loads(args.cfg.read_text()), elf=args.elf,
                           expected_sha256=args.expected_sha256)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(certificate, sort_keys=True,
                                      separators=(",", ":")) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
