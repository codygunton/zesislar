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
EXECUTION_INSTRUCTION_COUNT = 950

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


def _phase_ranks(edges: dict[int, list[int]], reachable: set[int],
                 back_edges: set[tuple[int, int]],
                 terminal_nodes: set[int]) -> tuple[dict[int, int], int]:
    """Rank CFG blocks after removing the seven loop back edges."""
    forward = {
        node: [target for target in edges[node]
               if (node, target) not in back_edges]
        for node in reachable
    }
    visiting: set[int] = set()
    ranks: dict[int, int] = {}

    def rank(node: int) -> int:
        if node in ranks:
            return ranks[node]
        if node in visiting:
            raise ValueError("non-back-edge cycle in writeSuccess CFG")
        visiting.add(node)
        successors = forward[node]
        if node in terminal_nodes:
            value = 0
        elif not successors:
            # A loop latch can have only its back edge after edge removal.
            # Its phase rank is the reset point for the enclosing loop.
            value = 0
        else:
            value = max(rank(target) + 1 for target in successors)
        visiting.remove(node)
        ranks[node] = value
        return value

    rank(ENTRY_PC)
    if set(ranks) != reachable:
        missing = sorted(reachable - set(ranks))[0]
        raise ValueError(f"CFG block {missing:#x} cannot reach a terminal without a back edge")
    for source, targets in edges.items():
        for target in targets:
            if (source, target) not in back_edges and ranks[target] >= ranks[source]:
                raise ValueError(f"phase rank does not decrease on {source:#x} -> {target:#x}")
    return ranks, max(ranks.values()) + 1


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


def _bounded_path_length(edges: dict[int, list[int]], terminal_nodes: set[int],
                         back_edges: set[tuple[int, int]], budgets: dict[tuple[int, int], int]) -> int:
    """Compute the longest path while enforcing each declared loop budget."""
    missing = back_edges - budgets.keys()
    if missing:
        source, target = sorted(missing)[0]
        raise ValueError(f"missing loop budget for back edge {source:#x} -> {target:#x}")
    if any(value < 0 for value in budgets.values()):
        raise ValueError("loop budgets must be non-negative")
    edge_order = sorted(back_edges)
    start = (ENTRY_PC, (0,) * len(edge_order))
    pending = [start]
    longest: dict[tuple[int, tuple[int, ...]], int] = {start: 1}
    best = 0
    while pending:
        node, counts = pending.pop()
        length = longest[(node, counts)]
        if node in terminal_nodes:
            # Add the synthetic terminal exit PC to the path length.
            best = max(best, length + 1)
            continue
        for target in edges[node]:
            next_counts = list(counts)
            edge = (node, target)
            if edge in budgets:
                index = edge_order.index(edge)
                next_counts[index] += 1
                if next_counts[index] > budgets[edge]:
                    continue
            state = (target, tuple(next_counts))
            if length + 1 > longest.get(state, 0):
                longest[state] = length + 1
                pending.append(state)
    if not best:
        raise ValueError("bounded CFG paths do not reach the writeSuccess exit")
    return best


def generate(cfg: dict, *, elf: Path | None = None,
             expected_sha256: str | None = None,
             loop_budgets: dict[tuple[int, int], int] | None = None) -> dict:
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
    terminal_sources = {source for source, _ in exits}
    terminal_nodes = {
        start for start in reachable
        if any(_as_pc(instruction.get("pc"), field="instruction PC")
               in terminal_sources
               for instruction in blocks[start].get("instructions", []))
    }
    phase_ranks, phase_bound = _phase_ranks(
        edges, reachable, back_edges, terminal_nodes)
    budgets = loop_budgets or {}
    if loop_budgets:
        missing = back_edges - budgets.keys()
        if missing:
            source, target = sorted(missing)[0]
            raise ValueError(f"missing loop budget for back edge {source:#x} -> {target:#x}")
    result = {
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
        "phaseRank": [{"pc": pc, "rank": phase_ranks[pc]}
                      for pc in sorted(reachable)],
        "phaseBound": phase_bound,
        # Level 1 reports 950 static instructions across the complete
        # execution region.  This value is not a dynamic path bound.
        "instructionCount": len(pcs),
        "executionInstructionCount": EXECUTION_INSTRUCTION_COUNT,
    }
    if loop_budgets:
        result["loopBudgets"] = [{"from": source, "to": target,
                                  "maxTraversals": budgets[(source, target)]}
                                 for source, target in sorted(back_edges)]
        result["pathBound"] = _bounded_path_length(
            edges, terminal_nodes, back_edges, budgets)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cfg", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--elf", type=Path)
    parser.add_argument("--expected-sha256")
    parser.add_argument("--loop-budget", action="append", default=[],
                        metavar="FROM:TO:COUNT")
    args = parser.parse_args()
    budgets = {}
    for item in args.loop_budget:
        source, target, count = item.split(":")
        budgets[(_as_pc(source, field="loop budget source"),
                 _as_pc(target, field="loop budget target"))] = int(count)
    certificate = generate(json.loads(args.cfg.read_text()), elf=args.elf,
                           expected_sha256=args.expected_sha256,
                           loop_budgets=budgets or None)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(certificate, sort_keys=True,
                                      separators=(",", ":")) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
