#!/usr/bin/env python3
"""Collect Assume and AssumeReg events from the pinned writeSuccess traces."""

import argparse
import json
import re
from collections import Counter
from pathlib import Path


REGION_RANGES = (
    (0x10190, 0x101C4),
    (0x101D4, 0x101F8),
    (0x14D30, 0x15A14),
    (0x15B9C, 0x15D38),
)
LOOKUP = re.compile(
    r"Lemma lookup_a([0-9a-f]+)\s*:\s*\n"
    r"\s*lookup 0x[0-9a-f]+ = Some \("
    r"IslaTraces\.([A-Za-z0-9_]+)\.a[0-9a-f]+\.a[0-9a-f]+\)\."
)


def in_region(address: int) -> bool:
    return any(start <= address < stop for start, stop in REGION_RANGES)


def indexed_traces(index: Path, trace_root: Path) -> list[tuple[int, Path]]:
    entries_by_address = {}
    for match in LOOKUP.finditer(index.read_text()):
        address = int(match.group(1), 16)
        if in_region(address):
            theory = match.group(2)
            entries_by_address[address] = trace_root / theory / f"a{address:x}.v"
    for trace_path in trace_root.glob("write_success_*/a*.v"):
        match = re.fullmatch(r"a([0-9a-f]+)\.v", trace_path.name)
        if match is None:
            continue
        address = int(match.group(1), 16)
        if not in_region(address) or address in entries_by_address:
            continue
        previous = entries_by_address.get(address)
        if previous is None or ("monolithic" in previous.parent.name and
                                "monolithic" not in trace_path.parent.name):
            entries_by_address[address] = trace_path
    return sorted(entries_by_address.items())


def event_term(line: str, constructor: str) -> str | None:
    stripped = " ".join(line.strip().split())
    prefix = constructor + " "
    if not stripped.startswith(prefix) or " :t:" not in stripped:
        return None
    return stripped.rsplit(" :t:", 1)[0][len(prefix):]


def collect(index: Path, trace_root: Path) -> dict:
    assume_occurrences: list[dict] = []
    assume_reg_occurrences: list[dict] = []
    traces = indexed_traces(index, trace_root)
    for address, trace_path in traces:
        if not trace_path.is_file():
            raise FileNotFoundError(trace_path)
        relative = trace_path.relative_to(trace_root).as_posix()
        for line_number, line in enumerate(trace_path.read_text().splitlines(), 1):
            assume = event_term(line, "Assume")
            if assume is not None:
                assume_occurrences.append({
                    "pc": f"0x{address:x}",
                    "trace": relative,
                    "line": line_number,
                    "term": assume,
                })
            assume_reg = event_term(line, "AssumeReg")
            if assume_reg is not None:
                assume_reg_occurrences.append({
                    "pc": f"0x{address:x}",
                    "trace": relative,
                    "line": line_number,
                    "term": assume_reg,
                })

    def distinct(occurrences: list[dict]) -> list[dict]:
        counts = Counter(item["term"] for item in occurrences)
        first = {}
        for item in occurrences:
            first.setdefault(item["term"], item)
        return [dict(first[term], occurrences=counts[term]) for term in sorted(first)]

    return {
        "ranges": [[f"0x{start:x}", f"0x{stop:x}"]
                   for start, stop in REGION_RANGES],
        "trace_count": len(traces),
        "assume_occurrence_count": len(assume_occurrences),
        "assume_reg_occurrence_count": len(assume_reg_occurrences),
        "assumes": distinct(assume_occurrences),
        "assume_regs": distinct(assume_reg_occurrences),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", required=True, type=Path)
    parser.add_argument("--trace-root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    inventory = collect(args.index, args.trace_root)
    args.output.write_text(json.dumps(inventory, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
