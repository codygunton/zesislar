#!/usr/bin/env python3
"""Bind the open native record to retained I67 active-count measurements."""

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
STATUS_ROOT = "b30a7d0bcdd3ac03a6a58765e6a1ac5bb7872221"
MEASUREMENT_ROOT = "e17a8888ac3aed392397113fb97d0a244a2bba6e"
I67_SHA256 = "e56b6babca8856a093fcbaec03346d044b8eda8ab601f6f5229efd3e7fc96082"


def binding(path):
    path = Path(path)
    return {"path": str(path.resolve()),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def generate(table_path, *, workspace=None, status_root=None, productions=None):
    workspace = Path(workspace) if workspace is not None else ROOT
    table_binding = binding(table_path)
    if table_binding["sha256"] != I67_SHA256:
        raise ValueError("The retained I67 table hash differs.")
    table_path = Path(table_path).resolve()
    table = json.loads(table_path.read_text())
    measurement_workspace = table_path.parents[2]
    if table["root"] != MEASUREMENT_ROOT:
        raise ValueError("The measurement root differs.")
    source = workspace / "ZesuSsz/Evidence/DecodeItemOpenNativeHypotheses.v"
    text = source.read_text()
    record = re.search(r"Record DecodeItemOpenNativeHypotheses : Prop := \{(.*?)\}\.",
                       text, re.S).group(1)
    fields = re.findall(r"native800d([0-9a-f]{4})\s*:\s*(\w+)", record)
    if len({site for site, _ in fields}) != len(fields):
        raise ValueError("The open record must contain unique closure fields.")
    measurements = {row["block"]: row for row in table["rows"]}
    count_body = re.search(r"Definition decodeItemI67NativeResidualCounts.*?:=\s*(.*?)\]\.", text, re.S).group(1)
    checked_counts = {"0x800d" + site: int(count) if count else None
                      for site, count in re.findall(r"0x800d([0-9a-f]{4}), (?:Some (\d+)%nat|None)", count_body)}
    rows = []
    for site, definition in fields:
        block = "0x800d" + site
        measured = measurements[block]
        if block not in checked_counts or checked_counts[block] != measured.get("goal_count"):
            raise ValueError("The checked active count differs: " + block)
        source_binding = binding(measured["source"])
        if source_binding["sha256"] != measured["source_sha256"]:
            raise ValueError("The measured source hash differs: " + block)
        captures = []
        for capture in measured.get("captures", []):
            for kind in ("json", "text"):
                capture_path = Path(capture[kind])
                if not capture_path.is_absolute():
                    capture_path = measurement_workspace / capture_path
                item = binding(capture_path)
                if item["sha256"] != capture[kind + "_sha256"]:
                    raise ValueError("The capture hash differs: " + block)
                captures.append(item)
        rows.append({"block": block, "closure": "open", "definition": definition,
                     "record_field": "native800d" + site,
                     "printed_active_count": measured.get("goal_count"),
                     "measurement_outcome": measured["outcome"],
                     "statement_sha256": measured["statement_sha256"],
                     "source": source_binding, "captures": captures,
                     "auxiliary_groups": "unavailable"})
    closed = {}
    productions = productions or {}
    definitions = re.findall(r"Definition decodeItemOpenNativeClosure([0-9a-f]{4})\s*:", text)
    for site in sorted(set(definitions) - {site for site, _ in fields}):
        module, theorem = productions.get(site, (
            "ZesuSsz.Proofs.DecodeItem.Auto.Block800d" + site,
            "DesignedBoundary_800d" + site))
        production = workspace / (module.replace(".", "/") + ".v")
        production_text = production.read_text()
        if not re.search(r"Lemma " + re.escape(theorem) + r"\b", production_text):
            raise ValueError("The named production theorem is unavailable: " + site)
        closed[site] = {"theorem": module + "." + theorem, "source": binding(production),
                        "successor_premises": sorted(set(re.findall(
                            r"instr_pre (0x[0-9a-f]+)", production_text)))}
    # Keep the existing 6974 field for readers of the first status schema.
    return {"status_root": status_root or STATUS_ROOT, "measurement_root": MEASUREMENT_ROOT,
            "approved_switches": table["approved_switches"],
            "hint_modules": table["hint_modules"], "open_closures": len(fields),
            "open_record": binding(source), "measurement_table": table_binding,
            "closed_native": closed, "closed_6974": closed.get("6974"),
            "rows": rows,
            "limits": ["Counts measure printed active records on e17, not current Root proof states.",
                       "A null count means the final active count is unavailable.",
                       "The inventory supplies no native closure for the fifteen open statements."]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--i67-table", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = generate(args.i67_table)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
