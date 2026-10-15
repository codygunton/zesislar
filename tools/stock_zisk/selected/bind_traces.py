#!/usr/bin/env python3
"""Bind one selected function without changing the platform trace binder."""
import argparse
import hashlib
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[3]
PLATFORM = ROOT / "tools/stock_zisk/platform"
sys.path.insert(0, str(PLATFORM))
from function_binding import bind


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--function", required=True)
    parser.add_argument("--trace-name", default="closure")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    result = bind(ROOT, args.out.resolve(), args.function, args.trace_name, check=args.check)
    result["generator_sources"] = {
        str(path.relative_to(ROOT)): sha(path) for path in
        (Path(__file__).resolve(), PLATFORM / "function_binding.py",
         PLATFORM / "indexes.py", PLATFORM / "exports.py")}
    report = args.report or (ROOT / "generated/isla-traces/stock-zisk" /
                             args.trace_name / "function-binding.json")
    rendered = json.dumps(result, indent=2) + "\n"
    if args.check:
        if not report.is_file() or report.read_text() != rendered:
            raise ValueError("The selected-function binding report is stale.")
    else:
        report.parent.mkdir(parents=True, exist_ok=True)
        report.write_text(rendered)
    print(json.dumps({"function": result["function"],
                      "instruction_count": result["instruction_count"],
                      "logical_module": result["logical_module"],
                      "report": str(report), "sha256": sha(report)}))


if __name__ == "__main__":
    main()
