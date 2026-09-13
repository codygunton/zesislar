#!/usr/bin/env python3
"""Print failed compiler diagnostics without Dune's environment records."""

import argparse
import json
from pathlib import Path

from coqc_recipe import trace_events


def failed_compilers(data: bytes, line_limit: int = 12):
    for event in trace_events(data):
        if not isinstance(event, list) or event[:2] != ["process", "finish"]:
            continue
        fields = {field[0]: field[1:] for field in event[3:]
                  if isinstance(field, list) and field}
        if Path(fields.get("prog", [""])[0]).name != "coqc":
            continue
        exit_code = fields.get("exit", ["0"])[0]
        if exit_code == "0":
            continue
        targets = fields.get("target_files", [[]])[0]
        output = fields.get("stdout", [""])[0] + fields.get("stderr", [""])[0]
        lines = output.splitlines()
        start = next((max(0, index - 1) for index, line in enumerate(lines)
                      if "Error:" in line), max(0, len(lines) - line_limit))
        yield {"exit": exit_code,
               "targets": [str(target) for target in targets],
               "diagnostic": "\n".join(lines[start:start + line_limit])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("build_dir", type=Path)
    parser.add_argument("--lines", type=int, default=12)
    args = parser.parse_args()
    if args.lines < 1:
        parser.error("--lines must be positive")
    for failure in failed_compilers((args.build_dir / "trace.csexp").read_bytes(), args.lines):
        print(json.dumps(failure, sort_keys=True))


if __name__ == "__main__":
    main()
