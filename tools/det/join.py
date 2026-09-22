#!/usr/bin/env python3
"""Join the WP1 measurements into one row per lemma.

- `stepped` gives the frame the search sees at a fixed 600-step budget and
  how many of those hypotheses are memory points.
- `counted` gives the seconds the whole block automation costs, and how
  many instructions it stepped, at almost no measurement overhead.
- `prefix` gives what the probe pays to compile the module text before the
  automation runs, so the automation seconds can be isolated.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def read(path: Path) -> dict:
    out = {}
    if not path or not path.exists():
        return out
    for line in path.read_text().split("\n"):
        if line.strip():
            record = json.loads(line)
            if record.get("reached_end"):
                out[(record["module"], record["lemma"])] = record
    return out


def outcomes(path: Path) -> dict:
    """Every record, successful or not, for the outcome and the budget."""
    out = {}
    for line in (path.read_text().split("\n") if path.exists() else []):
        if line.strip():
            record = json.loads(line)
            key = (record["module"], record["lemma"])
            if key not in out or record.get("reached_end"):
                out[key] = record
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frames", type=Path, required=True)
    parser.add_argument("--counted", type=Path, required=True)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    arguments = parser.parse_args()
    frames = read(arguments.frames)
    counted_all = outcomes(arguments.counted)
    prefixes = read(arguments.prefix)
    rows = []
    for key, frame in frames.items():
        run = counted_all.get(key)
        if run is None:
            continue
        head = prefixes.get(key, {}).get("wall", 0.0)
        seconds = run.get("wall", 0.0)
        rows.append({
            "module": key[0], "lemma": key[1],
            "frame": frame["frame"], "mapsto": frame["mapsto"],
            "frame_seconds": frame.get("wall", 0.0),
            "instructions": run.get("instructions", 0),
            "instr_pre": run.get("instr_pre", 0),
            "seconds": seconds, "prefix_seconds": head,
            "automation_seconds": round(max(0.05, seconds - head), 2),
            "passes": len(run.get("zesu_run_seconds", [])),
            "outcome": ("closed_or_residual" if run.get("reached_end")
                        else "timeout_or_error"),
            "reached_end": bool(run.get("reached_end")),
        })
    rows.sort(key=lambda row: (row["module"], row["lemma"]))
    arguments.out.parent.mkdir(parents=True, exist_ok=True)
    arguments.out.write_text("".join(json.dumps(r) + "\n" for r in rows))
    complete = [r for r in rows if r["reached_end"] and r["prefix_seconds"]]
    print(f"joined {len(rows)} lemmas; {len(complete)} with a prefix cost "
          f"and a finished run")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
