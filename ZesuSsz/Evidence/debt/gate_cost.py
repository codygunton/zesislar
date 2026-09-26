"""Per-module build cost of ZesuSsz from Dune trace files.

Dune writes `trace.csexp` in each build directory. Each `process finish`
event carries the wall time and the rusage of one `coqc`. This script
reads every trace under the given roots, keeps successful `coqc` runs of
`ZesuSsz/*.v`, and writes, per module, the latest run (wall and CPU seconds, peak RSS)
and the maximum over all runs since `--since`.

The gate logs themselves carry no per-module times, so this is the only
per-module record. Environment blocks in the traces are never read out.
"""

import argparse
import json
import os
import time
from pathlib import Path

from csexp import parse_all


def trace_files(roots, since):
    for root in roots:
        for dirpath, dirnames, filenames in os.walk(root):
            # Skip the per-module source copies: traces live at build roots.
            dirnames[:] = [d for d in dirnames if d not in ("default", ".sandbox")]
            if "trace.csexp" in filenames:
                path = Path(dirpath) / "trace.csexp"
                if path.stat().st_mtime >= since:
                    yield path


def coqc_runs(path):
    for event in parse_all(path.read_bytes()):
        if not (isinstance(event, list) and event[:2] == ["process", "finish"]):
            continue
        fields = {x[0]: x[1] for x in event[3:] if isinstance(x, list) and len(x) == 2}
        if not fields.get("prog", "").endswith("/coqc") or fields.get("exit") != "0":
            continue
        source = fields["process_args"][-1]
        if not (source.startswith("ZesuSsz/") and source.endswith(".v")):
            continue
        rusage = {k: v for k, v in fields.get("rusage", [])}
        start_ns, dur_ns = event[2]
        yield {
            "module": source,
            "start": int(start_ns) / 1e9,
            "seconds": int(dur_ns) / 1e9,
            "cpu": (int(rusage.get("user_cpu_time", 0))
                    + int(rusage.get("system_cpu_time", 0))) / 1e9,
            "rss_gib": int(rusage.get("maxrss", 0)) / 1024 / 1024,
            "trace": str(path),
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--roots", nargs="+", required=True)
    parser.add_argument("--since", default="2026-09-20")
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    since = time.mktime(time.strptime(args.since, "%Y-%m-%d"))

    latest, worst = {}, {}
    for path in trace_files(args.roots, since):
        for run in coqc_runs(path):
            name = run["module"]
            if name not in latest or run["start"] > latest[name]["start"]:
                latest[name] = run
            w = worst.setdefault(name, {"seconds": 0.0, "cpu": 0.0, "rss_gib": 0.0, "runs": 0})
            w["seconds"] = max(w["seconds"], run["seconds"])
            w["cpu"] = max(w["cpu"], run["cpu"])
            w["rss_gib"] = max(w["rss_gib"], run["rss_gib"])
            w["runs"] += 1

    out = {}
    for name, run in latest.items():
        out[name] = {
            "seconds": round(run["seconds"], 3),
            "cpu": round(run["cpu"], 3),
            "rss_gib": round(run["rss_gib"], 3),
            "date": time.strftime("%Y-%m-%d", time.localtime(run["start"])),
            "trace": run["trace"],
            "max_seconds": round(worst[name]["seconds"], 3),
            "max_cpu": round(worst[name]["cpu"], 3),
            "max_rss_gib": round(worst[name]["rss_gib"], 3),
            "runs": worst[name]["runs"],
        }
    Path(args.out).write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    print(f"{len(out)} modules from traces since {args.since}")


if __name__ == "__main__":
    main()
