#!/usr/bin/env python3
"""WP1: run the frame and profile probes over a lemma list.

One record per (lemma, shape). The frame probe gives the hypothesis count the
proof search sees; the profile probe gives the tactic tree with a local and a
total share per tactic. Both run through `tools/coqc_scratch.sh`, under
`nice`, with the concurrency and load rules of the determinism plan.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "residual"))

import probes  # noqa: E402
import timed  # noqa: E402
from capture import MAX_RSS, TACTIC_TIME, gnu_time, limit_env  # noqa: E402
from goals import context_size  # noqa: E402

PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")
SCRATCH = Path("tools/coqc_scratch.sh")
GUARD = Path(__file__).resolve().parents[1] / "resource_guard.sh"


def guard_jobs(requested: int | None = None) -> int:
    """The concurrency memory allows, never more than asked for.

    Threads are a ceiling; memory is the binding limit. The guard computes
    min(48, floor(0.8 * MemAvailable / 6 GiB)).
    """
    if not GUARD.exists():
        return requested or 8
    allowed = int(subprocess.run([str(GUARD), "jobs"], capture_output=True,
                                 text=True).stdout.strip() or 1)
    return min(requested, allowed) if requested else allowed


def wait_for_room() -> None:
    """Block until the guard says another job may start."""
    if GUARD.exists():
        subprocess.run([str(GUARD), "wait"])
        return
    while True:
        running = subprocess.run(["pgrep", "-c", "coqc"], capture_output=True,
                                 text=True).stdout.strip()
        if int(running or 0) < 48 and os.getloadavg()[0] < 80:
            return
        time.sleep(5)


def module_path(name: str) -> Path:
    candidate = Path(name)
    return candidate if candidate.exists() else PROOF_DIR / candidate.name


def run_one(module: str, lemma: str, shape: str, build_dir: Path,
            seconds: int) -> dict:
    path = module_path(module)
    source = probes.probe_text(path, lemma, shape)
    probe_dir = build_dir / "det" / "probes"
    probe_dir.mkdir(parents=True, exist_ok=True)
    probe = probe_dir / f"{path.stem}__{lemma}__{shape}.v"
    probe.write_text(source)
    wait_for_room()
    command = [*gnu_time(), "timeout", str(seconds + 60), "nice", "-n", "10",
               "bash", str(SCRATCH), str(probe), str(build_dir)]
    started = time.monotonic()
    done = subprocess.run(command, capture_output=True, text=True,
                          env=limit_env(seconds))
    wall = round(time.monotonic() - started, 2)
    output = done.stdout + "\n" + done.stderr
    record = {"module": path.name, "lemma": lemma, "shape": shape,
              "exit": done.returncode, "wall": wall,
              "reached_end": probes.END in output}
    timing = TACTIC_TIME.findall(output)
    record["zesu_run_seconds"] = [float(value) for value in timing]
    rss = MAX_RSS.search(done.stderr)
    if rss:
        record["rss_mib"] = int(rss.group("kb")) // 1024
    text = probes.marked(output)
    if shape in {"timed", "counted"}:
        record.update(timed.measurements(output))
        (probe_dir / f"{path.stem}__{lemma}__{shape}.txt").write_text(text[-200000:])
    elif shape == "qed":
        found = re.search(r"Finished transaction in ([0-9.]+) secs", output)
        record["qed_seconds"] = float(found.group(1)) if found else 0.0
    elif shape == "prefix":
        pass
    else:
        frame, points = context_size(text)
        record.update({"frame": frame, "mapsto": points})
        (probe_dir / f"{path.stem}__{lemma}__{shape}.txt").write_text(text)
    if not record["reached_end"]:
        record["error_lines"] = [line for line in output.split("\n")
                                 if line.strip().startswith("Error")][:5]
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--set", type=Path, required=True,
                        help="one MODULE:LEMMA per line")
    parser.add_argument("--shape", default="stepped",
                        choices=sorted(probes.BODIES))
    parser.add_argument("--build-dir", type=Path,
                        default=Path("_build/agents/det"))
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--seconds", type=int, default=900)
    parser.add_argument("--out", type=Path, required=True)
    arguments = parser.parse_args()
    targets = [line.split(":", 1) for line in
               arguments.set.read_text().split("\n") if ":" in line]
    arguments.out.parent.mkdir(parents=True, exist_ok=True)
    done = set()
    if arguments.out.exists():
        for line in arguments.out.read_text().split("\n"):
            if line.strip():
                record = json.loads(line)
                # Only a probe that reached its end marker is finished work:
                # one that failed because its module was not built yet must
                # run again on the next pass.
                if record.get("reached_end"):
                    done.add((record["module"], record["lemma"],
                              record["shape"]))
    jobs = guard_jobs(arguments.jobs)
    print(f"resource guard allows {jobs} concurrent jobs", file=sys.stderr,
          flush=True)
    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        futures = {
            pool.submit(run_one, module, lemma, arguments.shape,
                        arguments.build_dir, arguments.seconds):
            (module, lemma)
            for module, lemma in targets
            if (Path(module).name, lemma, arguments.shape) not in done}
        with arguments.out.open("a") as handle:
            for future in concurrent.futures.as_completed(futures):
                module, lemma = futures[future]
                try:
                    record = future.result()
                except Exception as error:  # noqa: BLE001
                    record = {"module": Path(module).name, "lemma": lemma,
                              "shape": arguments.shape, "exit": -1,
                              "error_lines": [str(error)]}
                handle.write(json.dumps(record) + "\n")
                handle.flush()
                mark = record.get("frame", record.get("instructions", ""))
                print(f"{record['shape']:8s} {record.get('wall', 0):8.1f}s "
                      f"{mark!s:>8} {record['module']}:{lemma}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
