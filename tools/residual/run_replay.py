#!/usr/bin/env python3
"""Replay a set of hand proofs and record every stop the automation hits.

Idempotent per commit, like `run_corpus.py`: a proof that already has a
replay record is skipped. Work runs in a rolling pool under the compute
rules of section 3.
"""

from __future__ import annotations

import argparse
import json
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402
import replay  # noqa: E402
from costs import module_costs  # noqa: E402
from population import population  # noqa: E402
from run_corpus import (PROOF_DIR, current_commit, tier_lemmas,  # noqa: E402
                        wait_for_machine)
from tiers import rule_15_modules  # noqa: E402

REPLAY = Path("ZesuSsz/Evidence/residuals/replay.jsonl")


def iris_proofs(records: list[dict], modules: set[str] | None,
                tier: int | None) -> list[tuple[Path, str]]:
    """The Iris hand proofs of a tier or a module list, cheapest module first."""
    wanted = []
    for record in records:
        if record.get("population") != "iris":
            continue
        if tier is not None and record.get("tier") != tier:
            continue
        if modules and record["module"] not in modules:
            continue
        wanted.append((PROOF_DIR / record["module"], record["lemma"]))
    return wanted


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tier", type=int, default=None)
    parser.add_argument("--modules", type=Path, default=None)
    parser.add_argument("--sample", type=int, default=None,
                        help="a random sample of this many proofs")
    parser.add_argument("--seed", type=int, default=20260918)
    parser.add_argument("--jobs", type=int, default=12)
    parser.add_argument("--coqc-cap", type=int, default=40)
    parser.add_argument("--load-cap", type=float, default=60.0)
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--build-dir", type=Path,
                        default=Path("_build/agents/corpus"))
    parser.add_argument("--scratch", type=Path,
                        default=Path("tools/coqc_scratch.sh"))
    parser.add_argument("--corpus", type=Path, default=corpus.CORPUS)
    parser.add_argument("--output", type=Path, default=REPLAY)
    arguments = parser.parse_args()

    repository = Path.cwd()
    commit = current_commit(repository)
    modules = None
    if arguments.modules:
        modules = {Path(name).name for name in
                   arguments.modules.read_text().split() if name.strip()}
    wanted = iris_proofs(corpus.read(arguments.corpus), modules, arguments.tier)
    if arguments.sample and arguments.sample < len(wanted):
        import random
        random.Random(arguments.seed).shuffle(wanted)
        wanted = wanted[:arguments.sample]

    done = {(r["module"], r["lemma"]) for r in corpus.read(arguments.output)}
    pending = [item for item in wanted if (item[0].name, item[1]) not in done]
    costs = module_costs(arguments.build_dir)
    default = sorted(s for s, _ in costs.values())[len(costs) // 2] if costs else 0
    pending.sort(key=lambda item: costs.get(item[0].name, (default, 0))[0])
    if arguments.limit:
        pending = pending[:arguments.limit]
    print(f"replay: {len(wanted)} proofs, {len(pending)} pending",
          file=sys.stderr, flush=True)

    goal_dir = arguments.build_dir / "residuals"
    probe_dir = goal_dir / "probes"
    lock = threading.Lock()
    counts: dict[str, int] = {}
    started = time.monotonic()
    finished = 0

    def one(module: Path, lemma: str) -> dict:
        wait_for_machine(arguments.coqc_cap, arguments.load_cap)
        try:
            result = replay.run(module, lemma, arguments.build_dir,
                                arguments.scratch, probe_dir, goal_dir)
            entry = replay.record(result)
        except Exception as failure:
            entry = {"module": module.name, "lemma": lemma, "outcome": "error",
                     "seconds": 0.0, "rss_mib": 0, "n_lines": 0,
                     "n_sentences": 0, "closes_at": None, "steps": [],
                     "error_lines": [f"{type(failure).__name__}: {failure}"]}
        entry["commit"] = commit
        entry["population"] = "iris"
        return entry

    with ThreadPoolExecutor(max_workers=arguments.jobs) as pool:
        futures = {pool.submit(one, module, lemma): (module, lemma)
                   for module, lemma in pending}
        for future in as_completed(futures):
            entry = future.result()
            with lock:
                with arguments.output.open("a") as handle:
                    handle.write(json.dumps(entry) + "\n")
                counts[entry["outcome"]] = counts.get(entry["outcome"], 0) + 1
                finished += 1
                if finished % 10 == 0 or finished == len(pending):
                    rate = finished / max(1e-9, time.monotonic() - started) * 60
                    print(f"{finished}/{len(pending)} {json.dumps(counts)} "
                          f"{rate:.1f}/min", file=sys.stderr, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
