#!/usr/bin/env python3
"""Probe, label, and classify a tier of hand-written proofs.

The run is idempotent: a proof that already has a record at the current
commit is skipped, so an interrupted run continues where it stopped. Probes
run in batches of `--jobs`, and the run waits before a batch whenever the
machine already carries the compliance plan's agents.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402
from capture import capture  # noqa: E402
from classify import classify  # noqa: E402
from costs import module_costs  # noqa: E402
from label import label_proof  # noqa: E402
from modules import parse_module  # noqa: E402
from tiers import tier_one_modules  # noqa: E402

PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")
# Section 3 of the plan sets these: this agent runs its own probes, and it
# waits when the machine already carries the compliance plan's agents.
COQC_CAP = 40
LOAD_CAP = 60.0
WAIT_SECONDS = 30
SOLVER_CLASS = "C4"


def current_commit(repository: Path) -> str:
    return subprocess.run(["git", "rev-parse", "origin/islaris-native"],
                          cwd=repository, capture_output=True, text=True,
                          check=True).stdout.strip()


def busy_reason(coqc_cap: int, load_cap: float) -> str | None:
    """A reason to wait, or None when this agent may start a batch."""
    running = subprocess.run(["pgrep", "-c", "coqc"], capture_output=True,
                             text=True).stdout.strip()
    count = int(running) if running.isdigit() else 0
    if count >= coqc_cap:
        return f"{count} coqc processes"
    load = os.getloadavg()[0]
    if load > load_cap:
        return f"load {load:.1f}"
    return None


def wait_for_machine(coqc_cap: int, load_cap: float) -> None:
    while True:
        reason = busy_reason(coqc_cap, load_cap)
        if reason is None:
            return
        print(f"waiting: {reason}", file=sys.stderr, flush=True)
        time.sleep(WAIT_SECONDS)


def tier_lemmas(tier: int, repository: Path) -> list[tuple[Path, str]]:
    """The hand-written proofs of one tier.

    Tier 2 keeps its oldest modules last, as the plan asks, by taking the
    tier-1 recency order and reversing what is left.
    """
    tier_one = set(tier_one_modules(repository))
    wanted: list[tuple[Path, str]] = []
    for module in sorted(PROOF_DIR.glob("*.v")):
        if (tier == 1) != (str(module) in tier_one):
            continue
        for proof in parse_module(module):
            if proof.hand_lines:
                wanted.append((module, proof.name))
    return wanted


def probe_one(module: Path, lemma: str, tier: int, commit: str,
              build_dir: Path, scratch: Path, seconds: int = 300) -> dict:
    probe_dir = build_dir / "residuals" / "probes"
    goal_dir = build_dir / "residuals"
    result = capture(module, lemma, build_dir, scratch, probe_dir,
                     seconds=seconds)
    label_class, label_classes = label_proof(
        [line for line in (raw.strip() for raw in result.label_lines) if line])
    if result.error_kind == "not_bi":
        # A pure Coq helper lemma: the outcome stays `error`, but the pure
        # probe still shows which class the untouched goal belongs to.
        pure = capture(module, lemma, build_dir, scratch, probe_dir,
                       variant="pure")
        for field in ("goal_count", "goal_heads", "goal_text", "goal_sha256",
                      "full_goal_text"):
            setattr(result, field, getattr(pure, field))
    prediction = classify(result.goal_text,
                          "residual" if result.goal_text else result.outcome)
    solver = result.solver
    if prediction.pred_class == SOLVER_CLASS:
        second = capture(module, lemma, build_dir, scratch, probe_dir,
                         solver=True,
                         variant="pure" if result.error_kind == "not_bi"
                         else "standard")
        solver = second.solver
    if result.goal_sha256:
        goal_dir.mkdir(parents=True, exist_ok=True)
        (goal_dir / f"{result.goal_sha256}.txt").write_text(result.full_goal_text)
    record = {key: value for key, value in result.__dict__.items()
              if key not in {"full_goal_text", "probe"}}
    record.update({"commit": commit, "tier": tier,
                   "label_class": label_class, "label_classes": label_classes,
                   "pred_class": prediction.pred_class,
                   "pred_detail": prediction.detail, "solver": solver})
    return record


def failure_record(module: Path, lemma: str, tier: int, commit: str,
                   failure: BaseException) -> dict:
    return {"module": module.name, "lemma": lemma, "commit": commit,
            "tier": tier, "outcome": "error", "seconds": 0.0, "rss_mib": 0,
            "zesu_run_seconds": [], "goal_count": 0, "goal_heads": [],
            "goal_text": "", "goal_sha256": "", "label_lines": [],
            "label_class": "Lother", "label_classes": ["Lother"],
            "pred_class": "n/a", "pred_detail": {}, "solver": "",
            "error_kind": "tool_failure", "probe_variant": "standard",
            "error_lines": [f"{type(failure).__name__}: {failure}"]}


def cheapest_first(pending: list[tuple[Path, str]],
                   build_dir: Path) -> list[tuple[Path, str]]:
    """Order the work by module compile cost, cheapest first.

    A probe recompiles its module up to the target `Proof.`, so the setup
    build's own cost per module predicts it. Cheap work first keeps the
    corpus growing while the slowest modules run.
    """
    costs = module_costs(build_dir)
    if not costs:
        return pending
    default = sorted(seconds for seconds, _ in costs.values())[len(costs) // 2]
    return sorted(pending,
                  key=lambda item: (costs.get(item[0].name, (default, 0))[0],
                                    item[0].name, item[1]))


def parse_only(name: str) -> tuple[Path, str]:
    path, _, lemma = name.rpartition(":")
    module = Path(path)
    if not module.exists():
        module = PROOF_DIR / Path(path).name
    return module, lemma


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tier", type=int, choices=(1, 2), default=1)
    parser.add_argument("--jobs", type=int, default=12)
    parser.add_argument("--coqc-cap", type=int, default=COQC_CAP,
                        help="wait while this many coqc processes run")
    parser.add_argument("--load-cap", type=float, default=LOAD_CAP,
                        help="wait while the 1-minute load is above this")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--seconds", type=int, default=300,
                        help="probe time limit")
    parser.add_argument("--redo", action="store_true",
                        help="replace records whose outcome is timeout")
    parser.add_argument("--build-dir", type=Path,
                        default=Path("_build/agents/corpus"))
    parser.add_argument("--scratch", type=Path,
                        default=Path("tools/coqc_scratch.sh"))
    parser.add_argument("--corpus", type=Path, default=corpus.CORPUS)
    parser.add_argument("--only", action="append", default=[],
                        help="probe only MODULE.v:LEMMA (repeatable)")
    arguments = parser.parse_args()

    repository = Path.cwd()
    commit = current_commit(repository)
    existing = corpus.read(arguments.corpus)
    done = corpus.keys(existing)

    wanted = ([parse_only(name) for name in arguments.only] if arguments.only
              else tier_lemmas(arguments.tier, repository))
    if arguments.redo:
        # Drop only the timeouts this run would reprobe, never a record of a
        # set this invocation does not visit.
        scope = {(module.name, lemma) for module, lemma in wanted}
        keep = [r for r in existing
                if r["outcome"] != "timeout"
                or (r["module"], r["lemma"]) not in scope]
        Path(arguments.corpus).write_text(
            "".join(json.dumps(corpus.order(r)) + "\n" for r in keep))
        existing = keep
        done = corpus.keys(existing)
    pending = [(module, lemma) for module, lemma in wanted
               if corpus.Key(module.name, lemma, commit) not in done]
    pending = cheapest_first(pending, arguments.build_dir)
    if arguments.limit:
        pending = pending[:arguments.limit]
    print(f"tier {arguments.tier}: {len(wanted)} proofs, {len(pending)} pending",
          file=sys.stderr, flush=True)

    counts: dict[str, int] = {}
    started = time.monotonic()
    lock = threading.Lock()
    finished = 0

    def probe(module: Path, lemma: str) -> dict:
        wait_for_machine(arguments.coqc_cap, arguments.load_cap)
        try:
            return probe_one(module, lemma, arguments.tier, commit,
                             arguments.build_dir, arguments.scratch,
                             arguments.seconds)
        except Exception as failure:  # record the gap, keep the run going
            return failure_record(module, lemma, arguments.tier, commit,
                                  failure)

    # A rolling pool, not fixed batches: one probe that runs to the 300 second
    # limit must not hold back the other workers.
    with ThreadPoolExecutor(max_workers=arguments.jobs) as pool:
        futures = {pool.submit(probe, module, lemma): (module, lemma)
                   for module, lemma in pending}
        for future in as_completed(futures):
            record = future.result()
            with lock:
                corpus.append([record], arguments.corpus)
                counts[record["outcome"]] = counts.get(record["outcome"], 0) + 1
                finished += 1
                if finished % 25 == 0 or finished == len(pending):
                    rate = finished / max(1e-9, time.monotonic() - started) * 60
                    print(f"{finished}/{len(pending)} {json.dumps(counts)} "
                          f"{rate:.1f}/min", file=sys.stderr, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
