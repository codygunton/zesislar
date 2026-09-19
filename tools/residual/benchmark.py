#!/usr/bin/env python3
"""E4: measure one automation commit against a frozen lemma set.

Every rule the compliance orchestrator lands is measured here before the
lead accepts it. The corpus branch never contains an automation change: the
commit's `ZesuSsz/Automation/` is exported read only into a build tree of
this worktree, and the proofs stay exactly as they are on this branch.
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import shutil
import statistics
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402
from capture import capture  # noqa: E402
from classify import classify  # noqa: E402
from tiers import rule_15_modules  # noqa: E402

PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")
SET_FILE = Path("ZesuSsz/Evidence/residuals/benchmark_set.txt")
RESULT_DIR = Path("ZesuSsz/Evidence/residuals/benchmark")
AUTOMATION = "ZesuSsz/Automation"
# A source tree of its own, so nothing under the worktree is ever rewritten.
TREE = Path("_build/agents/bench")


def freeze(repository: Path, output: Path = SET_FILE) -> list[tuple[str, str]]:
    """The benchmark set: the rule-15 modules, plus every tier-1 residual."""
    modules = {Path(name).name for name in rule_15_modules(repository)}
    chosen: list[tuple[str, str]] = []
    for record in corpus.read():
        if record.get("population") != "iris":
            continue
        if record["module"] in modules or (record.get("tier") == 1
                                           and record["outcome"] == "residual"):
            chosen.append((record["module"], record["lemma"]))
    chosen.sort()
    output.write_text("\n".join(f"{module}:{lemma}"
                                for module, lemma in chosen) + "\n")
    return chosen


def read_set(path: Path = SET_FILE) -> list[tuple[str, str]]:
    return [tuple(line.split(":", 1)) for line in path.read_text().split("\n")
            if line.strip()]


def source_tree(repository: Path, commit: str, tree: Path = TREE) -> Path:
    """A build tree whose `Automation/` comes from `commit`, proofs unchanged.

    The worktree's own sources are hard linked, so the copy is cheap and the
    originals cannot be written through it by accident: the export replaces
    whole files rather than editing them.
    """
    root = tree / commit[:12]
    if root.exists():
        shutil.rmtree(root)
    root.mkdir(parents=True)
    for entry in sorted(repository.iterdir()):
        if entry.name in {"_build", "build", ".git", "docs"}:
            continue
        target = root / entry.name
        if entry.is_dir():
            shutil.copytree(entry, target, copy_function=os.link,
                            dirs_exist_ok=True)
        else:
            os.link(entry, target)
    exported = root / AUTOMATION
    shutil.rmtree(exported)
    exported.mkdir(parents=True)
    archive = subprocess.run(["git", "archive", commit, AUTOMATION],
                             cwd=repository, capture_output=True, check=True)
    subprocess.run(["tar", "-x", "-C", str(root), "--strip-components=0"],
                   input=archive.stdout, check=True)
    return root


def build(root: Path, jobs: int) -> None:
    """Build the tree. The build dir must be absolute: make runs in `root`."""
    done = subprocess.run(
        ["nice", "-n", "10", "make", "check-iris",
         f"AGENT_BUILD_DIR={root.resolve() / '_build'}", f"AGENT_JOBS={jobs}"],
        cwd=root, capture_output=True, text=True)
    if done.returncode:
        tail = (done.stderr or done.stdout).strip().split("\n")[-25:]
        raise SystemExit("benchmark build failed:\n" + "\n".join(tail))


def measure(root: Path, pairs: list[tuple[str, str]], jobs: int,
            seconds: int) -> list[dict]:
    from concurrent.futures import ThreadPoolExecutor
    build_dir = (root / "_build").resolve()
    probe_dir = build_dir / "residuals" / "probes"
    scratch = root / "tools" / "coqc_scratch.sh"

    def one(module: str, lemma: str) -> dict:
        result = capture(root / PROOF_DIR / module, lemma,
                         build_dir.resolve(),
                         scratch, probe_dir, seconds=seconds)
        prediction = classify(result.goal_text,
                              "residual" if result.goal_text else result.outcome)
        return {"module": module, "lemma": lemma, "outcome": result.outcome,
                "seconds": result.seconds, "pred_class": prediction.pred_class}

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        return list(pool.map(lambda pair: one(*pair), pairs))


def summary(rows: list[dict]) -> dict:
    seconds = sorted(row["seconds"] for row in rows)
    return {"probed": len(rows),
            "outcomes": dict(collections.Counter(r["outcome"] for r in rows)),
            "classes": dict(collections.Counter(r["pred_class"] for r in rows)),
            "closed_fraction": round(
                sum(1 for r in rows if r["outcome"] == "closed")
                / max(1, len(rows)), 4),
            "median_seconds": round(statistics.median(seconds), 2) if seconds else 0}


def delta(now: dict, before: dict | None) -> list[str]:
    lines = [f"probed {now['probed']}  closed "
             f"{100 * now['closed_fraction']:.1f}%  median "
             f"{now['median_seconds']:.1f} s",
             "outcomes " + json.dumps(now["outcomes"], sort_keys=True),
             "classes  " + json.dumps(now["classes"], sort_keys=True)]
    if before is None:
        lines.append("no earlier run to compare")
        return lines
    lines.append(f"delta closed {100 * (now['closed_fraction'] - before['closed_fraction']):+.1f} "
                 f"points; median seconds "
                 f"{now['median_seconds'] - before['median_seconds']:+.1f}")
    for name in sorted(set(now["classes"]) | set(before["classes"])):
        change = now["classes"].get(name, 0) - before["classes"].get(name, 0)
        if change:
            lines.append(f"  {name} {change:+d}")
    return lines


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--automation", required=True,
                        help="the commit whose ZesuSsz/Automation to measure")
    parser.add_argument("--freeze", action="store_true",
                        help="rewrite benchmark_set.txt first")
    parser.add_argument("--jobs", type=int, default=12)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--limit", type=int, default=None)
    arguments = parser.parse_args()

    repository = Path.cwd()
    commit = subprocess.run(["git", "rev-parse", arguments.automation],
                            cwd=repository, capture_output=True, text=True,
                            check=True).stdout.strip()
    pairs = freeze(repository) if arguments.freeze else read_set()
    if arguments.limit:
        pairs = pairs[:arguments.limit]
    print(f"benchmark {commit[:12]}: {len(pairs)} lemmas", file=sys.stderr,
          flush=True)

    root = source_tree(repository, commit)
    build(root, arguments.jobs)
    rows = measure(root, pairs, arguments.jobs, arguments.seconds)

    RESULT_DIR.mkdir(parents=True, exist_ok=True)
    result = {"automation": commit, "summary": summary(rows), "rows": rows}
    earlier = sorted(RESULT_DIR.glob("*.json"))
    before = None
    if earlier:
        before = json.loads(earlier[-1].read_text())["summary"]
    (RESULT_DIR / f"{commit[:12]}.json").write_text(json.dumps(result))
    for line in delta(result["summary"], before):
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
