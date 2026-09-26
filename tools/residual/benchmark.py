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
import signal
import statistics
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "det"))

import corpus  # noqa: E402
from capture import capture  # noqa: E402
from classify import VERSION as CLASSIFIER, classify  # noqa: E402
from goals import conclusion_text  # noqa: E402
from signature import signature  # noqa: E402
from tiers import rule_15_modules  # noqa: E402
import coqc_slots  # noqa: E402

GUARD = Path(__file__).resolve().parents[1] / "resource_guard.sh"
SCRATCH = Path(__file__).resolve().parents[1] / "coqc_scratch.sh"


def guard_jobs(requested: int) -> int:
    """Never start more jobs than memory allows (plan section 4)."""
    if not GUARD.exists():
        return requested
    allowed = int(subprocess.run([str(GUARD), "jobs"], capture_output=True,
                                 text=True).stdout.strip() or 1)
    return min(requested, allowed)

PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")
SET_FILE = Path("ZesuSsz/Evidence/residuals/benchmark_set.txt")
RULE_15_SET = Path("ZesuSsz/Evidence/residuals/benchmark_set_rule15.txt")
RESULT_DIR = Path("ZesuSsz/Evidence/residuals/benchmark")
AUTOMATION = "ZesuSsz/Automation"
# The probe's block call (`capture.BLOCK_CALL`); `--variant` sets it.
VARIANT = ["standard"]
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


def freeze_rule_15(repository: Path, output: Path = RULE_15_SET) -> list:
    """The benchmark set restricted to the rule-15 era.

    The whole set answers "did this rule help the corpus". This one answers
    "did it help the population the harness must serve", which is the
    question the compliance plan asks.
    """
    modules = {Path(name).name for name in rule_15_modules(repository)}
    chosen = sorted((record["module"], record["lemma"])
                    for record in corpus.read()
                    if record.get("population") == "iris"
                    and record["module"] in modules)
    output.write_text("\n".join(f"{module}:{lemma}"
                                 for module, lemma in chosen) + "\n")
    return chosen


def read_set(path: Path = SET_FILE) -> list[tuple[str, str]]:
    return [tuple(line.split(":", 1)) for line in path.read_text().split("\n")
            if line.strip()]


# Derived inputs the build needs that git does not carry. The Isla traces
# are 12 MiB generated from the pinned ELF and are the same for every
# commit on this branch, so they are copied rather than regenerated.
DERIVED = ("generated", "build")


# A WIP tip may carry a test module that does not build yet, and an arm
# needs the whole tree built. For WIP tips the arm builds without this
# directory (lead's ruling 2026-09-24) and the arm file says so.
TESTS_DIR = "ZesuSsz/Proofs/Tests"


def tree_marker(commit: str, without_tests: bool) -> str:
    return commit + (f" without {TESTS_DIR}" if without_tests else "")


def source_tree(repository: Path, commit: str, tree: Path = TREE,
                without_tests: bool = False) -> Path:
    """An immutable checkout of `commit`, with its own build directory.

    Plan 9.1, after the arm that measured nothing: a benchmark arm never
    reads the working tree. The first v2 arm did -- the tree's
    `Automation/` was byte for byte the commit's, so the runner reused
    the worktree's own build -- and then the worktree was edited while
    the arm ran. Every probe failed to build, all 305 rows landed in the
    `n/a` class, and the arm was worthless.

    So the tree comes from `git archive` and nothing in it is a link to
    anything the worktree can write. The derived inputs git does not
    carry are copied in; they are outputs of the pinned ELF, not
    sources.
    """
    root = tree / commit[:12]
    marker = root / ".arm-commit"
    if (marker.exists()
            and marker.read_text().strip() == tree_marker(commit, without_tests)):
        # The tree is already this commit's, built and never written
        # since. Measuring ten rules at one commit should cost one
        # build, not ten.
        return root
    if root.exists():
        shutil.rmtree(root)
    root.mkdir(parents=True)
    archive = subprocess.run(["git", "archive", commit],
                             cwd=repository, capture_output=True, check=True)
    subprocess.run(["tar", "-x", "-C", str(root)],
                   input=archive.stdout, check=True)
    for name in DERIVED:
        source = repository / name
        if not source.exists():
            continue
        shutil.copytree(source, root / name, dirs_exist_ok=True,
                        symlinks=True)
    if without_tests:
        shutil.rmtree(root / TESTS_DIR, ignore_errors=True)
    return root


def mark_built(root: Path, commit: str, without_tests: bool = False) -> None:
    """Record that this tree is this commit's and has been built."""
    (root / ".arm-commit").write_text(tree_marker(commit, without_tests) + "\n")


def wait_for_room() -> None:
    """Block until the guard lets one more job start (plan section 4)."""
    if GUARD.exists():
        subprocess.run([str(GUARD), "wait"], check=True)


def launch_width(root: Path, requested: int) -> int:
    """Size one launch after the guard releases it."""
    while True:
        wait_for_room()
        allowed, _, _ = coqc_slots.width(guard_jobs(requested), root)
        if allowed:
            return allowed
        time.sleep(5)


def build(root: Path, requested: int) -> None:
    """Build the tree. The build dir must be absolute: make runs in `root`.

    Populating a new arm's build directory from the Dune cache is the disk
    burst that spiked load on 2026-09-22, so it runs in the idle IO class.
    It is batch work, not a gate: ZESU_ARM keeps it off the gate lock."""
    jobs = launch_width(root, requested)
    # While this marker lives, every guard ramps its launches.
    marker = Path(f"/tmp/zesu-populating.{os.getpid()}")
    marker.write_text(str(root))
    with tempfile.TemporaryFile(mode="w+") as output:
        process = subprocess.Popen(
            ["ionice", "-c3", "nice", "-n", "10", "make", "check-iris",
             f"AGENT_BUILD_DIR={root.resolve() / '_build'}", f"AGENT_JOBS={jobs}"],
            cwd=root, stdout=output, stderr=subprocess.STDOUT,
            start_new_session=True, env={**os.environ, "ZESU_ARM": "1"})
        while True:
            try:
                status = process.wait(timeout=30)
                break
            except subprocess.TimeoutExpired:
                current, _, other = coqc_slots.width(jobs, root)
                if current < jobs:
                    os.killpg(process.pid, signal.SIGTERM)
                    process.wait()
                    marker.unlink(missing_ok=True)
                    raise SystemExit(
                        f"benchmark build stopped: width {jobs} exceeds "
                        f"{current} slots with {other} other coqc")
        output.seek(0)
        lines = output.read().strip().split("\n")
    marker.unlink(missing_ok=True)
    if not status:
        # `check-iris` compiles only the Automation modules a proof
        # imports. A candidate's switch is imported by nothing but its
        # probes (and, on a WIP tip, by the tests an arm leaves out), so
        # the whole Automation directory is built too.
        done = subprocess.run(
            ["ionice", "-c3", "nice", "-n", "10", "opam", "exec",
             f"--switch={Path.home() / 'islaris'}", "--", "dune",
             "build", "--root", ".",
             f"--build-dir={root.resolve() / '_build'}",
             "--cache=enabled", f"-j{jobs}", "@ZesuSsz/Automation/all"],
            cwd=root, capture_output=True, text=True,
            env={**os.environ, "ZESU_ARM": "1"})
        status = done.returncode
        lines = (done.stderr or done.stdout).strip().split("\n")
    if status:
        tail = lines[-25:]
        raise SystemExit("benchmark build failed:\n" + "\n".join(tail))


class ProbeWidth:
    """Reduce new probe launches when other coqc processes appear."""

    def __init__(self, maximum: int, root: Path):
        self.maximum = maximum
        self.root = root
        self.condition = threading.Condition()
        self.stop = threading.Event()
        self.active = 0
        self.allowed = maximum
        self.watcher = threading.Thread(target=self.watch, daemon=True)

    def watch(self) -> None:
        while not self.stop.wait(30):
            with self.condition:
                self.allowed = coqc_slots.width(self.maximum, self.root)[0]
                self.condition.notify_all()

    def acquire(self) -> None:
        with self.condition:
            while True:
                self.allowed = coqc_slots.width(self.maximum, self.root)[0]
                if self.active < self.allowed:
                    self.active += 1
                    return
                self.condition.wait(timeout=30)

    def release(self) -> None:
        with self.condition:
            self.active -= 1
            self.condition.notify_all()

    def __enter__(self):
        self.watcher.start()
        return self

    def __exit__(self, *_):
        self.stop.set()
        self.watcher.join()


def measure(root: Path, pairs: list[tuple[str, str]], jobs: int,
            seconds: int, build_dir: Path | None = None,
            imports: tuple[str, ...] = ()) -> list[dict]:
    from concurrent.futures import ThreadPoolExecutor
    root = root.resolve()
    build_dir = (build_dir.resolve() if build_dir is not None else
                 ((root / "_build") if root.name != "residual-corpus"
                  else root / "_build" / "agents" / "corpus").resolve())
    probe_dir = build_dir / "residuals" / "probes"
    # Old commits can predate the guard. Keep the proof source immutable,
    # but run every probe through the current guarded compiler wrapper.
    scratch = SCRATCH

    goal_dir = build_dir / "residuals"

    def one(module: str, lemma: str) -> dict:
        wait_for_room()
        width.acquire()
        try:
            result = capture(root / PROOF_DIR / module, lemma,
                             build_dir.resolve(),
                             scratch, probe_dir, seconds=seconds,
                             variant=VARIANT[0],
                             imports=imports, cwd=root)
        finally:
            width.release()
        if result.goal_sha256:
            goal_dir.mkdir(parents=True, exist_ok=True)
            (goal_dir / f"{result.goal_sha256}.txt").write_text(
                result.full_goal_text)
        prediction = classify(result.goal_text,
                              "residual" if result.goal_text else result.outcome)
        signature_text = ""
        if result.goal_text:
            signature_text = signature(conclusion_text(result.goal_text)[1])
        # The digest lets a later baseline be reclassified from the stored
        # text, with no rebuild, the way iteration 3 reclassified the replay.
        return {"module": module, "lemma": lemma, "outcome": result.outcome,
                "seconds": result.seconds, "pred_class": prediction.pred_class,
                "signature": signature_text,
                "goal_sha256": result.goal_sha256}

    with ProbeWidth(jobs, root) as width:
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            return list(pool.map(lambda pair: one(*pair), pairs))


# Lead's policy, 2026-09-23: a lemma whose batch outcome is an error or a
# timeout is probed again alone, and the alone result is the stored
# outcome. The automation's tactics carry wall-clock timeouts, and a 48-wide
# batch spends them on memory traffic: `suffix_word2_load_correct` was an
# error at 206 s in the batch and a residual at 135 s alone, same goal.
REPROBE = {"error", "timeout"}
BATCH_FIELDS = ("outcome", "seconds", "pred_class", "signature", "goal_sha256")


def reprobe_alone(root: Path, rows: list[dict], seconds: int,
                  imports: tuple[str, ...] = ()) -> list[dict]:
    """Rows with each error or timeout replaced by its alone result.

    The alone probes run one at a time after the batch. A replaced row is
    flagged `reprobed` and keeps the batch result under `batch`.
    """
    result = []
    for row in rows:
        if row["outcome"] not in REPROBE:
            result.append(row)
            continue
        alone = measure(root, [(row["module"], row["lemma"])], 1, seconds,
                        None, imports)[0]
        alone["reprobed"] = True
        alone["batch"] = {name: row.get(name) for name in BATCH_FIELDS}
        print(f"reprobed {row['module']}:{row['lemma']}: batch "
              f"{row['outcome']} {row['seconds']:.0f} s, alone "
              f"{alone['outcome']} {alone['seconds']:.0f} s",
              file=sys.stderr, flush=True)
        result.append(alone)
    return result


def reprobe_line(rows: list[dict]) -> str:
    again = [row for row in rows if row.get("reprobed")]
    moved = [row for row in again if row["outcome"] != row["batch"]["outcome"]]
    return (f"reprobed alone {len(again)} (error or timeout in the batch); "
            f"{len(moved)} changed outcome")


def summary(rows: list[dict]) -> dict:
    seconds = sorted(row["seconds"] for row in rows)
    return {"probed": len(rows),
            "outcomes": dict(collections.Counter(r["outcome"] for r in rows)),
            "classes": dict(collections.Counter(r["pred_class"] for r in rows)),
            "closed_fraction": round(
                sum(1 for r in rows if r["outcome"] == "closed")
                / max(1, len(rows)), 4),
            "median_seconds": round(statistics.median(seconds), 2) if seconds else 0,
            "reprobed": sum(1 for r in rows if r.get("reprobed")),
            "reprobe_changed": sum(1 for r in rows if r.get("reprobed")
                                   and r["outcome"] != r["batch"]["outcome"])}


def delta(now: dict, before: dict | None, classifier: str = CLASSIFIER,
          before_classifier: str | None = None) -> list[str]:
    lines = [f"classifier v{classifier}",
             f"reprobed alone {now.get('reprobed', 0)}, "
             f"{now.get('reprobe_changed', 0)} changed outcome",
             f"probed {now['probed']}  closed "
             f"{100 * now['closed_fraction']:.1f}%  median "
             f"{now['median_seconds']:.1f} s",
             "outcomes " + json.dumps(now["outcomes"], sort_keys=True),
             "classes  " + json.dumps(now["classes"], sort_keys=True)]
    if before is None:
        lines.append("no earlier run to compare")
        return lines
    if before_classifier != classifier:
        lines.append(f"(earlier run classified with v{before_classifier}; "
                     "class deltas mix classifier versions)")
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
    parser.add_argument("--set", type=Path, default=SET_FILE,
                        help="the frozen lemma set to measure")
    parser.add_argument("--name", default="",
                        help="suffix for the stored baseline")
    parser.add_argument("--jobs", type=int, default=12)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--import", dest="imports", action="append",
                        default=[],
                        help="a module every probe requires, for measuring "
                             "a rule that is built but not exported")
    parser.add_argument("--variant", default="standard",
                        help="the probe's block call, from capture.BLOCK_CALL")
    parser.add_argument("--no-reprobe", action="store_true",
                        help="keep batch errors and timeouts as they are "
                             "(the policy is to re-probe them alone)")
    parser.add_argument("--without-tests", action="store_true",
                        help=f"build the arm tree without {TESTS_DIR}; for "
                             "WIP tips only, recorded in the arm file")
    parser.add_argument("--build-dir", type=Path, default=None,
                        # Kept for callers that still pass it; an arm now
                        # always builds inside its own checkout, so the
                        # value is ignored. Plan 9.1.
                        help="the build tree the probes compile against; "
                             "needed when the worktree builds elsewhere")
    arguments = parser.parse_args()
    VARIANT[0] = arguments.variant

    repository = Path.cwd()
    commit = subprocess.run(["git", "rev-parse", arguments.automation],
                            cwd=repository, capture_output=True, text=True,
                            check=True).stdout.strip()
    pairs = (freeze(repository) if arguments.freeze
             else read_set(arguments.set))
    if arguments.limit:
        pairs = pairs[:arguments.limit]
    print(f"benchmark {commit[:12]}: {len(pairs)} lemmas", file=sys.stderr,
          flush=True)

    # Always an immutable checkout. There is no path here that reads the
    # working tree: that is plan 9.1 and it is the whole point.
    root = source_tree(repository, commit,
                       without_tests=arguments.without_tests)
    print(f"arm tree {root}", file=sys.stderr, flush=True)
    if not (root / ".arm-commit").exists():
        build(root, arguments.jobs)
        mark_built(root, commit, arguments.without_tests)
    jobs = launch_width(root, arguments.jobs)
    print(f"resource guard allows {jobs} concurrent jobs", file=sys.stderr,
          flush=True)
    rows = measure(root, pairs, jobs, arguments.seconds, None,
                   tuple(arguments.imports))
    if not any(row["outcome"] in ("closed", "residual") for row in rows):
        # Every probe failed: a missing import or build, not a measurement.
        raise SystemExit(f"every probe failed ({len(rows)}); arm not stored")
    if not arguments.no_reprobe:
        rows = reprobe_alone(root, rows, arguments.seconds,
                             tuple(arguments.imports))

    RESULT_DIR.mkdir(parents=True, exist_ok=True)
    result = {"automation": commit, "summary": summary(rows), "rows": rows,
              "classifier": CLASSIFIER, "imports": list(arguments.imports),
              "variant": arguments.variant,
              "seconds": arguments.seconds}
    if arguments.without_tests:
        result["excluded"] = [TESTS_DIR]
    stem = commit[:12] + (f"-{arguments.name}" if arguments.name else "")
    earlier = sorted(RESULT_DIR.glob(f"*{arguments.name}.json")
                     if arguments.name else
                     [path for path in RESULT_DIR.glob("*.json")
                      if "-" not in path.stem])
    before, before_classifier = None, None
    if earlier:
        stored = json.loads(earlier[-1].read_text())
        before, before_classifier = stored["summary"], stored.get("classifier", "1")
    (RESULT_DIR / f"{stem}.json").write_text(json.dumps(result))
    for line in delta(result["summary"], before, CLASSIFIER, before_classifier):
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
