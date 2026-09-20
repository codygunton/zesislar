#!/usr/bin/env python3
"""Measure an automation change A against B in one interleaved run.

Two runs of the same probes, minutes apart, are not comparable at the few
percent level: WP2 measured a 28 percent slowdown on small lemmas and a 20
percent speedup on large ones in an arm whose automation had not changed at
all. Machine state, cache warmth and scheduling move the numbers more than
the change does.

So both arms run in the same thread pool, alternating lemma by lemma, and
the comparison is the paired ratio. The two arms are two source trees whose
`ZesuSsz/Automation` comes from two commits; everything else is hard linked
from the worktree, as `tools/residual/benchmark.py` does.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "residual"))

import probes  # noqa: E402
import run_profile  # noqa: E402
from benchmark import source_tree  # noqa: E402

PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")


def build(root: Path, jobs: int) -> Path:
    """Build the arm's proofs with Dune directly.

    `make check-iris` also runs the evidence checks, which need the paths of
    the real worktree and fail in a hard-linked copy. The proofs are all
    this arm needs, and Dune writes the trace that `coqc_scratch.sh` reads.
    """
    build_dir = (root / "_build" / "agents" / "ab").resolve()
    # Dune wants the parent of its build directory to exist already.
    build_dir.parent.mkdir(parents=True, exist_ok=True)
    done = subprocess.run(
        ["nice", "-n", "10", "opam", "exec", "--switch",
         str(Path.home() / "islaris"), "--", "dune", "build", "--root", ".",
         "--build-dir", str(build_dir), "--cache=enabled", f"-j{jobs}",
         "@ZesuSsz/Proofs/all"],
        cwd=root, capture_output=True, text=True)
    if done.returncode:
        tail = (done.stderr or done.stdout).strip().split("\n")[-20:]
        raise SystemExit(f"build of {root} failed:\n" + "\n".join(tail))
    recipe(root, build_dir)
    return build_dir


# One module, compiled for real, so the Dune trace holds a `coqc` command
# line. A build that the cache satisfies runs no process at all, and then
# `coqc_scratch.sh` has no recipe to imitate and every probe dies at once.
RECIPE_TARGET = "ZesuSsz/Proofs/WriteSuccess/Interfaces.vo"


def recipe(root: Path, build_dir: Path) -> None:
    if (build_dir / "coqc_recipe.json").exists():
        return
    (build_dir / "default" / RECIPE_TARGET).unlink(missing_ok=True)
    subprocess.run(
        ["nice", "-n", "10", "opam", "exec", "--switch",
         str(Path.home() / "islaris"), "--", "dune", "build", "--root", ".",
         "--build-dir", str(build_dir), "--cache=disabled", "-j8",
         RECIPE_TARGET],
        cwd=root, capture_output=True, text=True, check=True)


def probe(arm: str, root: Path, build_dir: Path, module: str, lemma: str,
          seconds: int) -> dict:
    path = root / PROOF_DIR / module
    source = probes.probe_text(path, lemma, "counted")
    probe_dir = build_dir / "det" / "probes"
    probe_dir.mkdir(parents=True, exist_ok=True)
    file = probe_dir / f"{path.stem}__{lemma}__counted.v"
    file.write_text(source)
    run_profile.wait_for_room()
    command = ["timeout", str(seconds + 60), "nice", "-n", "10", "bash",
               str(root / "tools" / "coqc_scratch.sh"), str(file),
               str(build_dir)]
    started = time.monotonic()
    done = subprocess.run(command, capture_output=True, text=True,
                          env=run_profile.limit_env(seconds), cwd=root)
    output = done.stdout + "\n" + done.stderr
    return {"arm": arm, "module": module, "lemma": lemma,
            "wall": round(time.monotonic() - started, 2),
            "reached_end": probes.END in output,
            "run_seconds": round(sum(
                float(v) for v in run_profile.TACTIC_TIME.findall(output)), 3),
            "instructions": output.count("INSTR-ASM")}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--set", type=Path, required=True)
    parser.add_argument("--before", required=True,
                        help="the commit whose Automation is the A arm")
    parser.add_argument("--after", default="HEAD",
                        help="the commit whose Automation is the B arm; "
                             "HEAD means this worktree, built already")
    parser.add_argument("--build-dir", type=Path,
                        default=Path("_build/agents/det"),
                        help="the worktree's own build, for the B arm")
    parser.add_argument("--jobs", type=int, default=48)
    parser.add_argument("--seconds", type=int, default=600)
    parser.add_argument("--out", type=Path, required=True)
    arguments = parser.parse_args()
    repository = Path.cwd()
    commit = subprocess.run(["git", "rev-parse", arguments.before],
                            capture_output=True, text=True,
                            check=True).stdout.strip()
    # The A arm's tree is expensive to build, so it is kept between runs and
    # a stamp says which automation it holds. `source_tree` would delete it.
    # Absolute: the probe runs with the arm's tree as its working directory,
    # so a relative path to the scratch script would resolve inside it.
    before_root = (Path("_build/agents/ab") / commit[:12]).resolve()
    stamp = before_root / ".automation-commit"
    if not (stamp.exists() and stamp.read_text().strip() == commit):
        if before_root.exists():
            shutil.rmtree(before_root)
        before_root = source_tree(repository, commit,
                                  Path("_build/agents/ab")).resolve()
        (before_root / ".automation-commit").write_text(commit)
    print(f"building the A arm in {before_root}", file=sys.stderr, flush=True)
    before_build = build(before_root, arguments.jobs)
    arms = {"before": (before_root, before_build),
            "after": (repository, arguments.build_dir.resolve())}
    targets = [line.split(":", 1) for line in
               arguments.set.read_text().split("\n") if ":" in line]
    work = [(arm, module, lemma) for module, lemma in targets
            for arm in ("before", "after")]
    arguments.out.parent.mkdir(parents=True, exist_ok=True)
    jobs = run_profile.guard_jobs(arguments.jobs)
    print(f"resource guard allows {jobs} concurrent jobs", file=sys.stderr,
          flush=True)
    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        futures = {pool.submit(probe, arm, *arms[arm], module, lemma,
                               arguments.seconds): (arm, module, lemma)
                   for arm, module, lemma in work}
        with arguments.out.open("a") as handle:
            for future in concurrent.futures.as_completed(futures):
                arm, module, lemma = futures[future]
                try:
                    record = future.result()
                except Exception as error:  # noqa: BLE001
                    record = {"arm": arm, "module": module, "lemma": lemma,
                              "reached_end": False, "error": str(error)}
                handle.write(json.dumps(record) + "\n")
                handle.flush()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
