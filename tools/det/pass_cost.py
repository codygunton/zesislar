#!/usr/bin/env python3
"""What one module costs here, against the same module at another commit.

Row 6 of the bundle owes a demonstration that rule set v1 runs the tactic
it always ran. The cheapest demonstration that cannot be argued with is a
clock: compile one module alone against this tree and against an
immutable checkout of the baseline commit, and compare.

The module the argument is about is
`WriteSuccessExactByteListsPublicResources.v`. With a rule set v2 step in
v1's search list it failed `check-iris` three times with "Timeout!"; with
the step moved into `zesu_run_pass_v2` it must cost what it costs on
`origin/islaris-native`.

Each arm builds the module's dependency closure with Dune and then
compiles the module itself with `tools/coqc_scratch.sh`, which runs one
`coqc` in its own cgroup scope and reports wall time and peak RSS. The
baseline arm is an immutable `git archive` checkout (plan 9.1), so the
working tree cannot leak into it; the timing runs are sequential, because
two compiles at once do not measure one compile.
"""

from __future__ import annotations

import argparse
import importlib.util
import os
import re
import statistics
import subprocess
import sys
from pathlib import Path

MODULE = "ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactByteListsPublicResources.v"
RESULT = re.compile(r"exit=(?P<exit>-?\d+) ms=(?P<ms>\d+) rss_kb=(?P<rss>\d+)")


def benchmark_module():
    """`tools/residual/benchmark.py`, for its immutable checkout."""
    spec = importlib.util.spec_from_file_location(
        "zesu_benchmark", Path("tools/residual/benchmark.py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def environment(tree: Path) -> dict:
    env = dict(os.environ)
    env["ISLA_REPO"] = env.get("ISLA_REPO", str(Path.home() / "isla"))
    env["ISLA_SNAP_REPO"] = env.get("ISLA_SNAP_REPO",
                                    str(Path.home() / "isla-snapshots"))
    env["PATH"] = f"{tree / 'bin'}:{Path.home() / 'islaris/bin'}:{env['PATH']}"
    return env


def build(tree: Path, build_dir: Path, target: str, jobs: int) -> None:
    """The module's dependency closure, and the module, in this tree."""
    done = subprocess.run(
        ["nice", "-n", "10", "opam", "exec",
         f"--switch={Path.home() / 'islaris'}", "--",
         "dune", "build", "--root", ".", "--build-dir", str(build_dir),
         "--cache=enabled", f"-j{jobs}", target],
        cwd=tree, env=environment(tree), text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if done.returncode:
        tail = done.stdout.strip().split("\n")[-20:]
        raise SystemExit(f"{tree}: build failed\n" + "\n".join(tail))


# Any module of the theory gives the same compiler flags, and this is the
# smallest one. Dune prunes files it does not own from the root of a build
# directory, so a no-op build deletes the recipe `coqc_scratch.sh` reads
# and leaves a trace with no `coqc` in it. Recompiling one small module
# with the cache off puts a recipe back.
RECIPE_SEED = "ZesuSsz/Automation/Alignment"


def ensure_recipe(tree: Path, build_dir: Path) -> None:
    """A `coqc` recipe in this build directory, whatever Dune pruned."""
    sys.path.insert(0, str(Path("tools").resolve()))
    from coqc_recipe import project_recipe, remember_recipe

    if project_recipe(remember_recipe(build_dir)):
        return
    (build_dir / "default" / f"{RECIPE_SEED}.vo").unlink(missing_ok=True)
    subprocess.run(
        ["nice", "-n", "10", "opam", "exec",
         f"--switch={Path.home() / 'islaris'}", "--",
         "dune", "build", "--root", ".", "--build-dir", str(build_dir),
         "--cache=disabled", "-j1", f"{RECIPE_SEED}.vo"],
        cwd=tree, env=environment(tree), check=True,
        stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT)
    if not project_recipe(remember_recipe(build_dir)):
        raise SystemExit(f"{build_dir}: no coqc recipe after a forced build")


def timed(scratch: Path, source: Path, build_dir: Path,
          seconds: int, memory_mib: int) -> dict:
    """One `coqc` on one module, alone, in its own scope."""
    env = dict(os.environ)
    env["ZESU_COQC_SECONDS"] = str(seconds)
    env["ZESU_COQC_MEMORY_MIB"] = str(memory_mib)
    env.setdefault("ZESU_MODULE_LIMIT_GIB", str(max(6, memory_mib // 1024)))
    done = subprocess.run(["bash", str(scratch), str(source), str(build_dir)],
                          capture_output=True, text=True, env=env)
    found = RESULT.search(done.stdout)
    if not found:
        raise SystemExit("no timing line from coqc_scratch.sh:\n"
                         + done.stdout + done.stderr)
    return {"exit": int(found["exit"]), "seconds": int(found["ms"]) / 1000,
            "rss_gib": int(found["rss"]) / (1024 * 1024),
            "limit": done.stderr.strip()}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", default=MODULE)
    parser.add_argument("--before", default="origin/islaris-native",
                        help="the commit this tree is compared against")
    parser.add_argument("--jobs", type=int, default=32)
    parser.add_argument("--seconds", type=int, default=1800)
    parser.add_argument("--memory-mib", type=int, default=16384)
    parser.add_argument("--tolerance", type=float, default=10.0,
                        help="how much slower this tree may be, in percent")
    parser.add_argument("--repeat", type=int, default=3,
                        help="timed runs per arm, interleaved")
    arguments = parser.parse_args()

    repository = Path.cwd()
    scratch = repository / "tools" / "coqc_scratch.sh"
    target = arguments.module.removesuffix(".v") + ".vo"
    commit = subprocess.run(["git", "rev-parse", arguments.before],
                            capture_output=True, text=True,
                            check=True).stdout.strip()

    baseline = benchmark_module().source_tree(repository, commit)
    arms = [("here", repository, repository / "_build/agents/det"),
            (commit[:12], baseline, baseline / "_build")]

    # Build both closures first, then time both, so neither compile is
    # measured beside a 32-job build.
    for _, tree, build_dir in arms:
        build(tree, build_dir.resolve(), target, arguments.jobs)
        ensure_recipe(tree, build_dir.resolve())

    # Interleaved, like `ab.py`: two runs minutes apart are not comparable
    # at the few per cent level, and this difference is a few per cent.
    runs: dict[str, list[dict]] = {name: [] for name, _, _ in arms}
    for _ in range(arguments.repeat):
        for name, _, build_dir in arms:
            source = (build_dir / "default" / arguments.module).resolve()
            runs[name].append(timed(scratch, source, build_dir.resolve(),
                                    arguments.seconds, arguments.memory_mib))

    print("| arm | exit | median s | runs | peak GiB |")
    print("|---|---|---|---|---|")
    medians = {}
    for name, _, _ in arms:
        rows = runs[name]
        seconds = sorted(row["seconds"] for row in rows)
        medians[name] = statistics.median(seconds)
        print(f"| {name} | {max(row['exit'] for row in rows)} | "
              f"{medians[name]:.1f} | "
              + ", ".join(f"{value:.1f}" for value in seconds) + " | "
              f"{max(row['rss_gib'] for row in rows):.1f} |")

    here, before = medians[arms[0][0]], medians[arms[1][0]]
    if before <= 0:
        return 1
    change = 100 * (here - before) / before
    slower = change > arguments.tolerance
    print(f"\n{arguments.module}: {change:+.1f} percent against "
          f"{arms[1][0]}. The check is one-sided: this tree may be faster,"
          f" and fails only if it is more than {arguments.tolerance:.0f}"
          f" percent slower.")
    failed = any(row["exit"] for rows in runs.values() for row in rows)
    return 1 if slower or failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
