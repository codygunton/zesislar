#!/usr/bin/env python3
"""One benchmark arm per rule, on both baselines, and the delta table.

Plan 9.1: an arm builds from an immutable checkout of the named commit.
Every arm here names the same commit, so the checkout and its build
happen once and the arms differ only in which rule module each probe
imports.

The reference arm imports nothing: that is rule set v1, and row 6 owes a
demonstration that it changes no outcome. Every other arm imports one
switch or one module, so its delta is that rule's and nobody else's.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

RESULTS = Path("ZesuSsz/Evidence/residuals/benchmark")
FULL = Path("ZesuSsz/Evidence/residuals/benchmark_set.txt")
RULE15 = Path("ZesuSsz/Evidence/residuals/benchmark_set_rule15.txt")

# name -> the modules a probe requires for that rule and nothing else.
ARMS: list[tuple[str, list[str]]] = [
    ("v1", []),
    ("spectable", ["ZesuSsz.Automation.SpecTable"]),
    ("wordarraybytes", ["ZesuSsz.Automation.WordArrayBytes"]),
    ("stackarray", ["ZesuSsz.Automation.StackArrayLookup",
                    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts"]),
    ("witnessarith", ["ZesuSsz.Automation.Switches.WitnessArith",
                      "ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts"]),
    ("spectail", ["ZesuSsz.Automation.Switches.SpecTail"]),
    ("lookupreduce", ["ZesuSsz.Automation.Switches.LookupReduce"]),
    ("callreturn", ["ZesuSsz.Automation.Switches.CallReturn"]),
    ("sealedopen", ["ZesuSsz.Automation.Switches.SealedOpen",
                    "ZesuSsz.Proofs.WriteSuccess.InterfacesCoverage"]),
    ("v2", ["ZesuSsz.Automation.Sets.v2",
            "ZesuSsz.Proofs.WriteSuccess.InterfacesCoverage",
            "ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts"]),
]


def run(commit: str, name: str, imports: list[str], lemma_set: Path,
        jobs: int, seconds: int, suffix: str) -> int:
    command = [sys.executable, "tools/residual/benchmark.py",
               "--automation", commit, "--set", str(lemma_set),
               "--name", f"{name}{suffix}", "--jobs", str(jobs),
               "--seconds", str(seconds)]
    for module in imports:
        command += ["--import", module]
    print(f"== arm {name}{suffix}", flush=True)
    return subprocess.run(command).returncode


def summary_of(commit: str, name: str) -> dict | None:
    path = RESULTS / f"{commit[:12]}-{name}.json"
    if not path.exists():
        return None
    return json.loads(path.read_text())["summary"]


def table(commit: str, suffix: str) -> list[str]:
    base = summary_of(commit, f"v1{suffix}")
    if base is None:
        return [f"no v1{suffix} arm on record"]
    classes = sorted({name for arm, _ in ARMS
                      for name in (summary_of(commit, f"{arm}{suffix}")
                                   or {}).get("classes", {})})
    head = "| arm | closed | median s | " + " | ".join(classes) + " |"
    rows = [head, "|" + "---|" * (len(classes) + 3)]
    for arm, _ in ARMS:
        now = summary_of(commit, f"{arm}{suffix}")
        if now is None:
            continue
        if arm == "v1":
            cells = [f"{100 * now['closed_fraction']:.1f}%",
                     f"{now['median_seconds']:.1f}"]
            cells += [str(now["classes"].get(name, 0)) for name in classes]
        else:
            cells = [f"{100 * (now['closed_fraction'] - base['closed_fraction']):+.1f}",
                     f"{now['median_seconds'] - base['median_seconds']:+.1f}"]
            cells += [f"{now['classes'].get(name, 0) - base['classes'].get(name, 0):+d}"
                      for name in classes]
        rows.append(f"| {arm} | " + " | ".join(cells) + " |")
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--commit", default="HEAD")
    parser.add_argument("--jobs", type=int, default=44)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--only", action="append", default=[],
                        help="run just these arms")
    parser.add_argument("--set", choices=("full", "rule15", "both"),
                        default="both")
    parser.add_argument("--table-only", action="store_true")
    parser.add_argument("--out", type=Path, default=None)
    arguments = parser.parse_args()

    commit = subprocess.run(["git", "rev-parse", arguments.commit],
                            capture_output=True, text=True,
                            check=True).stdout.strip()
    wanted = [(name, modules) for name, modules in ARMS
              if not arguments.only or name in arguments.only]
    sets = ([(FULL, "")] if arguments.set == "full" else
            [(RULE15, "-rule15")] if arguments.set == "rule15" else
            [(FULL, ""), (RULE15, "-rule15")])
    if not arguments.table_only:
        for lemma_set, suffix in sets:
            for name, modules in wanted:
                run(commit, name, modules, lemma_set, arguments.jobs,
                    arguments.seconds, suffix)
    text = "\n".join(
        [f"## Deltas per rule at {commit[:12]}", "",
         "The full set, 305 lemmas. `v1` is the reference row and shows",
         "its own figures; every other row is a difference from it.", ""]
        + table(commit, "")
        + ["", "The rule-15 set, 48 lemmas.", ""]
        + table(commit, "-rule15") + [""])
    print(text)
    if arguments.out:
        arguments.out.parent.mkdir(parents=True, exist_ok=True)
        arguments.out.write_text(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
