"""Split the hand-written proofs into the two capture tiers.

Tier 1 is the current work front: the newest proof modules and the modules
that per-module commits touched since 2026-09-14. Two tree-wide sweeps since
that date rewrote almost every module, so a sweep commit does not make a
module recent; `SWEEP_FILES` drops those commits from the tier-1 evidence.
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass
from pathlib import Path

PROOF_GLOB = "ZesuSsz/Proofs/WriteSuccess/*.v"
# The tiers describe the proof history, not this branch.
HISTORY = "origin/islaris-native"
FROZEN_TIER_ONE = Path("ZesuSsz/Evidence/residuals/tier1_modules.txt")
FROZEN_RULE_15 = Path("ZesuSsz/Evidence/residuals/rule15_modules.txt")
ADDED_SINCE = "2026-09-10"
# The rule-15 era: the modules written after the rule-15 automation
# landed. 2026-09-15 is the boundary that gives the 54 records the
# lead counted in the section 9 review.
RULE_15_SINCE = "2026-09-15"
MODIFIED_SINCE = "2026-09-14"
NEWEST_ADDED = 50
SWEEP_FILES = 100


@dataclass
class Commit:
    sha: str
    date: str
    files: list[str]


def commits(arguments: list[str], repository: Path,
            since: str | None = None) -> list[Commit]:
    """Every non-merge commit that touched a proof, newest first.

    Two details keep this stable. The walk starts at `HISTORY`, not at
    `HEAD`, so this plan's own commits cannot shift a tier. And the date
    filter runs here rather than as `--since`: git prunes traversal at the
    first commit older than the cutoff, which made the same command return
    179 commits on one day and 126 on the next.
    """
    command = ["git", "log", "--no-merges", "--pretty=format:COMMIT %h %cs",
               "--name-only", *arguments, HISTORY, "--", PROOF_GLOB]
    output = subprocess.run(command, cwd=repository, capture_output=True,
                            text=True, check=True).stdout
    found: list[Commit] = []
    for line in output.split("\n"):
        if line.startswith("COMMIT "):
            _, sha, date = line.split()
            found.append(Commit(sha=sha, date=date, files=[]))
        elif line.strip() and found:
            found[-1].files.append(line.strip())
    if since:
        found = [commit for commit in found if commit.date >= since]
    return found


def newest_added(repository: Path) -> list[str]:
    """The `NEWEST_ADDED` modules that appeared last, newest first."""
    order: list[str] = []
    seen: set[str] = set()
    for commit in commits(["--diff-filter=A"], repository,
                          ADDED_SINCE):
        if len(commit.files) > SWEEP_FILES:
            continue
        for path in commit.files:
            if path not in seen:
                seen.add(path)
                order.append(path)
    return order[:NEWEST_ADDED]


def recently_modified(repository: Path) -> set[str]:
    return {path
            for commit in commits([], repository, MODIFIED_SINCE)
            if len(commit.files) <= SWEEP_FILES
            for path in commit.files}


def tier_one_modules(repository: Path) -> list[str]:
    """The tier-1 modules, from the frozen list when one exists.

    The corpus was probed against one set of modules, and every statistic
    refers to it. Recomputing the set from the history on each run would
    silently change the denominator, so the frozen file wins.
    """
    kept = frozen(FROZEN_TIER_ONE)
    if kept is not None:
        return kept
    paths = set(newest_added(repository)) | recently_modified(repository)
    return sorted(path for path in paths if (repository / path).exists())


def rule_15_modules(repository: Path) -> list[str]:
    """The modules added in the rule-15 era, the harness's real population."""
    kept = frozen(FROZEN_RULE_15)
    if kept is not None:
        return kept
    order: list[str] = []
    seen: set[str] = set()
    for commit in commits(["--diff-filter=A"], repository, RULE_15_SINCE):
        if len(commit.files) > SWEEP_FILES:
            continue
        for path in commit.files:
            if path not in seen and (repository / path).exists():
                seen.add(path)
                order.append(path)
    return sorted(order)


def frozen(path: Path) -> list[str] | None:
    """A module list written to disk, which no later commit can shift."""
    if not Path(path).exists():
        return None
    return [line.strip() for line in Path(path).read_text().split("\n")
            if line.strip() and not line.startswith("#")]
