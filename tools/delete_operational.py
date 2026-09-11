#!/usr/bin/env python3
"""Delete the operational proof layer and each Rocq module that imports it."""

from __future__ import annotations

import fnmatch
import re
import shutil
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
COQ_ROOT = ROOT / "ZesuSsz"

OPERATIONAL_ROOTS = (
    "ZesuSsz/Contracts/InstructionBoundary.v",
    "ZesuSsz/Contracts/ExecutionCertificate.v",
    "ZesuSsz/Contracts/ExecutionCertificateExamples.v",
    "ZesuSsz/Contracts/IslaMemoryOperational.v",
    "ZesuSsz/Experiments/WriteSuccessOperationalModel.v",
    "ZesuSsz/Experiments/WriteSuccessOperationalDefinitions.v",
    "ZesuSsz/Experiments/WriteSuccessSegmentAutomation.v",
    "ZesuSsz/Experiments/WriteSuccessCoverageAutomation.v",
    "ZesuSsz/Experiments/WriteSuccessConcreteRepresentation.v",
    "ZesuSsz/Experiments/WriteSuccessConcreteMachine.v",
    "ZesuSsz/Experiments/WriteSuccessCfgCertificate.v",
    "ZesuSsz/Generated/WriteSuccessCertificate.v",
)

DELETE_PATTERNS = (
    "ZesuSsz/Experiments/WriteSuccessSegment*.v",
    "ZesuSsz/Experiments/WriteSuccess*Operational*.v",
    "ZesuSsz/Experiments/WriteSuccess*Rank*.v",
    "ZesuSsz/Experiments/WriteSuccess*Coverage*.v",
    "ZesuSsz/Experiments/WriteSuccess*Concrete*.v",
    "ZesuSsz/Experiments/WriteSuccess*Counterexample*.v",
    "ZesuSsz/Experiments/WriteSuccessTraceAssumptions*.v",
    "ZesuSsz/Experiments/WriteSuccess*Position*.v",
    "ZesuSsz/Experiments/WriteSuccess*Recorded*.v",
    "ZesuSsz/Experiments/WriteSuccess*Blocker*.v",
    "ZesuSsz/Experiments/WriteSuccess*Iteration*.v",
    "ZesuSsz/Experiments/WriteSuccessCp1Concrete.v",
    "ZesuSsz/Experiments/WriteSuccessReviewInterfaces.v",
    "ZesuSsz/Experiments/WriteSuccessRepresentedPrefix.v",
    "ZesuSsz/Experiments/WriteSuccessOutputOwned.v",
    "ZesuSsz/Experiments/WriteSuccessHostObservation.v",
    "ZesuSsz/Evidence/generate_write_success_segments.py",
    "ZesuSsz/Evidence/test_generate_write_success_segments.py",
    "ZesuSsz/Evidence/templates",
    "ZesuSsz/Evidence/generate_write_success_trace_assumptions.py",
    "ZesuSsz/Evidence/test_generate_write_success_trace_assumptions.py",
    "ZesuSsz/Evidence/generate_write_success_certificate.py",
    "ZesuSsz/Evidence/check_write_success_certificate.py",
    "ZesuSsz/Evidence/test_write_success_certificate.py",
    "ZesuSsz/Evidence/write_success_certificate.json",
)

EXPLICIT_PROOF_DELETIONS = {
    "ZesuSsz/Experiments/WriteSuccessCp1Concrete.v",
    "ZesuSsz/Experiments/WriteSuccessReviewInterfaces.v",
    "ZesuSsz/Experiments/WriteSuccessRepresentedPrefix.v",
    "ZesuSsz/Experiments/WriteSuccessOutputOwned.v",
    "ZesuSsz/Experiments/WriteSuccessHostObservation.v",
}

RETAINED_PROOF_MODULES = {
    "ZesuSsz/Experiments/WriteSuccessWithdrawalsIterationBody.v",
}

IMPORT_RE = re.compile(
    r"(?:From\s+(\S+)\s+)?Require\s+Import\s+(.+?)\."
    r"(?=\s*(?:\(\*|$|\n))",
    re.S,
)


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def module_name(path: Path) -> str:
    return relative(path)[:-2].replace("/", ".")


def imports(path: Path) -> set[str]:
    text = path.read_text(encoding="utf-8")
    found: set[str] = set()
    for match in IMPORT_RE.finditer(text):
        prefix, names = match.groups()
        for token in names.split():
            found.add(f"{prefix}.{token}" if prefix else token)
    return found


def pattern_targets() -> set[Path]:
    targets: set[Path] = set()
    for pattern in DELETE_PATTERNS:
        if pattern == "ZesuSsz/Evidence/templates":
            directory = ROOT / pattern
            if directory.exists():
                targets.update(path for path in directory.rglob("*") if path.is_file())
            continue
        targets.update(
            path for path in ROOT.glob(pattern) if path.is_file()
        )
    return targets


def main() -> int:
    modules = list(COQ_ROOT.rglob("*.v"))
    by_name = {module_name(path): path for path in modules}
    deleted = {ROOT / path for path in OPERATIONAL_ROOTS if (ROOT / path).exists()}
    direct_patterns = pattern_targets()
    deleted_names = {module_name(path) for path in deleted if path.suffix == ".v"}

    # First compute only the modules that import an operational root.
    changed = True
    while changed:
        changed = False
        for name, path in by_name.items():
            if path in deleted:
                continue
            if imports(path) & deleted_names:
                deleted.add(path)
                deleted_names.add(name)
                changed = True

    retained_proofs = []
    for path in sorted(direct_patterns):
        text = path.read_text(encoding="utf-8", errors="replace")
        is_proof = "iStartProof" in text or "liARun" in text
        is_explicit = relative(path) in EXPLICIT_PROOF_DELETIONS
        is_retained = relative(path) in RETAINED_PROOF_MODULES
        if is_proof and (is_retained or (path not in deleted and not is_explicit)):
            deleted.discard(path)
            retained_proofs.append(path)
            continue
        deleted.add(path)

    # Remove residue that imports any file which Appendix A deletes.
    deleted_names.update(
        module_name(path) for path in deleted if path.suffix == ".v"
    )
    changed = True
    while changed:
        changed = False
        for name, path in by_name.items():
            if path in deleted or relative(path) in RETAINED_PROOF_MODULES:
                continue
            if imports(path) & deleted_names:
                deleted.add(path)
                deleted_names.add(name)
                changed = True

    for path in retained_proofs:
        print("KEEP " + relative(path))

    for path in sorted(deleted):
        print(relative(path))
    for path in sorted(deleted, reverse=True):
        if path.exists():
            path.unlink()

    templates = ROOT / "ZesuSsz/Evidence/templates"
    if templates.exists():
        shutil.rmtree(templates)
        print(relative(templates) + "/")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
