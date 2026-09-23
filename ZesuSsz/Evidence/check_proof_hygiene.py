#!/usr/bin/env python3
"""Enforce proof hygiene and ratchet away legacy forbidden identifiers."""

import fnmatch
import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools" / "residual"))
from modules import parse_module
BASELINE_PATH = Path(__file__).with_name("hygiene_baseline.json")
SIZE_BASELINE_PATH = Path(__file__).with_name("proof_size_baseline.json")
RECORD_BASELINE_PATH = Path(__file__).with_name("residual_record_baseline.json")
RESIDUAL_CORPUS = ROOT / "ZesuSsz" / "Evidence" / "residuals" / "corpus.jsonl"
DET_EVIDENCE = ROOT / "ZesuSsz" / "Evidence" / "det"
LEMMA_RECORD = re.compile(r'"lemma"\s*:\s*"([^"]+)"')
AUTOMATION_PREFIX = "ZesuSsz/Automation/"
HOOKS_PATH = "ZesuSsz/Automation/Hooks.v"
LEGACY_PATH = "ZesuSsz/Automation/AllLegacy.v"
LEGACY_HOOKS_PATH = "ZesuSsz/Automation/Legacy/Hooks.v"
PROOFS_PREFIX = "ZesuSsz/Proofs/"
SHELL_ALLOWLIST = {"ZesuSsz/Compliance/Shell.v"}
GENERATED_PREFIX = "generated/"

PLACEHOLDER = re.compile(
    r"^\s*(?:(?:Admitted|admit|Abort)\s*\.|"
    r"(?:Axiom|Parameter|Hypothesis|Variable)\b)"
)
HOOK_REDEFINITION = re.compile(
    r"\b(?:Ltac\s+\w+\s*::=|(?:liAStep|liAAsm|liStep)\s*::=)"
)
LEGACY_HOOK_LINES = {
    "Ltac liAStep ::= zesu_liAStep.",
}
FORBIDDEN_IDENTIFIERS = (
    "IslaInstructionSegment",
    "writeSuccessTraceAssumptions",
    "zesu_ld_byte_array_at_spec",
    "zesu_lbu_byte_array_at_spec",
    "zesu_ld_array_at_spec",
    "solve_zesu_ld_array_at",
    "mem_mapsto_array_recombine_u64_read",
    "Local Remove Hints subsume_instr_pre'_inst",
    "Local Remove Hints subsume_instr_pre_zesu_inst",
)
A1_MODULES = (
    "ZesuSsz.Contracts.InstructionBoundary",
    "ZesuSsz.Contracts.ExecutionCertificate",
    "ZesuSsz.Contracts.ExecutionCertificateExamples",
    "ZesuSsz.Contracts.IslaMemoryOperational",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessOperationalModel",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessOperationalDefinitions",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessSegmentAutomation",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessCoverageAutomation",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessConcreteRepresentation",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessConcreteMachine",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessCfgCertificate",
    "ZesuSsz.Generated.WriteSuccessCertificate",
)
A2_PATTERNS = (
    "WriteSuccessSegment*.v",
    "WriteSuccess*Operational*.v",
    "WriteSuccess*Rank*.v",
    "WriteSuccess*Coverage*.v",
    "WriteSuccess*Concrete*.v",
    "WriteSuccess*Counterexample*.v",
    "WriteSuccessTraceAssumptions*.v",
    "WriteSuccess*Position*.v",
    "WriteSuccess*Recorded*.v",
    "WriteSuccess*Blocker*.v",
    "WriteSuccess*Iteration*.v",
    "WriteSuccessCp1Concrete.v",
    "WriteSuccessReviewInterfaces.v",
    "WriteSuccessRepresentedPrefix.v",
    "WriteSuccessOutputOwned.v",
    "WriteSuccessHostObservation.v",
)
A2_EXCEPTIONS = {"WriteSuccessWithdrawalsIterationBody.v"}
CP1_ENFORCED = True


def tracked_files() -> list[str]:
    """Every file the repository would carry, tracked or not yet added.

    `git ls-files` alone lists only tracked files, so a new module escapes
    every rule here until it is committed. A `Ltac … ::=` outside
    `Hooks.v` survived two commits that way. `--others
    --exclude-standard` adds the files that are new but not ignored, which
    is what a reviewer would see.
    """
    output = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard"],
        cwd=ROOT, text=True
    )
    return sorted(set(output.splitlines()))


def recorded_lemmas() -> set[str]:
    """Every lemma that has a residual record on disk.

    A hand line is a debt, and a debt has to be visible: the record says
    what the automation refused and which class it belongs to, so the
    line becomes a ticket instead of a habit. The corpus is the store the
    replay writes; the `det` evidence adds the records the probes write.
    """
    names: set[str] = set()
    for path in [RESIDUAL_CORPUS, *sorted(DET_EVIDENCE.rglob("*.jsonl"))]:
        if not path.exists():
            continue
        with path.open() as handle:
            for line in handle:
                match = LEMMA_RECORD.search(line)
                if match:
                    names.add(match.group(1))
    return names


def record_ratchet_failures(
    name: str,
    entries: list[tuple[str, str, int]],
    recorded: set[str],
    baseline: list[str],
) -> list[str]:
    """The ratchet itself, over (lemma, statement, hand-line count)."""
    failures = []
    for lemma, statement, hand in entries:
        if "instr_body" not in statement or hand == 0:
            continue
        if lemma in recorded or f"{name}:{lemma}" in baseline:
            continue
        failures.append(
            f"hand lines with no residual record: {name}: {lemma}: "
            f"{hand} lines"
        )
    return failures


def residual_record_failures(
    name: str, text: str, recorded: set[str], baseline: list[str]
) -> list[str]:
    """A new lemma with hand lines needs a residual record.

    The ratchet is one-way: everything that has hand lines today is in the
    baseline, and a lemma added after it either closes with the block
    automation alone or arrives with the record that explains why it
    cannot.
    """
    path = ROOT / name
    try:
        proofs = parse_module(path)
    except (OSError, ValueError):
        return []
    lines = text.splitlines()
    entries = [
        (proof.name,
         "\n".join(lines[proof.declaration_line:proof.proof_line]),
         len(proof.hand_lines))
        for proof in proofs
    ]
    return record_ratchet_failures(name, entries, recorded, baseline)


def forbidden_counts(text: str) -> dict[str, int]:
    return {
        identifier: text.count(identifier)
        for identifier in FORBIDDEN_IDENTIFIERS
        if text.count(identifier)
    }


def ratchet_failures(
    name: str, counts: dict[str, int], baseline: dict[str, dict[str, int]]
) -> list[str]:
    failures = []
    allowed = baseline.get(name, {})
    for identifier, count in counts.items():
        limit = allowed.get(identifier, 0)
        if count > limit:
            failures.append(
                f"forbidden-name increase: {name}: {identifier}: {count} > {limit}"
            )
    return failures


def proof_size_warnings(name: str, lines: list[str]) -> list[str]:
    warnings = []
    proof_start = None
    statement_has_instr_body = False
    rename_count = 0
    for number, line in enumerate(lines, 1):
        if proof_start is None:
            statement_has_instr_body = statement_has_instr_body or "instr_body" in line
            if re.match(r"^\s*Proof\.", line):
                if re.search(r"\bQed\.", line):
                    statement_has_instr_body = False
                else:
                    proof_start = number
                    rename_count = 0
            elif re.match(r"^\s*(?:Definition|Lemma|Theorem|Corollary)\b", line):
                statement_has_instr_body = "instr_body" in line
            continue
        rename_count += line.count("iRename select")
        if re.match(r"^\s*Qed\.", line):
            if rename_count > 5:
                warnings.append(
                    f"proof has {rename_count} iRename select calls: {name}:{proof_start}"
                )
            proof_lines = number - proof_start - 1
            if statement_has_instr_body and proof_lines > 40:
                warnings.append(
                    f"instr_body proof has {proof_lines} lines: {name}:{proof_start}"
                )
            proof_start = None
            statement_has_instr_body = False
    return warnings


def proof_size_metrics(messages: list[str]) -> dict[str, int]:
    line_counts = [
        int(match.group(1))
        for message in messages
        if (match := re.search(r"instr_body proof has (\d+) lines", message))
    ]
    rename_counts = [
        int(match.group(1))
        for message in messages
        if (match := re.search(r"proof has (\d+) iRename", message))
    ]
    return {
        "long_proofs": len(line_counts),
        "max_proof_lines": max(line_counts, default=0),
        "rename_proofs": len(rename_counts),
        "max_renames": max(rename_counts, default=0),
    }


def proof_size_ratchet_failures(
    name: str, messages: list[str], baseline: dict[str, dict[str, int]]
) -> list[str]:
    current = proof_size_metrics(messages)
    allowed = baseline.get(name, {})
    failures = []
    for metric, count in current.items():
        limit = allowed.get(metric, 0)
        if count > limit:
            failures.append(
                f"proof-size increase: {name}: {metric}: {count} > {limit}"
            )
    return failures


def main() -> None:
    baseline_data = json.loads(BASELINE_PATH.read_text())
    baseline = baseline_data["files"]
    legacy_entries = set(baseline_data["legacy_entry_files"])
    size_baseline_data = json.loads(SIZE_BASELINE_PATH.read_text())
    size_baseline = size_baseline_data["files"]
    record_baseline = (json.loads(RECORD_BASELINE_PATH.read_text())["lemmas"]
                       if RECORD_BASELINE_PATH.exists() else [])
    recorded = recorded_lemmas()
    failures: list[str] = []
    warnings: list[str] = []
    remaining = 0
    for name in tracked_files():
        if name.startswith("generated/isla-traces/"):
            failures.append(f"tracked generated Isla trace: {name}")
        if not name.endswith(".v"):
            continue
        path = ROOT / name
        if not path.exists():
            # `git ls-files --cached` still lists a file that has been
            # deleted in the working tree. A reviewer sees the deletion,
            # so the checker does too.
            continue
        text = path.read_text()
        lines = text.splitlines()

        # Generated Sail interfaces contain upstream Axiom declarations.
        # Reviewed proof files remain subject to the complete placeholder check.
        if name not in SHELL_ALLOWLIST and not name.startswith(GENERATED_PREFIX):
            for number, line in enumerate(lines, 1):
                if PLACEHOLDER.search(line):
                    failures.append(
                        f"proof placeholder: {name}:{number}: {line.strip()}"
                    )

        if name != HOOKS_PATH:
            for number, line in enumerate(lines, 1):
                if HOOK_REDEFINITION.search(line):
                    if (name != LEGACY_HOOKS_PATH or
                            line.strip() not in LEGACY_HOOK_LINES):
                        failures.append(f"Lithium hook redefinition: {name}:{number}")

        if name.startswith(PROOFS_PREFIX):
            normal_entry = "Require Import ZesuSsz.Automation.All." in text
            legacy_entry = "Require Import ZesuSsz.Automation.AllLegacy." in text
            if not normal_entry and not (name in legacy_entries and legacy_entry):
                failures.append(f"missing Automation.All import: {name}")
            if legacy_entry and name not in legacy_entries:
                failures.append(f"unapproved Automation.AllLegacy import: {name}")
            if normal_entry and legacy_entry:
                failures.append(f"both Automation entries imported: {name}")
            if (path.name not in A2_EXCEPTIONS and
                    any(fnmatch.fnmatch(path.name, pattern) for pattern in A2_PATTERNS)):
                failures.append(f"Appendix A.2 file remains: {name}")
            failures.extend(residual_record_failures(
                name, text, recorded, record_baseline))
            size_messages = proof_size_warnings(name, lines)
            if CP1_ENFORCED:
                warnings.extend(size_messages)
                failures.extend(
                    proof_size_ratchet_failures(name, size_messages, size_baseline)
                )
            else:
                warnings.extend(size_messages)

        for module in A1_MODULES:
            if module in text:
                failures.append(f"imports Appendix A.1 module: {name}: {module}")

        if not name.startswith(AUTOMATION_PREFIX):
            counts = forbidden_counts(text)
            remaining += sum(counts.values())
            failures.extend(ratchet_failures(name, counts, baseline))

    if warnings:
        print(f"warning: {len(warnings)} proof-size baseline violations remain", file=sys.stderr)
    if remaining:
        print(
            f"warning: {remaining} baseline forbidden-name occurrences remain",
            file=sys.stderr,
        )
    if failures:
        raise SystemExit("\n".join(failures))


if __name__ == "__main__":
    main()
