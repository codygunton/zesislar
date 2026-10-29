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
from modules import PROOF_OPENER, parse_module
BASELINE_PATH = Path(__file__).with_name("hygiene_baseline.json")
SIZE_BASELINE_PATH = Path(__file__).with_name("proof_size_baseline.json")
TRUSTED_DECLARATIONS_PATH = Path(__file__).with_name("hygiene_trusted_declarations.json")
AUTOMATION_PREFIX = "ZesuSsz/Automation/"
HOOKS_PATH = "ZesuSsz/Automation/Hooks.v"
LEGACY_PATH = "ZesuSsz/Automation/AllLegacy.v"
LEGACY_HOOKS_PATH = "ZesuSsz/Automation/Legacy/Hooks.v"
PROOFS_PREFIX = "ZesuSsz/Proofs/"
GENERATED_PROOFS_PREFIX = "ZesuSsz/Generated/"
SHELL_ALLOWLIST = {"ZesuSsz/Compliance/Shell.v"}
GENERATED_PREFIX = "generated/"

PLACEHOLDER = re.compile(
    r"^\s*(?:(?:Admitted|admit|Abort)\s*\.|"
    r"(?:Axiom|Parameter|Hypothesis|Variable)\b)"
)
HOOK_REDEFINITION = re.compile(
    r"\b(?:Ltac\s+\w+\s*::=|(?:liAStep|liAAsm|liStep)\s*::=)"
)
FORBIDDEN_EXECUTABLE_FORMS = (
    ("timeout identifier", re.compile(r"(?<![\w'])timeoutf?(?![\w'])")),
    ("Timeout command", re.compile(r"\b(?P<default>Set\s+Default\s+)?Timeout\s+\d+\b")),
    ("default timeout", re.compile(r"\bSet\s+Default\s+Timeout\b")),
    ("disabled checking", re.compile(r"\bUnset\b[^.]*\bChecking\b")),
    ("bypass_check identifier", re.compile(r"(?<![\w'])bypass_check(?![\w'])")),
)
TRUSTED_DECLARATION_FORMS = (
    ("ML declaration", re.compile(r"\bDeclare\s+ML\s+Module\b")),
    ("external declaration", re.compile(r"\bLtac2\s+@\s*external\b")),
)
DECLARATION_TOKEN = re.compile(r'"(?:[^"]|"")*"|[\w\x27]+|:=|->|=>|[^\s]')
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
RETIRED_PROOF_MODULES = (
    "ZesuSsz.Proofs.DecodeItem.Join6ae0.From6a38",
    "ZesuSsz.Proofs.DecodeItem.Join6ae0.From6ad8",
)


def executable_text(text: str, *, mask_strings: bool = True) -> str:
    """Mask nested comments and optional strings without changing offsets."""
    result = list(text)
    depth = 0
    quoted = False
    index = 0
    while index < len(text):
        pair = text[index:index + 2]
        if depth:
            if pair == "(*":
                result[index:index + 2] = "  "
                depth += 1
                index += 2
            elif pair == "*)":
                result[index:index + 2] = "  "
                depth -= 1
                index += 2
            else:
                if text[index] != "\n":
                    result[index] = " "
                index += 1
        elif quoted:
            if pair == '""':
                if mask_strings:
                    result[index:index + 2] = "  "
                index += 2
            else:
                if text[index] == '"':
                    quoted = False
                if mask_strings and text[index] != "\n":
                    result[index] = " "
                index += 1
        elif pair == "(*":
            result[index:index + 2] = "  "
            depth = 1
            index += 2
        elif text[index] == '"':
            if mask_strings:
                result[index] = " "
            quoted = True
            index += 1
        else:
            index += 1
    return "".join(result)


def normalized_declaration(text: str) -> str:
    """Preserve string contents and lexical tokens, ignoring comments and spacing."""
    return " ".join(DECLARATION_TOKEN.findall(executable_text(text, mask_strings=False)))


def trusted_declarations() -> set[tuple[str, str]]:
    rows = json.loads(TRUSTED_DECLARATIONS_PATH.read_text())["declarations"]
    result = set()
    for row in rows:
        name, statement = row["path"], row["statement"]
        if statement != normalized_declaration(statement):
            raise ValueError(f"A trusted declaration is not normalized: {name}")
        key = (name, statement)
        if key in result:
            raise ValueError(f"A trusted declaration repeats: {name}")
        result.add(key)
    return result


def trusted_declaration_failures(
    name: str, text: str, trusted: set[tuple[str, str]]
) -> list[str]:
    code = executable_text(text)
    failures = []
    seen = set()
    endings = list(re.finditer(r"\.(?=\s|$)", code))
    for label, pattern in TRUSTED_DECLARATION_FORMS:
        for match in pattern.finditer(code):
            start = max((ending.end() for ending in endings
                         if ending.end() <= match.start()), default=0)
            end = next((ending.end() for ending in endings
                        if ending.start() >= match.end()), len(text))
            statement = normalized_declaration(text[start:end])
            key = (name, statement)
            if key not in trusted or key in seen:
                number = code.count("\n", 0, match.start()) + 1
                failures.append(f"unapproved {label}: {name}:{number}")
            seen.add(key)
    return failures


def executable_form_failures(name: str, text: str) -> list[str]:
    code = executable_text(text)
    failures = []
    for label, pattern in FORBIDDEN_EXECUTABLE_FORMS:
        for match in pattern.finditer(code):
            if match.groupdict().get("default"):
                # Set Default Timeout has its own diagnostic.
                continue
            number = code.count("\n", 0, match.start()) + 1
            failures.append(f"forbidden {label}: {name}:{number}")
    return failures


def retired_module_failures(name: str, text: str) -> list[str]:
    """Prevent superseded hand modules and their imports from returning."""
    failures = []
    code = re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    for module in RETIRED_PROOF_MODULES:
        if name == module.replace(".", "/") + ".v":
            failures.append(f"retired proof module remains: {name}")
        prefix, short = module.rsplit(".", 1)
        relative = (rf"\bFrom\s+{re.escape(prefix)}\s+Require\s+"
                    rf"(?:Import|Export)\s+[^.]*\b{short}\b")
        if module in code or re.search(relative, code):
            failures.append(f"imports retired proof module: {name}: {module}")
    return failures


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


def generated_hand_line_failures(name: str, text: str) -> list[str]:
    """Generated instruction-body proofs must use only block automation."""
    if not name.startswith(GENERATED_PROOFS_PREFIX):
        return []
    path = ROOT / name
    proofs = parse_module(path)
    lines = text.splitlines()
    failures = []
    for proof in proofs:
        statement = "\n".join(lines[proof.declaration_line:proof.proof_line])
        if "instr_body" in statement and proof.hand_lines:
            failures.append(
                f"generated instr_body proof has hand lines: {name}: "
                f"{proof.name}: {len(proof.hand_lines)} lines"
            )
    return failures


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
            if PROOF_OPENER.match(line):
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
    trusted = trusted_declarations()
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
        failures.extend(executable_form_failures(name, text))
        failures.extend(trusted_declaration_failures(name, text, trusted))
        failures.extend(generated_hand_line_failures(name, text))
        failures.extend(retired_module_failures(name, text))

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
