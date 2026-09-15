#!/usr/bin/env python3
"""Measure the remaining Lithium automation debt in one JSON row."""

import argparse
import json
import re
import statistics
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def tracked_rocq_files(root: Path) -> dict[str, str]:
    names = subprocess.check_output(
        ["git", "ls-files", "*.v"], cwd=root, text=True
    ).splitlines()
    return {name: (root / name).read_text() for name in names}


def is_new_style(name: str, text: str) -> bool:
    return name.startswith("ZesuSsz/Proofs/") and bool(
        re.search(r"\bzesu_(?:run|block)\b", text)
    )


def instr_body_proof_lines(text: str) -> list[int]:
    counts: list[int] = []
    statement_has_instr_body = False
    in_statement = False
    proof_start = None
    for number, line in enumerate(text.splitlines(), 1):
        if proof_start is None:
            if re.match(r"^\s*(?:Definition|Lemma|Theorem|Corollary)\b", line):
                in_statement = True
                statement_has_instr_body = "instr_body" in line
            elif in_statement:
                statement_has_instr_body = "instr_body" in line or statement_has_instr_body
            if re.match(r"^\s*Proof\.", line):
                proof_start = number
            continue
        if re.match(r"^\s*Qed\.", line):
            if statement_has_instr_body:
                counts.append(number - proof_start - 1)
            proof_start = None
            statement_has_instr_body = False
            in_statement = False
    return counts


def count_files(files: dict[str, str], pattern: str) -> int:
    regex = re.compile(pattern, re.MULTILINE)
    return sum(bool(regex.search(text)) for text in files.values())


def count_matches(files: dict[str, str], pattern: str) -> int:
    regex = re.compile(pattern, re.MULTILINE)
    return sum(len(regex.findall(text)) for text in files.values())


def build_log_metrics(log_root: Path) -> dict[str, object]:
    records = 0
    failures = 0
    for path in log_root.rglob("log.jsonl"):
        for line in path.read_text().splitlines():
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            records += 1
            failures += row.get("exit", 0) != 0
    return {
        "build_log_records": records,
        "build_log_failures": failures,
        "build_log_failure_fraction": failures / records if records else 0.0,
    }


def measure(
    files: dict[str, str], log_root: Path,
    benchmark_wall_ms: int | None, benchmark_zesu_run_ms: int | None,
) -> dict[str, object]:
    new_style = {
        name: text for name, text in files.items() if is_new_style(name, text)
    }
    toggle = (
        r"Local Remove Hints subsume_instr_pre'_inst[\s\S]*?"
        r"Local Existing Instance subsume_instr_pre_wand_inst"
    )
    code_destruct = r"iEval\s*\(rewrite\s+/[^\n]*instr_map"
    pose_correct = r"iPoseProof\s*\(\s*[A-Za-z0-9_'.]+_correct\b"
    proof_lines = [
        count
        for text in new_style.values()
        for count in instr_body_proof_lines(text)
    ]
    row: dict[str, object] = {
        "new_style_modules": len(new_style),
        "toggle_pairs_total": count_files(files, toggle),
        "toggle_pairs_new_style": count_files(new_style, toggle),
        "framed_continuations_import_files": count_files(
            files, r"^\s*Import\s+[^\n]*FramedContinuations"
        ),
        "guard_instance_lines": count_matches(
            files, r"^\s*Local Existing Instance subsume_instr_pre_guard_inst"
        ),
        "instr_pre_wand_total": count_matches(files, r"iApply\s+\(instr_pre_wand"),
        "instr_pre_wand_new_style": count_matches(
            new_style, r"iApply\s+\(instr_pre_wand"
        ),
        "manual_code_destructuring_files": count_files(files, code_destruct),
        "ipose_correct_occurrences": count_matches(new_style, pose_correct),
        "unshelve_total": count_matches(files, r"\bUnshelve\."),
        "unshelve_new_style": count_matches(new_style, r"\bUnshelve\."),
        "local_hint_rewrite_files": count_files(
            files, r"^\s*#\[local\]\s+Hint Rewrite"
        ),
        "remove_isla_traces_files": count_files(
            files, r"^\s*Local Remove Hints IslaTraces"
        ),
        "ilob_files": count_files(files, r"\biLöb\b"),
        "instr_body_proofs": len(proof_lines),
        "instr_body_proof_lines_median": statistics.median(proof_lines)
        if proof_lines else 0,
        "instr_body_proof_lines_max": max(proof_lines, default=0),
        "benchmark_wall_ms": benchmark_wall_ms,
        "benchmark_zesu_run_ms": benchmark_zesu_run_ms,
    }
    row.update(build_log_metrics(log_root))
    return row


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--log-root", type=Path)
    parser.add_argument("--benchmark-wall-ms", type=int)
    parser.add_argument("--benchmark-zesu-run-ms", type=int)
    args = parser.parse_args()
    common = subprocess.check_output(
        ["git", "rev-parse", "--git-common-dir"], cwd=args.root, text=True
    ).strip()
    base = (args.root / common).resolve().parent
    log_root = args.log_root or base
    print(json.dumps(measure(
        tracked_rocq_files(args.root), log_root,
        args.benchmark_wall_ms, args.benchmark_zesu_run_ms,
    ), sort_keys=True))


if __name__ == "__main__":
    main()
