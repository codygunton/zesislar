"""Prepare the dispatched Hand proof-size ratchet and run its project gate."""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "ZesuSsz/Evidence"))
from check_proof_hygiene import proof_size_metrics, proof_size_warnings, proof_size_ratchet_failures
from modules import parse_module

SESSION_KEYS = ("ZESU_WRITER_ID", "ZESU_DIAGNOSTIC_PROBE", "ZESU_PROBE_ISSUE",
                "ZESU_PROOF_CPU_LIMIT", "ZESU_SCOPE_CPU", "ZESU_MODULE_LIMIT_GIB", "ZESU_GATE_CLASS")


def gate_environment(environment):
    result = dict(environment)
    for key in SESSION_KEYS:
        result.pop(key, None)
    return result


def prepare(root, module, *, record_size=False):
    root = Path(root).resolve()
    path = (root / module).resolve()
    name = path.relative_to(root).as_posix()
    if not name.startswith("ZesuSsz/Proofs/DecodeItem/Hand/") or path.suffix != ".v":
        raise ValueError("Select a DecodeItem Hand module.")
    text = path.read_text()
    lines = text.splitlines()
    if not lines or lines[0] != "Require Import ZesuSsz.Automation.All.":
        raise ValueError("The Hand module must import Automation.All first.")
    if any(token in text for token in ("Admitted.", "Abort.")):
        raise ValueError("The Hand module must contain a complete proof.")
    native = [p for p in parse_module(path)
              if "instr_body" in "\n".join(lines[p.declaration_line:p.proof_line])]
    if not native:
        raise ValueError("The Hand module has no native statement.")
    counts = [p.terminator_line - p.proof_line + 1 for p in native]
    if max(counts) > 80:
        raise ValueError("The Hand proof exceeds 80 lines from Proof through Qed.")
    messages = proof_size_warnings(name, lines)
    metrics = proof_size_metrics(messages)
    if metrics["max_renames"] > 5:
        raise ValueError("The Hand proof exceeds the rename limit.")
    baseline = root / "ZesuSsz/Evidence/proof_size_baseline.json"
    data = json.loads(baseline.read_text())
    if record_size:
        data["files"][name] = {key: count for key, count in metrics.items() if count}
        baseline.write_text(json.dumps(data, indent=2) + "\n")
    failures = proof_size_ratchet_failures(name, messages, data["files"])
    if failures:
        raise ValueError("Missing measured Hand baseline. Use --record-size after the dispatched size review.")
    return {"module": name, "proof_lines": counts, "metrics": metrics,
            "proof_verification_performed": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, default=ROOT)
    parser.add_argument("--module", required=True)
    parser.add_argument("--agent", default="spec-a")
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--record-size", action="store_true")
    parser.add_argument("--check-fast", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.jobs <= 48:
        parser.error("The worker count must be between 1 and 48.")
    report = prepare(args.workspace, args.module, record_size=args.record_size)
    print(json.dumps(report), flush=True)
    if args.check_fast:
        root = args.workspace.resolve()
        return subprocess.call(["make", "check-fast", "CHECK_AGENT=" + args.agent,
            "AGENT_BUILD_DIR=" + str(root / "_build/agents" / args.agent),
            "FAST_JOBS=" + str(args.jobs)], cwd=root, env=gate_environment(os.environ))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
