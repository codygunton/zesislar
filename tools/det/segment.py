#!/usr/bin/env python3
"""One segment, from an address range to a probed module.

`make gen-segment ENTRY=0x156e8 EXIT=0x15744` lands here. The tool does
the three things the range already determines, and says plainly what it
cannot determine:

1. the calls the range makes, as `□ instr_pre <callee> <contract>`
   premises, from the `jal`/`jalr` targets of the disassembly mapped to
   the closed B2/B4 contracts. A block never steps into a callee.
2. the spec record the generator reads, written to `--spec-out`, with
   everything the range fixes filled in.
3. the probe, when the record is complete: `infer_boundary.py` runs the
   block and reports the exit boundary or the first stall.

What the range does not determine is the predicate that holds at the
entry and the binders it needs. Those come from the segment's interface,
or from the previous segment's inferred exit once chain generation runs.
Pass them with `--spec` and `--binders`, or fill the template in.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from call_sites import premises as call_premises  # noqa: E402
from gen_segment import GENERATED_DIR, PROOF_DIR, generate  # noqa: E402
from infer_boundary import infer  # noqa: E402
from modules import find_proof  # noqa: E402

TEMPLATE_SPEC = "FILL IN: the predicate that holds at the entry"
TEMPLATE_BINDERS = "FILL IN: the binders the predicate needs"
BOUNDARY_SET = Path("ZesuSsz/Evidence/det/boundary_set.txt")


def existing_segment(entry: int, exit_address: int,
                     boundary_set: Path = BOUNDARY_SET) -> tuple[Path, str] | None:
    """Find a merged statement whose exact range is already recorded."""
    for line in boundary_set.read_text().splitlines():
        if line.count(":") != 2:
            continue
        module, lemma, exit_text = line.split(":")
        if int(exit_text, 16) != exit_address:
            continue
        path = PROOF_DIR / module
        proof = find_proof(path, lemma)
        source = "\n".join(path.read_text().splitlines()[
            proof.declaration_line:proof.proof_line])
        match = re.search(r"\binstr_body\s+0x([0-9a-fA-F]+)", source)
        if match and int(match.group(1), 16) == entry:
            return path, lemma
    return None


def generate_existing(path: Path, lemma: str, exit_address: int,
                      out_dir: Path, out: Path, build_dir: Path,
                      seconds: int) -> dict:
    """Generate an opt-in module and probe its existing boundary."""
    source, generated_name = generate(path, lemma, [])
    out_dir.mkdir(parents=True, exist_ok=True)
    target = out_dir / f"Generated{path.stem}.v"
    target.write_text(source)
    record = infer(path, lemma, hex(exit_address), build_dir, [], seconds,
                   extra_imports=("ZesuSsz.Automation.Sets.v2",))
    record.update({"generated": str(target), "generated_lemma": generated_name})
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(record) + "\n")
    goal_head = record.get("signature") or next(
        iter(record.get("conclusion", "").splitlines()), "")
    print(f"generated {target}")
    print(f"{record['seconds']:.1f}s outcome={record['outcome']} "
          f"class={record.get('pred_class', 'none')} goal={goal_head[:100]}")
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--entry", required=True)
    parser.add_argument("--exit", dest="exit_address", required=True)
    parser.add_argument("--name", default=None,
                        help="the lemma name; default is derived from the "
                             "entry address")
    parser.add_argument("--like", default="WriteSuccessExactWithdrawalsNativeConnection.v",
                        help="an existing module whose imports the segment "
                             "shares")
    parser.add_argument("--spec", default=TEMPLATE_SPEC)
    parser.add_argument("--binders", default=TEMPLATE_BINDERS)
    parser.add_argument("--import", dest="imports", action="append",
                        default=[])
    parser.add_argument("--spec-out", type=Path,
                        default=Path("_build/agents/det/segment.json"))
    parser.add_argument("--out", type=Path,
                        default=Path("_build/agents/det/segment.jsonl"))
    parser.add_argument("--seconds", type=int, default=900)
    parser.add_argument("--probe", action="store_true",
                        help="run the probe once the record is complete")
    parser.add_argument("--out-dir", type=Path, default=GENERATED_DIR)
    parser.add_argument("--build-dir", type=Path,
                        default=Path("_build/agents/det"))
    arguments = parser.parse_args()

    entry = int(arguments.entry, 16)
    exit_address = int(arguments.exit_address, 16)
    if arguments.spec == TEMPLATE_SPEC and arguments.binders == TEMPLATE_BINDERS:
        existing = existing_segment(entry, exit_address)
        if existing:
            record = generate_existing(*existing, exit_address,
                                       arguments.out_dir, arguments.out,
                                       arguments.build_dir, arguments.seconds)
            return 1 if record["outcome"] == "error" else 0
    calls, modules, unknown = call_premises(entry, exit_address)
    print(f"calls in [{arguments.entry}, {arguments.exit_address}): "
          f"{len(calls)} premises, {len(modules)} contract modules")
    for line in calls:
        print(f"  {line.strip()}")
    for target in unknown:
        print(f"  no closed contract for {target}; the segment cannot be "
              f"stated until one exists")

    default_imports = [
        "ZesuSsz.Automation.All",
        "ZesuSsz.Automation.Sets.v2",
        "ZesuSsz.Contracts.Endpoints",
        "ZesuSsz.Contracts.IslarisCode",
        "ZesuSsz.Proofs.WriteSuccess.Interfaces",
        "ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract",
        "ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation",
        "ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts",
    ]
    record = {
        "name": arguments.name or f"write_success_segment_{entry:x}",
        "entry": arguments.entry,
        "exit": arguments.exit_address,
        "like": arguments.like,
        "imports": default_imports + list(arguments.imports),
        "binders": arguments.binders,
        "spec": arguments.spec,
    }
    arguments.spec_out.parent.mkdir(parents=True, exist_ok=True)
    arguments.spec_out.write_text(json.dumps([record], indent=2) + "\n")
    print(f"spec record written to {arguments.spec_out}")

    if TEMPLATE_SPEC in record["spec"] or TEMPLATE_BINDERS in record["binders"]:
        print("the entry predicate is still a template: fill it in, then "
              "re-run with --probe")
        return 0
    if not arguments.probe:
        return 0
    return subprocess.run(
        [sys.executable, str(HERE / "infer_boundary.py"),
         "--specs", str(arguments.spec_out), "--out", str(arguments.out),
         "--seconds", str(arguments.seconds)]).returncode


if __name__ == "__main__":
    raise SystemExit(main())
