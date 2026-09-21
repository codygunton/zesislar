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
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from call_sites import premises as call_premises  # noqa: E402

TEMPLATE_SPEC = "FILL IN: the predicate that holds at the entry"
TEMPLATE_BINDERS = "FILL IN: the binders the predicate needs"


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
    arguments = parser.parse_args()

    entry = int(arguments.entry, 16)
    exit_address = int(arguments.exit_address, 16)
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
