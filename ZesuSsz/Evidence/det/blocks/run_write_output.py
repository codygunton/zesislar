#!/usr/bin/env python3
"""Infer the pinned writeOutput states and stage each available block.

Run this script from the repository root. Pass --entries with the canonical
block_entries.json path. Probe records stay in the selected build directory.
Use --generate-only to stage sources from an existing measurement run.
Set ZESU_SCRATCH_COQC_BINARY to a compiler adapter when shared artifacts
provide the dependencies. The scratch compiler still uses the normal guard.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tools/det"))
import infer_boundary  # noqa: E402

loader = importlib.util.spec_from_file_location("gen_block", ROOT / "tools/block/gen_block.py")
gen_block = importlib.util.module_from_spec(loader)
loader.loader.exec_module(gen_block)

TABLE_SHA256 = "dae0800e0d8b93d916c80a4c1fbebdd425964f43b2e2225712ead50b74104adc"
LEADERS = (0x14d80, 0x14e28, 0x14e38, 0x14e48, 0x14e58, 0x14e68, 0x14e78,
           0x14ed4, 0x14f08, 0x15180, 0x15200, 0x15228, 0x153d4, 0x155bc,
           0x156c0, 0x1572c, 0x15754)
CALL_RULE = "Require Import ZesuSsz.Automation.Sets.call."


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--entries", type=Path, required=True)
    parser.add_argument("--build-dir", type=Path,
                        default=ROOT / "_build/agents/writer-generator")
    parser.add_argument("--workers", type=int, choices=range(1, 17), default=4)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--generate-only", action="store_true")
    args = parser.parse_args()
    if Path.cwd().resolve() != ROOT:
        parser.error("run this script from the repository root")
    raw = args.entries.read_bytes()
    if hashlib.sha256(raw).hexdigest() != TABLE_SHA256:
        parser.error("the canonical entry table digest differs")
    entries = json.loads(raw)
    if len(entries) != 87:
        parser.error("the canonical entry table must contain 87 rows")
    args.build_dir = args.build_dir.resolve()
    records_dir = args.build_dir / "wp2-write-output"
    records_dir.mkdir(parents=True, exist_ok=True)
    for name in ("ARISTOTLE_API_KEY", "OPEN_ROUTER_API_KEY", "PROVER_API_KEY"):
        os.environ.pop(name, None)
    cfg = json.loads((ROOT / "build/endpoint-cfg/zesu-cfg.json").read_text())
    blocks = {gen_block.address(block["start"]): block
              for function in cfg["functions"]
              if gen_block.address(function["start"]) == 0x14d30
              for block in function["blocks"]}

    def measure(leader: int) -> None:
        selected = entries[hex(leader)]
        module = ROOT / "ZesuSsz/Proofs/WriteSuccess" / (selected["module"] + ".v")
        stop = hex(gen_block.address(blocks[leader]["end"]))
        entry = None
        parameter_types = {}
        for kind in ("entry", "stop"):
            if kind == "stop" and entry is None:
                (records_dir / f"stop_{leader:x}.jsonl").unlink(missing_ok=True)
                continue
            record = infer_boundary.infer(
                module, selected["lemma"], stop, args.build_dir, [], args.seconds,
                CALL_RULE, stop=stop, after_return=True, entry_only=kind == "entry",
                entry_state=entry if kind == "stop" else None)
            record["canonical_table_sha256"] = TABLE_SHA256
            record["probe_entry"] = hex(leader)
            if kind == 'stop':
                record['parameter_types'] = parameter_types
            (records_dir / f"{kind}_{leader:x}.jsonl").write_text(json.dumps(record) + "\n")
            print(f"{hex(leader)} {kind}: {record['outcome']}", flush=True)
            if kind == "entry" and record['outcome'] == 'reached':
                parameter_types = dict(gen_block.gen_boundary.sections(record['context'])[0])
                record['standard_call_frame'] = True
                entry = (gen_block.state_source(leader, record),
                         gen_block.state_application(leader, record))

    if not args.generate_only:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            list(pool.map(measure, LEADERS))
    states = {}
    for leader in LEADERS:
        for kind in ("stop", "entry"):
            path = records_dir / f"{kind}_{leader:x}.jsonl"
            if path.exists():
                record = json.loads(path.read_text())
                selected = entries[hex(leader)]
                if (record.get('canonical_table_sha256') != TABLE_SHA256
                        or record.get('probe_entry') != hex(leader)
                        or record.get('module') != selected['module'] + '.v'
                        or record.get('lemma') != selected['lemma']):
                    raise ValueError(f'the probe selection differs at {hex(leader)}')
                if record.get("outcome") == "reached":
                    record["standard_call_frame"] = True
                    states.setdefault(gen_block.address(record["state_entry"]), record)
    # The pinned entry selection supplies each leader's exact input.
    for leader in LEADERS:
        path = records_dir / f"entry_{leader:x}.jsonl"
        if path.exists():
            record = json.loads(path.read_text())
            if record.get("outcome") == "reached":
                record["standard_call_frame"] = True
                states[leader] = record
    staging = ROOT / gen_block.STAGING
    for child in ("States", "Blocks"):
        (staging / child).mkdir(parents=True, exist_ok=True)
    (staging / "dune").write_text("(data_only_dirs States Blocks)\n")
    for address, state in states.items():
        (staging / "States" / f"State_{address:x}.v").write_text(
            gen_block.state_source(address, state))
    staged = 0
    for leader in LEADERS:
        block = blocks[leader]
        try:
            source, _name = gen_block.generate(block, states)
            dependencies = [leader, *map(gen_block.address, block["successors"])]
            for address in dict.fromkeys(dependencies):
                (staging / "States" / f"State_{address:x}.v").write_text(
                    gen_block.state_source(address, states[address]))
            (staging / "Blocks" / f"Block_{leader:x}.v").write_text(source)
            staged += 1
            print(f"{hex(leader)}: staged", flush=True)
        except (ValueError, KeyError) as error:
            (staging / "Blocks" / f"Block_{leader:x}.v").unlink(missing_ok=True)
            print(f"{hex(leader)}: residual {error}", flush=True)
    print(f"staged {staged}/{len(LEADERS)} blocks", flush=True)
    return 0 if staged == len(LEADERS) else 1


if __name__ == "__main__":
    raise SystemExit(main())
