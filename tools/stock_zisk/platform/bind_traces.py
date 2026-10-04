#!/usr/bin/env python3
"""Bind completed trace generation without rerunning unchanged instructions."""
import argparse
import hashlib
import json
from pathlib import Path
import re
from traces import validate_instruction_modules
ROOT=Path(__file__).resolve().parents[3]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def rec(path): return {"path":str(path),"sha256":sha(path)}
def main():
    parser=argparse.ArgumentParser();parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args();out=args.out.resolve()
    report=json.loads((out / "coverage.json").read_text())
    dump=out.parent / (out.name + ".selected.dump")
    if sha(dump) != report["dump_sha256"]:
        raise ValueError("The selected instruction dump changed after generation")
    pcs=[int(m[1],16) for line in dump.read_text().splitlines()
         if (m:=re.match(r"^([0-9a-fA-F]+):\s+[0-9a-fA-F]{8}\s+",line))]
    if len(set(pcs)) != len(pcs): raise ValueError("The selected instruction dump repeats a PC")
    generated_count=validate_instruction_modules(out,pcs)
    if generated_count != report["generated_count"] or generated_count != report["instruction_count"]-len(report["unsupported_runtime_boundaries"]):
        raise ValueError("The reported coverage differs from the instruction modules")
    if report["platform_snapshot_sha256"] != sha(ROOT / "build/stock-zisk/platform/riscv64-zisk.ir"):
        raise ValueError("The platform snapshot changed after generation")
    if report["config_sha256"] != sha(ROOT / "ZesuSsz/riscv64_zesu.toml"):
        raise ValueError("The selected configuration changed after generation")
    for path,value in report["files"].items():
        if sha(ROOT/path) != value: raise ValueError("A generated trace changed: " + path)
    inputs={"generator":rec(ROOT / "tools/stock_zisk/platform/traces.py"),
      "footprint_wrapper":rec(ROOT / "tools/stock_zisk/platform/bin/isla-footprint"),
      "footprint":rec(Path("/home/cody/isla/target/release/isla-footprint")),
      "frontend":rec(Path("/home/cody/islaris/_opam/bin/islaris")),
      "snapshot":rec(ROOT / "build/stock-zisk/platform/riscv64-zisk.ir"),
      "configuration":rec(ROOT / "ZesuSsz/riscv64_zesu.toml")}
    derived={str(p.relative_to(ROOT)):dict(rec(p),schema_version=1)
       for p in sorted(out.iterdir()) if p.is_file() and p.name != "manifest-fragment.json"}
    data={"schema_version":1,"inputs":inputs,"derived":derived,
          "traces":{"elf_sha256":report["elf_sha256"],"instruction_count":report["instruction_count"],
            "generated_count":generated_count,"instruction_modules_validated":True,"full_closure_coverage":report["full_closure_coverage"],
            "unsupported_runtime_boundaries":report["unsupported_runtime_boundaries"],
            "manifest_binding_pending":True}}
    (out / "manifest-fragment.json").write_text(json.dumps(data,indent=2)+"\n")
    print(f"Trace fragment: {len(derived)} files, coverage {report['generated_count']}/{report['instruction_count']}")
if __name__ == "__main__": main()
