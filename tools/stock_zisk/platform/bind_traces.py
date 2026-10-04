#!/usr/bin/env python3
"""Bind completed trace generation without rerunning unchanged instructions."""
import argparse
import hashlib
import json
from pathlib import Path
import re
from traces import validate_instruction_modules, Image, ELFFile
from exports import selected_commitments, validate_exports
from indexes import approved_regions, validate_partition, validate_indexes
ROOT=Path(__file__).resolve().parents[3]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def rec(path): return {"path":str(path),"sha256":sha(path)}
def validate_expected_files(out, manifest, trace_name):
    expected = json.loads(manifest.read_text())
    prefix = "generated/isla-traces/stock-zisk/" + trace_name + "/"
    records = {name[len(prefix):]: record for name,record in expected.get("project_derived",{}).items()
               if name.startswith(prefix) and name[len(prefix):] not in {"manifest-fragment.json", "generation-measurement.json"}}
    actual = {path.name: path for path in out.iterdir() if path.is_file()
              and path.name not in {"manifest-fragment.json", "generation-measurement.json"}}
    if records.keys() != actual.keys():
        raise ValueError("Regenerated files differ from the manifest file list")
    for name,path in actual.items():
        if sha(path) != records[name]["sha256"]:
            raise ValueError("Regenerated file differs from the manifest: " + name)

def validate_expected_commitments(commitments, manifest, trace_name):
    expected = json.loads(manifest.read_text())
    if commitments != expected.get("traces", {}).get(trace_name, {}).get("commitments"):
        raise ValueError("The regenerated commitments differ from the tracked manifest")

def main():
    parser=argparse.ArgumentParser();parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--check-manifest",type=Path)
    parser.add_argument("--trace-name",default="closure")
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
        actual_path = out / Path(path).name if report["schema_version"] == 2 else ROOT/path
        if sha(actual_path) != value: raise ValueError("A generated trace changed: " + path)
    if "indexes" in report:
        regions = {name: {int(pc,16) for pc in values} for name,values in report["indexes"]["regions"].items()}
        inventory_path = ROOT / "build/stock-zisk/inventory.json"
        for key in ["elf_sha256", "platform_snapshot_sha256", "config_sha256"]:
            if report["indexes"][key] != report[key]:
                raise ValueError("The index input differs: " + key)
        approved = approved_regions(json.loads(inventory_path.read_text()), set(pcs))
        if regions != approved: raise ValueError("Indexes differ from the approved regions")
        validate_partition(regions, set(pcs))
        validate_indexes(out, regions, report["indexes"]["coqdir"])
        if (out / "instrs.v").exists(): raise ValueError("The closure-wide index must be absent")
    groups = regions if "indexes" in report else {"decodeItem": set(pcs)}
    inventory_path = ROOT / "build/stock-zisk/inventory.json"
    elf = ROOT / "build/stock-zisk/zesu-zisk.elf"
    if sha(elf) != report["elf_sha256"]: raise ValueError("The selected ELF changed")
    with elf.open("rb") as stream:
        commitments = selected_commitments(json.loads(inventory_path.read_text()), Image(ELFFile(stream)), groups)
    if commitments != report.get("commitments"):
        raise ValueError("The coverage byte or CFG commitments differ from the selected ELF")
    for name, commitment in commitments.items():
        path = out / ("index_" + name + ".v" if "indexes" in report else "instrs.v")
        validate_exports(path, name, commitment)
    if args.check_manifest:
        validate_expected_commitments(commitments, args.check_manifest, args.trace_name)
        validate_expected_files(out, args.check_manifest, args.trace_name)
        print("Regenerated deterministic files match the tracked manifest")
        return
    inputs={"generator":rec(ROOT / "tools/stock_zisk/platform/traces.py"),
      "index_tests":rec(ROOT / "tools/stock_zisk/platform/test_build.py"),
      "inventory_generator":rec(ROOT / "tools/stock_zisk/closure.py"),
      "exporter":rec(ROOT / "tools/stock_zisk/platform/exports.py"),
      "callee_identity":rec(ROOT / "ZesuSsz/Contracts/CalleeIdentity/CalleeId.v"),
      "callee_theory":rec(ROOT / "ZesuSsz/Contracts/CalleeIdentity/dune"),
      "index_checker":rec(ROOT / "tools/stock_zisk/platform/indexes.py"),
      "cache_replay":rec(ROOT / "tools/stock_zisk/platform/cache_footprint.py"),
      "binder":rec(ROOT / "tools/stock_zisk/platform/bind_traces.py"),
      "footprint_wrapper":rec(ROOT / "tools/stock_zisk/platform/bin/isla-footprint"),
      "footprint":rec(Path("/home/cody/isla/target/release/isla-footprint")),
      "frontend":rec(Path("/home/cody/islaris/_opam/bin/islaris")),
      "snapshot":rec(ROOT / "build/stock-zisk/platform/riscv64-zisk.ir"),
      "configuration":rec(ROOT / "ZesuSsz/riscv64_zesu.toml")}
    derived={str(p.relative_to(ROOT)):dict(rec(p),schema_version=1)
       for p in sorted(out.iterdir()) if p.is_file() and p.name not in {"manifest-fragment.json", "generation-measurement.json"}}
    data={"schema_version":1,"inputs":inputs,"derived":derived,
          "traces":{"elf_sha256":report["elf_sha256"],"instruction_count":report["instruction_count"],
            "generated_count":generated_count,"instruction_modules_validated":True,"full_closure_coverage":report["full_closure_coverage"],
            "unsupported_runtime_boundaries":report["unsupported_runtime_boundaries"],
            "unmodeled_instructions":report["unsupported_runtime_boundaries"],
            "commitments":commitments,
            "manifest_binding_pending":True}}
    (out / "manifest-fragment.json").write_text(json.dumps(data,indent=2)+"\n")
    print(f"Trace fragment: {len(derived)} files, coverage {report['generated_count']}/{report['instruction_count']}")
if __name__ == "__main__": main()
