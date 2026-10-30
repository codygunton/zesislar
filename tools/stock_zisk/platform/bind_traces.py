#!/usr/bin/env python3
"""Bind completed trace generation without rerunning unchanged instructions."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import tomllib
from types import SimpleNamespace
from traces import selected_rows, selected_dump, resolve_trace_elf, normalize_dune_package
from access_regions import annotate_regions, read_source_map
from traces import validate_instruction_modules, Image, ELFFile
from exports import selected_commitments, validate_exports
from indexes import approved_regions, validate_partition, validate_indexes
ROOT=Path(__file__).resolve().parents[3]
TRACE_ONLY_GROUPS = {
    "eql": ("ZesuSsz.Stock.Eql", 74, 46),
    "decodeItemRegions": ("ZesuSsz.Stock.DecodeItemRegions", 116, 50),
}
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def rec(path): return {"path":str(path),"sha256":sha(path)}
def validate_expected_files(out, manifest, trace_name):
    excluded = {"manifest-fragment.json", "generation-measurement.json"}
    if trace_name in TRACE_ONLY_GROUPS:
        excluded.add("trace-manifest.json")
    expected = json.loads(manifest.read_text())
    prefix = "generated/isla-traces/stock-zisk/" + trace_name + "/"
    records = {name[len(prefix):]: record for name,record in expected.get("project_derived",{}).items()
               if name.startswith(prefix) and name[len(prefix):] not in excluded}
    actual = {path.name: path for path in out.iterdir() if path.is_file()
              and path.name not in excluded}
    if records.keys() != actual.keys():
        raise ValueError("Regenerated files differ from the manifest file list")
    for name,path in actual.items():
        if sha(path) != records[name]["sha256"]:
            raise ValueError("Regenerated file differs from the manifest: " + name)

def validate_expected_commitments(commitments, manifest, trace_name):
    expected = json.loads(manifest.read_text())
    if commitments != expected.get("traces", {}).get(trace_name, {}).get("commitments"):
        raise ValueError("The regenerated commitments differ from the tracked manifest")

def input_path(record):
    path = Path(record["path"])
    return path if path.is_absolute() else ROOT / path


def validate_trace_only(out, trace_name):
    if trace_name not in TRACE_ONLY_GROUPS:
        raise ValueError("Trace-only production binding requires the approved eql group or decodeItemRegions group")
    coqdir, instruction_count, access_count = TRACE_ONLY_GROUPS[trace_name]
    report = json.loads((out / "trace-manifest.json").read_text())
    if (report.get("schema") != "stock-zisk.trace-only.v1" or report.get("arch") != "riscv64"
            or report.get("coqdir") != coqdir
            or report.get("instruction_count") != instruction_count
            or report.get("generated_count") != instruction_count):
        raise ValueError(f"The {trace_name} trace manifest has an invalid identity or coverage")
    inputs = report["inputs"]
    required = {"manifest", "elf", "dump", "driver", "frontend", "footprint",
                "footprint_wrapper", "platform_snapshot", "config", "decoder",
                "per_load_regions", "region_renderer"}
    if not required <= inputs.keys():
        raise ValueError(f"The {trace_name} trace manifest omits a required input")
    if "load_exemptions" in inputs:
        raise ValueError(f"The {trace_name} production group must constrain every memory access")
    for record in [*inputs.values(), report["selected_dump"]]:
        if sha(input_path(record)) != record["sha256"]:
            raise ValueError(f"An {trace_name} trace input changed: " + record["path"])
    if "region_source_map" in inputs:
        descriptor = input_path(inputs["manifest"])
        recipe = json.loads(descriptor.read_text())
        if recipe.get("schema") != "stock-zisk.eql-trace-input.v1":
            raise ValueError("The production eql descriptor is invalid")
        selected_elf = resolve_trace_elf(SimpleNamespace(manifest=descriptor, trace_only=True,
            region_source_map=input_path(inputs["region_source_map"]),
            region_source_map_sha256=inputs["region_source_map"]["sha256"]), recipe)
        if selected_elf != input_path(inputs["elf"]).resolve():
            raise ValueError(f"The {trace_name} manifest differs from its mapped ELF")
    config = tomllib.loads(input_path(inputs["config"]).read_text())
    reset = config["registers"]["reset"]
    if reset.get("medeleg.bits") != "0x0000000000000000" or reset.get("mideleg.bits") != "0x0000000000000000":
        raise ValueError(f"The {trace_name} delegation reset configuration differs")
    with input_path(inputs["elf"]).open("rb") as stream:
        rows = selected_rows(SimpleNamespace(closure=False, dump=input_path(inputs["dump"])), Image(ELFFile(stream)))
    rows, accesses, sources = annotate_regions(rows, input_path(inputs["per_load_regions"]),
                                               inputs["per_load_regions"].get("payload_sha256", inputs["per_load_regions"]["sha256"]),
                                               None, None,
                                               read_source_map(input_path(inputs["region_source_map"]), inputs["region_source_map"]["sha256"])
                                               if "region_source_map" in inputs else None)
    source_set = {(str(input_path(row).resolve()), row["sha256"]) for row in inputs.values()}
    if any((row["path"], row["sha256"]) not in source_set for row in sources):
        raise ValueError(f"The {trace_name} manifest omits a region source binding")
    if (len(rows) != instruction_count or len({row["pc"] for row in rows}) != instruction_count
            or len(accesses) != access_count
            or not all(row["constraint_emitted"] for row in accesses)):
        raise ValueError(f"The {trace_name} instruction or constrained-access coverage differs")
    if trace_name == "decodeItemRegions" and (
            sum(row.get("operation") == "load" for row in accesses) != 15
            or sum(row.get("operation") == "store" for row in accesses) != 35):
        raise ValueError("The decodeItemRegions load/store coverage differs")
    if input_path(report["selected_dump"]).read_text() != selected_dump(rows):
        raise ValueError(f"The {trace_name} selected dump differs from its checked region policy")
    pcs = [row["pc"] for row in rows]
    validate_instruction_modules(out, pcs)
    expected = {f"a{pc:x}.{suffix}" for pc in pcs for suffix in ["v", "isla"]} | {"instrs.v", "dune"}
    actual = {path.name for path in out.iterdir() if path.is_file()
              and path.name not in {"trace-manifest.json", "manifest-fragment.json", "generation-measurement.json"}}
    if set(report["files"]) != expected or actual != expected:
        raise ValueError(f"The {trace_name} emitted file set differs")
    for name, digest in report["files"].items():
        if sha(out / name) != digest:
            raise ValueError(f"An {trace_name} output hash differs: " + name)
    if "region_source_map" in inputs:
        frontend_dune = report.get("frontend_dune")
        if frontend_dune is None or sha(input_path(frontend_dune)) != frontend_dune["sha256"]:
            raise ValueError(f"The {trace_name} frontend dune provenance differs")
        if normalize_dune_package(input_path(frontend_dune).read_text()) != (out / "dune").read_text():
            raise ValueError(f"The {trace_name} dune differs from package normalization")
    return report


def bind_trace_only(out, trace_name, check_manifest):
    report = validate_trace_only(out, trace_name)
    _, instruction_count, access_count = TRACE_ONLY_GROUPS[trace_name]
    if "region_source_map" not in report["inputs"]:
        raise ValueError(f"Production {trace_name} binding requires a durable region source map")
    if check_manifest:
        recipe = json.loads(check_manifest.read_text())
        group = recipe.get("traces", {}).get(trace_name, {})
        if (group.get("kind") != "trace_only" or group.get("native_proof_coverage") is not False
                or group.get("region_assume_obligations") != access_count
                or group.get("input_hashes") != {name: row["sha256"] for name, row in report["inputs"].items()}):
            raise ValueError(f"The {trace_name} manifest group differs from its production pins")
        validate_expected_files(out, check_manifest, trace_name)
        print(f"The {trace_name} trace files match their production pins; proof obligations remain open")
        return
    inputs = dict(report["inputs"], binder=rec(Path(__file__).resolve()))
    derived = {str(path.relative_to(ROOT)): dict(rec(path), schema_version=1)
               for path in sorted(out.iterdir()) if path.is_file()
               and path.name not in {"trace-manifest.json", "manifest-fragment.json", "generation-measurement.json"}}
    data = {"schema_version": 1, "inputs": inputs, "derived": derived,
            "traces": {"kind": "trace_only", "elf_sha256": report["inputs"]["elf"]["sha256"],
                       "instruction_count": instruction_count, "generated_count": instruction_count,
                       "instruction_modules_validated": True, "native_proof_coverage": False,
                       "region_assume_obligations": access_count,
                       "input_hashes": {name: row["sha256"] for name, row in report["inputs"].items()},
                       "manifest_binding_pending": True}}
    (out / "manifest-fragment.json").write_text(json.dumps(data, indent=2) + "\n")
    print(f"{trace_name} trace fragment: {instruction_count} instruction pairs; all {access_count} region obligations remain open")


def main():
    parser=argparse.ArgumentParser();parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--check-manifest",type=Path)
    parser.add_argument("--trace-name",default="closure")
    args=parser.parse_args();out=args.out.resolve()
    if (out / "trace-manifest.json").exists():
        bind_trace_only(out, args.trace_name, args.check_manifest)
        return
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
      "callee_identity":rec(ROOT / "ZesuStock/CalleeIdentity.v"),
      "callee_theory":rec(ROOT / "ZesuStock/dune"),
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
