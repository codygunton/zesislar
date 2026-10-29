#!/usr/bin/env python3
"""Generate selected-ELF traces through the unchanged Islaris frontend."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import time
import tempfile

ROOT = Path(__file__).resolve().parents[3]
TRACE_FRONTEND = Path("/home/cody/islaris/_opam/bin/islaris")
TRACE_FOOTPRINT = Path("/home/cody/isla/target/release/isla-footprint")
sys.path.insert(0, str(Path(__file__).resolve().parent))
from indexes import approved_regions, validate_indexes
from exports import native_prefix, append_exports, selected_commitments
sys.path.insert(0,str(ROOT / "tools/stock_zisk"))
from closure import Image
from elftools.elf.elffile import ELFFile
from riscv import decode, decode_range

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def validate_instruction_modules(out, pcs):
    expected={f"a{pc:x}.v" for pc in pcs}
    actual={p.name for p in out.iterdir() if p.is_file() and re.fullmatch(r"a[0-9a-fA-F]+\.v",p.name)}
    missing=sorted(expected-actual); extra=sorted(actual-expected)
    if missing or extra:
        raise ValueError(f"Instruction modules differ: missing={missing[:10]}, extra={extra[:10]}")
    return len(actual)
def selected_rows(args, image):
    if args.closure:
        inventory=json.loads((args.manifest.parent / "inventory.json").read_text())
        rows={}
        for function in inventory["functions"]:
            for row in function["rows"]: rows[row["pc"]]=row
        for region in inventory["inline_decodeSingleTx"]["block_ranges"]:
            for row in decode_range(region["start"], image.read(region["start"], region["end"]-region["start"])):
                rows[row["pc"]]=row
        return [rows[pc] for pc in sorted(rows)]
    rows=[]
    for line in args.dump.read_text().splitlines():
        m=re.match(r"\s*([0-9a-fA-F]+):\s*([0-9a-fA-F]{8})\s+",line)
        if m:
            pc,word=int(m[1],16),int(m[2],16)
            row=decode(pc,image.read(pc,4))
            if row["word"] != word: raise ValueError(f"Dump byte mismatch at {pc:#x}")
            rows.append(row)
    if not rows: raise ValueError("The input dump contains no instructions")
    return rows

def trace_only_inputs(args, elf):
    paths = {
        "manifest": args.manifest, "elf": elf, "dump": args.dump,
        "driver": Path(__file__).resolve(), "frontend": TRACE_FRONTEND,
        "footprint": TRACE_FOOTPRINT,
        "footprint_wrapper": ROOT / "tools/stock_zisk/platform/bin/isla-footprint",
        "platform_snapshot": ROOT / "build/stock-zisk/platform/riscv64-zisk.ir",
        "config": ROOT / "ZesuSsz/riscv64_zesu.toml",
        "decoder": ROOT / "tools/stock_zisk/riscv.py",
    }
    return {name: {"path": str(path.resolve()), "sha256": sha(path)}
            for name, path in paths.items()}


def generate_trace_only(args, rows, inputs):
    """Generate an isolated dataset without region commitments or exports."""
    pcs = [row["pc"] for row in rows]
    if len(pcs) != len(set(pcs)):
        raise ValueError("The trace-only dump repeats an instruction address")
    if any(row["kind"] == "runtime" for row in rows):
        raise ValueError("Trace-only generation cannot omit runtime instructions")
    dump = args.out.parent / (args.out.name + ".selected.dump")
    log = args.out.parent / (args.out.name + ".generation.log")
    if any(path.exists() for path in [args.out, dump, log]):
        raise ValueError("Trace-only generation requires a new output directory and sidecar files")
    args.out.parent.mkdir(parents=True, exist_ok=True)
    dump.write_text("\n".join(f"{row['pc']:x}: {row['word']:08x} {row['mnemonic']}"
                              for row in rows) + "\n")
    selected_dump_hash = sha(dump)
    env = dict(os.environ, OPAM_SWITCH_PREFIX="/home/cody/islaris/_opam")
    env["PATH"] = str(ROOT / "tools/stock_zisk/platform/bin") + ":" + str(ROOT / "bin") + ":" + str(TRACE_FRONTEND.parent) + ":" + env["PATH"]
    command = [str(TRACE_FRONTEND), str(dump), "--arch=riscv64",
               "--coqdir=" + args.coqdir, f"-j{args.jobs}", "-o", str(args.out)]
    started = time.monotonic()
    with log.open("w") as output:
        result = subprocess.run(command, env=env, stdout=output,
                                stderr=subprocess.STDOUT, cwd=ROOT)
    if result.returncode:
        raise RuntimeError("Trace-only generation failed; inspect " + str(log))
    for record in inputs.values():
        if sha(Path(record["path"])) != record["sha256"]:
            raise ValueError("A trace-only input changed: " + record["path"])
    if sha(dump) != selected_dump_hash:
        raise ValueError("The selected trace-only dump changed")
    generated = validate_instruction_modules(args.out, pcs)
    expected = {f"a{pc:x}.isla" for pc in pcs}
    actual = {path.name for path in args.out.iterdir()
              if path.is_file() and re.fullmatch(r"a[0-9a-fA-F]+\.isla", path.name)}
    if expected != actual:
        raise ValueError(f"Instruction traces differ: missing={sorted(expected-actual)}, extra={sorted(actual-expected)}")
    report = {
        "schema": "stock-zisk.trace-only.v1", "arch": "riscv64",
        "coqdir": args.coqdir, "inputs": inputs,
        "selected_dump": {"path": str(dump), "sha256": selected_dump_hash},
        "instruction_count": len(rows), "generated_count": generated,
        "files": {path.name: sha(path) for path in sorted(args.out.iterdir()) if path.is_file()},
        "command": command, "workers": args.jobs,
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
    }
    (args.out / "trace-manifest.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Generated {generated}/{len(rows)} trace-only instructions")

def ensure_callee_theory(out):
    dune = out / "dune"
    if dune.exists():
        text = dune.read_text()
        text = text.replace("ZesuSsz.CalleeIdentity", "ZesuStock")
        if "ZesuStock" not in text:
            text = text.replace("RecordUpdate Ltac2)", "RecordUpdate Ltac2 ZesuStock)")
        dune.write_text(text)

def generate_indexes(args, rows, recipe, elf):
    supported = [row for row in rows if row["kind"] != "runtime"]
    ensure_callee_theory(args.out)
    validate_instruction_modules(args.out, [row["pc"] for row in supported])
    inventory_path = args.manifest.parent / "inventory.json"
    regions = approved_regions(json.loads(inventory_path.read_text()), {row["pc"] for row in supported})
    frozen = args.out / "generation-measurement.json"
    coverage = args.out / "coverage.json"
    if not frozen.exists():
        frozen.write_bytes(coverage.read_bytes())
    previous = json.loads(coverage.read_text())
    if previous["elf_sha256"] != sha(elf):
        raise ValueError("The frozen selected ELF changed")
    dump_path = args.out.parent / (args.out.name + ".selected.dump")
    expected_dump = "\n".join(f"{row['pc']:x}: {row['word']:08x} {row['mnemonic']}" for row in supported) + "\n"
    if sha(dump_path) != previous["dump_sha256"] or dump_path.read_text() != expected_dump:
        raise ValueError("The frozen instruction dump differs from the selected ELF")
    for path, value in previous["files"].items():
        if not re.fullmatch(r"a[0-9a-f]+\.(v|isla)", Path(path).name):
            continue
        if sha(args.out / Path(path).name) != value:
            raise ValueError("The frozen trace changed: " + path)
    for key, path in [("platform_snapshot_sha256", ROOT / "build/stock-zisk/platform/riscv64-zisk.ir"),
                      ("config_sha256", ROOT / "ZesuSsz/riscv64_zesu.toml")]:
        if previous[key] != sha(path):
            raise ValueError("The frozen trace input changed: " + key)
    cache = {}
    by_pc = {row["pc"]: row for row in supported}
    for row in supported:
        opcode = row["word"].to_bytes(4, "little").hex()
        path = args.out / f"a{row['pc']:x}.isla"
        if opcode in cache and sha(Path(cache[opcode])) != sha(path):
            raise ValueError("Equal opcodes have different cached traces")
        cache[opcode] = str(path)
    with tempfile.TemporaryDirectory(prefix="zisk-index-") as directory:
        stage = Path(directory)
        cache_wrapper = ROOT / "tools/stock_zisk/platform/cache_footprint.py"
        if not os.access(cache_wrapper, os.X_OK):
            raise ValueError("The cached footprint wrapper is not executable")
        (stage / "isla-footprint").symlink_to(cache_wrapper)
        (stage / "cache.json").write_text(json.dumps(cache))
        env = dict(os.environ, OPAM_SWITCH_PREFIX="/home/cody/islaris/_opam", ZISK_TRACE_CACHE=str(stage / "cache.json"))
        env["PATH"] = str(stage) + ":" + str(Path(env["OPAM_SWITCH_PREFIX"]) / "bin") + ":" + env["PATH"]
        for name, pcs in regions.items():
            output = stage / name
            output.mkdir()
            dump = stage / (name + ".dump")
            dump.write_text("\n".join(f"{pc:x}: {by_pc[pc]['word']:08x} {by_pc[pc]['mnemonic']}" for pc in sorted(pcs)) + "\n")
            command = [str(Path(env["OPAM_SWITCH_PREFIX"]) / "bin/islaris"), str(dump),
                       "--arch=riscv64", "--coqdir=" + args.coqdir, f"-j{args.jobs}", "-o", str(output)]
            result = subprocess.run(command, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode:
                raise RuntimeError(result.stdout.decode()[-2000:])
            for pc in pcs:
                if (output / f"a{pc:x}.v").read_bytes() != (args.out / f"a{pc:x}.v").read_bytes():
                    raise ValueError(f"The frontend changed the cached instruction at {pc:#x}")
            (args.out / ("index_" + name + ".v")).write_bytes((output / "instrs.v").read_bytes())
    validate_indexes(args.out, regions, args.coqdir)
    with elf.open("rb") as stream:
        commitments = selected_commitments(json.loads(inventory_path.read_text()), Image(ELFFile(stream)), regions)
    for name, commitment in commitments.items():
        append_exports(args.out / ("index_" + name + ".v"), name, commitment)
    (args.out / "instrs.v").unlink(missing_ok=True)
    descriptor = {"schema_version": 1, "coqdir": args.coqdir,
                  "elf_sha256": previous["elf_sha256"],
                  "platform_snapshot_sha256": previous["platform_snapshot_sha256"],
                  "config_sha256": previous["config_sha256"],
                  "regions": {name: [hex(pc) for pc in sorted(pcs)] for name, pcs in regions.items()}}
    (args.out / "indexes.json").write_text(json.dumps(descriptor, indent=2) + "\n")
    files = {"generated/isla-traces/stock-zisk/closure/" + path.name: sha(path) for path in sorted(args.out.iterdir())
             if path.is_file() and path.name not in {"coverage.json", "manifest-fragment.json", "generation-measurement.json"}}
    report = {key: previous[key] for key in ["elf_sha256", "platform_snapshot_sha256", "config_sha256", "dump_sha256",
              "instruction_count", "generated_count", "unsupported_runtime_boundaries", "full_closure_coverage"]}
    report.update(schema_version=2, files=files, indexes=descriptor, commitments=commitments,
                  unmodeled_instructions=previous["unsupported_runtime_boundaries"])
    coverage.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Validated {len(supported)} instructions in {len(regions)} native indexes")

def canonical_decodeitem(args, rows, elf):
    coverage = args.out / "coverage.json"
    frozen = args.out / "generation-measurement.json"
    ensure_callee_theory(args.out)
    if not frozen.exists():
        frozen.write_bytes(coverage.read_bytes())
    previous = json.loads(coverage.read_text())
    supported = [row for row in rows if row["kind"] != "runtime"]
    validate_instruction_modules(args.out, [row["pc"] for row in supported])
    dump = args.out.parent / (args.out.name + ".selected.dump")
    expected_dump = "\n".join(f"{row['pc']:x}: {row['word']:08x} {row['mnemonic']}" for row in supported) + "\n"
    if dump.read_text() != expected_dump or sha(dump) != previous["dump_sha256"]:
        raise ValueError("The cached DecodeItem dump differs from the selected ELF")
    for key, path in [("elf_sha256", elf),
                      ("platform_snapshot_sha256", ROOT / "build/stock-zisk/platform/riscv64-zisk.ir"),
                      ("config_sha256", ROOT / "ZesuSsz/riscv64_zesu.toml")]:
        if previous[key] != sha(path):
            raise ValueError("The cached DecodeItem input changed: " + key)
    for path, value in previous["files"].items():
        if not re.fullmatch(r"a[0-9a-f]+\.(v|isla)", Path(path).name):
            continue
        if sha(args.out / Path(path).name) != value:
            raise ValueError("The cached DecodeItem file changed: " + path)
    cache = {}
    for row in supported:
        opcode = row["word"].to_bytes(4, "little").hex()
        path = args.out / f"a{row['pc']:x}.isla"
        if opcode in cache and sha(Path(cache[opcode])) != sha(path):
            raise ValueError("Equal opcodes have different cached traces")
        cache[opcode] = str(path)
    with tempfile.TemporaryDirectory(prefix="zisk-decode-index-") as directory:
        stage = Path(directory)
        cache_wrapper = ROOT / "tools/stock_zisk/platform/cache_footprint.py"
        if not os.access(cache_wrapper, os.X_OK):
            raise ValueError("The cached footprint wrapper is not executable")
        (stage / "isla-footprint").symlink_to(cache_wrapper)
        (stage / "cache.json").write_text(json.dumps(cache))
        output = stage / "output"
        output.mkdir()
        env = dict(os.environ, OPAM_SWITCH_PREFIX="/home/cody/islaris/_opam", ZISK_TRACE_CACHE=str(stage / "cache.json"))
        env["PATH"] = str(stage) + ":" + str(Path(env["OPAM_SWITCH_PREFIX"]) / "bin") + ":" + env["PATH"]
        command = [str(Path(env["OPAM_SWITCH_PREFIX"]) / "bin/islaris"), str(dump),
                   "--arch=riscv64", "--coqdir=" + args.coqdir, f"-j{args.jobs}", "-o", str(output)]
        result = subprocess.run(command, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(result.stdout.decode()[-2000:])
        for row in supported:
            name = f"a{row['pc']:x}.v"
            if (output / name).read_bytes() != (args.out / name).read_bytes():
                raise ValueError("The frontend changed the cached DecodeItem file: " + name)
        (args.out / "instrs.v").write_bytes((output / "instrs.v").read_bytes())
    with elf.open("rb") as stream:
        commitments = selected_commitments(json.loads((args.manifest.parent / "inventory.json").read_text()),
            Image(ELFFile(stream)), {"decodeItem": {row["pc"] for row in supported}})
    append_exports(args.out / "instrs.v", "decodeItem", commitments["decodeItem"])
    files = {"generated/isla-traces/stock-zisk/decodeItem/" + path.name: sha(path)
             for path in sorted(args.out.iterdir()) if path.is_file()
             and path.name not in {"coverage.json", "manifest-fragment.json", "generation-measurement.json"}}
    report = {key: previous[key] for key in ["elf_sha256", "platform_snapshot_sha256", "config_sha256", "dump_sha256",
              "instruction_count", "generated_count", "unsupported_runtime_boundaries", "full_closure_coverage"]}
    report.update(schema_version=2, files=files, commitments=commitments,
                  unmodeled_instructions=previous["unsupported_runtime_boundaries"])
    coverage.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Validated {len(supported)} DecodeItem instructions with the native index")

def native_records(recipe, group):
    prefix = "generated/isla-traces/stock-zisk/" + group + "/"
    records = {name[len(prefix):]: record["sha256"]
               for name, record in recipe["project_derived"].items()
               if name.startswith(prefix) and name[len(prefix):] not in
                  {"manifest-fragment.json", "generation-measurement.json"}}
    if not records or "coverage.json" not in records:
        raise ValueError("The manifest has no native trace dataset: " + group)
    if any(Path(name).name != name for name in records):
        raise ValueError("A native trace record contains an invalid filename")
    return records


def native_dataset_matches(directory, records, dump):
    if any(not (directory / name).is_file() or sha(directory / name) != value
           for name, value in records.items()):
        return False
    report = json.loads((directory / "coverage.json").read_text())
    return dump.is_file() and sha(dump) == report["dump_sha256"]


def ensure_native_indexes(args):
    recipe = json.loads(args.manifest.read_text())
    args.cache_dir.mkdir(parents=True, exist_ok=True)
    binder = ROOT / "tools/stock_zisk/platform/bind_traces.py"
    for group, out, coqdir in [
            ("decodeItem", args.decode_out, "ZesuSsz.Stock.DecodeItem"),
            ("closure", args.closure_out, "ZesuSsz.Stock.Closure")]:
        records = native_records(recipe, group)
        key = hashlib.sha256(json.dumps(records, sort_keys=True).encode()).hexdigest()
        cache = args.cache_dir / group / key
        dump = out.parent / (out.name + ".selected.dump")
        check = [sys.executable, str(binder), "--out", str(out),
                 "--check-manifest", str(args.manifest), "--trace-name", group]
        if not native_dataset_matches(out, records, dump):
            if native_dataset_matches(cache, records, cache / "selected.dump"):
                out.mkdir(parents=True, exist_ok=True)
                for name in records:
                    shutil.copy2(cache / name, out / name)
                shutil.copy2(cache / "selected.dump", dump)
                print("Restored validated native indexes:", group, flush=True)
            else:
                command = [sys.executable, str(Path(__file__).resolve()),
                           "--manifest", str(args.manifest), "--dump", str(args.dump),
                           "--coqdir", coqdir, "--jobs", str(args.jobs)]
                if group == "closure":
                    command.append("--closure")
                required = {name: value for name, value in records.items()
                            if name in {"coverage.json", "dune"}
                            or re.fullmatch(r"a[0-9a-f]+\.(v|isla)", name)}
                if native_dataset_matches(out, required, dump):
                    subprocess.run(command + ["--out", str(out)], check=True)
                else:
                    out.parent.mkdir(parents=True, exist_ok=True)
                    with tempfile.TemporaryDirectory(prefix="native-traces-", dir=out.parent) as directory:
                        fresh = Path(directory) / group
                        subprocess.run(command + ["--out", str(fresh)], check=True)
                        subprocess.run(check[:3] + [str(fresh)] + check[4:], check=True)
                        out.mkdir(parents=True, exist_ok=True)
                        for name in records:
                            shutil.copy2(fresh / name, out / name)
                        shutil.copy2(fresh.parent / (fresh.name + ".selected.dump"), dump)
        subprocess.run(check, check=True)
        # Each cache entry contains only files checked against the tracked manifest.
        # Measurements stay in their original output directory.
        if not native_dataset_matches(cache, records, cache / "selected.dump"):
            cache.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.TemporaryDirectory(prefix="native-cache-", dir=cache.parent) as directory:
                staged = Path(directory)
                for name in records:
                    shutil.copy2(out / name, staged / name)
                shutil.copy2(dump, staged / "selected.dump")
                if cache.exists():
                    # A corrupt cache does not invalidate the checked output dataset.
                    continue
                try:
                    staged.rename(cache)
                except FileExistsError:
                    pass

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--manifest",type=Path,default=Path("build/stock-zisk/build-recipe.json"))
    ap.add_argument("--dump",type=Path,default=Path("build/stock-zisk/decodeItem.raw.dump"))
    ap.add_argument("--out",type=Path,default=Path("generated/isla-traces/stock-zisk/decodeItem"))
    ap.add_argument("--coqdir",default="ZesuSsz.Stock.DecodeItem")
    ap.add_argument("--jobs",type=int,default=6)
    ap.add_argument("--closure",action="store_true")
    ap.add_argument("--indexes",action="store_true")
    ap.add_argument("--trace-only", action="store_true",
                    help="Generate a new isolated trace dataset without region commitments or exports")
    ap.add_argument("--ensure-native-indexes", action="store_true")
    ap.add_argument("--cache-dir", type=Path, default=ROOT / "_build/stock-zisk/native-trace-cache")
    ap.add_argument("--decode-out", type=Path, default=ROOT / "generated/isla-traces/stock-zisk/decodeItem")
    ap.add_argument("--closure-out", type=Path, default=ROOT / "generated/isla-traces/stock-zisk/closure")
    args=ap.parse_args()
    if args.trace_only and (args.closure or args.indexes or args.ensure_native_indexes):
        ap.error("--trace-only cannot combine with closure or native-index modes")
    if not 1 <= args.jobs <= 6: raise ValueError("Use one to six workers for this child")
    args.manifest = args.manifest.resolve()
    if args.ensure_native_indexes:
        args.cache_dir = args.cache_dir.resolve()
        args.decode_out = args.decode_out.resolve()
        args.closure_out = args.closure_out.resolve()
        ensure_native_indexes(args)
        return
    args.out = args.out.resolve()
    args.dump = args.dump.resolve()
    args.manifest = args.manifest.resolve()
    recipe=json.loads(args.manifest.read_text()); elf=args.manifest.parent / "zesu-zisk.elf"
    if sha(elf) != recipe["elf_sha256"]: raise ValueError("The selected ELF hash changed")
    trace_inputs = trace_only_inputs(args, elf) if args.trace_only else None
    with elf.open("rb") as stream:
        image=Image(ELFFile(stream)); rows=selected_rows(args,image)
        for row in rows:
            actual=decode(row["pc"],image.read(row["pc"],4))
            if actual["word"] != row["word"]: raise ValueError("The inventory instruction bytes changed")
            if actual["kind"] == "unsupported":
                raise ValueError(f"Unsupported {actual['extension']} at {actual['pc']:#x}: {actual['word']:#010x}")
    if args.trace_only:
        generate_trace_only(args, rows, trace_inputs)
        return
    if args.indexes and not args.closure:
        raise ValueError("Bounded indexes require closure selection")
    args.indexes = args.closure
    if (args.out / "coverage.json").exists():
        if args.indexes:
            generate_indexes(args, rows, recipe, elf)
        else:
            canonical_decodeitem(args, rows, elf)
        return
    unsupported=[{"pc":hex(r["pc"]),"opcode":f"{r['word']:08x}",
       "name":"memcpy CSR0x813 runtime service", "reason":"The pinned instruction model does not implement this ZisK service"}
       for r in rows if r["kind"] == "runtime"]
    supported=[r for r in rows if r["kind"] != "runtime"]
    args.out.parent.mkdir(parents=True,exist_ok=True)
    # This dump supplies only selected instruction bytes. The configuration
    # supplies platform facts. No instruction memory footprint is assumed.
    dump=args.out.parent / (args.out.name + ".selected.dump")
    dump.write_text("\n".join(f"{r['pc']:x}: {r['word']:08x} {r['mnemonic']}" for r in supported)+"\n")
    env=dict(os.environ, OPAM_SWITCH_PREFIX="/home/cody/islaris/_opam")
    env["PATH"]=str(ROOT / "tools/stock_zisk/platform/bin")+":"+str(ROOT / "bin")+":"+str(Path(env["OPAM_SWITCH_PREFIX"]) / "bin")+":"+env["PATH"]
    command=[str(Path(env["OPAM_SWITCH_PREFIX"]) / "bin/islaris"),str(dump),
       "--arch=riscv64","--coqdir="+args.coqdir,f"-j{args.jobs}","-o",str(args.out)]
    started=time.monotonic()
    log = args.out.parent / (args.out.name + ".generation.log")
    with log.open("w") as output:
        result = subprocess.run(command,env=env,stdout=output,stderr=subprocess.STDOUT,cwd=ROOT)
    if result.returncode:
        print("\n".join(log.read_text().splitlines()[-20:]))
        raise RuntimeError("Trace generation failed; inspect " + str(log))
    generated_count=validate_instruction_modules(args.out,[r["pc"] for r in supported])
    # The standalone project has its own theory graph. Remove the frontend's
    # upstream package declaration and use the established theory dependencies.
    dune=args.out / "dune"
    text=dune.read_text();text=re.sub(r"^ \(package islaris\)\n","",text,flags=re.M)
    text=text.replace("(theories isla isla.riscv64)","(theories isla isla.riscv64 lithium iris stdpp RecordUpdate Ltac2 ZesuStock)")
    dune.write_text(text)
    prefix = "generated/isla-traces/stock-zisk/" + ("closure" if args.closure else "decodeItem") + "/"
    files={prefix + p.name:sha(p)
           for p in sorted(args.out.iterdir()) if p.is_file()}
    report={"schema_version":1,"elf_sha256":sha(elf),"manifest_sha256":sha(args.manifest),
       "platform_snapshot_sha256":sha(ROOT / "build/stock-zisk/platform/riscv64-zisk.ir"),
       "config_sha256":sha(ROOT / "ZesuSsz/riscv64_zesu.toml"),"dump_sha256":sha(dump),
       "instruction_count":len(rows),"generated_count":generated_count,"unsupported_runtime_boundaries":unsupported,
       "full_closure_coverage":not unsupported,"manifest_binding_pending":True,"files":files,
       "command":command,"seconds":round(time.monotonic()-started,3),
       "peak_rss_kib":resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,"workers":args.jobs}
    (args.out / "coverage.json").write_text(json.dumps(report,indent=2)+"\n")
    print(f"Generated {generated_count}/{len(rows)} traces with {args.jobs} workers in {report['seconds']} seconds")
    for boundary in unsupported: print("REFUSED runtime boundary:",boundary)
    if args.indexes:
        generate_indexes(args, rows, recipe, elf)
    else:
        canonical_decodeitem(args, rows, elf)
if __name__ == "__main__": main()
