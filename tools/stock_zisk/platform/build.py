#!/usr/bin/env python3
"""Compile a platform layer and link it into a hash-pinned instruction model."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import resource

BASE_SHA256 = "1883a3851579230cae1ba0e3975e7ccb3b6ec6a3c0cb8e73d317728777fb8d4a"  # Filled from the selected snapshot below.
HOOKS = ("zchecked_mem_read", "zchecked_mem_write", "zwithin_phys_mem",
         "zwithin_mmio_readable", "zwithin_mmio_writable")
ADDED = ("zzzisk_width", "zzzisk_contains", "zzzisk_smoke_fetch")

def digest(data):
    return hashlib.sha256(data).hexdigest()

def functions(text):
    return {m.group(1): m.group(0) for m in re.finditer(
        r"^fn (\w+)\([^\n]*\) \{\n.*?^\}", text, re.M | re.S)}

def link(base, adapter):
    if digest(base.encode()) != BASE_SHA256:
        raise ValueError("The base snapshot hash does not match its pin")
    original = base
    before, compiled = functions(base), functions(adapter)
    location_index = len(re.findall(r'"[^"]*"', base.split("\nfiles ")[-1]))
    def locations(body):
        return re.sub(r"`0 (?=\d+:)", "`" + str(location_index) + " ", body)
    report = []
    for name in HOOKS:
        if name not in before or name not in compiled:
            raise ValueError(f"Missing platform hook {name}")
        body = locations(compiled[name])
        base = base.replace(before[name], body, 1)
        report.append({"name": name, "original_sha256": digest(before[name].encode()),
                       "generated_sha256": digest(body.encode())})
    after = functions(base)
    for name in before:
        if name not in HOOKS and after[name] != before[name]:
            raise ValueError(f"Non-platform body changed: {name}")
    restored = base
    for name in HOOKS:
        restored = restored.replace(after[name], before[name], 1)
    if restored != original:
        raise ValueError("Non-platform declarations changed")
    # Add only the compiled platform helpers and registers. Shared model types
    # and primitive declarations remain the pinned declarations.
    extra = []
    for name in ADDED:
        val = re.search(r"^val " + name + r" : [^\n]+", adapter, re.M)
        extra.extend([val.group(0), locations(compiled[name])])
    for name in ("zzzisk_input_end", "zzzisk_free_input"):
        extra.append(re.search(r"^register " + name + r" : [^\n]+", adapter, re.M).group(0))
    files_pos = base.index("\nfiles ")
    base = base[:files_pos] + "\n\n" + "\n\n".join(extra) + base[files_pos:]
    # Location annotations do not affect execution. Keep the compiled adapter
    # file index valid when it follows the pinned source file table.
    files_pos = base.index("\nfiles ")
    base = base[:files_pos] + base[files_pos:].rstrip() + ' "tools/stock_zisk/platform/adapter.sail"\n'
    return base, {"replacements": report, "unchanged_function_count": len(before) - len(HOOKS),
                  "non_platform_functions_byte_identical": True,
                  "non_platform_declarations_byte_identical": True}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", type=Path, default=Path("/home/cody/isla-snapshots/riscv64.ir"))
    ap.add_argument("--out", type=Path, default=Path("build/stock-zisk/platform"))
    ap.add_argument("--jobs", type=int, default=6)
    args = ap.parse_args()
    src = Path(__file__).resolve().parent
    root = src.parents[2]
    out = args.out.resolve(); out.mkdir(parents=True, exist_ok=True)
    compiler_build = root / "_build/platform-compiler"; compiler_build.mkdir(parents=True,exist_ok=True)
    for f in (src / "compiler").iterdir():
        if f.is_file(): shutil.copy2(f, compiler_build / f.name)
    started = time.monotonic()
    subprocess.run(["opam", "exec", "--switch=/home/cody/islaris", "--", "dune", "build",
        "--root", str(compiler_build), "--build-dir", "_build-out", "--cache=enabled",
        f"-j{args.jobs}", "sail_plugin_isla.cmxs"], check=True)
    plugin = compiler_build / "_build-out/default/sail_plugin_isla.cmxs"
    shutil.copy2(plugin, out / "sail_plugin_isla.cmxs")
    plugin = out / "sail_plugin_isla.cmxs"
    sail = Path("/home/cody/islaris/_opam/bin/sail")
    env = dict(os.environ); env["PATH"] = "/home/cody/isla:" + str(sail.parent) + ":" + env["PATH"]
    command = [str(sail), "--plugin", str(plugin), "-isla"]
    for name in HOOKS + ("zzzisk_smoke_fetch",): command += ["-isla_preserve", ("zisk_smoke_fetch" if name == "zzzisk_smoke_fetch" else name[1:])]
    command += [str(src / "adapter.sail"), "-o", str(out / "adapter")]
    subprocess.run(command, env=env, check=True, cwd=root)
    base = args.base.read_text(); adapter = (out / "adapter.ir").read_text()
    linked, report = link(base, adapter)
    snapshot = out / "riscv64-zisk.ir"; snapshot.write_text(linked)
    report.update({"schema_version": 1, "base_sha256": digest(base.encode()),
      "snapshot_sha256": digest(linked.encode()), "adapter_source_sha256": digest((src / "adapter.sail").read_bytes()),
      "sail_sha256": digest(sail.read_bytes()), "plugin_sha256": digest(plugin.read_bytes()),
      "compiler_patch": "Remove obsolete Initial_check.opt_undefined_gen assignment; Sail 0.17 generates undefined values by default.",
      "command": command, "seconds": round(time.monotonic() - started, 3),
      "peak_rss_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
      "workers": args.jobs})
    (out / "build-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))

if __name__ == "__main__": main()
