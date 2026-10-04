#!/usr/bin/env python3
"""Emit platform bindings for parent manifest integration."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "build/stock-zisk/platform"
def record(path):
    return {"path":str(path),"sha256":hashlib.sha256(path.read_bytes()).hexdigest()}
def main():
    source = ROOT / "tools/stock_zisk/platform"
    inputs = {str(p.relative_to(ROOT)):record(p) for p in sorted(source.rglob("*"))
              if p.is_file() and "__pycache__" not in p.parts and p.name != "EntryProbe.v"}
    for name,path in {"sail":Path("/home/cody/islaris/_opam/bin/sail"),
     "base_snapshot":Path("/home/cody/isla-snapshots/riscv64.ir"),
     "isla_footprint":Path("/home/cody/isla/target/release/isla-footprint"),
     "islaris":Path("/home/cody/islaris/_opam/bin/islaris"),
     "sail_plugin":OUT / "sail_plugin_isla.cmxs",
     "config":ROOT / "ZesuSsz/riscv64_zesu.toml"}.items(): inputs[name]=record(path)
    derived = {str(p.relative_to(ROOT)):dict(record(p),schema_version=1)
       for p in sorted(OUT.rglob("*")) if p.is_file() and p.name != "manifest-fragment.json"}
    data = {"schema_version":1,"inputs":inputs,"derived":derived,
      "platform":{"kind":"dedicated-zisk-platform-layer","snapshot":"build/stock-zisk/platform/riscv64-zisk.ir",
       "config":"ZesuSsz/riscv64_zesu.toml","replaced_hooks":["checked_mem_read","checked_mem_write",
        "within_phys_mem","within_mmio_readable","within_mmio_writable"],
       "registers":{"zisk_input_end":"input section end; dynamic decoder resource",
                    "zisk_free_input":"current target free_input; dynamic decoder resource"},
       "input_relation":"The selected emulator merges its zero header and multiple-of-eight input into one section. Its end equals 0x40000008 + input_len.",
       "source":"core/src/mem.rs:240-293,366-388; emulator/src/emu_context.rs:50-71",
       "instruction_semantics":"unchanged; all non-platform declarations remain byte-identical",
       "runtime_boundary":"memcpy CSR0x813 remains an explicit runtime service; this platform does not implement it"}}
    (OUT / "manifest-fragment.json").write_text(json.dumps(data,indent=2)+"\n")
    print(f"Platform fragment: {len(inputs)} inputs and {len(derived)} derived files")
if __name__ == "__main__": main()
