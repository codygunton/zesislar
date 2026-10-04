#!/usr/bin/env python3
"""Generate selected-ELF traces through the unchanged Islaris frontend."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
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

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--manifest",type=Path,default=Path("build/stock-zisk/build-recipe.json"))
    ap.add_argument("--dump",type=Path,default=Path("build/stock-zisk/decodeItem.raw.dump"))
    ap.add_argument("--out",type=Path,default=Path("generated/isla-traces/stock-zisk/decodeItem"))
    ap.add_argument("--coqdir",default="ZesuSsz.Stock.DecodeItem")
    ap.add_argument("--jobs",type=int,default=6)
    ap.add_argument("--closure",action="store_true")
    args=ap.parse_args()
    if not 1 <= args.jobs <= 6: raise ValueError("Use one to six workers for this child")
    args.out = args.out.resolve()
    args.dump = args.dump.resolve()
    args.manifest = args.manifest.resolve()
    recipe=json.loads(args.manifest.read_text()); elf=args.manifest.parent / "zesu-zisk.elf"
    if sha(elf) != recipe["elf_sha256"]: raise ValueError("The selected ELF hash changed")
    with elf.open("rb") as stream:
        image=Image(ELFFile(stream)); rows=selected_rows(args,image)
        for row in rows:
            actual=decode(row["pc"],image.read(row["pc"],4))
            if actual["word"] != row["word"]: raise ValueError("The inventory instruction bytes changed")
            if actual["kind"] == "unsupported":
                raise ValueError(f"Unsupported {actual['extension']} at {actual['pc']:#x}: {actual['word']:#010x}")
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
    text=text.replace("(theories isla isla.riscv64)","(theories isla isla.riscv64 lithium iris stdpp RecordUpdate Ltac2)")
    dune.write_text(text)
    files={str(p.relative_to(ROOT)):sha(p) for p in sorted(args.out.iterdir()) if p.is_file()}
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
if __name__ == "__main__": main()
