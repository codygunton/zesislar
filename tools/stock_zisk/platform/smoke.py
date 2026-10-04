#!/usr/bin/env python3
"""Retained instruction-trace checks for the selected ZisK platform."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import time

INPUT = 0x40000000
RAM = 0xa0000000
# Each row names its table region or a required boundary case.
CASES = [
 ("input", "ld", INPUT + 8, "read", 16),
 ("executable_text", "fetch", 0x80000000, "fetch", 16),
 ("read_only_data", "ld", 0x8010fd80, "read", 16),
 ("gap", "ld", 0x88000000, "load_fault", 16),
 ("ram", "ld", RAM + 64, "read", 16),
 ("stack", "ld", 0xa03ffff8, "read", 16),
 ("heap", "ld", 0xa0d34520, "read", 16),
 ("system", "ld", 0xa0400000, "read", 16),
 ("output", "sd", 0xa0410000, "write", 16),
 ("input_write", "sd", INPUT + 8, "store_fault", 16),
 ("text_data_read", "ld", 0x80000000, "load_fault", 16),
 ("oversized_input_end", "ld", 0x80000000, "load_fault", 0x50000000),
 ("misaligned_ram", "ld", RAM + 1, "read", 16),
 ("misaligned_ram_write", "sd", RAM + 1, "write", 16),
 ("special_word", "ld", INPUT, "special", 16),
 ("zero_fallback", "ld", INPUT + 128, "zero", 16),
 ("section_crossing", "ld", INPUT + 20, "zero", 16),
 ("empty_input", "ld", INPUT + 8, "zero", 0),
 ("header_byte", "lb", INPUT, "read", 16),
 ("header_half", "lh", INPUT + 2, "read", 16),
 ("header_word", "lw", INPUT + 4, "read", 16),
 ("header_data_join", "lh", INPUT + 7, "read", 16),
 ("empty_header_crossing", "lh", INPUT + 7, "load_fault", 0),
 ("rodata_write", "sd", 0x8010fd80, "store_fault", 16),
 ("ram_end_crossing", "ld", 0xbffffffc, "load_fault", 16),
 ("input_end_crossing", "ld", 0x7ffffffc, "load_fault", 16),
 ("text_end_crossing", "fetch", 0x8010fd76, "fetch_fault", 16),
 ("rodata_end_crossing", "ld", 0x80118674, "load_fault", 16),
 ("address_wrap", "ld", 0xfffffffffffffffc, "load_fault", 16),
]
OPCODES = {"lb":0x00058503,"lh":0x00059503,"lw":0x0005a503,
           "ld":0x0005b503,"sd":0x00a5b023}

def check_trace(trace, expected, address):
    reads = re.findall(r"\(read-mem [^\n]+", trace)
    writes = re.findall(r"\(write-mem [^\n]+", trace)
    trap = "(write-reg |mcause|" in trace
    if expected in ("read", "fetch"):
        assert not trap and len(reads) == 1, (expected, reads, trap)
        assert f"#x{address:016x}" in reads[0], reads
        if expected == "fetch":
            assert "|Read_ifetch|" in reads[0], reads
            assert "(write-reg |x10| nil #x0000000000000001)" in trace
    elif expected == "write":
        assert not trap and len(writes) == 1, (writes, trap)
        assert f"#x{address:016x}" in writes[0], writes
    elif expected in ("zero", "special"):
        assert not trap and not reads and not writes, (reads,writes,trap)
        value = 0 if expected == "zero" else 0x1122334455667788
        assert f"(write-reg |x10| nil #x{value:016x})" in trace, expected
    elif expected == "fetch_fault":
        # The direct fetch test calls the platform hook. Its exception result
        # does not invoke the instruction trap handler.
        assert not reads and not writes, (reads,writes)
        assert "(write-reg |x10| nil #x0000000000000000)" in trace
    else:
        assert trap and not reads and not writes, (reads,writes,trap)
        code = 5 if expected == "load_fault" else 7
        assert f"#x{code:016x}" in trace, expected
    assert "|rv_htif_tohost|" not in trace.replace("(assume-reg |rv_htif_tohost| nil #x0000000000000000)", "")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--snapshot", type=Path, default=Path("build/stock-zisk/platform/riscv64-zisk.ir"))
    ap.add_argument("--config", type=Path, default=Path("ZesuSsz/riscv64_zesu.toml"))
    ap.add_argument("--out", type=Path, default=Path("build/stock-zisk/platform/smoke"))
    args = ap.parse_args(); args.out.mkdir(parents=True,exist_ok=True)
    root = Path(__file__).resolve().parents[3]
    env = dict(os.environ, LD_LIBRARY_PATH="/home/cody/isla")
    env["PATH"] = str(root / "bin") + ":" + env["PATH"]
    binary = "/home/cody/isla/target/release/isla-footprint"
    started=time.monotonic(); report=[]
    for name, op, addr, expected, input_len in CASES:
        cmd = [binary,"-A",str(args.snapshot),"-C",str(args.config),"-T","1","-x","-e","big",
               "-i", f"{addr:08x}" if op == "fetch" else f"{OPCODES[op]:08x}",
               "-I",f"x11=0x{addr:016x}","-I",f"zisk_input_end=0x{INPUT+8+input_len:016x}",
               "-I","zisk_free_input=0x1122334455667788","--simplify","--timeout","30"]
        if op == "fetch": cmd += ["-f","zisk_smoke_fetch"]
        result=subprocess.run(cmd,capture_output=True,text=True,env=env,check=True)
        check_trace(result.stdout,expected,addr)
        path=args.out / (name + ".isla"); path.write_text(result.stdout)
        report.append({"case":name,"operation":op,"address":hex(addr),"expected":expected,
          "input_len":input_len,"trace_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),"command":cmd})
    output={"schema_version":1,"cases":report,"seconds":round(time.monotonic()-started,3),
       "peak_rss_kib":resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,"workers":1,
       "snapshot_sha256":hashlib.sha256(args.snapshot.read_bytes()).hexdigest(),
       "config_sha256":hashlib.sha256(args.config.read_bytes()).hexdigest(),
       "footprint_sha256":hashlib.sha256(Path(binary).read_bytes()).hexdigest()}
    (args.out / "report.json").write_text(json.dumps(output,indent=2)+"\n")
    print(f"Platform smoke traces: {len(report)} passed, {output['seconds']} seconds, {output['peak_rss_kib']} KiB")
if __name__ == "__main__": main()
