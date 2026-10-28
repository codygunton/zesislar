#!/usr/bin/env python3
"""Test ancestor enforcement with a private 64 MiB parent, without proofs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

PARENT_BYTES = 64 * 1024**2
CHILD_BYTES = 192 * 1024**2

def command(*args, check=True):
    reply = subprocess.run(args, capture_output=True, text=True, check=False)
    if check and reply.returncode:
        raise RuntimeError({"command": args, "returncode": reply.returncode,
                            "stdout": reply.stdout, "stderr": reply.stderr})
    return reply

def read_events(path):
    return dict((key, int(value)) for key, value in
                (line.split() for line in (path / "memory.events").read_text().splitlines()))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("The output already exists.")
    args.output.mkdir(parents=True)
    parent = f"zesuparentcontrol{os.getuid()}p{os.getpid()}.slice"
    child = parent[:-6] + "-child.slice"
    unit = f"zesuparentcontrol{os.getpid()}.scope"
    boot_path = Path("/proc/sys/kernel/random/boot_id")
    result = {"schema": "resource-parent.live-control.v1", "parent": parent,
              "child": child, "parent_bytes": PARENT_BYTES, "child_bytes": CHILD_BYTES,
              "swap_max_bytes": 0, "proof_ran": False, "real_parent_stressed": False,
              "boot_before": boot_path.read_text().strip(), "started_ns": time.time_ns()}
    process = None
    try:
        for name, limit in [(parent, PARENT_BYTES), (child, CHILD_BYTES)]:
            command("systemctl", "--user", "set-property", "--runtime", name,
                    f"MemoryMax={limit}", "MemorySwapMax=0")
            command("systemctl", "--user", "start", name)
        physical = command("systemctl", "--user", "show", parent, "-p", "ControlGroup", "--value").stdout.strip()
        parent_path = Path("/sys/fs/cgroup") / physical.lstrip("/")
        child_path = parent_path / child
        assert child_path.is_dir(), "The child is outside its private parent."
        assert int((parent_path / "memory.max").read_text()) == PARENT_BYTES
        assert int((child_path / "memory.max").read_text()) == CHILD_BYTES
        assert (parent_path / "memory.swap.max").read_text().strip() == "0"
        result["parent_path"] = str(parent_path)
        result["before"] = read_events(parent_path)
        allocator = "import time; blocks=[]\nfor _ in range(160):\n blocks.append(bytearray(1024*1024)); time.sleep(.01)\ntime.sleep(1)\n"
        argv = ["systemd-run", "--user", "--scope", "--quiet", "--unit=" + unit,
                "--slice=" + child, sys.executable, "-c", allocator]
        result["command"] = argv
        process = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        stdout, stderr = process.communicate(timeout=30)
        result.update(returncode=process.returncode, stdout=stdout, stderr=stderr,
                      after=read_events(parent_path), child_events=read_events(child_path),
                      peak_bytes=int((parent_path / "memory.peak").read_text()),
                      boot_after=boot_path.read_text().strip())
        assert process.returncode != 0, "The allocation survived the parent limit."
        assert result["after"]["oom_kill"] > result["before"]["oom_kill"]
        assert result["after"]["max"] > result["before"]["max"]
        assert result["child_events"]["max"] == 0, "The child hit its own limit."
        assert result["boot_after"] == result["boot_before"]
        result["success"] = True
    except Exception as error:
        result.update(success=False, error=str(error))
    finally:
        cleanup = []
        for name in [unit, child, parent]:
            reply = command("systemctl", "--user", "stop", name, check=False)
            cleanup.append({"unit": name, "returncode": reply.returncode, "stderr": reply.stderr})
        if process is not None and process.poll() is None:
            process.kill()
            process.communicate()
        for name in [child, parent]:
            reply = command("systemctl", "--user", "revert", name, check=False)
            cleanup.append({"revert": name, "returncode": reply.returncode})
        result["cleanup"] = cleanup
        result["ended_ns"] = time.time_ns()
        result["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        (args.output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if result.get("success") else 1

if __name__ == "__main__":
    raise SystemExit(main())
