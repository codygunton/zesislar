#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <file.v> <build-dir>" >&2
  exit 2
fi

scratch_file=$(realpath "$1")
build_dir=$(realpath "$2")
trace_file="$build_dir/trace.csexp"

if [[ ! -f "$scratch_file" || ( -z "${ZESU_SCRATCH_RECIPE:-}" && ! -f "$trace_file" ) ]]; then
  echo "the scratch file or Dune trace does not exist" >&2
  exit 2
fi

python3 - "$scratch_file" "$build_dir" "$trace_file" "$(dirname "$(realpath "$0")")" <<'PY'
import os
import resource
import subprocess
import sys
import tempfile
import time
from pathlib import Path


probe = os.environ.get("ZESU_DIAGNOSTIC_PROBE", "0")
if probe not in ("0", "1"):
    raise SystemExit("the diagnostic probe flag must be zero or one")
wall_text = os.environ.get("ZESU_SCRATCH_WALL_SECONDS", "300")
memory_gib = int(os.environ.get("ZESU_SCRATCH_MEMORY_GIB", "6"))
if probe == "1":
    if (wall_text != "none" or os.environ.get("ZESU_PRIMARY_CPU_LIMIT") != "none" or
            os.environ.get("ZESU_PROOF_CPU_LIMIT") != "unlimited" or memory_gib != 64 or
            os.environ.get("ZESU_PROBE_ISSUE") != "10" or os.environ.get("ZESU_IN_GATE")):
        raise SystemExit("the diagnostic probe requires issue10, 64 GiB, and unlimited CPU and wall time")
    wall_limit = None
else:
    if wall_text == "none":
        if not 0 < int(os.environ.get("ZESU_PRIMARY_CPU_LIMIT", "0")) <= 2400:
            raise SystemExit("an unlimited wall budget requires an explicit CPU budget")
        cpu = int(os.environ["ZESU_PRIMARY_CPU_LIMIT"])
        if cpu > 1200 and os.environ.get("ZESU_COMPLETION_ENTRY") not in ("0x800d6a24", "0x800d6ac4"):
            raise SystemExit("the CPU exception requires an authorized completion entry")
        wall_limit = None
    else:
        wall_limit = float(wall_text)
        if not 0 < wall_limit <= 300:
            raise SystemExit("the scratch wall budget must be between zero and 300 seconds")

    if memory_gib not in (6, 12) or (memory_gib == 12 and
            (wall_limit is not None or os.environ.get("ZESU_COMPLETION_ENTRY") != "0x800d698c")):
        raise SystemExit("the memory exception requires completion entry0x800d698c")

source = Path(sys.argv[1])
build_dir = Path(sys.argv[2])
sys.path.insert(0, sys.argv[4])
from coqc_recipe import remember_recipe, read_snapshot

snapshot = os.environ.get("ZESU_SCRATCH_RECIPE")
snapshot_hash = os.environ.get("ZESU_SCRATCH_RECIPE_SHA256")
if bool(snapshot) != bool(snapshot_hash):
    raise SystemExit("the compiler recipe snapshot requires both path and SHA256")
recipe = read_snapshot(Path(snapshot), snapshot_hash) if snapshot else remember_recipe(build_dir)
if recipe is None:
    raise SystemExit("no coqc compiler recipe exists; build a focused proof target first")
command = recipe["command"]
compiler = os.environ.get("ZESU_SCRATCH_COQC_BINARY", command[0])
working_dir = recipe["working_dir"]

flags = []
skip = False
for argument in command[1:]:
    if skip:
        skip = False
        continue
    if argument == "-o":
        skip = True
        continue
    if argument.endswith(".v"):
        continue
    flags.append(argument)

with tempfile.TemporaryDirectory(prefix="zesu-coqc-") as output_dir:
    output = Path(output_dir) / f"{source.stem}.vo"
    guard = os.environ.get("ZESU_RESOURCE_GUARD", str(Path(sys.argv[4]) / "resource_guard.sh"))
    subprocess.run([guard, "wait"], check=True)
    reservation = os.environ.get("ZESU_COQC_RESERVATION", "")
    owns_reservation = not reservation
    if owns_reservation:
        reservation = subprocess.run(
            [guard, "reserve-coqc", str(os.getpid())], check=True,
            capture_output=True, text=True).stdout.strip()
    if not reservation:
        raise SystemExit("resource guard returned no coqc reservation")
    started = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    process = None
    try:
        subprocess.run([guard, "confirm-coqc", reservation], check=True)
        process = subprocess.Popen(
            [guard, "scope", "scratch-coqc", "--", compiler, *flags, "-o", str(output), str(source)],
            cwd=working_dir,
            env={**os.environ, "ZESU_COQC_RESERVATION": reservation,
                 "ZESU_MODULE_LIMIT_GIB": str(memory_gib)},
        )
        limit = None
        while process.poll() is None:
            elapsed = time.monotonic() - started
            try:
                status = Path(f"/proc/{process.pid}/status").read_text()
                rss_kb = next(int(line.split()[1]) for line in status.splitlines()
                              if line.startswith("VmRSS:"))
            except (FileNotFoundError, ProcessLookupError, StopIteration):
                rss_kb = 0
            if (wall_limit is not None and elapsed > wall_limit) or rss_kb > memory_gib * 1024 * 1024:
                limit = "time" if wall_limit is not None and elapsed > wall_limit else "memory"
                process.terminate()
                try:
                    process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
                break
            time.sleep(0.25)
        returncode = process.wait()
    finally:
        if process is not None and process.poll() is None:
            process.terminate()
            process.wait()
        if owns_reservation:
            subprocess.run([guard, "release-coqc", reservation], check=True)
    elapsed_ms = round((time.monotonic() - started) * 1000)
    after = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    print(f"exit={returncode} ms={elapsed_ms} rss_kb={max(before, after)}")
    if limit is not None:
        print(f"proof limit exceeded: {limit}", file=sys.stderr)
    raise SystemExit(returncode)
PY
