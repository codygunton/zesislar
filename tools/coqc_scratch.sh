#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <file.v> <build-dir>" >&2
  exit 2
fi

scratch_file=$(realpath "$1")
build_dir=$(realpath "$2")
trace_file="$build_dir/trace.csexp"

if [[ ! -f "$scratch_file" || ! -f "$trace_file" ]]; then
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


source = Path(sys.argv[1])
build_dir = Path(sys.argv[2])
sys.path.insert(0, sys.argv[4])
from coqc_recipe import remember_recipe

recipe = remember_recipe(build_dir)
if recipe is None:
    raise SystemExit("no coqc compiler recipe exists; build a focused proof target first")
command = recipe["command"]
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
    guard = str(Path(sys.argv[4]) / "resource_guard.sh")
    subprocess.run([guard, "wait"], check=True)
    reservation = subprocess.run(
        [guard, "reserve-coqc", str(os.getpid())], check=True,
        capture_output=True, text=True).stdout.strip()
    if not reservation:
        raise SystemExit("resource guard returned no coqc reservation")
    started = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    process = None
    try:
        process = subprocess.Popen(
            [command[0], *flags, "-o", str(output), str(source)],
            cwd=working_dir,
        )
        subprocess.run([guard, "mark-coqc", reservation, str(process.pid)],
                       check=True)
        limit = None
        while process.poll() is None:
            elapsed = time.monotonic() - started
            try:
                status = Path(f"/proc/{process.pid}/status").read_text()
                rss_kb = next(int(line.split()[1]) for line in status.splitlines()
                              if line.startswith("VmRSS:"))
            except (FileNotFoundError, ProcessLookupError, StopIteration):
                rss_kb = 0
            if elapsed > 300 or rss_kb > 6 * 1024 * 1024:
                limit = "time" if elapsed > 300 else "memory"
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
        subprocess.run([guard, "release-coqc", reservation], check=True)
    elapsed_ms = round((time.monotonic() - started) * 1000)
    after = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    print(f"exit={returncode} ms={elapsed_ms} rss_kb={max(before, after)}")
    if limit is not None:
        print(f"proof limit exceeded: {limit}", file=sys.stderr)
    raise SystemExit(returncode)
PY
