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
    started = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    result = subprocess.run(
        [command[0], *flags, "-o", str(output), str(source)],
        cwd=working_dir,
        check=False,
    )
    elapsed_ms = round((time.monotonic() - started) * 1000)
    after = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    print(f"exit={result.returncode} ms={elapsed_ms} rss_kb={max(before, after)}")
    raise SystemExit(result.returncode)
PY
