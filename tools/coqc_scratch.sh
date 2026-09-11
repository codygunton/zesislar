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

python3 - "$scratch_file" "$build_dir" "$trace_file" <<'PY'
import os
import resource
import subprocess
import sys
import tempfile
import time
from pathlib import Path


source = Path(sys.argv[1])
build_dir = Path(sys.argv[2])
data = Path(sys.argv[3]).read_bytes()
offset = 0


def parse():
    global offset
    if data[offset:offset + 1] == b"(":
        offset += 1
        result = []
        while data[offset:offset + 1] != b")":
            result.append(parse())
        offset += 1
        return result
    colon = data.index(b":", offset)
    length = int(data[offset:colon])
    offset = colon + 1
    atom = data[offset:offset + length].decode()
    offset += length
    return atom


command = None
working_dir = None
while offset < len(data):
    event = parse()
    if not isinstance(event, list) or event[:2] != ["process", "start"]:
        continue
    fields = {
        field[0]: field[1:]
        for field in event[3:]
        if isinstance(field, list) and field
    }
    program = fields.get("prog", [""])[0]
    raw_args = fields.get("process_args", [])
    args = raw_args[0] if len(raw_args) == 1 and isinstance(raw_args[0], list) else raw_args
    if Path(program).name == "coqc" and any(arg.endswith(".v") for arg in args):
        command = [program, *args]
        working_dir = fields.get("dir", [str(build_dir / "default")])[0]

if command is None:
    raise SystemExit("no coqc compile command exists in trace.csexp")

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
