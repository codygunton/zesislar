#!/usr/bin/env python3
"""Exclude environment headers from completed Dune traces."""

import subprocess
import sys
import tempfile
from pathlib import Path

from coqc_recipe import trace_environment_header, trace_records


def reject_environment_header(data):
    consumed = 0
    for event, raw in trace_records(data):
        consumed += len(raw)
        if trace_environment_header(event):
            raise ValueError("A Dune environment header cannot enter an evidence package")
    if data[consumed:].startswith((b"(6:config4:init", b"(3:env")):
        raise ValueError("An incomplete Dune environment header cannot enter an evidence package")


def scrub_trace(path):
    path = Path(path)
    if not path.is_file():
        return
    records = list(trace_records(path.read_bytes()))
    if not any(trace_environment_header(event) for event, _ in records):
        return
    data = b"".join(raw for event, raw in records
                    if not trace_environment_header(event))
    reject_environment_header(data)
    # Replace the completed trace. Never change a file while Dune writes it.
    with tempfile.TemporaryDirectory(dir=path.parent, prefix=".safe-trace-") as directory:
        pending = Path(directory) / path.name
        pending.write_bytes(data)
        pending.chmod(path.stat().st_mode & 0o777)
        pending.replace(path)


def trace_paths(command):
    paths = set()
    root = Path.cwd()
    for index, arg in enumerate(command):
        if arg == "--root" and index + 1 < len(command):
            root = Path(command[index + 1]).resolve()
        elif arg.startswith("--root="):
            root = Path(arg[len("--root="):]).resolve()
    for index, arg in enumerate(command):
        for option, suffix in (("--build-dir", "trace.csexp"), ("--trace-file", None)):
            value = None
            if arg == option and index + 1 < len(command):
                value = command[index + 1]
            elif arg.startswith(option + "="):
                value = arg[len(option) + 1:]
            if value:
                path = Path(value)
                if not path.is_absolute():
                    path = root / path
                paths.add(path / suffix if suffix else path)
    return paths


def main():
    command = sys.argv[1:]
    if command[:1] == ["--"]:
        command = command[1:]
    if not command:
        raise SystemExit("A build command is required")
    paths = trace_paths(command)
    result = subprocess.run(command, check=False)
    for path in paths:
        scrub_trace(path)
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
