#!/usr/bin/env python3
"""Run one Dune build and append its resource record as JSON."""

import argparse
import json
import os
import resource
import subprocess
import sys
import time
from pathlib import Path

from coqc_recipe import remember_recipe
from dune_trace_guard import scrub_trace


def error_class(returncode: int, output: str) -> str | None:
    if returncode == 0:
        return None
    if returncode in (124, 137) or returncode < 0:
        return "resource_or_signal"
    if "Error:" in output:
        return "rocq_error"
    return "build_error"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--build-dir", required=True)
    parser.add_argument("--target", required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a Dune build command is required after --")

    remember_recipe(Path(args.build_dir))
    started = time.monotonic()
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    elapsed_ms = round((time.monotonic() - started) * 1000)
    scrub_trace(Path(args.build_dir) / "trace.csexp")
    remember_recipe(Path(args.build_dir))
    sys.stdout.write(result.stdout)
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    record = {
        "target": args.target,
        "ms": elapsed_ms,
        "rss_kb": usage.ru_maxrss,
        "exit": result.returncode,
        "error_class": error_class(result.returncode, result.stdout),
    }

    log_path = Path(args.build_dir) / "log.jsonl"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    line = (json.dumps(record, sort_keys=True) + "\n").encode()
    descriptor = os.open(log_path, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
    try:
        os.write(descriptor, line)
    finally:
        os.close(descriptor)
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
