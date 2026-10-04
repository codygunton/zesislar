#!/usr/bin/env python3
"""Replay validated Isla files for the unchanged frontend emitter."""
import json
import os
from pathlib import Path
import sys

args = sys.argv[1:]
if args[0] != "riscv64.ir" or "--reset-constraint" in args or "--partial" in args:
    raise SystemExit("The cache accepts only selected plain instructions")
opcode = args[args.index("-i") + 1]
cache = json.loads(Path(os.environ["ZISK_TRACE_CACHE"]).read_text())
if opcode not in cache:
    raise SystemExit("The validated cache does not contain this opcode")
sys.stdout.buffer.write(Path(cache[opcode]).read_bytes())
