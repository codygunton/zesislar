"""Per-module compile cost, read from the Dune trace.

A probe costs about what its module costs, because it recompiles the module
text up to the target `Proof.`. The Dune trace of the setup build already
holds that number, so `run_corpus.py` can order its work cheapest first and
reach useful statistics before the slowest modules finish.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coqc_recipe import trace_events  # noqa: E402

NANOSECONDS = 1e9


def fields(event: list) -> dict:
    return {field[0]: field[1:] for field in event[3:]
            if isinstance(field, list) and field}


def source_of(event: list) -> str | None:
    """The `.v` file a `coqc` process compiled, if this event is one."""
    names = fields(event).get("process_args", [])
    arguments = names[0] if len(names) == 1 and isinstance(names[0], list) else names
    for argument in arguments:
        if isinstance(argument, str) and argument.endswith(".v"):
            return argument
    return None


def module_costs(build_dir: Path) -> dict[str, tuple[float, int]]:
    """Map each compiled `.v` path to its seconds and peak RSS in MiB."""
    trace = Path(build_dir) / "trace.csexp"
    if not trace.exists():
        return {}
    costs: dict[str, tuple[float, int]] = {}
    for event in trace_events(trace.read_bytes()):
        if not isinstance(event, list) or event[:2] != ["process", "finish"]:
            continue
        source = source_of(event)
        if source is None:
            continue
        stamps = event[2] if isinstance(event[2], list) else ["0", "0"]
        seconds = int(stamps[-1]) / NANOSECONDS if len(stamps) > 1 else 0.0
        usage = dict((entry[0], entry[1]) for entry in
                     fields(event).get("rusage", [[]])[0]
                     if isinstance(entry, list) and len(entry) > 1)
        rss_mib = int(usage.get("maxrss", 0)) // 1024
        name = Path(source).name
        if seconds >= costs.get(name, (0.0, 0))[0]:
            costs[name] = (round(seconds, 2), rss_mib)
    return costs
