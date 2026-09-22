#!/usr/bin/env python3
"""Machine figures for a report, from Prometheus, not from `free` or `df`.

Plan section 4, guard rule 6: memory, load, and disk figures in a report
are the peak and p90 over the report window, queried against
`instance="lucy"` (see `~/GRAFANA.md`). A figure read at report time
shows the quiet minute after the work, not the work.

    python3 tools/det/prom.py window --since 2026-09-22T15:00 [--until …]
    python3 tools/det/prom.py window --minutes 60
    python3 tools/det/prom.py now

`window` prints one line: peak and p90 of memory used, swap used, load5,
blocked processes, CPU busy and disk read, and `/home` free at the end.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import sys
import urllib.parse
import urllib.request

URL = os.environ.get("ZESU_PROMETHEUS", "https://prometheus.lightningbug.icu")
INSTANCE = os.environ.get("ZESU_PROM_INSTANCE", "lucy")
GIB = 1024 ** 3
MIB = 1024 ** 2

# name -> (expression, unit divisor, unit label, format)
SERIES = {
    "memory used": (
        "node_memory_MemTotal_bytes{i} - node_memory_MemAvailable_bytes{i}",
        GIB, "GiB", "{:.1f}"),
    "swap used": (
        "node_memory_SwapTotal_bytes{i} - node_memory_SwapFree_bytes{i}",
        GIB, "GiB", "{:.1f}"),
    "load5": ("node_load5{i}", 1, "", "{:.0f}"),
    "blocked": ("node_procs_blocked{i}", 1, "", "{:.0f}"),
    "cpu busy": (
        "100 * (1 - avg(rate(node_cpu_seconds_total{im}[1m])))",
        1, "%", "{:.0f}"),
    "disk read": (
        "sum(rate(node_disk_read_bytes_total{i}[1m]))", MIB, "MiB/s", "{:.0f}"),
}


def selector(extra: str = "") -> str:
    inner = f'instance="{INSTANCE}"' + (f",{extra}" if extra else "")
    return "{" + inner + "}"


def expression(name: str) -> str:
    text = SERIES[name][0]
    return text.replace("{im}", selector('mode="idle"')).replace(
        "{i}", selector())


def query(promql: str, at: float, fetch=None) -> float | None:
    """One instant query; None when the series is absent."""
    fetch = fetch or _fetch
    reply = fetch("query", {"query": promql, "time": f"{at:.0f}"})
    if reply.get("status") != "success":
        raise RuntimeError(f"prometheus: {reply.get('error', reply)}")
    result = reply["data"]["result"]
    return float(result[0]["value"][1]) if result else None


def _fetch(path: str, parameters: dict) -> dict:
    target = f"{URL}/api/v1/{path}?{urllib.parse.urlencode(parameters)}"
    with urllib.request.urlopen(target, timeout=20) as reply:
        return json.load(reply)


def window(start: float, end: float, fetch=None) -> dict:
    """Peak and p90 of every series over [start, end]."""
    seconds = max(60, int(end - start))
    figures = {}
    for name in SERIES:
        base = expression(name)
        peak = query(f"max_over_time(({base})[{seconds}s:15s])", end, fetch)
        p90 = query(f"quantile_over_time(0.9, ({base})[{seconds}s:15s])",
                    end, fetch)
        figures[name] = (peak, p90)
    free = query("node_filesystem_avail_bytes"
                 + selector('mountpoint="/home"'), end, fetch)
    total = query("node_memory_MemTotal_bytes" + selector(), end, fetch)
    return {"figures": figures, "home free": free, "memory total": total}


def render(start: float, end: float, data: dict) -> str:
    def stamp(value: float) -> str:
        return dt.datetime.fromtimestamp(value).strftime("%H:%M")

    parts = []
    for name, (peak, p90) in data["figures"].items():
        _, divisor, unit, form = SERIES[name]
        if peak is None:
            parts.append(f"{name} n/a")
            continue
        text = f"{name} peak {form.format(peak / divisor)}"
        text += f" p90 {form.format(p90 / divisor)}"
        if name == "memory used" and data["memory total"]:
            text += f" of {data['memory total'] / GIB:.0f}"
        parts.append(text + (f" {unit}" if unit else ""))
    if data["home free"] is not None:
        parts.append(f"/home free {data['home free'] / GIB:.0f} GiB")
    return (f"prometheus {INSTANCE} {stamp(start)}-{stamp(end)}: "
            + "; ".join(parts))


def parse_time(text: str) -> float:
    return dt.datetime.fromisoformat(text).timestamp()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    commands = parser.add_subparsers(dest="command", required=True)
    span = commands.add_parser("window", help="peak and p90 over a window")
    span.add_argument("--since", help="ISO time; the window start")
    span.add_argument("--until", help="ISO time; default now")
    span.add_argument("--minutes", type=int, help="window length instead")
    span.add_argument("--json", action="store_true")
    commands.add_parser("now", help="the last five minutes")
    arguments = parser.parse_args(argv)

    end = dt.datetime.now().timestamp()
    if arguments.command == "now":
        start = end - 300
    else:
        if arguments.until:
            end = parse_time(arguments.until)
        if arguments.since:
            start = parse_time(arguments.since)
        elif arguments.minutes:
            start = end - 60 * arguments.minutes
        else:
            parser.error("window needs --since or --minutes")
    try:
        data = window(start, end)
    except (OSError, RuntimeError) as error:
        print(f"prometheus unavailable: {error}", file=sys.stderr)
        return 1
    if getattr(arguments, "json", False):
        print(json.dumps(data))
    else:
        print(render(start, end, data))
    return 0


if __name__ == "__main__":
    sys.exit(main())
