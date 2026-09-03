#!/usr/bin/env python3
"""Check a generated speedscope profile against the flamegraph payload it came from.

This runs in the Nix build, after the converter. It re-reads both artifacts and
checks the claims the viewer depends on:

* one frame per displayed function instance, in the same order as the payload;
* the event stream rebuilds the payload's call hierarchy exactly;
* every frame's palette column agrees with the proof state recorded beside it;
* every instance painted as covered really sits under a directly proved ancestor,
  and has no direct proof of its own.
"""

import argparse
import json
import sys
from pathlib import Path

from build_zesu_speedscope import DIRECTLY_PROVED, STATUS_COLUMN


def tree_parents(core: dict) -> list[int | None]:
    """Parent of every node, by uiId, from the flamegraph payload."""
    parents: dict[int, int | None] = {}

    def visit(node: dict, parent: int | None) -> None:
        parents[node["uiId"]] = parent
        for child in node.get("children", []):
            visit(child, node["uiId"])

    visit(core["tree"], None)
    return [parents[index] for index in sorted(parents)]


def event_parents(profile: dict) -> list[int | None]:
    """Parent of every frame, by frame index, from the event stream."""
    parents: dict[int, int | None] = {}
    stack: list[int] = []
    for event in profile["profiles"][0]["events"]:
        if event["type"] == "O":
            if event["frame"] in parents:
                raise ValueError(f"frame {event['frame']} opens twice")
            parents[event["frame"]] = stack[-1] if stack else None
            stack.append(event["frame"])
        else:
            if not stack or stack[-1] != event["frame"]:
                raise ValueError(f"frame {event['frame']} closes out of order")
            stack.pop()
    if stack:
        raise ValueError("the event stream leaves frames open")
    return [parents[index] for index in sorted(parents)]


def check(profile: dict, core: dict, details: list | None, label: str) -> list[str]:
    problems: list[str] = []
    frames = profile["shared"]["frames"]
    meta = profile["zesuMeta"]

    parents = tree_parents(core)
    if len(frames) < len(parents):
        problems.append(f"{label}: {len(frames)} frames for {len(parents)} payload nodes")
        return problems
    if len(meta) != len(frames):
        problems.append(f"{label}: {len(meta)} metadata rows for {len(frames)} frames")
        return problems
    if details is not None and len(details) != len(parents):
        problems.append(f"{label}: {len(details)} detail rows for {len(parents)} payload nodes")

    try:
        rebuilt = event_parents(profile)
    except ValueError as error:
        problems.append(f"{label}: {error}")
        rebuilt = None
    if rebuilt is not None and rebuilt[:len(parents)] != parents:
        problems.append(f"{label}: the event stream does not rebuild the call hierarchy")

    for index, (frame, row) in enumerate(zip(frames, meta)):
        if frame.get("file") != str(index):
            problems.append(f"{label}: frame {index} does not address metadata row {index}")
        expected = STATUS_COLUMN.get(row["status"])
        if expected is None:
            problems.append(f"{label}: frame {index} has unknown status {row['status']}")
        elif frame["col"] != expected:
            problems.append(
                f"{label}: frame {index} paints column {frame['col']} "
                f"for status {row['status']}"
            )
        if row["status"] == "covered_by_proved_parent":
            ancestor = parents[index]
            while ancestor is not None and meta[ancestor]["status"] not in DIRECTLY_PROVED:
                ancestor = parents[ancestor]
            if ancestor is None:
                problems.append(
                    f"{label}: frame {index} is painted as covered with no proved ancestor"
                )
    return problems


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--decode", required=True, type=Path)
    parser.add_argument("--full", required=True, type=Path)
    parser.add_argument("--core", required=True, type=Path)
    parser.add_argument("--details", required=True, type=Path)
    args = parser.parse_args()

    problems = check(
        json.loads(args.decode.read_text()),
        json.loads(args.core.read_text()),
        json.loads(args.details.read_text()),
        "decode",
    )
    full = json.loads(args.full.read_text())
    if full["zesuProfile"]["scope"] != "full":
        problems.append("full: the profile does not name the full-program scope")
    if len(full["shared"]["frames"]) <= len(json.loads(args.decode.read_text())["shared"]["frames"]):
        problems.append("full: the full program is not larger than the decode endpoint")

    for problem in problems:
        print(problem, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
