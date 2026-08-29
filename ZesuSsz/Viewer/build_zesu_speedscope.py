#!/usr/bin/env python3
"""Convert the zesu flamegraph payload into a speedscope profile.

The speedscope viewer replaces the D3 flamegraph, so this converter must keep
every claim the D3 viewer made:

* one frame per displayed function instance, in generator (address) order;
* the resolved proof state of that instance, including coverage inherited from
  a proved parent, which the D3 viewer computed while it painted;
* the compact metadata the header and the level rail read.

Full detail records stay in the separate details payload the viewer fetches
lazily, exactly as the D3 viewer fetched them.
"""

import argparse
import json
from pathlib import Path

# Proof states, in the order the palette expects. The viewer paints:
#   0 red, 1 yellow/red stripes, 2 yellow, 3 green/yellow stripes, 4 green,
#   5 white with a green border.
NOT_STARTED = 0
CONTRACT_SPECIFIED = 1
PROOF_IN_PROGRESS = 2
CONDITIONALLY_PROVEN = 3
UNCONDITIONALLY_PROVEN = 4
COVERED_BY_PROVED_PARENT = 5

STATUS_COLUMN = {
    "not_selected": NOT_STARTED,
    "not_started": NOT_STARTED,
    "proof_not_started": NOT_STARTED,
    "contract_not_specified": NOT_STARTED,
    "invalid_target_model": NOT_STARTED,
    "contracted": CONTRACT_SPECIFIED,
    "contract_specified_assumption": CONTRACT_SPECIFIED,
    "contract_consumed": CONTRACT_SPECIFIED,
    "in_progress": PROOF_IN_PROGRESS,
    "proof_in_progress": PROOF_IN_PROGRESS,
    "conditionally_proven": CONDITIONALLY_PROVEN,
    "proved": UNCONDITIONALLY_PROVEN,
    "unconditionally_proven": UNCONDITIONALLY_PROVEN,
    "covered_by_proved_parent": COVERED_BY_PROVED_PARENT,
}

DIRECTLY_PROVED = ("proved", "unconditionally_proven")

COVERED_CONDITION = (
    "A proved parent covers this instance. This instance has no direct proof."
)

# Metadata the viewer needs before a click: the header line, the level rail,
# and the search index all read these.
CORE_META_FIELDS = (
    "owner",
    "machineOwner",
    "qualified",
    "displayTreeLevel",
    "refinementLevel",
    "machineInstructionCount",
)


def index_progress(progress: dict) -> dict:
    """Key the proof states the way the D3 viewer keyed them.

    Both the owner and the qualified name address the same state, and a later
    state overrides an earlier one under the same key.
    """
    states: dict[str, dict] = {}
    for state in progress.get("states", []):
        if state.get("owner"):
            states[state["owner"]] = state
        if state.get("qualified"):
            states[state["qualified"]] = state
    return states


def own_state(meta: dict, states: dict) -> dict:
    for key in (meta.get("owner"), meta.get("machineOwner"), meta.get("qualified")):
        if key and key in states:
            return states[key]
    return {"status": "not_selected"}


def resolve_state(meta: dict, ancestors: list[dict], states: dict) -> dict:
    """Resolve one instance's proof state, including inherited coverage."""
    own = own_state(meta, states)
    if own.get("status") in DIRECTLY_PROVED:
        return own
    for ancestor in reversed(ancestors):
        inherited = own_state(ancestor, states)
        if inherited.get("status") in DIRECTLY_PROVED:
            covered = dict(own)
            covered["status"] = "covered_by_proved_parent"
            covered["condition"] = COVERED_CONDITION
            covering = inherited.get("theorem") or inherited.get("contract")
            covered["coveringTheorem"] = covering
            return covered
    return own


def convert(flame: dict, progress: dict, scope: str, details_url: str) -> dict:
    states = index_progress(progress)
    meta_rows = flame["meta"]

    frames: list[dict] = []
    events: list[dict] = []
    frame_meta: list[dict] = []
    cursor = 0

    def walk(node: dict, ancestors: list[dict]) -> None:
        nonlocal cursor
        ui_id = node["uiId"]
        meta = meta_rows[ui_id]
        state = resolve_state(meta, ancestors, states)
        index = len(frames)
        if index != ui_id:
            raise ValueError(f"frame {index} does not match uiId {ui_id}")
        frames.append(
            {
                "name": meta.get("qualified") or node["name"],
                # `file` carries the metadata key, and `col` the proof state.
                # The fork reads both; upstream speedscope ignores them.
                "file": str(ui_id),
                "col": STATUS_COLUMN[state["status"]],
            }
        )
        row = {field: meta[field] for field in CORE_META_FIELDS if field in meta}
        row["name"] = node["name"]
        row["status"] = state["status"]
        for field in ("theorem", "contract", "condition", "coveringTheorem"):
            if state.get(field):
                row[field] = state[field]
        row["selfInstructions"] = node.get("self", 0)
        row["totalInstructions"] = node.get("value", 0)
        frame_meta.append(row)

        events.append({"type": "O", "at": cursor, "frame": index})
        cursor += node.get("self", 0)
        for child in node.get("children", []):
            walk(child, ancestors + [meta])
        events.append({"type": "C", "at": cursor, "frame": index})

    walk(flame["tree"], [])

    if cursor != flame["tree"].get("value", cursor):
        raise ValueError(
            f"instruction total {cursor} does not match the root value "
            f"{flame['tree'].get('value')}"
        )

    return {
        "$schema": "https://www.speedscope.app/file-format-schema.json",
        "name": f"zesu-{scope}",
        "exporter": "build_zesu_speedscope.py",
        "shared": {"frames": frames},
        "profiles": [
            {
                "type": "evented",
                "name": (
                    "Zesu SSZ-decode call hierarchy"
                    if scope == "decode"
                    else "authentic Zesu full-program call hierarchy"
                ),
                "unit": "none",
                "startValue": 0,
                "endValue": cursor,
                "events": events,
            }
        ],
        # Non-standard keys the zesu fork reads and upstream speedscope ignores.
        "zesuMeta": frame_meta,
        "zesuProfile": {
            "scope": scope,
            "total": flame["total"],
            "programTotal": flame["programTotal"],
            "detailsUrl": details_url,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--core", required=True, type=Path, help="flame-core payload")
    parser.add_argument("--progress", required=True, type=Path)
    parser.add_argument("--scope", required=True, choices=("decode", "full"))
    parser.add_argument("--details-url", required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    profile = convert(
        json.loads(args.core.read_text()),
        json.loads(args.progress.read_text()),
        args.scope,
        args.details_url,
    )
    args.output.write_text(json.dumps(profile, sort_keys=True, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
