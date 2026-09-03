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


def parse_pc(value: int | str) -> int:
    return value if isinstance(value, int) else int(value, 0)


def index_proof_regions(
    progress: dict,
) -> tuple[tuple[int, int] | None, list[tuple[int, int, dict]]]:
    scope = progress.get("regionScope")
    if not scope:
        return None, []
    start = parse_pc(scope["startPc"])
    end = parse_pc(scope["endPc"])
    if start >= end or start % 4 or end % 4:
        raise ValueError("proof region scope must be a nonempty aligned PC range")

    regions = []
    for state in progress.get("proofRegions", []):
        region_start = parse_pc(state["startPc"])
        region_end = parse_pc(state["endPc"])
        if (region_start < start or region_end > end or region_start >= region_end
                or region_start % 4 or region_end % 4):
            raise ValueError("proof region must be aligned and inside its scope")
        if state["status"] not in STATUS_COLUMN:
            raise ValueError(f"unknown proof region status: {state['status']}")
        regions.append((region_start, region_end, state))
    return (start, end), regions


def convert(flame: dict, progress: dict, scope: str, details_url: str,
            details: list[dict] | None = None) -> dict:
    states = index_progress(progress)
    region_scope, proof_regions = index_proof_regions(progress)
    meta_rows = flame["meta"]
    detail_rows = details or [{} for _ in meta_rows]

    frames: list[dict] = [{} for _ in meta_rows]
    events: list[dict] = []
    frame_meta: list[dict] = [{} for _ in meta_rows]
    cursor = 0

    def prepare(node: dict, ancestors: list[dict]) -> None:
        ui_id = node["uiId"]
        meta = meta_rows[ui_id]
        state = resolve_state(meta, ancestors, states)
        frames[ui_id] = {
            "name": meta.get("qualified") or node["name"],
            # `file` carries the metadata key, and `col` the proof state.
            # The fork reads both; upstream speedscope ignores them.
            "file": str(ui_id),
            "col": STATUS_COLUMN[state["status"]],
        }
        row = {field: meta[field] for field in CORE_META_FIELDS if field in meta}
        row["name"] = node["name"]
        row["status"] = state["status"]
        for field in ("theorem", "contract", "condition", "coveringTheorem"):
            if state.get(field):
                row[field] = state[field]
        row["selfInstructions"] = node.get("self", 0)
        row["totalInstructions"] = node.get("value", 0)
        frame_meta[ui_id] = row
        for child in node.get("children", []):
            prepare(child, ancestors + [meta])

    prepare(flame["tree"], [])

    def region_state(pc: int) -> dict | None:
        if region_scope is None or not region_scope[0] <= pc < region_scope[1]:
            return None
        state = {"status": "not_started", "label": "No completed proof"}
        for region_start, region_end, candidate in proof_regions:
            if region_start <= pc < region_end:
                state = candidate
        return state

    def add_region_frame(pcs: list[int], state: dict, level: int) -> int:
        start, end = pcs[0], pcs[-1] + 4
        label = state.get("label", state["status"].replace("_", " "))
        name = f"{label} [{start:#x}, {end:#x})"
        index = len(frames)
        frames.append({
            "name": name,
            "file": str(index),
            "col": STATUS_COLUMN[state["status"]],
        })
        row = {
            "name": name,
            "qualified": name,
            "displayTreeLevel": level,
            "refinementLevel": 1,
            "machineInstructionCount": len(pcs),
            "selfInstructions": len(pcs),
            "totalInstructions": len(pcs),
            "status": state["status"],
            "startPc": start,
            "endPc": end,
        }
        for field in ("theorem", "condition"):
            if state.get(field):
                row[field] = state[field]
        frame_meta.append(row)
        return index

    def expand_runs(row: dict) -> set[int]:
        return {
            pc
            for run in row.get("runs", [])
            for pc in range(run["start"], run["end"], 4)
        }

    def owned_pcs(node: dict) -> list[int]:
        ui_id = node["uiId"]
        if meta_rows[ui_id].get("pcs"):
            return sorted(meta_rows[ui_id]["pcs"])
        own = expand_runs(detail_rows[ui_id])
        for child in node.get("children", []):
            child_detail = detail_rows[child["uiId"]]
            if child_detail.get("kind") == "inlinedFunctionInstance":
                own -= expand_runs(child_detail)
        return sorted(own)

    def walk(node: dict) -> None:
        nonlocal cursor
        ui_id = node["uiId"]
        meta = meta_rows[ui_id]
        events.append({"type": "O", "at": cursor, "frame": ui_id})

        pcs = owned_pcs(node)
        if (len(pcs) == node.get("self", 0)
                and any(region_state(pc) is not None for pc in pcs)):
            groups: list[tuple[list[int], dict]] = []
            for pc in pcs:
                state = region_state(pc) or {
                    "status": "not_selected",
                    "label": "Outside proof scope",
                }
                if (groups and groups[-1][1] == state
                        and groups[-1][0][-1] + 4 == pc):
                    groups[-1][0].append(pc)
                else:
                    groups.append(([pc], state))
            for group_pcs, state in groups:
                index = add_region_frame(
                    group_pcs, state, meta.get("displayTreeLevel", 0) + 1
                )
                events.append({"type": "O", "at": cursor, "frame": index})
                cursor += len(group_pcs)
                events.append({"type": "C", "at": cursor, "frame": index})
        else:
            cursor += node.get("self", 0)

        for child in node.get("children", []):
            walk(child)
        events.append({"type": "C", "at": cursor, "frame": ui_id})

    walk(flame["tree"])

    if cursor != flame["tree"].get("value", cursor):
        raise ValueError(
            f"instruction total {cursor} does not match the root value "
            f"{flame['tree'].get('value')}"
        )

    result = {
        "$schema": "https://www.speedscope.app/file-format-schema.json",
        "name": f"zesu-{scope}",
        "exporter": "build_zesu_speedscope.py",
        "shared": {"frames": frames},
        "profiles": [{
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
        }],
        # Non-standard keys the zesu fork reads and upstream speedscope ignores.
        "zesuMeta": frame_meta,
        "zesuProfile": {
            "scope": scope,
            "total": flame["total"],
            "programTotal": flame["programTotal"],
            "detailsUrl": details_url,
        },
    }
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--core", required=True, type=Path, help="flame-core payload")
    parser.add_argument("--progress", required=True, type=Path)
    parser.add_argument("--scope", required=True, choices=("decode", "full"))
    parser.add_argument("--details-url", required=True)
    parser.add_argument("--details-input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    profile = convert(
        json.loads(args.core.read_text()),
        json.loads(args.progress.read_text()),
        args.scope,
        args.details_url,
        json.loads(args.details_input.read_text()),
    )
    args.output.write_text(json.dumps(profile, sort_keys=True, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
