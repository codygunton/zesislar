#!/usr/bin/env python3
"""Build an honest Level 1 proof-map payload from generated evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def build(cfg: dict, flame: dict, manifest: dict, evidence: dict,
          bindings: dict, progress: dict) -> dict:
    documents = (manifest, evidence, bindings)
    if any(cfg["artifact"] != document["artifact"] for document in documents):
        raise ValueError("CFG, manifest, evidence, and bindings describe different artifacts")

    rows = manifest["instances"]
    expected = {row["qualified"] for row in rows}
    states = {row["qualified"]: row for row in progress["states"]}
    if set(states) != expected:
        raise ValueError("progress does not name the exact Level 1 inventory")

    observed: dict[str, dict] = {}
    for vector in evidence["vectors"]:
        for measured in vector["instances"]:
            slot = observed.setdefault(measured["id"], {
                "vectors": [], "owned": set(), "extent": set(), "exits": set(),
            })
            if measured["entryReached"]:
                slot["vectors"].append(vector["label"])
            slot["owned"].update(measured["executedOwnedPcs"])
            slot["extent"].update(measured["executedExtentPcs"])
            slot["exits"].update(tuple(edge) for edge in measured["observedExitTransitions"])
    bindings_by_id = {row["id"]: row["bindings"] for row in bindings["instances"]}
    ids = {row["id"] for row in rows}
    if set(observed) != ids or set(bindings_by_id) != ids:
        raise ValueError("evidence or bindings do not name the exact Level 1 instances")

    main = next(row for row in cfg["functionInstances"]
                if row["kind"] == "concrete" and row["name"] == "ssz_decode_root.main")
    selected = {pc for row in rows for pc in row["executionPcs"]}
    glue_pcs = sorted(set(main["pcs"]) - selected)
    if len(glue_pcs) != 24:
        raise ValueError("expected exactly 24 Level 0 glue instructions")

    boundaries = []
    regions = []
    nodes = [{
        "id": "spec", "label": "EVM-Sail decoder", "kind": "specification",
        "column": 0, "status": "artifact", "instructionCount": 0,
    }]
    edges = []
    flame_states = [{
        "owner": main["id"], "qualified": main["name"], "status": "proof_not_started",
    }]
    for row in rows:
        capture = observed[row["id"]]
        state = states[row["qualified"]]
        status = state["status"]
        boundary_id = "level1-" + row["id"].replace(":", "-")
        source = row["functionInstanceIdentity"]["function"]["declaration"]
        boundary = {
            "id": boundary_id,
            "instanceId": row["id"],
            "qualified": row["qualified"],
            "entryPc": row["entryPc"],
            "instructionPcs": row["instructionPcs"],
            "executionPcs": row["executionPcs"],
            "exitPcs": row["exitPcs"],
            "ownedInstructionCount": row["ownedInstructionCount"],
            "subtreeInstructionCount": row["subtreeInstructionCount"],
            "source": source,
            "observedVectors": sorted(capture["vectors"]),
            "observedOwnedInstructionCount": len(capture["owned"]),
            "observedExtentInstructionCount": len(capture["extent"]),
            "observedExitTransitions": [list(edge) for edge in sorted(capture["exits"])],
            "dwarfBindings": bindings_by_id[row["id"]],
            "evidenceStatus": "captured",
            "contractStatus": "specified_assumption",
            "proofStatus": "not_started",
        }
        boundaries.append(boundary)
        regions.append({
            "id": boundary_id,
            "label": row["qualified"],
            "authoringState": status,
            "blocker": "The Level 1 machine proof is not complete.",
            "scope": "selected-child",
            "pcs": row["executionPcs"],
            "boundaryIds": [boundary_id],
            "evidence": "Entry registers, executed PCs, memory accesses, and exits were captured.",
            "preparation": {
                "liveRegisters": [
                    f"{item['name']} = x{item['machineRegister']}"
                    for item in bindings_by_id[row["id"]]
                    if item["machineRegister"] is not None
                ],
                "protectedMemory": [],
                "prerequisites": ["instantiate the Rocq Level1MachineModel clauses"],
                "sourceIdentity": f"{source['file']}::{source['qualifiedName']}",
            },
        })
        node_id = "contract-" + boundary_id
        nodes.append({
            "id": node_id, "label": row["qualified"], "kind": "level1Contract",
            "column": 1, "status": status, "proofStatus": "not_started",
            "evidenceStatus": "captured", "contractStatus": "specified_assumption",
            "level0UseStatus": "consumed", "boundaryId": boundary_id,
            "instructionCount": row["subtreeInstructionCount"],
        })
        edges.extend([
            {"source": "spec", "target": node_id, "kind": "semantic-review"},
            {"source": node_id, "target": "assembly", "kind": "dependency"},
        ])
        flame_states.append({
            "owner": row["id"], "qualified": row["qualified"], "status": status,
            **{field: state[field] for field in ("contract", "theorem", "condition")
               if state.get(field)},
        })
    flame_states.extend(dict(state) for state in progress.get("frameStates", []))

    regions.append({
        "id": "level0-glue", "label": "main parent-owned glue",
        "authoringState": "proof_not_started", "blocker": "The assembly proof is not complete.",
        "scope": "parent", "pcs": glue_pcs, "boundaryIds": [],
        "evidence": "The CFG identifies the parent-owned instructions.",
    })
    nodes.extend([
        {"id": "glue", "label": "main parent-owned glue", "kind": "parentGlue",
         "column": 1, "status": "proof_not_started", "proofStatus": "not_started",
         "phase": "level0-glue", "instructionCount": len(glue_pcs),
         "provedInstructionCount": 0},
        {"id": "assembly", "label": "Level 1 contract assembly", "kind": "conversion",
         "column": 2, "status": "proof_not_started", "proofStatus": "not_started"},
        {"id": "root", "label": "MainComplianceStatement", "kind": "parent",
         "column": 3, "status": "proof_not_started", "proofStatus": "not_started"},
    ])
    edges.extend([
        {"source": "glue", "target": "assembly", "kind": "dependency"},
        {"source": "assembly", "target": "root", "kind": "dependency"},
    ])
    return {
        "schemaVersion": 2,
        "target": flame["machineRegionInputs"]["target"],
        "targetModel": {"status": "valid_bare_metal", "reason": "Pinned RV64IM ELF"},
        "artifact": cfg["artifact"],
        "instructions": [], "blocks": [], "boundaries": boundaries, "manifests": [],
        "formalCoverage": {
            "directPcCount": 0, "boundaryRegionPcCount": len(selected & set(main["pcs"])),
            "conditionalContractPcCount": 0, "endpointPcCount": flame["uniqueProgramTotal"],
        },
        "compilerProvenance": {"state": "same-ELF DWARF"},
        "phases": [{"id": "level0-glue", "label": "main parent-owned glue", "pcs": glue_pcs}],
        "authoringRegions": regions,
        "flameProgress": {"states": flame_states},
        "refinementGraph": {"nodes": nodes, "edges": edges},
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    for name in ("cfg", "flame", "manifest", "evidence", "bindings", "progress", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--flame-progress-output", type=Path)
    args = parser.parse_args()
    documents = [json.loads(getattr(args, name).read_text())
                 for name in ("cfg", "flame", "manifest", "evidence", "bindings", "progress")]
    result = build(*documents)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    if args.flame_progress_output:
        args.flame_progress_output.write_text(
            json.dumps(result["flameProgress"], sort_keys=True, separators=(",", ":")) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
