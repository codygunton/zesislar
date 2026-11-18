"""Project authenticated witness data by source indices and source names.

The producer authenticates the full values and the resolved slots.
This module binds that metadata and selects existing tuple fields.
It does not infer slot names from runtime types or select new values.
"""

import hashlib
from pathlib import Path

from render_support import identifier
from source_witness_bindings import bound_json, pointer
from witness_data import (
    _source_declaration,
    check_witness_shape,
    declared_witness_slots,
    product,
    value_spine,
)


def _record(binding):
    if set(binding) != {"path", "sha256", "pointer"}:
        raise ValueError("A phase record needs an exact file and pointer.")
    return pointer(bound_json({k: binding[k] for k in ("path", "sha256")}),
                   binding["pointer"])


def project_witness_phase(full_metadata, phase_metadata, *, value_name="full_values"):
    """Return a typed tuple projection. Emit no proof script."""
    full = _record(full_metadata)
    if set(full) != {"schema", "source_declaration", "target_declaration",
                     "mapping_fragment", "slots"}:
        raise ValueError("The full witness metadata has unsupported fields.")
    if full["schema"] != "source.full-witness-mapping.v1":
        raise ValueError("The full witness metadata has an unsupported schema.")
    if full["source_declaration"] == full["target_declaration"]:
        raise ValueError("Target-only provenance cannot authenticate a phase.")
    for declaration in (full["source_declaration"], full["target_declaration"]):
        _source_declaration(declaration)
    target = full["target_declaration"]
    layout = declared_witness_slots(Path(target["path"]).read_text(),
                                    target["declaration"])
    slots = full["slots"]
    check_witness_shape(layout["declared"], slots)
    vacuous = {slot["name"] for slot in layout["vacuous"]}
    for slot in slots:
        if set(slot) != {"name", "type", "vacuous"}:
            raise ValueError("A full witness slot needs its exact metadata.")
        if type(slot["vacuous"]) is not bool or slot["vacuous"] != (slot["name"] in vacuous):
            raise ValueError("A vacuous flag differs from the source body.")
    fragment = full["mapping_fragment"]
    if set(fragment) != {"path", "sha256"}:
        raise ValueError("The mapping fragment needs its exact file binding.")
    if hashlib.sha256(Path(fragment["path"]).read_bytes()).hexdigest() != fragment["sha256"]:
        raise ValueError("The full mapping fragment changed.")
    phase = _record(phase_metadata)
    if set(phase) != {"schema", "full_metadata", "retained", "resolved"}:
        raise ValueError("The phase needs retained and resolved source slots.")
    if phase["schema"] != "source.witness-phase.v1" or phase["full_metadata"] != full_metadata:
        raise ValueError("The phase belongs to another full witness mapping.")
    groups = {}
    for role in ("retained", "resolved"):
        indices = []
        for selection in phase[role]:
            if set(selection) != {"source_index", "name"}:
                raise ValueError("A phase slot needs its source index and name.")
            index = selection["source_index"]
            if type(index) is not int or not 0 <= index < len(slots):
                raise ValueError("The phase source index is invalid.")
            if selection["name"] != slots[index]["name"]:
                raise ValueError("The phase source name differs from its index.")
            indices.append(index)
        if indices != sorted(set(indices)):
            raise ValueError("The phase changes source order or repeats a slot.")
        groups[role] = indices
    retained, resolved = groups["retained"], groups["resolved"]
    if not retained or sorted(retained + resolved) != list(range(len(slots))):
        raise ValueError("The phase omits or duplicates a full witness slot.")
    if any(slots[index]["vacuous"] for index in resolved):
        raise ValueError("The runtime phase must retain every vacuous slot.")
    name = identifier(value_name, "phase tuple parameter")
    terms = []
    for index in retained:
        term = name
        for _ in range(index):
            term = "(snd " + term + ")"
        terms.append("(fst " + term + ")")
    selected = [slots[index] for index in retained]
    full_type = product([slot["type"] for slot in slots])
    phase_type = product([slot["type"] for slot in selected])
    return {"full_type": full_type, "phase_type": phase_type,
            "projection": "(fun " + name + " : " + full_type + " => " + value_spine(terms) + ")",
            "source_indices": retained, "slots": selected,
            "internal_order": list(reversed(selected)),
            "full_metadata": full_metadata, "phase_metadata": phase_metadata,
            "proof_scripts_emitted": False, "values_inferred_from_types": False}
