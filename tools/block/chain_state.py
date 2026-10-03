"""Normalize native successor captures without adding owned resources."""

from __future__ import annotations

from copy import deepcopy
import json
import re
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "det"))
import gen_boundary  # noqa: E402


def _mentions(text: str, name: str) -> bool:
    return re.search(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])", text) is not None


def _prune_locals(coq, spatial, binders, sorts, provenance):
    """Keep locals referenced by ownership, parameters, or provenance."""
    locals_, _ = gen_boundary.local_parts(
        gen_boundary.free_locals(coq, binders), sorts, True)
    kinds = dict(locals_)
    roots = " ".join(spatial) + " " + binders + " " + json.dumps(provenance)
    live = {name for name in kinds if _mentions(roots, name)}
    parameters = set(gen_boundary.explicit_arguments(binders).split())
    facts = [kind for name, kind in coq if sorts.get(name) == "Prop"]
    while True:
        required_facts = [fact for fact in facts
                          if re.search(r"[<>≤≥]", fact)
                          or any(_mentions(fact, name) for name in live | parameters)]
        referenced = " ".join([*(kinds[name] for name in live), *required_facts])
        expanded = live | {name for name in kinds if _mentions(referenced, name)}
        if expanded == live:
            break
        live = expanded
    unused = set(kinds) - live
    return [(name, kind) for name, kind in coq
            if name not in unused and not any(_mentions(kind, local) for local in unused)]


def normalize_successor(capture: dict, *, entry: int | str, binders: str,
                        name: str, imports=(), provenance=None) -> dict:
    """Return a state record from an actual predecessor capture.

    The caller must validate native provenance before using this adapter.
    The original capture remains unchanged. Code hypotheses stay in capture
    metadata; every other persistent resource stays in the boundary.
    """
    state = deepcopy(capture)
    outcome = state.get("outcome", "reached")
    if outcome not in {"reached", "unreachable-successor"}:
        raise ValueError(f"successor was not reached: {outcome}")
    if "stack_size" in state:
        raise ValueError("chain states cannot manufacture stack resources")
    if "context" in state:
        coq, persistent, spatial = gen_boundary.sections(state["context"])
    else:
        coq = [tuple(item) for item in state.get("coq", [])]
        persistent = state.get("persistent", [])
        spatial = state.get("spatial", [])
    persistent_resources = [atom for atom in persistent
                            if not re.match(r"^(?:instr|instr_pre|instr_body)\s", atom)]
    spatial = gen_boundary.normalize_temporaries(
        [atom for body in [*spatial, *persistent_resources]
         for atom in gen_boundary.spatial_atoms(body)])
    sorts = state.get("local_sorts", state.get("sorts", {}))
    provenance = deepcopy(provenance if provenance is not None
                          else state.get("provenance", {}))
    coq = _prune_locals(coq, spatial, binders, sorts, provenance)
    state.update(entry=entry, state_entry=entry, name=name, binders=binders,
                 outcome=outcome, coq=coq, spatial=spatial,
                 persistent=deepcopy(persistent), provenance=provenance,
                 imports=list(dict.fromkeys([*state.get("imports", []), *imports])),
                 complete_registers=False, preserve_post_register_precision=True)
    # Generation must use the normalized data rather than reparsing the capture.
    state.pop("context", None)
    return state


def normalize_captured_literals(atoms: list[str], memory_widths: dict[str, int],
                                trace_widths: dict[str, int]) -> list[str]:
    """Restore the captured bit width that Rocq omits from word numerals."""
    def ungroup(address: str) -> str:
        while address.startswith("(") and address.endswith(")"):
            depth = 0
            for index, character in enumerate(address):
                depth += (character == "(") - (character == ")")
                if depth == 0:
                    break
            if index != len(address) - 1:
                break
            address = address[1:-1].strip()
        return address

    def captured_width(address: str, widths: dict[str, int]) -> int | None:
        return next((width for key, width in widths.items()
                     if ungroup(key) == ungroup(address)), None)

    normalized = []
    for atom in atoms:
        for event in reversed(list(re.finditer(r"SWriteMem\s+", atom))):
            start = event.end()
            end = start
            if atom[start] == "(":
                depth = 1
                end += 1
                while depth and end < len(atom):
                    depth += (atom[end] == "(") - (atom[end] == ")")
                    end += 1
            else:
                while end < len(atom) and not atom[end].isspace():
                    end += 1
            value = re.match(r"\s+(\d+)%bv\b", atom[end:])
            if value is not None:
                address = atom[start:end]
                width = captured_width(address, trace_widths)
                if not isinstance(width, int) or width <= 0:
                    raise ValueError(f"missing captured bit width for write event: {address}")
                atom = (atom[:end] + f" (BV {width} {value.group(1)})"
                        + atom[end + value.end():])
        array = re.fullmatch(r"(.+?)\s*↦ₘ∗\s*(\[[^\[\]]*\])", atom)
        if array is not None and re.search(r"\d+%bv\b(?!\s*:\s*bv\s+\d+\b)", array.group(2)):
            address, values = array.groups()
            width = captured_width(address, memory_widths)
            if not isinstance(width, int) or width <= 0:
                raise ValueError(f"missing captured bit width for memory array: {atom}")
            values = re.sub(r"(\d+)%bv\b(?!\s*:\s*bv\s+\d+\b)", lambda value:
                            f"(BV {width} {value.group(1)})", values)
            atom = f"{address} ↦ₘ∗ {values}"
        match = re.fullmatch(r"(.+?)\s*↦ₘ\s*(\d+)(?:%bv)?", atom)
        if match is None:
            normalized.append(atom)
            continue
        address, value = match.groups()
        width = captured_width(address, memory_widths)
        if not isinstance(width, int) or width <= 0:
            raise ValueError(f"missing captured bit width for memory word: {atom}")
        normalized.append(f"{address} ↦ₘ (BV {width} {value})")
    return normalized



def render_successor(state: dict) -> str:
    """Render the recorded resources; do not complete or weaken registers."""
    imports = ["ZesuSsz.Automation.All", "ZesuSsz.Automation.SealedCoverage",
               "isla.riscv64.riscv64", *state.get("imports", [])]
    header = "\n".join(f"Require Import {module}." for module in dict.fromkeys(imports))
    if state.get("outcome") == "unreachable-successor":
        body = (f'Definition {state["name"]} {state["binders"]} : iProp Sigma := False%I.\n')
    elif state.get("outcome", "reached") == "reached":
        body = gen_boundary.boundary_source(
            state["name"], state["binders"], state.get("coq", []),
            normalize_captured_literals(state["spatial"],
                                        state.get("memory_word_widths", {}),
                                        state.get("trace_value_widths", {})),
            seal=state.get("seal_memory", False),
            call_resources=state.get("call_resources", False),
            sorts=state.get("local_sorts", state.get("sorts", {})))
    else:
        raise ValueError("cannot render an unreached successor")
    return "(* Native successor capture; no resources added. *)\n" + header + "\n\n" + body
