"""Seed values from source-bound register shapes without creating ownership."""
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re

from symbolic_state import Expr, SymbolicState, operation


@dataclass
class SystemShapeSeed:
    state: SymbolicState
    binders: list
    mask_equalities: list
    collection_ownership_id: str
    sources: list

    def to_dict(self):
        return {"state": self.state.to_dict(), "binders": self.binders,
                "mask_equalities": self.mask_equalities,
                "collection_ownership_id": self.collection_ownership_id,
                "collection_preserved": True, "created_ownership": [],
                "sources": self.sources}


def _sources(rows):
    if not isinstance(rows, list) or not rows:
        raise ValueError("A system shape needs source bindings.")
    for row in rows:
        path = Path(row["path"])
        if hashlib.sha256(path.read_bytes()).hexdigest() != row["sha256"]:
            raise ValueError("A system shape source hash differs.")
    return [dict(row) for row in rows]


def _expression(value):
    return value if isinstance(value, Expr) else Expr.from_dict(value)


def _typed(value, sort, width):
    if sort == "bits":
        if type(width) is not int or width <= 0 or value.width != width:
            raise ValueError("A system bitvector width differs.")
        if value.op not in {"bits", "input"}:
            raise ValueError("A system bitvector needs a source value or symbol.")
    elif sort == "bool":
        if width is not None or value.width is not None or value.op != "bool" or type(value.value) is not bool:
            raise ValueError("A system boolean has an invalid shape.")
    elif sort == "enum":
        if width is not None or value.width is not None or value.op != "enum" or not isinstance(value.value, str):
            raise ValueError("A system enumeration has an invalid shape.")
    else:
        raise ValueError("The system register sort is unsupported.")


def seed_system_shapes(state, rows, *, collection_ownership_id):
    """Return an initial value seed and obligations for its inherited collection.

    The caller supplies typed rows from the selected source map. This function
    checks their source hashes. The later native checker checks their meaning.
    """
    if not isinstance(collection_ownership_id, str) or not collection_ownership_id:
        raise ValueError("The system seed needs an inherited collection ID.")
    if state.trace_count or state.writes:
        raise ValueError("System shapes must seed an initial state.")
    result = state.copy()
    binders, equalities, sources = [], [], []
    keys, symbols = set(), set()
    for row in rows:
        key, shape = row["key"], row["shape"]
        if not isinstance(key, str) or not key or key in keys:
            raise ValueError("A system shape repeats or omits its register key.")
        keys.add(key)
        if shape not in {"exact", "mask", "bits"}:
            raise ValueError("The system register shape is unsupported.")
        if any(row.get(field, collection_ownership_id) != collection_ownership_id
               for field in ("collection_ownership_id", "ownership_id")):
            raise ValueError("A system shape names a different owned collection.")
        sources.extend(_sources(row.get("source_bindings")))
        sort, width = row.get("sort", "bits"), row.get("width")
        value = _expression(row["value"] if shape == "exact" else row["symbol"])
        _typed(value, sort, width)
        if key in result.registers and result.registers[key] != value:
            raise ValueError("A system shape conflicts with an existing register value.")
        if shape != "exact":
            if sort != "bits" or value.op != "input" or not isinstance(value.value, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", value.value):
                raise ValueError("A symbolic system shape needs a typed binder.")
            if value.value in symbols:
                raise ValueError("Two system shapes reuse one symbolic binder.")
            symbols.add(value.value)
            binder = dict(row.get("binder", {}))
            if binder.get("name", value.value) != value.value or binder.get("type", f"bv {width}") != f"bv {width}":
                raise ValueError("A system binder differs from its symbolic value.")
            binder.update(name=value.value, type=f"bv {width}", register=key,
                          collection_ownership_id=collection_ownership_id)
            binders.append(binder)
        result.registers[key] = value
        if shape == "mask":
            mask, expected = _expression(row["mask"]), _expression(row["expected"])
            _typed(mask, "bits", width)
            _typed(expected, "bits", width)
            condition = operation("=", operation("bvand", value, mask), expected)
            result.conditions.append(condition)
            equalities.append({"register": key, "condition": condition.to_dict(),
                               "source_bindings": [dict(r) for r in row["source_bindings"]]})
    result.reports.append({"kind": "source_system_shapes", "registers": sorted(keys),
                           "collection_ownership_id": collection_ownership_id,
                           "collection_preserved": True, "created_ownership": []})
    return SystemShapeSeed(result, binders, equalities, collection_ownership_id, sources)
