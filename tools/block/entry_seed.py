"""Read a symbolic input state from explicit entry resources or JSON data.

This is a source parser, not a proof checker. Opaque resources remain opaque.
"""
import re

from symbolic_state import Expr, MemoryRegion, SymbolicState, input_expr


def _code_mask(source, *, mask_strings=True):
    result, index, comments, string = list(source), 0, 0, False
    while index < len(source):
        if comments:
            if source.startswith("(*", index):
                comments += 1
            elif source.startswith("*)", index):
                comments -= 1
            else:
                result[index] = "\n" if source[index] == "\n" else " "
                index += 1
                continue
            result[index:index + 2] = "  "
            index += 2
        elif string:
            if mask_strings:
                result[index] = "\n" if source[index] == "\n" else " "
            if source[index] == '"':
                if source.startswith('""', index):
                    if mask_strings:
                        result[index:index + 2] = "  "
                    index += 2
                    continue
                string = False
            index += 1
        elif source.startswith("(*", index):
            result[index:index + 2] = "  "
            comments = 1
            index += 2
        else:
            if source[index] == '"':
                if mask_strings:
                    result[index] = " "
                string = True
            index += 1
    if comments or string:
        raise ValueError("The entry source has an unterminated comment or string.")
    return "".join(result)


def definition_body(source, declaration):
    mask = _code_mask(source)
    matches = list(re.finditer(r"\bDefinition\s+" + re.escape(declaration) + r"\b", mask))
    if len(matches) != 1:
        raise ValueError("The source must contain one entry resource definition.")
    depth, body_start = 0, None
    for index in range(matches[0].end(), len(mask)):
        char = mask[index]
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif depth == 0 and body_start is None and mask.startswith(":=", index):
            body_start = index + 2
        elif char == "." and depth == 0 and (index + 1 == len(mask) or mask[index + 1].isspace()):
            if body_start is None:
                break
            return source[body_start:index].strip()
    raise ValueError("The entry resource definition has no complete body.")


def resource_term(text, start):
    """Read through a separating conjunction without splitting nested terms."""
    depth = 0
    for index in range(start, len(text)):
        char = text[index]
        if char in "([{":
            depth += 1
        elif char in ")]}":
            if depth == 0:
                return text[start:index].strip()
            depth -= 1
        elif char == "∗" and depth == 0:
            return text[start:index].strip()
    return text[start:].strip()


def seed_from_resources(body, *, register_width=64, address_width=64):
    """Extract explicit register and byte-array resources; report opaque data."""
    if register_width <= 0 or address_width <= 0:
        raise ValueError("The input widths must be positive.")
    body = _code_mask(body, mask_strings=False)
    state = SymbolicState()
    for match in re.finditer(r'"([^"\n]+)"\s*↦ᵣ\s*RVal_Bits\s+', body):
        name = match.group(1)
        if name in state.registers:
            raise ValueError("The entry repeats a register resource: " + name)
        value = resource_term(body, match.end())
        if not value:
            raise ValueError("The register resource has no value.")
        state.registers[name] = input_expr(value, register_width)
    for match in re.finditer(r'([^∗]+?)\s*↦ₘ∗\s*', body):
        address = match.group(1).strip()
        value = resource_term(body, match.end())
        if not address or not value:
            raise ValueError("The byte-array resource has no address or value.")
        state.memory.append(MemoryRegion(
            input_expr(f"(Z_to_bv {address_width} ({address}))", address_width),
            byte_array=input_expr(value, None),
            length=input_expr(f"(List.length ({value}))", None)))
    if not state.registers:
        raise ValueError("The entry has no explicit register resources.")
    state.reports.append({"kind": "source_entry_seed", "opaque_resources_retained": True,
                          "symbolic_array_bounds": True})
    return state


def state_from_json(value):
    allowed = {"schema", "registers", "memory", "writes", "conditions", "reports",
               "endianness", "trace_count", "retained_registers"}
    if not isinstance(value, dict) or set(value) - allowed:
        raise ValueError("The input state has unsupported fields.")
    if value.get("writes") or value.get("trace_count", 0) or value.get("retained_registers"):
        raise ValueError("An initial state cannot contain an execution history.")
    registers = value.get("registers", {})
    if not isinstance(registers, dict) or not all(isinstance(k, str) for k in registers):
        raise ValueError("The input registers must be a named record.")
    memory = []
    for region in value.get("memory", []):
        if not isinstance(region, dict) or set(region) - {"base", "bytes", "byte_array", "length", "uninitialized",
                                                         "ownership_id", "minimum_length"}:
            raise ValueError("The input memory region has unsupported fields.")
        length = region.get("length")
        if isinstance(length, dict):
            length = Expr.from_dict(length)
        memory.append(MemoryRegion(Expr.from_dict(region["base"]),
            tuple(Expr.from_dict(item) for item in region.get("bytes", [])),
            Expr.from_dict(region["byte_array"]) if "byte_array" in region else None, length,
            region.get("uninitialized", False), region.get("ownership_id"), region.get("minimum_length", 0)))
    return SymbolicState({k: Expr.from_dict(v) for k, v in registers.items()}, memory,
                         [Expr.from_dict(v) for v in value.get("conditions", [])],
                         list(value.get("reports", [])),
                         endianness=value.get("endianness", "little"))
