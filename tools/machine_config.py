#!/usr/bin/env python3
"""Generate Sail settings from the reviewed Coq MachineMap instance."""

from __future__ import annotations

import argparse
import json
import re
import tomllib
from pathlib import Path


DEFAULT_FIELDS = {
    "rv_enable_writable_misa": "mapEnableWritableMisa",
    "rv_enable_rvc": "mapEnableRvc",
    "rv_enable_fdext": "mapEnableFdext",
    "rv_enable_pmp": "mapEnablePmp",
    "rv_enable_dirty_update": "mapEnableDirtyUpdate",
    "rv_enable_misaligned_access": "mapEnableMisalignedAccess",
    "rv_mtval_has_illegal_inst_bits": "mapMtvalHasIllegalInstBits",
    "rv_ram_base": "mapRamBase",
    "rv_ram_size": "mapRamSize",
    "rv_rom_base": "mapRomBase",
    "rv_rom_size": "mapRomSize",
    "rv_clint_base": "mapClintBase",
    "rv_clint_size": "mapClintSize",
    "rv_htif_tohost": "mapHtifTohost",
    "rv_insns_per_tick": "mapInsnsPerTick",
}


def read_machine(source: str, instance: str = "defaultMap") -> dict:
    if instance == "forkMap":
        raise ValueError("The historical forkMap cannot configure the stock platform.")
    schema = re.search(r"Record MachineMap\s*:.*?\{(.*?)\}\.", source, re.S)
    record = re.search(
        r"Definition " + re.escape(instance) + r"\s*:\s*MachineMap\s*:=\s*\{\|(.*?)\|\}\.",
        source, re.S,
    )
    if schema is None or record is None:
        raise ValueError("The source must contain the MachineMap schema and instance.")
    types = dict(re.findall(r"(map\w+)\s*:\s*(option\s+Z|Z|bool|string)\b", schema.group(1)))
    fields = re.findall(r"(map\w+)\s*:=\s*([^;]+?)(?:;|$)", record.group(1))
    values = dict(fields)
    if set(types) != set(values) or len(fields) != len(values):
        raise ValueError("The MachineMap instance must define every field exactly once.")
    result = {}
    for field, kind in types.items():
        value = values[field].strip()
        if kind == "bool":
            if value not in {"true", "false"}:
                raise ValueError(f"The field {field} must contain a Boolean literal.")
            result[field] = value == "true"
        elif kind.startswith("option"):
            if value == "None":
                result[field] = None
            elif value.startswith("Some "):
                result[field] = int(value[5:].removesuffix("%Z").strip(), 0)
            else:
                raise ValueError(f"The field {field} must contain Some address or None.")
        elif kind == "string":
            result[field] = json.loads(value.removesuffix("%string"))
        else:
            result[field] = int(value, 0)
    validate_machine(result)
    return result


def validate_machine(machine: dict) -> None:
    base = machine["mapRamBase"]
    end = base + machine["mapRamSize"]
    if not 0 <= base < end <= 2**64:
        raise ValueError("The RAM range must fit the 64-bit address space.")
    for name in ["Rom", "Clint"]:
        start, size = machine[f"map{name}Base"], machine[f"map{name}Size"]
        if size < 0 or start < 0 or start + size > 2**64:
            raise ValueError(f"The {name} range must fit the address space.")
        if size and start < end and base < start + size:
            raise ValueError(f"The {name} window must not overlap RAM.")
    if base <= machine["mapHtifTohost"] < end:
        raise ValueError("The HTIF address must lie outside RAM.")
    heap_start, heap_end = machine["mapHeapBase"], machine["mapHeapEnd"]
    input_start = machine["mapInputBufferAddress"]
    input_end = input_start + machine["mapInputCapacity"]
    if not base <= heap_start < heap_end <= end:
        raise ValueError("The heap must fit RAM.")
    if not 0 <= input_start < input_end <= 2**64:
        raise ValueError("The input range must fit the 64-bit address space.")
    if input_start < end and base < input_end:
        raise ValueError("The read-only input range must not overlap writable RAM.")
    if not machine["mapZiskPlatform"]:
        raise ValueError("The production map must select the stock ZisK platform.")
    if any(machine[f"map{name}{field}"] for name in ["Rom", "Clint"]
           for field in ["Base", "Size"]) or machine["mapHtifTohost"]:
        raise ValueError("The stock platform must disable generic device windows.")
    if not machine["mapEnableMisalignedAccess"]:
        raise ValueError("The stock platform must permit misaligned accesses.")


def toml_value(value: object, hexadecimal: bool = True) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, str):
        return json.dumps(value)
    return f'"0x{value:016x}"' if hexadecimal else str(value)


def generate_config(template: str, machine: dict) -> str:
    validate_machine(machine)
    settings = tomllib.loads(template)
    dynamic = {"zisk_input_end", "zisk_free_input"}
    registers = settings.get("registers", {})
    for section in ["defaults", "reset"]:
        if dynamic.intersection(registers.get(section, {})):
            raise ValueError("The adapter input registers must remain dynamic.")
    if any(register in constraint for register in dynamic
           for constraints in settings.get("constraints", {}).values()
           for constraint in (constraints if isinstance(constraints, list) else [constraints])):
        raise ValueError("The adapter input registers must remain dynamic.")
    sections = dict(re.findall(r"(?ms)^\[([^\]]+)\]\n(.*?)(?=^\[|\Z)", template))
    defaults = sections["registers.defaults"]
    for setting, field in DEFAULT_FIELDS.items():
        value = toml_value(machine[field], setting != "rv_insns_per_tick")
        defaults, count = re.subn(r"(?m)^" + setting + r"\s*=.*$", setting + " = " + value, defaults)
        if count != 1:
            raise ValueError(f"The template must define {setting} exactly once.")
    result = template.replace(sections["registers.defaults"], defaults, 1)
    reset = sections["registers.reset"]
    for setting, field in [("misa.bits", "mapMisa"), ("mtvec.bits", "mapMtvec"), ("cur_privilege", "mapPrivilege")]:
        key = setting if setting == "cur_privilege" else json.dumps(setting)
        reset, count = re.subn(r"(?m)^" + re.escape(key) + r"\s*=.*$", key + " = " + toml_value(machine[field]), reset)
        if count != 1:
            raise ValueError(f"The template must define {setting} exactly once.")
    result = result.replace(sections["registers.reset"], reset, 1)
    mask, value = machine["mapMstatusMask"], machine["mapMstatusValue"]
    result, count = re.subn(
        r"= \(bvand mstatus\.bits 0x[0-9a-fA-F]+\) 0x[0-9a-fA-F]+",
        f"= (bvand mstatus.bits 0x{mask:016x}) 0x{value:016x}", result,
    )
    if count != 1:
        raise ValueError("The template must define the mstatus constraint exactly once.")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=Path("ZesuSsz/Contracts/Machine.v"))
    parser.add_argument("--instance", default="defaultMap")
    parser.add_argument("--config", type=Path, default=Path("ZesuSsz/riscv64_zesu.toml"))
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    machine = read_machine(args.source.read_text(), args.instance)
    if args.json:
        print(json.dumps(machine, sort_keys=True, indent=2))
        return 0
    original = args.config.read_text()
    generated = generate_config(original, machine)
    if args.check:
        if generated != original:
            parser.error("The Sail configuration differs from the MachineMap instance.")
    else:
        args.config.write_text(generated)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
