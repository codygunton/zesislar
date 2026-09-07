#!/usr/bin/env python3
"""Generate paired operational segment proofs for supported writeSuccess traces."""

import argparse
import re
from pathlib import Path


MEMCPY_BYTE_PCS = [0x101D8, 0x101E0, 0x101E4, 0x101E8, 0x101EC, 0x101F0, 0x101F4]
OUTPUT_PCS = [0x10190, 0x10194, 0x10198, 0x1019C, 0x101A0]
INTEGER_PCS = [0x15D10, 0x15D14, 0x15D18, 0x15D1C, 0x15D20, 0x15D24, 0x15D28] + OUTPUT_PCS + [0x15D2C, 0x15D30, 0x15D34]
MEMCPY_PCS = [0x101D4] + MEMCPY_BYTE_PCS * 48 + [0x101D8, 0x101DC]
ITERATION_PCS = (
    [0x15694, 0x15698, 0x1569C, 0x156A0, 0x156A4]
    + MEMCPY_PCS
    + [0x156A8, 0x156AC, 0x156B0]
    + INTEGER_PCS
    + [0x156B4, 0x156B8, 0x156BC]
    + INTEGER_PCS
    + [0x156C0, 0x156C4, 0x156C8, 0x156CC]
    + OUTPUT_PCS
    + [0x156D0, 0x156D4, 0x156D8]
    + INTEGER_PCS
    + [0x156DC, 0x156E0, 0x156E4]
)

CONST_WRITE = re.compile(
    r'WriteReg "(?P<register>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Bits \(BV 64%N 0x(?P<constant>[0-9a-f]+)%Z\)\)\) '
    r'Mk_annot :t:\s*WriteReg "PC"',
    re.MULTILINE,
)

REGISTER_ADD = re.compile(
    r'ReadReg "(?P<source>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Symbolic 5%Z\)\) Mk_annot :t:.*?'
    r'Val \(Val_Symbolic 5%Z\) Mk_annot; '
    r'Val \(Val_Bits \(BV 64%N 0x(?P<addend>[0-9a-f]+)%Z\)\) Mk_annot.*?'
    r'WriteReg "(?P<destination>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Symbolic 6%Z\)\)',
    re.DOTALL,
)

PC_ADD_WRITE = re.compile(
    r'DefineConst 5%Z \(Manyop \(Bvmanyarith Bvadd\) '
    r'\[Val \(Val_Symbolic 3%Z\) Mk_annot; '
    r'Val \(Val_Bits \(BV 64%N 0x(?P<addend>[0-9a-f]+)%Z\)\) Mk_annot\].*?'
    r'WriteReg "(?P<destination>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Symbolic 5%Z\)\)',
    re.DOTALL,
)


def trace_path(trace_root: Path, pc: int) -> Path:
    matches = sorted(trace_root.glob(f"write_success_*/a{pc:x}.v"))
    matches = [path for path in matches if "monolithic" not in path.parent.name]
    if len(matches) != 1:
        raise ValueError(f"expected one pinned trace for 0x{pc:x}, found {len(matches)}")
    return matches[0]


def constant_write_metadata(trace_root: Path, pc: int) -> tuple[Path, str, int]:
    path = trace_path(trace_root, pc)
    source = path.read_text()
    constructors = [
        line.strip().split(" ", 1)[0]
        for line in source.splitlines()
        if ":t:" in line
    ]
    if constructors != ["Smt", "Assume", "Smt", "ReadReg", "Smt", "WriteReg", "WriteReg"]:
        raise ValueError(f"unsupported trace shape at 0x{pc:x}: {constructors}")
    match = CONST_WRITE.search(source)
    if match is None:
        raise ValueError(f"unsupported constant-write trace at 0x{pc:x}")
    return path, match.group("register"), int(match.group("constant"), 16)


def register_add_metadata(trace_root: Path, pc: int) -> tuple[Path, str, str, int]:
    path = trace_path(trace_root, pc)
    source = path.read_text()
    constructors = [
        line.strip().split(" ", 1)[0]
        for line in source.splitlines()
        if ":t:" in line
    ]
    expected = [
        "Smt", "Assume", "Smt", "ReadReg", "Smt", "Smt", "ReadReg",
        "Smt", "WriteReg", "WriteReg",
    ]
    if constructors != expected:
        raise ValueError(f"unsupported trace shape at 0x{pc:x}: {constructors}")
    match = REGISTER_ADD.search(source)
    if match is None:
        raise ValueError(f"unsupported register-add trace at 0x{pc:x}")
    return (
        path,
        match.group("source"),
        match.group("destination"),
        int(match.group("addend"), 16),
    )


def pc_add_write_metadata(trace_root: Path, pc: int) -> tuple[Path, str, int]:
    path = trace_path(trace_root, pc)
    source = path.read_text()
    constructors = [
        line.strip().split(" ", 1)[0]
        for line in source.splitlines()
        if ":t:" in line
    ]
    expected = ["Smt", "Assume", "Smt", "ReadReg", "Smt", "Smt", "WriteReg", "WriteReg"]
    if constructors != expected:
        raise ValueError(f"unsupported trace shape at 0x{pc:x}: {constructors}")
    match = PC_ADD_WRITE.search(source)
    if match is None:
        raise ValueError(f"unsupported PC-add-write trace at 0x{pc:x}")
    return path, match.group("destination"), int(match.group("addend"), 16)


def render_constant_write(template: Path, trace_root: Path, pc: int) -> str:
    if pc not in ITERATION_PCS:
        raise ValueError(f"0x{pc:x} is not in the 410-PC withdrawals iteration")
    next_pc = pc + 4
    source_path, register, constant = constant_write_metadata(trace_root, pc)
    next_path = trace_path(trace_root, next_pc)
    text = template.read_text()
    replacements = [
        ("IslaTraces.write_success_90.a15698", f"IslaTraces.{source_path.parent.name}.a{pc:x}"),
        ("IslaTraces.write_success_90.a1569c", f"IslaTraces.{next_path.parent.name}.a{next_pc:x}"),
        ("15698", f"{pc:x}"),
        ("1569c", f"{next_pc:x}"),
        ('"x12"', f'"{register}"'),
        ("oldX12", "old" + register.upper()),
        ("BV 64 48", f"BV 64 {constant}"),
    ]
    for old, new in replacements:
        text = text.replace(old, new)
    return text


def render_register_add(template: Path, trace_root: Path, pc: int) -> str:
    if pc not in ITERATION_PCS:
        raise ValueError(f"0x{pc:x} is not in the 410-PC withdrawals iteration")
    next_pc = pc + 4
    source_path, source_register, destination_register, addend = (
        register_add_metadata(trace_root, pc)
    )
    next_path = trace_path(trace_root, next_pc)
    text = template.read_text()
    replacements = [
        ("IslaTraces.write_success_90.a15694", f"IslaTraces.{source_path.parent.name}.a{pc:x}"),
        ("IslaTraces.write_success_90.a15698", f"IslaTraces.{next_path.parent.name}.a{next_pc:x}"),
        ("15694", f"{pc:x}"),
        ("15698", f"{next_pc:x}"),
        ('"x2"', f'"{source_register}"'),
        ('"x10"', f'"{destination_register}"'),
        ("oldX10", "old" + destination_register.upper()),
        ("BV 64 1744", f"BV 64 {addend}"),
    ]
    for old, new in replacements:
        text = text.replace(old, new)
    return text


def render_pc_add_write(template: Path, trace_root: Path, pc: int) -> str:
    if pc not in ITERATION_PCS:
        raise ValueError(f"0x{pc:x} is not in the 410-PC withdrawals iteration")
    next_pc = pc + 4
    source_path, destination_register, addend = pc_add_write_metadata(trace_root, pc)
    next_path = trace_path(trace_root, next_pc)
    text = template.read_text()
    replacements = [
        ("IslaTraces.write_success_90.a156a0", f"IslaTraces.{source_path.parent.name}.a{pc:x}"),
        ("IslaTraces.write_success_90.a156a4", f"IslaTraces.{next_path.parent.name}.a{next_pc:x}"),
        ("156a0", f"{pc:x}"),
        ("156a4", f"{next_pc:x}"),
        ('"x1"', f'"{destination_register}"'),
        ("oldX1", "old" + destination_register.upper()),
        ("BV 64 0xffffffffffffb000", f"BV 64 {addend}"),
    ]
    for old, new in replacements:
        text = text.replace(old, new)
    return text


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pc", required=True, type=lambda value: int(value, 0))
    parser.add_argument("--trace-root", required=True, type=Path)
    parser.add_argument("--template", required=True, type=Path)
    parser.add_argument(
        "--shape", choices=("constant-write", "register-add", "pc-add-write"),
        default="constant-write",
    )
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.shape == "constant-write":
        rendered = render_constant_write(args.template, args.trace_root, args.pc)
    elif args.shape == "register-add":
        rendered = render_register_add(args.template, args.trace_root, args.pc)
    else:
        rendered = render_pc_add_write(args.template, args.trace_root, args.pc)
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            raise SystemExit(f"generated segment differs: {args.output}")
    else:
        args.output.write_text(rendered)


if __name__ == "__main__":
    main()
