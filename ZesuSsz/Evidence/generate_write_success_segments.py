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

INDIRECT_JUMP = re.compile(
    r'ReadReg "(?P<base>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Symbolic 3%Z\)\).*?'
    r'Val \(Val_Symbolic 3%Z\) Mk_annot; '
    r'Val \(Val_Bits \(BV 64%N 0x(?P<offset>[0-9a-f]+)%Z\)\) Mk_annot.*?'
    r'WriteReg "(?P<link>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Symbolic 5%Z\)\).*?'
    r'WriteReg "PC" \[\] \(RegVal_Base \(Val_Symbolic 7%Z\)\)',
    re.DOTALL,
)

CONDITIONAL_BRANCH = re.compile(
    r'ReadReg "(?P<left>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Symbolic 5%Z\)\).*?'
    r'ReadReg "(?P<right>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Symbolic 6%Z\)\).*?'
    r'tcases \[.*?BranchAddress .*?WriteReg "PC".*?;.*?WriteReg "PC"',
    re.DOTALL,
)

DIRECT_JUMP = re.compile(
    r'DefineConst 5%Z .*?Val \(Val_Symbolic 3%Z\) Mk_annot; '
    r'Val \(Val_Bits \(BV 64%N 0x(?P<offset>[0-9a-f]+)%Z\)\) Mk_annot.*?'
    r'WriteReg "PC"',
    re.DOTALL,
)

TWO_REGISTER_ADD = re.compile(
    r'ReadReg "(?P<left>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Symbolic 5%Z\)\).*?'
    r'ReadReg "(?P<right>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Symbolic 6%Z\)\).*?'
    r'DefineConst 7%Z \(Manyop \(Bvmanyarith Bvadd\).*?'
    r'WriteReg "(?P<destination>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Symbolic 7%Z\)\)',
    re.DOTALL,
)

MEMORY_WRITE_BYTE = re.compile(
    r'ReadReg "(?P<base>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Symbolic 3%Z\)\).*?'
    r'ReadReg "(?P<value>x[0-9]+)" \[\] '
    r'\(RegVal_Base \(Val_Symbolic 18%Z\)\).*?'
    r'WriteMem .*?\(RegVal_Base \(Val_Symbolic 6%Z\)\) '
    r'\(RegVal_Base \(Val_Symbolic 19%Z\)\) 1%N None',
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


def indirect_jump_metadata(trace_root: Path, pc: int) -> tuple[Path, str, str, int]:
    path = trace_path(trace_root, pc)
    source = path.read_text()
    constructors = [
        line.strip().split(" ", 1)[0]
        for line in source.splitlines()
        if ":t:" in line
    ]
    expected = [
        "Smt", "Assume", "Smt", "Assume", "Smt", "ReadReg", "Smt",
        "ReadReg", "Smt", "Smt", "WriteReg", "WriteReg",
    ]
    if constructors != expected:
        raise ValueError(f"unsupported trace shape at 0x{pc:x}: {constructors}")
    match = INDIRECT_JUMP.search(source)
    if match is None:
        raise ValueError(f"unsupported indirect-jump trace at 0x{pc:x}")
    return (
        path,
        match.group("base"),
        match.group("link"),
        int(match.group("offset"), 16),
    )


def conditional_branch_metadata(trace_root: Path, pc: int) -> tuple[Path, str, str]:
    path = trace_path(trace_root, pc)
    source = path.read_text()
    constructors = [
        line.strip().split(" ", 1)[0]
        for line in source.splitlines()
        if ":t:" in line
    ]
    expected = [
        "Smt", "Assume", "Smt", "Assume", "ReadReg", "Smt", "Smt",
        "ReadReg", "Smt", "ReadReg", "Smt", "Smt", "Smt", "Smt",
        "BranchAddress", "WriteReg", "Smt", "WriteReg",
    ]
    if constructors != expected:
        raise ValueError(f"unsupported trace shape at 0x{pc:x}: {constructors}")
    match = CONDITIONAL_BRANCH.search(source)
    if match is None:
        raise ValueError(f"unsupported conditional-branch trace at 0x{pc:x}")
    return path, match.group("left"), match.group("right")


def direct_jump_metadata(trace_root: Path, pc: int) -> tuple[Path, int]:
    path = trace_path(trace_root, pc)
    source = path.read_text()
    constructors = [
        line.strip().split(" ", 1)[0]
        for line in source.splitlines()
        if ":t:" in line
    ]
    expected = [
        "Smt", "Assume", "Smt", "Assume", "ReadReg", "Smt", "Smt",
        "Smt", "WriteReg",
    ]
    if constructors != expected:
        raise ValueError(f"unsupported trace shape at 0x{pc:x}: {constructors}")
    match = DIRECT_JUMP.search(source)
    if match is None:
        raise ValueError(f"unsupported direct-jump trace at 0x{pc:x}")
    return path, int(match.group("offset"), 16)


def two_register_add_metadata(
    trace_root: Path, pc: int
) -> tuple[Path, str, str, str]:
    path = trace_path(trace_root, pc)
    source = path.read_text()
    constructors = [
        line.strip().split(" ", 1)[0]
        for line in source.splitlines()
        if ":t:" in line
    ]
    expected = [
        "Smt", "Assume", "Smt", "ReadReg", "Smt", "Smt", "ReadReg",
        "Smt", "ReadReg", "Smt", "WriteReg", "WriteReg",
    ]
    if constructors != expected:
        raise ValueError(f"unsupported trace shape at 0x{pc:x}: {constructors}")
    match = TWO_REGISTER_ADD.search(source)
    if match is None:
        raise ValueError(f"unsupported two-register-add trace at 0x{pc:x}")
    return (
        path,
        match.group("left"),
        match.group("right"),
        match.group("destination"),
    )


def render_generic_template(template: Path, replacements: dict[str, str]) -> str:
    if template.suffix != ".tmpl":
        raise ValueError("the renderer requires a generic template")
    text = template.read_text()
    if "__SOURCE_PC__" not in text:
        raise ValueError("generic template lacks the source-PC token")
    for old, new in replacements.items():
        text = text.replace(old, new)
    if re.search(r"__[A-Z_]+__", text):
        raise ValueError("generic template contains an unknown token")
    return text


def render_two_register_add(template: Path, trace_root: Path, pc: int) -> str:
    if pc not in ITERATION_PCS:
        raise ValueError(f"0x{pc:x} is not in the 410-PC withdrawals iteration")
    next_pc = pc + 4
    source_path, left, right, destination = two_register_add_metadata(trace_root, pc)
    next_path = trace_path(trace_root, next_pc)
    if source_path.parent != next_path.parent:
        raise ValueError(f"source and successor traces use different modules at 0x{pc:x}")
    replacements = {
        "__TRACE_MODULE__": source_path.parent.name,
        "__SOURCE_PC__": f"{pc:x}",
        "__NEXT_PC__": f"{next_pc:x}",
        "__LEFT_REGISTER__": left,
        "__RIGHT_REGISTER__": right,
        "__DEST_REGISTER__": destination,
        "__DEST_UPPER__": destination.upper(),
    }
    return render_generic_template(template, replacements)



def memory_read_long_metadata(trace_root: Path, pc: int) -> Path:
    path = trace_path(trace_root, pc)
    source = path.read_text()
    constructors = [
        line.strip().split(" ", 1)[0]
        for line in source.splitlines()
        if ":t:" in line
    ]
    expected = (
        ["AssumeReg"] * 10
        + ["Smt", "Assume", "Smt", "Assume", "Assume", "Smt",
           "ReadReg", "Smt", "ReadReg", "Smt", "ReadReg", "Smt",
           "ReadReg", "Smt", "Smt", "Smt", "ReadMem", "Smt",
           "WriteReg", "WriteReg"]
    )
    if constructors != expected:
        raise ValueError(f"unsupported long memory-read trace shape at 0x{pc:x}: {constructors}")
    required = [
        'ReadReg "x13" [] (RegVal_Base (Val_Symbolic 3%Z))',
        'ReadMem (RegVal_Base (Val_Symbolic 30%Z)) (RegVal_Poison) '
        '(RegVal_Base (Val_Symbolic 6%Z)) 1%N None',
        'WriteReg "x13" [] (RegVal_Base (Val_Symbolic 31%Z))',
    ]
    if any(fragment not in source for fragment in required):
        raise ValueError(f"unsupported long memory-read operands at 0x{pc:x}")
    return path


def memory_write_byte_metadata(
    trace_root: Path, pc: int
) -> tuple[Path, str, str]:
    path = trace_path(trace_root, pc)
    source = path.read_text()
    constructors = [
        line.strip().split(" ", 1)[0]
        for line in source.splitlines()
        if ":t:" in line
    ]
    expected = (
        ["AssumeReg"] * 10
        + ["Smt", "Assume", "Smt", "Assume", "Assume", "Smt",
           "ReadReg", "Smt", "ReadReg", "Smt", "ReadReg", "Smt",
           "ReadReg", "Smt", "ReadReg", "Smt", "Smt", "Smt", "Smt", "WriteMem",
           "WriteReg"]
    )
    if constructors != expected:
        raise ValueError(
            f"unsupported byte memory-write trace shape at 0x{pc:x}: {constructors}"
        )
    match = MEMORY_WRITE_BYTE.search(source)
    if match is None:
        raise ValueError(f"unsupported byte memory-write operands at 0x{pc:x}")
    return path, match.group("base"), match.group("value")


def render_memory_write_byte(template: Path, trace_root: Path, pc: int) -> str:
    if pc not in ITERATION_PCS:
        raise ValueError(f"0x{pc:x} is not in the 410-PC withdrawals iteration")
    path, base, value = memory_write_byte_metadata(trace_root, pc)
    next_pc = pc + 4
    next_path = trace_path(trace_root, next_pc)
    if path.parent != next_path.parent:
        raise ValueError(f"source and successor traces use different modules at 0x{pc:x}")
    return render_generic_template(template, {
        "__SOURCE_MODULE__": path.parent.name,
        "__SOURCE_PC__": f"{pc:x}",
        "__SOURCE_PC_UPPER__": f"{pc:X}",
        "__NEXT_PC__": f"{next_pc:x}",
        "__NEXT_PC_UPPER__": f"{next_pc:X}",
        "__BASE_REGISTER__": base,
        "__VALUE_REGISTER__": value,
    })


def render_memory_read_long(template: Path, trace_root: Path, pc: int) -> str:
    if pc not in ITERATION_PCS:
        raise ValueError(f"0x{pc:x} is not in the 410-PC withdrawals iteration")
    path = memory_read_long_metadata(trace_root, pc)
    next_pc = pc + 4
    next_path = trace_path(trace_root, next_pc)
    if path.parent != next_path.parent:
        raise ValueError(f"source and successor traces use different modules at 0x{pc:x}")
    return render_generic_template(template, {
        "__SOURCE_MODULE__": path.parent.name,
        "__SOURCE_PC__": f"{pc:x}",
        "__NEXT_PC__": f"{next_pc:x}",
    })


def check_generated_output(output: Path, rendered: str) -> None:
    if not output.is_file() or output.read_text() != rendered:
        raise ValueError(f"generated segment differs: {output}")


def render_constant_write(template: Path, trace_root: Path, pc: int) -> str:
    if pc not in ITERATION_PCS:
        raise ValueError(f"0x{pc:x} is not in the 410-PC withdrawals iteration")
    next_pc = pc + 4
    source_path, register, constant = constant_write_metadata(trace_root, pc)
    next_path = trace_path(trace_root, next_pc)
    return render_generic_template(template, {
        "__SOURCE_MODULE__": source_path.parent.name,
        "__NEXT_MODULE__": next_path.parent.name,
        "__SOURCE_PC__": f"{pc:x}",
        "__NEXT_PC__": f"{next_pc:x}",
        "__DEST_REGISTER__": register,
        "__DEST_UPPER__": register.upper(),
        "__CONSTANT__": str(constant),
    })


def render_register_add(template: Path, trace_root: Path, pc: int) -> str:
    if pc not in ITERATION_PCS:
        raise ValueError(f"0x{pc:x} is not in the 410-PC withdrawals iteration")
    next_pc = pc + 4
    source_path, source_register, destination_register, addend = (
        register_add_metadata(trace_root, pc)
    )
    next_path = trace_path(trace_root, next_pc)
    return render_generic_template(template, {
        "__SOURCE_MODULE__": source_path.parent.name,
        "__NEXT_MODULE__": next_path.parent.name,
        "__SOURCE_PC__": f"{pc:x}",
        "__NEXT_PC__": f"{next_pc:x}",
        "__SOURCE_REGISTER__": source_register,
        "__DEST_REGISTER__": destination_register,
        "__DEST_UPPER__": destination_register.upper(),
        "__ADDEND__": str(addend),
    })


def render_pc_add_write(template: Path, trace_root: Path, pc: int) -> str:
    if pc not in ITERATION_PCS:
        raise ValueError(f"0x{pc:x} is not in the 410-PC withdrawals iteration")
    next_pc = pc + 4
    source_path, destination_register, addend = pc_add_write_metadata(trace_root, pc)
    next_path = trace_path(trace_root, next_pc)
    return render_generic_template(template, {
        "__SOURCE_MODULE__": source_path.parent.name,
        "__NEXT_MODULE__": next_path.parent.name,
        "__SOURCE_PC__": f"{pc:x}",
        "__NEXT_PC__": f"{next_pc:x}",
        "__DEST_REGISTER__": destination_register,
        "__DEST_UPPER__": destination_register.upper(),
        "__ADDEND_HEX__": f"{addend:x}",
    })


def render_indirect_jump(template: Path, trace_root: Path, pc: int) -> str:
    path, base, link, offset = indirect_jump_metadata(trace_root, pc)
    if base != link:
        raise ValueError(f"unsupported indirect-jump operands at 0x{pc:x}")
    previous_pc = pc - 4
    _, destination, addend = pc_add_write_metadata(trace_root, previous_pc)
    if destination != base:
        raise ValueError(f"predecessor does not define the jump base at 0x{pc:x}")
    mask = (1 << 64) - 1
    return_address = (previous_pc + addend) & mask
    target_pc = ((return_address + offset) & mask) & ~1
    target_path = trace_path(trace_root, target_pc)
    return render_generic_template(template, {
        "__SOURCE_MODULE__": path.parent.name,
        "__TARGET_MODULE__": target_path.parent.name,
        "__SOURCE_PC__": f"{pc:x}",
        "__PREVIOUS_PC__": f"{previous_pc:x}",
        "__NEXT_PC__": f"{pc + 4:x}",
        "__TARGET_PC__": f"{target_pc:x}",
        "__RETURN_PC__": f"{return_address:x}",
        "__BASE_LINK_REGISTER__": base,
        "__OFFSET_HEX__": f"0x{offset:x}",
    })


def render_conditional_branch(template: Path, trace_root: Path, pc: int) -> str:
    if pc != 0x101D8:
        raise ValueError("the checked conditional-branch proof supports only 0x101d8")
    path, left, right = conditional_branch_metadata(trace_root, pc)
    if (path.parent.name, left, right) != ("write_success_02", "x15", "x12"):
        raise ValueError(f"unsupported conditional-branch operands at 0x{pc:x}")
    fallthrough_pc = 0x101DC
    taken_pc = 0x101F4
    fallthrough_path = trace_path(trace_root, fallthrough_pc)
    taken_path = trace_path(trace_root, taken_pc)
    return render_generic_template(template, {
        "__SOURCE_MODULE__": path.parent.name,
        "__FALLTHROUGH_MODULE__": fallthrough_path.parent.name,
        "__TAKEN_MODULE__": taken_path.parent.name,
        "__SOURCE_PC__": f"{pc:x}",
        "__FALLTHROUGH_PC__": f"{fallthrough_pc:x}",
        "__TAKEN_PC__": f"{taken_pc:x}",
        "__LEFT_REGISTER__": left,
        "__RIGHT_REGISTER__": right,
    })


def render_direct_jump(template: Path, trace_root: Path, pc: int) -> str:
    if pc != 0x101F4:
        raise ValueError("the checked direct-jump proof supports only 0x101f4")
    path, offset = direct_jump_metadata(trace_root, pc)
    if (path.parent.name, offset) != ("write_success_02", 0xFFFFFFFFFFFFFFE4):
        raise ValueError(f"unsupported direct-jump target at 0x{pc:x}")
    target_pc = 0x101D8
    target_path = trace_path(trace_root, target_pc)
    return render_generic_template(template, {
        "__SOURCE_MODULE__": path.parent.name,
        "__TARGET_MODULE__": target_path.parent.name,
        "__SOURCE_PC__": f"{pc:x}",
        "__TARGET_PC__": f"{target_pc:x}",
        "__OFFSET_HEX__": f"0x{offset:x}",
    })


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pc", required=True, type=lambda value: int(value, 0))
    parser.add_argument("--trace-root", required=True, type=Path)
    parser.add_argument("--template", required=True, type=Path)
    parser.add_argument(
        "--shape", choices=(
            "constant-write", "register-add", "pc-add-write", "indirect-jump",
            "conditional-branch", "direct-jump", "two-register-add",
            "memory-read-long",
            "memory-write-byte",
        ),
        default="constant-write",
    )
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.shape == "constant-write":
        rendered = render_constant_write(args.template, args.trace_root, args.pc)
    elif args.shape == "register-add":
        rendered = render_register_add(args.template, args.trace_root, args.pc)
    elif args.shape == "pc-add-write":
        rendered = render_pc_add_write(args.template, args.trace_root, args.pc)
    elif args.shape == "indirect-jump":
        rendered = render_indirect_jump(args.template, args.trace_root, args.pc)
    elif args.shape == "conditional-branch":
        rendered = render_conditional_branch(
            args.template, args.trace_root, args.pc
        )
    elif args.shape == "direct-jump":
        rendered = render_direct_jump(args.template, args.trace_root, args.pc)
    elif args.shape == "memory-read-long":
        rendered = render_memory_read_long(args.template, args.trace_root, args.pc)
    elif args.shape == "memory-write-byte":
        rendered = render_memory_write_byte(args.template, args.trace_root, args.pc)
    else:
        rendered = render_two_register_add(args.template, args.trace_root, args.pc)
    if args.check:
        try:
            check_generated_output(args.output, rendered)
        except ValueError as error:
            raise SystemExit(str(error)) from error
    else:
        args.output.write_text(rendered)


if __name__ == "__main__":
    main()
