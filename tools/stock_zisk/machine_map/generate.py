#!/usr/bin/env python3
"""Instantiate the stock layout from verified ELF and platform metadata."""
import argparse
import hashlib
import json
import sys
from pathlib import Path

BEGIN = "(* BEGIN GENERATED STOCK MAP *)"
END = "(* END GENERATED STOCK MAP *)"


def load_sections(recipe):
    """Retain every ELF load extent, including zero-filled writable memory."""
    sections = []
    for segment in recipe['elf_layout']['segments']:
        if segment['p_type'] != 'PT_LOAD':
            continue
        base, size, file_size = (segment[key] for key in ['p_vaddr', 'p_memsz', 'p_filesz'])
        if not 0 <= file_size <= size or base < 0 or base + size > 1 << 64:
            raise ValueError('Invalid ELF load extent')
        flags = segment['p_flags']
        if flags & ~7:
            raise ValueError('Unsupported ELF load permissions')
        sections.append({'sectionBase': base, 'sectionEnd': base + size,
                         'sectionFileEnd': base + file_size,
                         'sectionReadable': bool(flags & 4),
                         'sectionWritable': bool(flags & 2),
                         'sectionExecutable': bool(flags & 1)})
    return sections


def section_literal(section):
    values = [f'{key} := {str(value).lower() if isinstance(value, bool) else hex(value)}'
              for key, value in section.items()]
    return '{| ' + '; '.join(values) + ' |}'


def render(recipe, audit, symbols):
    by_name = {}
    for row in symbols.splitlines():
        fields = row.split()
        if len(fields) >= 8 and fields[0][:-1].isdigit() and fields[0].endswith(":"):
            by_name[fields[7]] = int(fields[1], 16)
    # The selected layout has one execute-only segment and one read-only segment.
    text = next(s for s in audit["load_segments"] if s["flags"] == 1)
    rodata = next(s for s in audit["load_segments"] if s["flags"] == 4)
    c = audit["constants"]
    a = audit["symbols"]
    values = {
        "mapPopulatedSections": '[\n    ' + ';\n    '.join(
            section_literal(section) for section in load_sections(recipe)) + '\n  ]',
        "mapRamBase": c["RAM_ADDR"], "mapRamSize": c["RAM_SIZE"],
        "mapTextBase": text["start"], "mapTextEnd": text["end"],
        "mapRodataBase": rodata["start"], "mapRodataEnd": rodata["end"],
        "mapDataBase": min(s["start"] for s in audit["load_segments"] if s["flags"] == 6),
        "mapHeapBase": a["__zesu_heap_bottom"], "mapHeapEnd": a["__zesu_heap_top"],
        "mapInputBufferAddress": c["INPUT_ADDR"], "mapInputCapacity": c["MAX_INPUT_SIZE"],
        "mapIoContextAddress": "None",
        "mapStartPc": recipe["elf_layout"]["entry"],
        "mapReadInputPc": "Some " + hex(by_name["read_input"]) + "%Z",
        "mapWriteOutputPc": "Some " + hex(by_name["write_output"]) + "%Z",
        "mapZkvmExitPc": "None", "mapMemcpyPc": by_name["memcpy"],
        "mapMainPc": by_name["main"],
        "mapHeapTopAddress": a["ZKVM_HEAP_TOP"], "mapHeapPosAddress": a["ZKVM_HEAP_POS"],
        # These generic device windows are disabled in the selected platform.
        "mapRomBase": 0, "mapRomSize": 0, "mapClintBase": 0, "mapClintSize": 0,
        "mapHtifTohost": 0,
        "mapEnableWritableMisa": "true", "mapEnableRvc": "false",
        "mapEnableFdext": "false", "mapEnablePmp": "false",
        "mapEnableDirtyUpdate": "false", "mapEnableMisalignedAccess": "true",
        "mapMtvalHasIllegalInstBits": "false", "mapInsnsPerTick": 10,
        "mapZiskPlatform": "true", "mapPrivilege": '\"Machine\"%string',
        "mapMisa": 0x8000000000001100, "mapMtvec": 0,
        "mapMstatusMask": 0x20000, "mapMstatusValue": 0,
    }
    rows = [f"  {name} := {hex(value) if isinstance(value, int) else value}" for name, value in values.items()]
    return (BEGIN + "\n" + "(** ELF SHA256: " + recipe["elf_sha256"] + ". *)\n"
            + "Definition defaultMap : MachineMap := {|\n" + ";\n".join(rows) + "\n|}.\nDefinition stockZiskMap := defaultMap.\n" + END)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--build", type=Path, default=Path("build/stock-zisk"))
    parser.add_argument("--output", type=Path, default=Path("ZesuSsz/Contracts/Machine.v"))
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    import manifest
    from build import PINS
    manifest.check(args.build, PINS)
    recipe = json.loads((args.build / "build-recipe.json").read_text())
    audit = json.loads((args.build / "platform-audit.json").read_text())
    if audit["artifact_identity"] != recipe["artifact_identity"]:
        raise SystemExit("The platform audit belongs to another artifact.")
    if hashlib.sha256((args.build / "zesu-zisk.elf").read_bytes()).hexdigest() != recipe["elf_sha256"]:
        raise SystemExit("The selected ELF hash differs from the recipe.")
    block = render(recipe, audit, (args.build / "symbols.txt").read_text())
    source = args.output.read_text()
    if BEGIN in source:
        start, end = source.index(BEGIN), source.index(END) + len(END)
    else:
        start = source.index("Definition defaultMap")
        end = source.index("\n", start)
        block += "\n"
    result = source[:start] + block + source[end:]
    if args.check:
        if source != result:
            raise SystemExit("The stock machine map differs from the selected metadata.")
    else:
        args.output.write_text(result)

if __name__ == "__main__":
    main()
