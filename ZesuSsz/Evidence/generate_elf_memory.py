#!/usr/bin/env python3
"""Generate the file-backed PT_LOAD bytes for the pinned endpoint."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from elftools.elf.elffile import ELFFile

from elf_identity import load_image_sha256


CHUNK_SIZE = 1024


def generate(elf_path: Path, output_dir: Path, level1_path: Path) -> None:
    level1 = level1_path.read_text()
    match = re.search(r'Definition artifactSha256 : string := "([0-9a-f]{64})"', level1)
    if match is None or load_image_sha256(elf_path) != match.group(1):
        raise ValueError("ELF load image does not match the pinned Level 1 artifact")

    with elf_path.open("rb") as stream:
        elf = ELFFile(stream)
        segments = [segment for segment in elf.iter_segments()
                    if segment["p_type"] == "PT_LOAD"]
        if len(segments) != 2:
            raise ValueError("expected exactly two PT_LOAD segments")
        rows = [(int(segment["p_vaddr"]), int(segment["p_memsz"]), segment.data())
                for segment in segments]
    if [(address, memory_length, len(data))
            for address, memory_length, data in rows] != [
            (0x10000, 0x8038, 0x8038),
            (0x19000, 0x240010d8, 0x10)]:
        raise ValueError("unexpected PT_LOAD ranges")

    output_dir.mkdir(parents=True, exist_ok=True)
    names = []
    for segment_name, (_, _, data) in zip(("rx", "rw"), rows):
        for index, offset in enumerate(range(0, len(data), CHUNK_SIZE)):
            name = f"{segment_name}_{index:02d}"
            names.append(name)
            values = data[offset:offset + CHUNK_SIZE]
            lines = ["Require Import ZesuSsz.Automation.All.",
                     "Require Import isla.opsem.",
                     "From Coq Require Import Lists.List.",
                     "Import ListNotations.",
                     f"Definition elf_{name} : list (bv 8) := ["]
            lines.extend(
                "  " + "; ".join(f"BV 8 {value}" for value in values[i:i + 16])
                + (";" if i + 16 < len(values) else "")
                for i in range(0, len(values), 16)
            )
            lines.append("].")
            lines.extend([
                f"Lemma elf_{name}_length : List.length elf_{name} = {len(values)}%nat.",
                "Proof. vm_compute. reflexivity. Qed.",
            ])
            (output_dir / f"{name}.v").write_text("\n".join(lines) + "\n")

    imports = "\n".join(f"Require Import ZesuSsz.Generated.ElfImage.{name}."
                        for name in names)
    rx_names = [f"elf_{name}" for name in names if name.startswith("rx_")]
    rx_expr = " ++\n  ".join(rx_names)
    rx_lengths = " ".join(f"elf_{name}_length" for name in names
                          if name.startswith("rx_"))
    (output_dir.parent / "ElfImage.v").write_text(
        "Require Import ZesuSsz.Automation.All.\n"
        "Require Import isla.opsem.\n"
        "From Coq Require Import Lists.List micromega.Lia.\n"
        + imports + "\n"
        + f"Definition elfRxBytes : list (bv 8) :=\n  {rx_expr}.\n"
        + "Definition elfRwBytes : list (bv 8) := elf_rw_00.\n"
        + "Lemma elf_rx_length : List.length elfRxBytes = 0x8038%nat.\n"
        + f"Proof. unfold elfRxBytes. repeat rewrite app_length. rewrite {rx_lengths}. reflexivity. Qed.\n"
        + "Lemma elf_rw_length : List.length elfRwBytes = 0x10%nat.\n"
        + "Proof. exact elf_rw_00_length. Qed.\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--elf", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path,
                        default=Path("ZesuSsz/Generated/ElfImage"))
    parser.add_argument("--level1", type=Path,
                        default=Path("ZesuSsz/Generated/Level1.v"))
    args = parser.parse_args()
    generate(args.elf, args.output_dir, args.level1)


if __name__ == "__main__":
    main()
