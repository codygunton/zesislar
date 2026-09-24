#!/usr/bin/env python3
"""Assemble the generated instruction maps for the compliance endpoint."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


def generate(trace_root: Path, output: Path) -> None:
    base_names = ["startup", "main", "read_input", "allocator_get",
                  "write_failure", "zkvm_exit"]
    writer_names = [f"write_success_{index:02d}" for index in range(128)]
    decoder_names = [f"decoder_{index:02d}" for index in range(278)]
    names = base_names + writer_names + decoder_names
    for name in names:
        if not (trace_root / name / "instrs.v").is_file():
            raise ValueError(f"missing generated instruction map: {name}")
    if not (trace_root / "write_success_blocks" / "Index.v").is_file():
        raise ValueError("missing generated writer Index")
    index_source = (trace_root / "write_success_blocks" / "Index.v").read_text()
    index_addresses = sorted({int(value, 16) for value in re.findall(
        r"Z\.compare address (0x[0-9a-f]+)", index_source)})
    writer_addresses = {int(value, 16) for name in writer_names for value in
                        re.findall(r"\((0x[0-9a-f]+)%Z,",
                                   (trace_root / name / "instrs.v").read_text())}
    if len(index_addresses) != 836 or not set(index_addresses) <= writer_addresses:
        raise ValueError("writer Index differs from the pinned instruction maps")
    decoder_addresses = [int(value, 16) for name in decoder_names for value in
                         re.findall(r"\((0x[0-9a-f]+)%Z,",
                                    (trace_root / name / "instrs.v").read_text())]
    if sorted(decoder_addresses) != list(range(0x12168, 0x14cb0, 4)):
        raise ValueError("decoder maps do not cover the pinned decoder span")
    direct_names = decoder_names + base_names + writer_names[:9] + writer_names[127:]
    direct_addresses = {int(value, 16) for name in direct_names for value in
                        re.findall(r"\((0x[0-9a-f]+)%Z,",
                                   (trace_root / name / "instrs.v").read_text())}
    if direct_addresses | set(index_addresses) != (
            direct_addresses | writer_addresses):
        raise ValueError("selected maps and writer Index omit a pinned address")

    lines = ["Require Import ZesuSsz.Automation.All.",
             "Require Import isla.opsem.",
             "From stdpp Require Import gmap.",
             "From Coq Require Import Lists.List.",
             "Require Import IslaTraces.write_success_blocks.Index."]
    lines += [f"Require Import IslaTraces.{name}.instrs." for name in direct_names]
    lines += ["", "Definition pinnedIndexAddresses : list Z := ["]
    lines += ["  " + "; ".join(f"{value:#x}%Z" for value in index_addresses[i:i + 12])
              + (";" if i + 12 < len(index_addresses) else "")
              for i in range(0, len(index_addresses), 12)]
    lines += ["].", "", "Definition pinnedIndexInstructions : list (Z * isla_trace) :=",
              "  omap (fun address =>",
              "    option_map (fun trace => (address, trace))",
              "      (IslaTraces.write_success_blocks.Index.lookup address))",
              "    pinnedIndexAddresses.", "",
              "Definition pinnedInstructions : list (Z * isla_trace) :=",
              "  " + " ++\n  ".join(
                  [f"IslaTraces.{name}.instrs.instr_map" for name in direct_names]
                  + ["pinnedIndexInstructions"]) + ".",
              "", "Definition pinnedInstructionTable : gmap addr isla_trace :=",
              "  <[ BV 64 0x14cb0 := IslaTraces.main.a14cb0.a14cb0 ]>",
              "  (<[ BV 64 0x12168 := IslaTraces.decoder_00.a12168.a12168 ]>",
              "    (list_to_map (List.map (fun item => (Z_to_bv 64 item.1, item.2))",
              "      pinnedInstructions))).", "",
              "Lemma pinned_main_instruction :",
              "  pinnedInstructionTable !! BV 64 0x14cb0 =",
              "    Some IslaTraces.main.a14cb0.a14cb0.",
              "Proof. apply lookup_insert. Qed.", "",
              "Lemma pinned_decoder_instruction :",
              "  pinnedInstructionTable !! BV 64 0x12168 =",
              "    Some IslaTraces.decoder_00.a12168.a12168.",
              "Proof.",
              "  unfold pinnedInstructionTable.",
              "  rewrite lookup_insert_ne; last (vm_compute; congruence).",
              "  apply lookup_insert.",
              "Qed.", "", "Global Opaque pinnedInstructionTable.", ""]
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--trace-root", type=Path,
                        default=Path("generated/isla-traces"))
    parser.add_argument("--output", type=Path,
                        default=Path("ZesuSsz/Generated/InstructionTable.v"))
    args = parser.parse_args()
    generate(args.trace_root, args.output)


if __name__ == "__main__":
    main()
