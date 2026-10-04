#!/usr/bin/env python3
"""Record pinned Sail item execution and contract-candidate images."""

import argparse
import ast
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / "ZesuSsz/Evidence/DECODE_ITEM_VECTORS.json"
ORACLE = ROOT / "ZesuSsz/Evidence/DecodeItemVectorOracle.v"
MODULUS = 1 << 64
INPUT_POINTER = 0x1000
OUTPUT_POINTER = 0x2000
STACK_POINTER = 0xA0001000
RETURN_ADDRESS = 0x4000
BEFORE = bytes(range(0xA0, 0xA0 + 40))


@dataclass(frozen=True)
class Vector:
    name: str
    data: bytes
    classes: tuple[str, ...]


def vectors() -> list[Vector]:
    return [
        Vector("single_byte", bytes([0x7F]), ("valid",)),
        Vector("empty_string", bytes([0x80]), ("valid", "empty_payload")),
        Vector("one_byte_string", bytes([0x81, 0x80]), ("valid",)),
        Vector("short_string", bytes([0x83, 1, 2, 3]), ("valid",)),
        Vector("empty_list", bytes([0xC0]), ("valid", "empty_payload")),
        Vector("short_list", bytes([0xC2, 1, 2]), ("valid",)),
        Vector("long_string_56", bytes([0xB8, 56] + [0x81] * 56),
               ("valid", "long_length")),
        Vector("long_list_56", bytes([0xF8, 56] + [0x80] * 56),
               ("valid", "long_length")),
        Vector("empty_input", b"", ("empty_input",)),
        Vector("short_string_missing_byte", bytes([0x81]),
               ("short_input", "truncated")),
        Vector("short_list_missing_byte", bytes([0xC1]),
               ("short_input", "truncated")),
        Vector("long_string_missing_length", bytes([0xB8]),
               ("truncated", "invalid_tag_shape")),
        Vector("long_list_missing_length", bytes([0xF8]),
               ("truncated", "invalid_tag_shape")),
        Vector("long_string_short_payload", bytes([0xB8, 56, 1]),
               ("truncated",)),
        Vector("long_list_short_payload", bytes([0xF8, 56, 0x80]),
               ("truncated",)),
        Vector("max_tag_missing_length", bytes([0xFF]),
               ("truncated", "invalid_tag_shape")),
        Vector("string_trailing_byte", bytes([0x80, 0]), ("trailing_bytes",)),
        Vector("list_trailing_byte", bytes([0xC0, 0]), ("trailing_bytes",)),
        Vector("noncanonical_single_byte", bytes([0x81, 1]),
               ("noncanonical_integer",)),
        Vector("noncanonical_integer_zero", bytes([0]),
               ("noncanonical_integer",)),
        Vector("noncanonical_integer_leading_zero", bytes([0x82, 0, 5]),
               ("noncanonical_integer",)),
        Vector("noncanonical_long_zero", bytes([0xB8, 0]),
               ("noncanonical_length",)),
        Vector("noncanonical_long_leading_zero", bytes([0xB9, 0, 56] + [1] * 56),
               ("noncanonical_length",)),
        Vector("length_2_64_minus_10", bytes([0xBF] + [0xFF] * 7 + [0xF6]),
               ("near_2_64",)),
        Vector("length_2_64_minus_9_wrap", bytes([0xBF] + [0xFF] * 7 + [0xF7]),
               ("near_2_64", "eight_byte_length_wrap")),
        Vector("length_2_64_minus_8_wrap", bytes([0xBF] + [0xFF] * 7 + [0xF8]),
               ("near_2_64", "eight_byte_length_wrap")),
        Vector("list_length_2_64_minus_9_wrap", bytes([0xFF] + [0xFF] * 7 + [0xF7]),
               ("near_2_64", "eight_byte_length_wrap")),
    ]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def coq_list(data: bytes) -> str:
    return "[" + "; ".join(map(str, data)) + "]"


def oracle_source(cases: list[Vector]) -> str:
    inputs = ";\n  ".join(coq_list(case.data) for case in cases)
    lines = [
        "From Coq Require Import List ZArith.",
        "Require Import ZesuSsz.Evidence.DecodeItemVectorOracle.",
        "Require Import ZesuSsz.Contracts.RlpDecodeItem.",
        "Import ListNotations.",
        "Open Scope Z_scope.",
        "Definition q23Inputs : list (list Z) := [",
        f"  {inputs}].",
        "Eval vm_compute in map decodeItemSailSummary q23Inputs.",
        "Eval vm_compute in map decodeItemCandidateSummary q23Inputs.",
    ]
    for case in cases:
        # The generator independently chooses the polarity. Rocq checks the
        # actual headerFits proposition, not the Python implementation.
        proposition = f"headerFits (decodeItemVectorBytes {coq_list(case.data)})"
        if header_fits(case.data):
            lines.append(f"Goal {proposition}. Proof. vm_compute; tauto. Qed.")
        else:
            lines.append(f"Goal ~ {proposition}. Proof. vm_compute; intros [H|[H|H]]; discriminate. Qed.")
    return "\n".join(lines) + "\n"


def header_fits(data: bytes) -> bool:
    if not data:
        return True
    prefix = data[0]
    width = prefix - 183 if 184 <= prefix <= 191 else (
        prefix - 247 if 248 <= prefix <= 255 else 0)
    if width == 0 or len(data) - 1 < width:
        return True
    length = int.from_bytes(data[1:1 + width], "big")
    return 1 + width + length < MODULUS


def summaries(output: str) -> tuple[list[list[int]], list[list[int]]]:
    chunks = re.findall(r"=\s*(\[.*?\])\s*:\s*list \(list Z\)", output, re.S)
    if len(chunks) != 2:
        raise RuntimeError("Rocq did not print both vector summary lists")
    result = tuple(ast.literal_eval(chunk.replace(";", ",")) for chunk in chunks)
    return result[0], result[1]


def candidate_image(data: bytes, summary: list[int]) -> tuple[dict, bytes]:
    if summary == [1]:
        image = bytearray(40)
        image[32] = 4
        return {"kind": "Error"}, bytes(image)
    if len(summary) != 4 or summary[0] != 0:
        raise RuntimeError(f"unexpected candidate summary: {summary}")
    _, list_flag, header_length, payload_length = summary
    pointer = 1 if data and data[0] == 0x80 else INPUT_POINTER + header_length
    consumed = (header_length + payload_length) % MODULUS
    image = bytearray(BEFORE)
    image[0:8] = (pointer % MODULUS).to_bytes(8, "little")
    image[8:16] = (payload_length % MODULUS).to_bytes(8, "little")
    image[16] = list_flag
    image[24:32] = consumed.to_bytes(8, "little")
    image[32:34] = b"\x00\x00"
    return ({"kind": "Success", "is_list": bool(list_flag),
             "header_length": header_length, "payload_length": payload_length,
             "payload_pointer": pointer, "consumed_mod_2_64": consumed}, bytes(image))


def sail_result(summary: list[int]) -> dict:
    if summary == [1]:
        return {"kind": "Reject", "fatal_error": "RlpDecode"}
    if len(summary) == 6 and summary[0] == 0:
        _, list_flag, full_length, content_length, source_bytes, source_length = summary
        return {"kind": "Success", "is_list": bool(list_flag),
                "full_length": full_length, "content_length": content_length,
                "source_bytes": source_bytes, "source_length": source_length}
    raise RuntimeError(f"unsupported Sail outcome in vector set: {summary}")


def generate(build_dir: Path) -> dict:
    cases = vectors()
    if len({case.name for case in cases}) != len(cases):
        raise RuntimeError("duplicate vector name")
    required = {"valid", "empty_input", "short_input", "truncated",
                "invalid_tag_shape", "near_2_64", "trailing_bytes",
                "noncanonical_integer", "eight_byte_length_wrap"}
    covered = {label for case in cases for label in case.classes}
    if required - covered:
        raise RuntimeError(f"missing vector classes: {sorted(required - covered)}")
    if not (INPUT_POINTER + max(len(case.data) for case in cases)
            < OUTPUT_POINTER < OUTPUT_POINTER + 40
            < STACK_POINTER - 16 < STACK_POINTER < MODULUS
            and 0xA0000000 + 16 <= STACK_POINTER <= 0xC0000000
            and 0 <= RETURN_ADDRESS < MODULUS
            and RETURN_ADDRESS % 4 == 0):
        raise RuntimeError("the fixed C1-A/B entry layout is invalid")
    for case in cases:
        if len(case.data) >= OUTPUT_POINTER - INPUT_POINTER:
            raise RuntimeError(f"input and output overlap: {case.name}")
    manifest = json.loads((ROOT / "generated/evm-sail-coq/rlp/SOURCE.json").read_text())
    if manifest["evmSailRevision"] != "d0e4aabdde52f9158d191dbc8add444abffd9a6a":
        raise RuntimeError("the pinned EVM-Sail revision changed")
    build_dir = build_dir.resolve()
    build_dir.mkdir(parents=True, exist_ok=True)
    command = ["opam", "exec", "--switch=/home/cody/islaris", "--", "dune", "build",
               "--root", ".", "--build-dir", str(build_dir), "--cache=enabled", "-j8",
               "ZesuSsz/Evidence/DecodeItemVectorOracle.vo"]
    dependency = subprocess.run(command, cwd=ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if dependency.returncode:
        raise RuntimeError("oracle build failed:\n" + dependency.stderr[-4000:])
    scratch = build_dir / "DecodeItemVectorEvaluation.v"
    scratch.write_text(oracle_source(cases))
    result = subprocess.run([str(ROOT / "tools/coqc_scratch.sh"), str(scratch),
                             str(build_dir)], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise RuntimeError(result.stderr[-4000:] + result.stdout[-1000:])
    sail, candidate = summaries(result.stdout)
    if len(sail) != len(cases) or len(candidate) != len(cases):
        raise RuntimeError("Rocq returned the wrong number of vector results")
    rows = []
    for case, sail_summary, candidate_summary in zip(cases, sail, candidate):
        fits = header_fits(case.data)
        candidate_value, image = candidate_image(case.data, candidate_summary)
        if len(image) != 40:
            raise RuntimeError(f"incorrect image size: {case.name}")
        if candidate_value["kind"] == "Success" and (
                image[17:24] != BEFORE[17:24] or image[34:40] != BEFORE[34:40]):
            raise RuntimeError(f"padding changed: {case.name}")
        rows.append({
            "name": case.name, "classes": list(case.classes),
            "input_bytes": list(case.data), "input_hex": case.data.hex(),
            "sail_outcome": sail_result(sail_summary),
            "c1_a": {"in_domain": fits,
                     "expected_40_byte_image_hex": image.hex() if fits else None},
            "c1_b": {"in_domain": True, "candidate": candidate_value,
                     "expected_40_byte_image_hex": image.hex()},
        })
    input_manifest = [{"name": case.name, "bytes": list(case.data)} for case in cases]
    input_digest = hashlib.sha256(json.dumps(input_manifest, sort_keys=True,
                             separators=(",", ":")).encode()).hexdigest()
    hashes = {
        "vector_inputs_sha256": input_digest,
        "generator_sha256": sha256(Path(__file__)),
        "oracle_sha256": sha256(ORACLE),
        "sail_run_sha256": sha256(ROOT / "ZesuSsz/Compliance/SailRun.v"),
        "contract_sha256": sha256(ROOT / "ZesuSsz/Contracts/RlpDecodeItem.v"),
        "generated_rlp_action_sha256": sha256(ROOT / "generated/evm-sail-coq/rlp/evm_rlp.v"),
        "generated_rlp_types_sha256": sha256(ROOT / "generated/evm-sail-coq/rlp/evm_rlp_types.v"),
        "generated_source_manifest_sha256": sha256(ROOT / "generated/evm-sail-coq/rlp/SOURCE.json"),
        "selected_elf_sha256": sha256(ROOT / "build/stock-zisk/zesu-zisk.elf"),
    }
    return {
        "label": "Pinned Sail execution through SailRun; no selected-ELF execution or proof",
        "sail_action": "SailRun.runRlpDecodeItem",
        "candidate_basis": "Contracts.RlpDecodeItem.candidateDecodeItem; not proved against the selected ELF",
        "scope": "All byte tags have an RLP form. Invalid-tag-shape cases have incomplete long headers. Integer canonicality belongs to an integer decoder, so item Success does not establish integer acceptance.",
        "source_revision": manifest["evmSailRevision"],
        "compiler_revision": manifest["sailCompilerRevision"],
        "fixture": {"input_pointer": INPUT_POINTER, "output_pointer": OUTPUT_POINTER,
                    "stack_pointer": STACK_POINTER, "return_address": RETURN_ADDRESS,
                    "before_output_bytes": list(BEFORE)},
        "hashes": hashes,
        "vectors": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-dir", type=Path,
                        default=ROOT / "_build/agents/worker1-child-blob")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(generate(args.build_dir), indent=2) + "\n"
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != rendered:
            raise SystemExit("decodeItem vector JSON is stale")
        print(f"checked {OUTPUT.relative_to(ROOT)}")
    else:
        OUTPUT.write_text(rendered)
        print(f"wrote {OUTPUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
