#!/usr/bin/env python3
"""Pin candidateParentHeader to the pinned ELF's emulated decodeParentHeader.

Two inputs, both committed:
- PARENT_HEADER_EMULATION.json: the results of running decodeParentHeader
  (0x800d5cb8) of build/stock-zisk/zesu-zisk.elf under Unicorn (RV64) on
  concrete inputs. It is test evidence, not proof. `--import-runs RUNS` builds
  it from a runs.json of the research harness (exec-check/drive.py) and records
  the SHA-256 of that file and of the ELF.
- PARENT_HEADER_VECTORS.json: the bytes of the 24 Sail-run header vectors.

Output: ParentHeaderCandidateVectors.v. For every input that satisfies
headerFits, Examples proved by vm_compute state that candidateParentHeader
equals the emulated result, that parentHeaderCandidateResult holds of the
80 result bytes the ELF wrote, and which KnownBug classes the input triggers
(EXPECTED_TRIGGERS below; reviewed data). Inputs whose outer header wraps
(the A runs) are outside headerFits and only their exclusion is stated.

`--check` fails when the committed .v differs from the rendered text.
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2]
EMULATION = ROOT / "ZesuSsz/Evidence/PARENT_HEADER_EMULATION.json"
VECTORS = ROOT / "ZesuSsz/Evidence/PARENT_HEADER_VECTORS.json"
OUTPUT = ROOT / "ZesuSsz/Evidence/ParentHeaderCandidateVectors.v"
ELF = ROOT / "build/stock-zisk/zesu-zisk.elf"
ELF_SHA256 = "e44c18d54ae3d77832df92aceb6eb7119de8eb2e8f1f1b4e585a6e33ea04ff95"

MISSING = "ParentHeaderMissingRequiredField"
# The KnownBug classes each input triggers, in knownBugs order. An input on
# which the emulated binary and Sail agree triggers none.
EXPECTED_TRIGGERS = {
    "cancun_real_header": [],
    "prague_real_header": [],
    **{f"cancun_after_field_{k:02d}": [MISSING] for k in range(1, 12)},
    **{f"cancun_after_field_{k:02d}": [] for k in range(12, 21)},
    # The wrapped item is the gas limit (field 9): the code and Sail both
    # reject it, and ParentHeaderUndecodedFieldRejected does not fire on a
    # wrapped item (row O2 of the approved trigger set).
    "required_nested_wrap": ["RlpLongLengthWrap"],
    "optional_nested_wrap": ["RlpLongLengthWrap"],
    "W1": ["ParentHeaderSkippedFieldShape"],
    "W2": ["ParentHeaderBlobGasUnaligned"],
    "W3": ["ParentHeaderTrailingBytes"],
    "W4": ["ParentHeaderUintOver8"],
    "W5": ["ParentHeaderUndecodedFieldRejected"],
    "W6": ["RlpUintNonCanonical"],
}

# Sail's verdict on each trigger witness of ParentHeaderBugTriggers.v, proved
# below by vm_compute of sailParentHeaderRun.
WITNESS_SAIL = {
    "wrapWitness": "Reject",
    "missingFieldWitness": "Success",
    "trailingBytesWitness": "Reject",
    "skippedFieldShapeWitness": "Reject",
    "blobGasUnalignedWitness": "Reject",
    "uintNonCanonicalWitness": "Reject",
    "uintNonCanonicalWitness2": "Reject",
    "uintNonCanonicalWitness3": "Reject",
    "uintOver8Witness": "Success",
    "undecodedFieldWitness": "Success",
    "excessBlobGasAboveLimitWitness": "Reject",
    "trailingItemMalformedWitness": "Reject",
}


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def import_runs(runs_path: Path) -> dict:
    """Copy the result data of a harness runs.json into the committed form."""
    runs = json.loads(runs_path.read_text())
    elf_sha = sha256_file(ELF)
    if elf_sha != ELF_SHA256:
        raise SystemExit(f"unexpected ELF SHA-256 {elf_sha}")

    def result(run):
        return {"label": run["label"], "result": run["result"],
                "result_hex": run["result_hex"], "exit": run["exit"],
                "oob_reads": run["oob_reads"]}

    controls = []
    for run in runs["controls"]:
        entry = result(run)
        entry["sail"] = run["sail"]
        controls.append(entry)
    witnesses = []
    for run in runs["W"]:
        entry = result(run)
        entry["input_hex"] = run["input_hex"]
        witnesses.append(entry)
    wraps = []
    for run in runs["A"]:
        entry = result(run)
        entry["input_head"] = run["input_head"]
        entry["input_len"] = run["input_len"]
        wraps.append(entry)
    return {
        "label": ("Unicorn 2.1.4 (RV64) runs of decodeParentHeader 0x800d5cb8; "
                  "test evidence, not proof"),
        "elf": "build/stock-zisk/zesu-zisk.elf",
        "elf_sha256": elf_sha,
        "runs_sha256": sha256_file(runs_path),
        "harness": ("_build/agents/researcher/exec-check/harness.py driven by "
                    "drive.py: input at 0x40000008, result at 0xa0700000 "
                    "poisoned with 0xaa, memcpy emulated at 0x800e06c0"),
        "controls": controls,
        "witnesses": witnesses,
        "outer_wraps": wraps,
    }


def coq_list(values: list[int], indent: str = "    ", per_line: int = 16) -> str:
    rows = []
    for start in range(0, len(values), per_line):
        rows.append(indent + "; ".join(str(v) for v in values[start:start + per_line]))
    return "[\n" + ";\n".join(rows) + "]"


def coq_option(value) -> str:
    return "None" if value is None else f"(Some {value})"


def expected_candidate(result: dict) -> str:
    if result["kind"] == "Error":
        return "candidateHeaderError"
    assert result["kind"] == "Success", result
    return ("candidateHeaderSuccess {|\n"
            f"    parentGasLimit := {result['gasLimit']};\n"
            f"    parentGasUsed := {result['gasUsed']};\n"
            f"    parentTimestamp := {result['timestamp']};\n"
            f"    parentBaseFee := {coq_option(result['baseFee'])};\n"
            f"    parentBlobGas := {coq_option(result['blobGasUsed'])};\n"
            f"    parentExcessBlobGas := {coq_option(result['excessBlobGas'])} |}}")


def render(emulation: dict, vectors: dict) -> str:
    inputs = {v["name"]: list(v["input_bytes"]) for v in vectors["vectors"]}
    cases = []
    for run in emulation["controls"]:
        cases.append((run["label"], inputs[run["label"]], run,
                      f"vector {run['label']} of PARENT_HEADER_VECTORS.json; "
                      f"Sail: {run['sail']}"))
    for run in emulation["witnesses"]:
        cases.append((run["label"], list(bytes.fromhex(run["input_hex"])), run,
                      f"witness {run['label']} of return-tail/sem/Counter.v"))
    if sorted(EXPECTED_TRIGGERS) != sorted(label for label, *_ in cases):
        raise SystemExit("EXPECTED_TRIGGERS does not name exactly the runs")

    out = []
    emit = out.append
    emit("(* Generated by ZesuSsz/Evidence/generate_parent_header_candidate_vectors.py;")
    emit("   do not edit. Emulation data: PARENT_HEADER_EMULATION.json")
    emit(f"   (runs.json SHA-256 {emulation['runs_sha256']},")
    emit(f"   ELF SHA-256 {emulation['elf_sha256']}).")
    emit("   The expected results are the pinned ELF's results under Unicorn")
    emit("   emulation: test evidence. Each Example is proved by vm_compute. *)")
    emit("From Coq Require Import List ZArith Lia.")
    emit("From stdpp Require Import bitvector.definitions.")
    emit("Require Import EvmSailRlp.evm_rlp_types.")
    emit("Require Import ZesuSsz.Compliance.KnownBugs.")
    emit("Require Import ZesuSsz.Contracts.RlpDecodeItem.")
    emit("Require Import ZesuSsz.Contracts.ParentHeader.")
    emit("Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.")
    emit("Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.")
    emit("Require Import ZesuSsz.Contracts.ParentHeaderBugTriggers.")
    emit("Require Import ZesuSsz.Compliance.SailRun.")
    emit("Require Import ZesuSsz.Compliance.ProjectionParentHeader.")
    emit("Require Import ZesuSsz.Contracts.ParentHeaderRung2.")
    emit("")
    emit("Import ListNotations.")
    emit("Open Scope Z_scope.")
    emit("")
    emit("Definition candidateVectorBytes (values : list Z) : list byte :=")
    emit("  map (Z_to_bv 8) values.")
    for label, data, run, source in cases:
        name = label
        result = list(bytes.fromhex(run["result_hex"]))
        assert len(result) == 80, label
        emit("")
        emit(f"(* {source}. Emulated exit: {run['exit']}. *)")
        emit(f"Definition candidateInput_{name} : list byte := candidateVectorBytes "
             + coq_list(data) + ".")
        emit(f"Definition candidateEmulatedResult_{name} : list byte := "
             "candidateVectorBytes " + coq_list(result) + ".")
        emit(f"Example candidateHeaderFits_{name} : headerFits candidateInput_{name}.")
        emit("Proof. vm_compute. auto. Qed.")
        emit(f"Example candidateMatchesEmulation_{name} :")
        emit(f"  candidateParentHeader candidateInput_{name} =")
        emit("  " + expected_candidate(run["result"]) + ".")
        emit("Proof. vm_compute. reflexivity. Qed.")
        emit(f"Example candidateResultMatchesEmulation_{name} :")
        emit(f"  parentHeaderCandidateResult candidateInput_{name}")
        emit(f"    candidateEmulatedResult_{name}.")
        emit("Proof. vm_compute. repeat split. Qed.")
        triggers = "; ".join(EXPECTED_TRIGGERS[label])
        emit(f"Example candidateTriggers_{name} :")
        emit(f"  parentHeaderTriggeredBugs candidateInput_{name} = [{triggers}].")
        emit("Proof. vm_compute. reflexivity. Qed.")

    emit("")
    emit("(* Sail's verdict on the trigger witnesses (proved, not emulated). *)")
    for witness, verdict in WITNESS_SAIL.items():
        emit(f"Example sailVerdict_{witness} :")
        if verdict == "Reject":
            emit(f"  sailParentHeaderRun {witness} (parentHeaderSailNode {witness}) =")
            emit("    Reject RlpDecode.")
            emit("Proof. vm_compute. reflexivity. Qed.")
        else:
            emit(f"  exists fields, sailParentHeaderRun {witness}")
            emit(f"    (parentHeaderSailNode {witness}) = Success fields.")
            emit("Proof. eexists. vm_compute. reflexivity. Qed.")
    emit("")
    emit("(* Outer length wraps. Every run below starts with ff followed by eight")
    emit("   ff length bytes: the outer header claims 2^64 - 1 payload bytes and")
    emit("   fails headerFits, whatever follows. These inputs are outside the")
    emit("   decodeParentHeader domain; the emulated binary reads past the input")
    emit("   on some of them. Runs:")
    for run in emulation["outer_wraps"]:
        emit(f"   - {run['label']}: {run['input_len']} bytes, head {run['input_head']},"
             f" exit {run['exit']}, {run['oob_reads']} reads outside the input.")
    emit("   *)")
    emit("Definition outerWrapHead : list byte := candidateVectorBytes (repeat 255 9).")
    emit("Example nineFfExcluded : ~ headerFits outerWrapHead.")
    emit("Proof. vm_compute. intuition discriminate. Qed.")
    emit("Lemma outerWrapExcluded (rest : list byte) :")
    emit("  ~ headerFits (outerWrapHead ++ rest).")
    emit("Proof.")
    emit("  intros Hfits. unfold headerFits in Hfits.")
    emit("  cbn [outerWrapHead candidateVectorBytes repeat map app] in Hfits.")
    emit("  set (width := longLengthWidth _) in Hfits.")
    emit("  assert (Hwidth : width = 8) by (vm_compute; reflexivity).")
    emit("  rewrite Hwidth in Hfits.")
    emit("  destruct Hfits as [Hzero | [Hshort | Hfit]].")
    emit("  - discriminate.")
    emit("  - cbn [List.length] in Hshort. lia.")
    emit("  - vm_compute in Hfit. discriminate.")
    emit("Qed.")
    return "\n".join(out) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--import-runs", type=Path,
                        help="rebuild PARENT_HEADER_EMULATION.json from a harness runs.json")
    parser.add_argument("--check", action="store_true",
                        help="fail when the committed output differs")
    args = parser.parse_args()
    if args.import_runs:
        EMULATION.write_text(json.dumps(import_runs(args.import_runs), indent=1) + "\n")
    emulation = json.loads(EMULATION.read_text())
    vectors = json.loads(VECTORS.read_text())
    text = render(emulation, vectors)
    if args.check:
        if OUTPUT.read_text() != text:
            print(f"{OUTPUT.relative_to(ROOT)} is stale", file=sys.stderr)
            return 1
        return 0
    OUTPUT.write_text(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
