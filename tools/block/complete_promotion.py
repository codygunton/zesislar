"""Update all source-level consumers of one named native closure.

Generated terms apply the production theorem. They never consume execution
evidence. Rocq compilation and statement verification remain required.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

import generate_table


PREFIX = "\n".join([
    "Require Import ZesuSsz.Automation.All.",
    "Require Import ZesuSsz.Automation.Approved.",
    "Require Import ZesuSsz.Compliance.DecodeItemHints.",
    "Require Import isla.riscv64.riscv64.",
    "Require Import ZesuSsz.Automation.BlockTable.",
    "Require Import ZesuSsz.Generated.DecodeItem.BlockTable.",
]) + "\n"


def binding(path):
    path = Path(path)
    return {"path": str(path.resolve()),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def remove_binders(text, name):
    """Remove only complete, balanced declarations of the selected hypothesis."""
    starts = list(re.finditer(r"^  \(" + re.escape(name) + r"\s*:", text, re.M))
    for match in reversed(starts):
        start = match.start()
        cursor = text.index("(", start)
        depth = 0
        for end in range(cursor, len(text)):
            depth += (text[end] == "(") - (text[end] == ")")
            if depth == 0:
                end += 1
                if text[end:end + 1] == "\n":
                    end += 1
                text = text[:start] + text[end:]
                break
        else:
            raise ValueError("The native hypothesis has an unbalanced declaration.")
    return text


def add_import(text, module):
    line = f"Require Import {module}.\n"
    if line not in text:
        pos = text.index("\nLemma ")
        text = text[:pos] + line + text[pos:]
    return text


def arguments(source, theorem):
    header = re.search(r"Lemma " + re.escape(theorem) + r"\b(.*?)\s+:\s*\n", source, re.S)
    if not header:
        raise ValueError("The named production theorem has no supported declaration.")
    return [name for group in re.findall(r"\(([^():]+)\s*:\s*[^()]+\)", header[1])
            for name in group.split()]


def render_adapter(pc, module, theorem, args):
    suffix = f"{pc:x}"
    conditional = f"ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter{suffix}Conditional"
    # These are the existing named adapter and native theorem. No new boundary
    # or machine execution proof is generated.
    return (PREFIX + f"Require Import {conditional}.\nRequire Import {module}.\n\n"
            f"Lemma decodeItemSlotBody{suffix} `{{!islaG Sigma}} `{{!threadG}} :\n"
            "  ⊢ block_table_pre decodeItemBlockTable -∗\n"
            f"    instr_body {hex(pc)} decodeItemState{suffix}.\nProof.\n"
            f"  apply decodeItemSlotBody{suffix}Conditional.\n"
            + ("  intros " + " ".join(args) + ".\n" if args else "")
            + f"  exact ({theorem} {' '.join(args)}).\nQed.\n"
            f"Print Assumptions decodeItemSlotBody{suffix}.\n")


def render_signature(pc):
    suffix = f"{pc:x}"
    return (PREFIX + "Require Import ZesuSsz.Generated.DecodeItem.PromotedBodies.\n"
            f"Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter{suffix}.\n\n"
            f"Lemma decodeItemPromoted{suffix[4:]}ExactSignature `{{!islaG Sigma}} `{{!threadG}} :\n"
            "  ⊢ block_table_pre decodeItemBlockTable -∗\n"
            f"    instr_body {hex(pc)} decodeItemState{suffix}.\n"
            f"Proof. exact decodeItemPromotedBody{suffix}. Qed.\n\n"
            f"Print Assumptions decodeItemSlotBody{suffix}.\n"
            f"Print Assumptions decodeItemPromotedBody{suffix}.\n"
            f"Print Assumptions decodeItemPromoted{suffix[4:]}ExactSignature.\n")


def update_promoted(text, pc):
    from promote_table import render_slots
    declarations = re.findall(r"Definition decodeItemPromotedBody([0-9a-f]+)\s*:", text)
    recorded = re.findall(
        r"Definition decodeItemPromotedBody([0-9a-f]+)\s*:.*?:=\s*"
        r"([A-Za-z_][A-Za-z0-9_.]+)\.\s", text, re.S)
    if len(recorded) != len(declarations) or len(set(declarations)) != len(declarations):
        raise ValueError("The recorded promoted proof terms are unavailable or ambiguous.")
    slots = {int(address, 16): {"pc": hex(int(address, 16)), "status": "proved",
                              "proof_module": lemma.rsplit('.', 1)[0], "proof_lemma": lemma}
             for address, lemma in recorded}
    slots[pc] = {"pc": hex(pc), "status": "proved",
                 "proof_module": f"ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter{pc:x}",
                 "proof_lemma": f"ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter{pc:x}.decodeItemSlotBody{pc:x}"}
    return render_slots({"proof_slots": [slots[address] for address in sorted(slots)]})


def refresh_counts(text, table):
    sites = re.findall(r"^  native800d([0-9a-f]+) :", text, re.M)
    rows = {row["block"]: row for row in table["rows"]}
    values = []
    for site in sites:
        count = rows["0x800d" + site].get("goal_count")
        if count is not None and (not isinstance(count, int) or count < 0):
            raise ValueError("The measured active count is invalid.")
        value = "None" if count is None else f"Some {count}%nat"
        values.append(f"(0x800d{site}, {value})")
    declaration = "Definition decodeItemI67NativeResidualCounts : list (Z * option nat) :=\n  [" + ";\n   ".join(values) + "]."
    pattern = r"Definition decodeItemI67NativeResidualCounts.*?\]\.[\n]"
    if re.search(pattern, text, re.S):
        return re.sub(pattern, declaration + "\n", text, flags=re.S)
    return text + ("\n(* I67 printed active counts. None means unavailable. *)\n" + declaration +
                   "\n\nLemma decodeItemI67StatusMatchesOpenBlocks :\n"
                   "  map fst decodeItemI67NativeResidualCounts = decodeItemOpenNativeBlocks.\n"
                   "Proof. reflexivity. Qed.\n")


def plan(workspace, pc, module, lemma, table=None):
    from promote_table import proof_module
    proof_module({"module": module, "lemma": lemma})
    workspace = Path(workspace).resolve()
    short = f"{pc:x}"[4:]
    native = "native" + f"{pc:x}"
    production = workspace / (module.replace(".", "/") + ".v")
    source = production.read_text()
    theorem = lemma.removeprefix(module + ".")
    args = arguments(source, theorem)
    conditional = workspace / f"ZesuSsz/Proofs/DecodeItem/TableSlots/Adapter{pc:x}Conditional.v"
    if not conditional.is_file():
        raise ValueError("The exact conditional adapter is unavailable.")
    if f"instr_body {hex(pc)}" not in source:
        raise ValueError("The production source names a different block.")
    outputs = {}
    adapter = f"ZesuSsz/Proofs/DecodeItem/TableSlots/Adapter{pc:x}.v"
    outputs[adapter] = render_adapter(pc, module, theorem, args)
    signature = f"ZesuSsz/Evidence/DecodeItemPromoted{short}Fixtures.v"
    promoted = "ZesuSsz/Generated/DecodeItem/PromotedBodies.v"
    outputs[promoted] = update_promoted((workspace / promoted).read_text(), pc)
    # The signature fixture imports the generated promoted bodies.
    outputs[signature] = render_signature(pc)
    compliance = "Scaffolding/DecodeItemNativeBlocksCompliance.v"
    original = (workspace / compliance).read_text()
    remaining = re.findall(r"^  \((native[0-9a-f]+)\s*:", original, re.M)
    if native not in remaining:
        raise ValueError("The closure is not an open compliance hypothesis.")
    remaining.remove(native)
    text = add_import(remove_binders(original, native), module)
    text = text.replace(f"({native} Sigma HG HT)", f"(@{theorem} Sigma HG HT)")
    outputs[compliance] = text
    fixtures = "Scaffolding/DecodeItemNativeBlocksComplianceFixtures.v"
    text = remove_binders((workspace / fixtures).read_text(), native)
    positive = "  exact (decodeItemNativeBlocksSelectedCompliance " + " ".join(remaining) + ")."
    text = re.sub(r"^  exact \(decodeItemNativeBlocksSelectedCompliance .*?\)\.", positive, text, flags=re.M)
    # Rebuild the negative application from the remaining hypotheses. The
    # positive application retains all of them.
    if remaining:
        negative = "  Fail exact (decodeItemNativeBlocksSelectedCompliance " + " ".join(remaining[1:]) + ")."
        text = re.sub(r"^  Fail exact \(decodeItemNativeBlocksSelectedCompliance .*?\)\.", negative, text, flags=re.M)
        if remaining[0] != "native800d6960":
            text = text.replace("decodeItemNativeBlocksMissingRootRejected",
                                "decodeItemNativeBlocksMissing" + remaining[0][10:] + "Rejected")
    else:
        text = re.sub(r"^  Fail exact \(decodeItemNativeBlocksSelectedCompliance .*?\)\.\n", "", text, flags=re.M)
        text = text.replace("decodeItemNativeBlocksMissingRootRejected", "decodeItemNativeBlocksNoOpenHypotheses")
    outputs[fixtures] = text
    status = "ZesuSsz/Evidence/DecodeItemOpenNativeHypotheses.v"
    text = (workspace / status).read_text()
    text = re.sub(r"^  " + native + r" : \w+;?\n", "", text, flags=re.M)
    text = re.sub(r"(Definition decodeItemOpenNativeBlocks : list Z :=\n  )\[(.*?)\]\.",
                  lambda m: m[1] + "[" + "; ".join(x for x in m[2].split("; ")
                                                  if x != hex(pc)) + "].", text)
    text = text.replace(";\n}.\n", "\n}.\n")
    record = re.search(r"Record DecodeItemOpenNativeHypotheses : Prop := \{(.*?)\n\}\.",
                       text, re.S)
    if not record:
        raise ValueError("The open native hypothesis record is unavailable.")
    fields = re.findall(r"^  native800d([0-9a-f]+)\s*:", record[1], re.M)
    pattern = "  destruct Hopen as [" + " ".join("H" + field for field in fields) + "]."
    text, replacements = re.subn(r"^  destruct Hopen as \[[^\]]*\]\.", pattern, text, flags=re.M)
    if replacements != 1:
        raise ValueError("The open native hypothesis destruct pattern is unavailable or ambiguous.")
    text = text.replace(f"(H{short} Sigma islaG0 H)", f"(@{lemma} Sigma islaG0 H)")
    count = len(remaining)
    text = re.sub(r"(length decodeItemOpenNativeBlocks = )\d+%nat", rf"\g<1>{count}%nat", text)
    text = add_import(text, module)
    # I67 measurements are independent of proof closure. Remove only this
    # open row; historical I62 counts remain unchanged.
    if table is not None:
        text = refresh_counts(text, table)
    outputs[status] = text
    status_fixtures = "ZesuSsz/Evidence/DecodeItemOpenNativeHypothesesFixtures.v"
    text = remove_binders((workspace / status_fixtures).read_text(), "H" + short)
    text = text.replace(" H" + short, "")
    # The record fixture deliberately lacks a hypothesis, unlike the
    # compliance fixture that tests an omitted application argument.
    if short == "6960" or not remaining:
        text = re.sub(r"\nLemma decodeItemOpenNativeMissing[0-9a-f]+Rejected\b.*?Qed\.\n", "\n", text, flags=re.S)
        text = re.sub(r"Print Assumptions decodeItemOpenNativeMissing[0-9a-f]+Rejected\.\n", "", text)
        if remaining:
            missing = remaining[0][10:]
            declarations = [f"  (H{name[10:]} : decodeItemOpenNativeClosure{name[10:]})"
                            for name in remaining[1:]]
            text += (f"\nLemma decodeItemOpenNativeMissing{missing}Rejected\n" +
                     "\n".join(declarations) + " : True.\nProof.\n"
                     "  Fail assert (Hopen : DecodeItemOpenNativeHypotheses) by (constructor; assumption).\n"
                     "  exact I.\nQed.\n" +
                     f"Print Assumptions decodeItemOpenNativeMissing{missing}Rejected.\n")
    outputs[status_fixtures] = text
    return outputs, {"production": binding(production), "conditional_adapter": binding(conditional),
                     "production_module": module, "production_lemma": lemma,
                     "native_hypothesis_removed": native, "remaining_native_hypotheses": remaining}


def complete(workspace, pc, module, lemma, output, status_table, *, dry_run=False,
             verification_directory=None, mcp_python=None):
    output = Path(output)
    directory = Path(verification_directory) if verification_directory else output.with_suffix('.verification')
    if output.exists() or (not dry_run and (directory.exists() or Path(str(directory) + '.inputs.json').exists())):
        raise ValueError("The promotion evidence already exists. Use a fresh output path.")
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "ZesuSsz/Evidence"))
    import generate_decode_item_native_status as status
    if binding(status_table)["sha256"] != status.I67_SHA256:
        raise ValueError("The retained I67 table hash differs.")
    table = json.loads(Path(status_table).read_text())
    outputs, provenance = plan(workspace, pc, module, lemma, table)
    workspace = Path(workspace).resolve()
    before = [binding(workspace / name) for name in outputs if (workspace / name).exists()]
    originals = {name: (workspace / name).read_bytes() if (workspace / name).exists() else None
                 for name in outputs}
    try:
        for name, text in outputs.items():
            path = workspace / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        root = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=workspace, text=True).strip()
        native_status = status.generate(status_table, workspace=workspace, status_root=root,
                                       productions={f"{pc:x}"[4:]: (module, lemma.split(".")[-1])})
    except Exception:
        for name, original in originals.items():
            path = workspace / name
            if original is None:
                path.unlink(missing_ok=True)
            else:
                path.write_bytes(original)
        raise
    report = {"entry_pc": hex(pc), **provenance, "previous_sources": before,
              "generated_sources": [binding(workspace / name) for name in outputs],
              "native_status": native_status, "status": "dry_run" if dry_run else "verification_pending",
              "success": False, "limits": ["Execution evidence supplies no proof premise."]}
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    if not dry_run:
        from promotion_verification import verify_generated
        try:
            report["verification"] = verify_generated(workspace, [workspace / name for name in outputs],
                                                       pc, directory, python=mcp_python)
            if report["verification"].get("success") is not True:
                raise ValueError("Generated-source verification did not pass.")
        except Exception as error:
            for name, original in originals.items():
                path = workspace / name
                if original is None:
                    path.unlink(missing_ok=True)
                else:
                    path.write_bytes(original)
            report.update(status="verification_failed", error=str(error), sources_restored=True)
            output.write_text(json.dumps(report, indent=2) + "\n")
            raise
        report.update(status="verified", success=True)
    else:
        report["limits"].append("Dry-run emitted sources without verification or a promotion success claim.")
    output.write_text(json.dumps(report, indent=2) + "\n")
    return report
