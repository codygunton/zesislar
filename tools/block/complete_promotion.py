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
from function_names import FunctionNames


PREFIX = "\n".join([
    "Require Import ZesuSsz.Automation.All.",
    "Require Import ZesuSsz.Automation.Approved.",
    "Require Import ZesuSsz.Compliance.DecodeItemHints.",
    "Require Import isla.riscv64.riscv64.",
    "Require Import ZesuSsz.Automation.BlockTable.",
    "Require Import ZesuSsz.Generated.DecodeItem.BlockTable.",
]) + "\n"


def render_prefix(name_prefix="decodeItem"):
    names = FunctionNames(name_prefix)
    return "\n".join([
        "Require Import ZesuSsz.Automation.All.",
        "Require Import ZesuSsz.Automation.Approved.",
        f"Require Import {names.hints}.",
        "Require Import isla.riscv64.riscv64.",
        "Require Import ZesuSsz.Automation.BlockTable.",
        f"Require Import {names.table_module}.",
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


def render_adapter(pc, module, theorem, args, *, design=None, workspace=None, name_prefix="decodeItem"):
    names = FunctionNames(name_prefix)
    suffix = f"{pc:x}"
    conditional = f"{names.proofs}.TableSlots.Adapter{suffix}Conditional"
    # These are the existing named adapter and native theorem. No new boundary
    # or machine execution proof is generated.
    adaptation = render_edge_adaptation(pc, theorem, args, design, workspace)
    imports = ""
    if adaptation:
        modules = {edge["resource_alternative"].rsplit(".", 1)[0]
                   for _, edge in selected_edge_targets(design, pc)}
        imports = "".join(f"Require Import {name}.\n" for name in sorted(modules))
    return (render_prefix(name_prefix) + f"Require Import {conditional}.\nRequire Import {module}.\n" + imports + "\n"
            f"Lemma {names.prefix}SlotBody{suffix} `{{!islaG Sigma}} `{{!threadG}} :\n"
            f"  ⊢ block_table_pre {names.table} -∗\n"
            f"    instr_body {hex(pc)} {names.state(pc)}.\nProof.\n"
            f"  apply {names.prefix}SlotBody{suffix}Conditional.\n"
            + ("  intros " + " ".join(args) + ".\n" if args else "")
            + (adaptation or f"  exact ({theorem} {' '.join(args)}).\n") + "Qed.\n"
            f"Print Assumptions {names.prefix}SlotBody{suffix}.\n")


def selected_edge_targets(design, pc):
    """Find explicit alternatives for this predecessor without changing the table."""
    if design is None:
        return []
    return [(block, edge) for block in design["blocks"]
            for edge in block["incoming_edges"]
            if edge["from_block"] != "caller" and
            generate_table.address(edge["from_block"]) == pc and
            "resource_alternative" in edge]


def render_edge_adaptation(pc, theorem, args, design, workspace):
    """Derive selected successor preconditions through the existing wand lemma."""
    selected = selected_edge_targets(design, pc)
    if not selected:
        return ""
    if workspace is None:
        raise ValueError("Edge adaptation requires a bound workspace.")
    import entry_schema
    workspace = Path(workspace).resolve()
    blocks = {generate_table.address(block["entry_pc"]): block for block in design["blocks"]}
    source = blocks.get(pc)
    if source is None:
        raise ValueError("The edge predecessor has no declared block.")
    source_fields = entry_schema.contract_fields(source)
    if source_fields is None or args != [binder["name"] for binder in source_fields["binders"]]:
        raise ValueError("The native arguments differ from the declared predecessor binders.")
    root = blocks[generate_table.address(design["entry_pc"])]
    root_names = {binder["name"] for binder in root["binders"]}
    alternatives = {}
    for target, edge in selected:
        address = generate_table.address(target["entry_pc"])
        if address not in map(generate_table.address, source["successor_pcs"]):
            raise ValueError("The selected resource belongs to an undeclared successor.")
        if address in alternatives:
            raise ValueError("The predecessor repeats a resource alternative for one successor.")
        fields = entry_schema.edge_contract_fields(target, edge)
        entry_schema.verify_sources(fields, workspace)
        entry_schema.verify_declarations(fields, workspace)
        entry_schema.verify_declarations(entry_schema.contract_fields(target), workspace)
        alternatives[address] = (target, fields)
    successors = list(map(generate_table.address, source["successor_pcs"]))
    hypotheses = [f"Hnext{target:x}" for target in successors]
    patterns = [f"[{name}]" if target in alternatives else name
                for target, name in zip(successors, hypotheses)]
    resources = " ".join([*patterns, "Hcode"])
    lines = ['  iIntros "' + " ".join([*hypotheses, "Hcode"]) + '".',
             f'  iApply ({theorem} {" ".join(args)} with "{resources}").']
    for address, name in zip(successors, hypotheses):
        if address not in alternatives:
            continue
        target, fields = alternatives[address]
        locals_ = []
        replacements = {}
        for binder in fields["binders"]:
            variable = binder["name"]
            if variable in root_names:
                own = next((item for item in source_fields["binders"] if item["name"] == variable), None)
                if own is None or own["type"] != binder["type"]:
                    raise ValueError("A shared successor parameter is absent or has another type.")
            else:
                if binder["type"] in {"Prop", "Type", "Set"}:
                    raise ValueError("A successor witness is not a data parameter.")
                fresh = f"next{address:x}_{variable}"
                while fresh in args or fresh in locals_:
                    fresh = "next_" + fresh
                locals_.append(fresh)
                replacements[variable] = fresh
        def substitute(value):
            for variable, fresh in replacements.items():
                value = re.sub(r"(?<![\w'.])" + re.escape(variable) + r"(?![\w'])",
                               lambda _: fresh, value)
            return value
        application = fields["resource_predicate"] + "".join(
            " (" + substitute(value) + ")" for value in fields["arguments"])
        pattern = " & ".join([*("%" + variable for variable in locals_), "Hentry"])
        if locals_:
            pattern = "(" + pattern + ")"
        lines += [f'  {{ iApply (instr_pre_wand with "{name} []"); [done|done|].',
                  f'    iIntros "{pattern}".',
                  f'    iAssert ({application})%I with "[Hentry]" as "Hselected".',
                  '    { iExact "Hentry". }']
        if locals_:
            lines.append("    iExists " + ", ".join(locals_) + ".")
        lines += ["    rewrite /" + target["resource_predicate"] + ".",
                  "    iFrame. }"]
    return "\n".join(lines) + "\n"


def render_signature(pc, *, name_prefix="decodeItem"):
    names = FunctionNames(name_prefix)
    suffix = f"{pc:x}"
    return (render_prefix(name_prefix) + f"Require Import ZesuSsz.Generated.{names.module}.PromotedBodies.\n"
            f"Require Import {names.proofs}.TableSlots.Adapter{suffix}.\n\n"
            f"Lemma {names.prefix}Promoted{suffix[4:]}ExactSignature `{{!islaG Sigma}} `{{!threadG}} :\n"
            f"  ⊢ block_table_pre {names.table} -∗\n"
            f"    instr_body {hex(pc)} {names.state(pc)}.\n"
            f"Proof. exact {names.prefix}PromotedBody{suffix}. Qed.\n\n"
            f"Print Assumptions {names.prefix}SlotBody{suffix}.\n"
            f"Print Assumptions {names.prefix}PromotedBody{suffix}.\n"
            f"Print Assumptions {names.prefix}Promoted{suffix[4:]}ExactSignature.\n")


def update_promoted(text, pc, *, name_prefix="decodeItem"):
    names = FunctionNames(name_prefix)
    from promote_table import render_slots
    declarations = re.findall(r"Definition " + re.escape(names.prefix) + r"PromotedBody([0-9a-f]+)\s*:", text)
    recorded = re.findall(
        r"Definition " + re.escape(names.prefix) + r"PromotedBody([0-9a-f]+)\s*:.*?:=\s*"
        r"([A-Za-z_][A-Za-z0-9_.]+)\.\s", text, re.S)
    if len(recorded) != len(declarations) or len(set(declarations)) != len(declarations):
        raise ValueError("The recorded promoted proof terms are unavailable or ambiguous.")
    slots = {int(address, 16): {"pc": hex(int(address, 16)), "status": "proved",
                              "proof_module": lemma.rsplit('.', 1)[0], "proof_lemma": lemma}
             for address, lemma in recorded}
    slots[pc] = {"pc": hex(pc), "status": "proved",
                 "proof_module": f"{names.proofs}.TableSlots.Adapter{pc:x}",
                 "proof_lemma": f"{names.proofs}.TableSlots.Adapter{pc:x}.{names.prefix}SlotBody{pc:x}"}
    return render_slots({"proof_slots": [slots[address] for address in sorted(slots)]}, name_prefix=name_prefix)


def refresh_counts(text, table, *, name_prefix="decodeItem"):
    names = FunctionNames(name_prefix)
    sites = re.findall(r"^  native([0-9a-f]+) :", text, re.M)
    rows = {row["block"]: row for row in table["rows"]}
    values = []
    for site in sites:
        count = rows["0x" + site].get("goal_count")
        if count is not None and (not isinstance(count, int) or count < 0):
            raise ValueError("The measured active count is invalid.")
        value = "None" if count is None else f"Some {count}%nat"
        values.append(f"(0x{site}, {value})")
    declaration = f"Definition {names.prefix}I67NativeResidualCounts : list (Z * option nat) :=\n  [" + ";\n   ".join(values) + "]."
    pattern = r"Definition " + re.escape(names.prefix) + r"I67NativeResidualCounts.*?\]\.[\n]"
    if re.search(pattern, text, re.S):
        return re.sub(pattern, declaration + "\n", text, flags=re.S)
    return text + ("\n(* I67 printed active counts. None means unavailable. *)\n" + declaration +
                   f"\n\nLemma {names.prefix}I67StatusMatchesOpenBlocks :\n"
                   f"  map fst {names.prefix}I67NativeResidualCounts = {names.prefix}OpenNativeBlocks.\n"
                   "Proof. reflexivity. Qed.\n")


def plan(workspace, pc, module, lemma, table=None, *, name_prefix="decodeItem"):
    names = FunctionNames(name_prefix)
    from promote_table import proof_module
    proof_module({"module": module, "lemma": lemma})
    workspace = Path(workspace).resolve()
    short = f"{pc:x}"[4:]
    native = "native" + f"{pc:x}"
    production = workspace / (module.replace(".", "/") + ".v")
    source = production.read_text()
    theorem = lemma.removeprefix(module + ".")
    args = arguments(source, theorem)
    conditional = workspace / f"{names.proof_directory}/TableSlots/Adapter{pc:x}Conditional.v"
    if not conditional.is_file():
        raise ValueError("The exact conditional adapter is unavailable.")
    if f"instr_body {hex(pc)}" not in source:
        raise ValueError("The production source names a different block.")
    outputs = {}
    adapter = f"{names.proof_directory}/TableSlots/Adapter{pc:x}.v"
    design_path = workspace / f"ZesuSsz/Evidence/{names.filename}_block_design.json"
    design = json.loads(design_path.read_text()) if design_path.is_file() else None
    if selected_edge_targets(design, pc):
        generate_table.bound_inputs(workspace / "build/stock-zisk/build-recipe.json",
                                    workspace / "build/stock-zisk/cfg.json", design_path)
    outputs[adapter] = render_adapter(pc, module, theorem, args, design=design, workspace=workspace, name_prefix=name_prefix)
    signature = f"ZesuSsz/Evidence/{names.module}Promoted{short}Fixtures.v"
    promoted = f"ZesuSsz/Generated/{names.module}/PromotedBodies.v"
    outputs[promoted] = update_promoted((workspace / promoted).read_text(), pc, name_prefix=name_prefix)
    # The signature fixture imports the generated promoted bodies.
    outputs[signature] = render_signature(pc, name_prefix=name_prefix)
    compliance = f"ZesuSsz/Compliance/{names.module}Compliance.v"
    original = (workspace / compliance).read_text()
    remaining = re.findall(r"^  \((native[0-9a-f]+)\s*:", original, re.M)
    if native not in remaining:
        raise ValueError("The closure is not an open compliance hypothesis.")
    remaining.remove(native)
    text = add_import(remove_binders(original, native), module)
    text = text.replace(f"({native} Sigma HG HT)", f"(@{theorem} Sigma HG HT)")
    outputs[compliance] = text
    status = f"ZesuSsz/Evidence/{names.module}OpenNativeHypotheses.v"
    text = (workspace / status).read_text()
    text = re.sub(r"^  " + native + r" : \w+;?\n", "", text, flags=re.M)
    text = re.sub(r"(Definition " + re.escape(names.prefix) + r"OpenNativeBlocks : list Z :=\n  )\[(.*?)\]\.",
                  lambda m: m[1] + "[" + "; ".join(x for x in m[2].split("; ")
                                                  if x != hex(pc)) + "].", text)
    text = text.replace(";\n}.\n", "\n}.\n")
    record = re.search(r"Record " + re.escape(names.module) + r"OpenNativeHypotheses : Prop := \{(.*?)\n\}\.",
                       text, re.S)
    if not record:
        raise ValueError("The open native hypothesis record is unavailable.")
    fields = re.findall(r"^  native([0-9a-f]+)\s*:", record[1], re.M)
    pattern = "  destruct Hopen as [" + " ".join("H" + field[4:] for field in fields) + "]."
    text, replacements = re.subn(r"^  destruct Hopen as \[[^\]]*\]\.", pattern, text, flags=re.M)
    if replacements != 1:
        raise ValueError("The open native hypothesis destruct pattern is unavailable or ambiguous.")
    text = text.replace(f"(H{short} Sigma islaG0 H)", f"(@{lemma} Sigma islaG0 H)")
    count = len(remaining)
    text = re.sub(r"(length " + re.escape(names.prefix) + r"OpenNativeBlocks = )\d+%nat", rf"\g<1>{count}%nat", text)
    text = add_import(text, module)
    # I67 measurements are independent of proof closure. Remove only this
    # open row; historical I62 counts remain unchanged.
    if table is not None:
        text = refresh_counts(text, table, name_prefix=name_prefix)
    outputs[status] = text
    return outputs, {"production": binding(production), "conditional_adapter": binding(conditional),
                     "production_module": module, "production_lemma": lemma,
                     "native_hypothesis_removed": native, "remaining_native_hypotheses": remaining}


def complete(workspace, pc, module, lemma, output, status_table, *, dry_run=False,
             verification_directory=None, mcp_python=None, name_prefix="decodeItem"):
    output = Path(output)
    directory = Path(verification_directory) if verification_directory else output.with_suffix('.verification')
    if output.exists() or (not dry_run and (directory.exists() or Path(str(directory) + '.inputs.json').exists())):
        raise ValueError("The promotion evidence already exists. Use a fresh output path.")
    status = None
    table = json.loads(Path(status_table).read_text()) if status_table is not None else None
    if name_prefix == "decodeItem":
        sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "ZesuSsz/Evidence"))
        import generate_decode_item_native_status as status
        if status_table is None or binding(status_table)["sha256"] != status.I67_SHA256:
            raise ValueError("The retained I67 table hash differs.")
    outputs, provenance = plan(workspace, pc, module, lemma, table, name_prefix=name_prefix)
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
        native_status = None
        if status is not None:
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
                                                       pc, directory, python=mcp_python,
                                                       name_prefix=name_prefix)
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
