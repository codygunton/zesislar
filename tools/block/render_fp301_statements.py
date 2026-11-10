"""Render FP301 return packages and caller statements from authenticated inputs."""

import argparse
import hashlib
import json
import re
from pathlib import Path

from production_modules import statement as caller_statement
from render_support import definition_introduction_source, unfold_declaration
from return_exit import (add_entry_facts, add_return_facts, add_return_precondition,
                         return_blocks, return_package)
from function_profiles import load_profile, return_header


ROOT = Path(__file__).resolve().parents[2]


def render_loop_head(block, header, structural=False, profile=None):
    """Keep the source classes and frame the existing caller continuation."""
    profile = profile or load_profile()
    domain_binder = ' (domain : ' + profile.args_type + ' -> Prop)'
    rows = json.loads((ROOT / profile['loop_head_fixture']).read_text())['rows']
    row = next((item for item in rows if item['block'] == block), None)
    if row is None:
        raise ValueError('No authenticated loop head exists: ' + block)
    definitions = []
    authenticated_classes = {}
    for index, source in enumerate(row['classes']):
        original = 'generatedLoop' + block + 'Class' + str(index)
        name = 'fp_machineAt' + block + '_LoopClass' + str(index)
        assert source.startswith('Definition ' + original + ' ')
        assert source.count(domain_binder.strip()) == 1
        assert source.count('⌜domain args⌝') == 1
        source = source.replace(original, name).replace(
            domain_binder, '').replace(
            '⌜domain args⌝', '⌜' + row['domain'] + ' args⌝').replace(
            'ByteWindowFold.zesu_byte_window_fold',
            'ZesuSsz.Automation2.ByteWindowFold.zesu_byte_window_fold')
        authenticated_classes[name] = source
        definitions.append((name, grouped_class(source)))
    name = 'fp_machineAt' + block
    alternatives = ' ∨ '.join(symbol + ' args returnAddress' for symbol, _ in definitions)
    definitions.append((name,
        'Definition ' + name + profile.telescope() + ' (K : iProp Sigma)'
        ' : iProp Sigma := ((' + alternatives + ') ∗ K)%I.\n'))
    extra = 'Require Import lithium.lvar.\nRequire Import ZesuSsz.Automation2.ByteWindowFold.\nRequire Import ZesuSsz.Contracts.LoopFoldStart.\n'
    output = header + extra
    if structural:
        output += 'Require Import ' + profile.qualified('Pilot' + block + 'Entries') + '.\n'
        for symbol, definition in definitions:
            output += unfold_declaration(symbol, instance_name=symbol + '_unfold', locality='export')
            output += (first_pass_registration(symbol, authenticated_classes[symbol], profile)
                       if symbol in authenticated_classes else
                       definition_introduction_source(definition, symbol)) + '\n'
    else:
        output += '\n'.join(source for _, source in definitions)
    assert not re.search(r'\b(?:Proof|Qed|Admitted|Axiom|Ltac)\b', output)
    return output


def selected_loop_declaration(source, header, profile=None):
    """Return a loop rendering only for its exact generated entry owner."""
    profile = profile or load_profile()
    if not profile['loop_heads']:
        return None
    heads = '|'.join(re.escape(head) for head in profile['loop_heads'])
    match = re.search(r'\bDefinition fp_machineAt(' + heads + r')(?:_|\s)', source)
    if match is None:
        match = re.search(r'\bInstance fp_machineAt(' + heads + r')(?:_|\s)', source)
    if match is None:
        return None
    return render_loop_head(match[1], header, structural='\nDefinition ' not in source,
                            profile=profile)


def render_unfold_opacity(source):
    """Keep the current renderer's idempotent opacity declarations."""
    from render_support import retain_unfold_opacity
    return retain_unfold_opacity(source)


def class_parts(source):
    """Split one authenticated class at top-level separating conjunctions."""
    match = re.search(r':=\s*\(\(∃ (.*?), \((.*)\)\)\)%I\.', source, re.S)
    if match is None:
        raise ValueError('The authenticated class shape changed.')
    binders, body = match.groups()
    chunks, start, depth = [], 0, 0
    for pos, char in enumerate(body):
        if char == '(':
            depth += 1
        elif char == ')':
            depth -= 1
        elif body.startswith(' ∗ ', pos) and depth == 0:
            chunks.append(body[start:pos]); start = pos + 3
    chunks.append(body[start:])
    first_pure = next(i for i, term in enumerate(chunks) if term.startswith('⌜'))
    resources, pure = chunks[:first_pure], chunks[first_pure:]
    if not all(term.startswith('⌜') and term.endswith('⌝') for term in pure):
        raise ValueError('An owned resource follows a pure class fact.')
    return binders, resources, [term[1:-1] for term in pure]


def conjunction(terms):
    return ' /\\ '.join('(' + term + ')' for term in terms)


def grouped_class(source):
    binders, resources, facts = class_parts(source)
    prefix = source[:source.index(':=')]
    return prefix + ':= (∃ ' + binders + ', (' + ' ∗ '.join(resources) + ') ∗ ⌜' + conjunction(facts) + '⌝)%I.\n'


def substitute(term, values):
    for name, value in values.items():
        term = re.sub(r'\b' + re.escape(name) + r'\b', '(' + value + ')', term)
    return term


def projection(term, index):
    for _ in range(index):
        term = '(proj2 ' + term + ')'
    return '(proj1 ' + term + ')'


def conj_term(terms):
    result = terms[-1]
    for term in reversed(terms[:-1]):
        result = '(conj ' + term + ' ' + result + ')'
    return result


def first_pass_registration(name, source, profile=None):
    """Render a proof term from the shared start theorem and entailment lemma.

    The count guard marker, the cursor base, and the start lemma are
    function inputs (`loop_first_pass` in the function profile).
    """
    profile = profile or load_profile()
    first_pass = profile['loop_first_pass']
    _, resources, facts = class_parts(source)
    guard = next(f for f in facts[6:] if first_pass['count_guard_marker'] in f)
    prefix = 'bv_zero_extend 128%N '
    begin = guard.index(prefix) + len(prefix)
    if guard[begin] != '(':
        raise ValueError('The source count is not parenthesized.')
    depth = 0
    for end in range(begin, len(guard)):
        depth += (guard[end] == '(') - (guard[end] == ')')
        if depth == 0:
            break
    count = guard[begin:end + 1]
    base = first_pass['cursor_base']
    cursor = '(bv_add (Z_to_bv 64 ' + base + ') (BV 64 1))'
    endpoint = '(bv_add (Z_to_bv 64 ' + base + ') (bv_add ' + count + ' (BV 64 1)))'
    values = {'machine_x13': 'BV 64 0', 'machine_x15': cursor,
              'machine_x16': 'first_x16', 'machine_x11': endpoint,
              'i': '(0%Z : lvar "zesuLoopIndex" Z)'}
    initial = [facts[0], guard, '1 <= bv_unsigned ' + count] + facts[6:]
    initial_text = '(' + conjunction(initial) + ')%Z'
    invariant_text = '(' + conjunction(facts) + ')%Z'
    resource_text = '(' + ' ∗ '.join(resources) + ')%I'
    telescope = profile.telescope()
    resource_fun = '(fun (machine_x13 machine_x15 machine_x16 machine_x11 : bv 64) (i : lvar "zesuLoopIndex" Z) => ' + resource_text + ')'
    invariant_fun = '(fun (machine_x13 machine_x15 machine_x16 machine_x11 : bv 64) (i : lvar "zesuLoopIndex" Z) => ' + invariant_text + ')'
    domain, count_guard, positive = [projection('Hinitial', i) for i in range(3)]
    index = '(bv_unsigned ' + cursor + ' - (' + base + ' + 1))%Z'
    def transport(fact, proof):
        template = substitute(fact, {**values, 'i': 'j'})
        return '(eq_ind ' + index + ' (fun j : Z => (' + template + ')%Z) ' + proof + ' 0 Hzero)'
    fields = [domain, 'eq_refl', transport(facts[2], 'Hcursor'),
              transport(facts[3], 'Hnonnegative'), 'Hendpoint', transport(facts[5], 'Hfold')]
    for i in range(len(facts[6:])):
        fields.append(projection('Hinitial', 3 + i) if i + 1 < len(facts[6:])
                      else '(proj2 ' + '(proj2 ' * (2 + i) + 'Hinitial' + ')' * (2 + i) + ')')
    derive = ('(fun Hinitial => let Hstart := @' + first_pass['start_lemma'] + ' args returnAddress '
              + cursor + ' ' + endpoint + ' ' + count + ' (BV 64 0) '
              + domain + ' eq_refl eq_refl ' + count_guard + ' ' + positive + ' eq_refl in '
              + 'match Hstart with conj Hzero (conj Hnonnegative (conj Hcursor (conj Hendpoint Hfold))) => '
              + conj_term(fields) + ' end)')
    specialized_resource = substitute(resource_text, values)
    source_pred = '(fun first_x16 : bv 64 => (' + specialized_resource + ' ∗ ⌜' + initial_text + '⌝)%I)'
    target = '(' + name + ' args returnAddress)'
    step = ('(@zesu_loop_first_pass_intro Sigma (bv 64) (bv 64) (bv 64) (bv 64) '
            + '(lvar "zesuLoopIndex" Z) ' + resource_fun + ' ' + invariant_fun + ' '
            + initial_text + ' (BV 64 0) ' + cursor + ' first_x16 ' + endpoint
            + ' (0%Z : lvar "zesuLoopIndex" Z) ' + derive + ')')
    return ('#[export] Instance ' + name + '_first_pass_intro' + telescope + ' :\n'
            + '  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma ' + target
            + ' (∃ first_x16 : bv 64, ' + source_pred + ' first_x16)%I :=\n'
            + '  @bi.exist_elim (iPropI Sigma) (bv 64) ' + source_pred + ' ' + target
            + ' (fun first_x16 => ' + step + ').\n')


def binding(path):
    path = Path(path)
    return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def read_bound(row):
    path = Path(row["path"])
    if binding(path) != row:
        raise ValueError("A return-renderer input changed: " + str(path))
    return path.read_text()


def render_entry_registers(source):
    """Render approved dead-register binders without changing other resources."""
    fixture = Path(__file__).resolve().parent / 'fixtures/fp301-entry-registers.json'
    for row in json.loads(fixture.read_text())['rows']:
        owner = re.escape(row['entry'])
        if not re.search(r'\b(?:Definition|Instance) ' + owner + r'(?:_intro)?\b', source):
            continue
        old, new = row['old_resource'], row['new_resource']
        if source.count(old) != 1 or source.count('(∃ ') != 1:
            raise ValueError('The approved register declaration changed: ' + row['entry'])
        if re.search(r'\b' + re.escape(row['binder']) + r'\b', source):
            raise ValueError('The approved register binder already exists: ' + row['binder'])
        source = source.replace(old, new, 1).replace(
            '(∃ ', '(∃ (' + row['binder'] + ' : ' + row['type'] + ') ', 1)
    return source


def render_declaration(source, header, profile=None):
    """Keep the bound declaration body and render its core-free header."""
    selected = selected_loop_declaration(source, header, profile)
    if selected is not None:
        return selected
    boundary = "Local Open Scope Z_scope.\n"
    if source.count(boundary) != 1 or not header.endswith(boundary):
        raise ValueError("A generated declaration lacks its exact header boundary.")
    if "Automation.All." in header or "Automation2.All." in header:
        raise ValueError("A generated declaration cannot import a core.")
    if re.search(r"\b(?:Definition fp_machineReturn|Instance fp_machineReturn_intro)\b", source):
        source = add_return_facts(source, (profile or load_profile()).get("return_facts", []))
    for symbol, spec in (profile or load_profile()).get("entry_facts", {}).items():
        if re.search(r"\b(?:Definition " + symbol + r"|Instance " + symbol + r"_intro)\b", source):
            source = add_entry_facts(source, spec["facts"])
            source = source.replace(boundary, "".join(line + "\n" for line in spec.get("requires", [])) + boundary, 1)
    return render_entry_registers(header + source.split(boundary, 1)[1])


CORE_IMPORT = "Require Import ZesuSsz.Automation2.All."


def core_import_last(source):
    """End the import block with the core import.

    `Require Import isla.riscv64.riscv64.` restores the library bodies of
    `lia`, `bv_solve`, and the Lithium step tactics. Only a later import of
    the core restores the Hooks.v redefinitions, so every caller ends its
    imports with it.
    """
    lines = source.split("\n")
    imports = [index for index, line in enumerate(lines)
               if line.startswith(("Require ", "From "))]
    if not imports:
        raise ValueError("A caller has no import block.")
    last = imports[-1]
    if lines[last] != CORE_IMPORT:
        lines.insert(last + 1, CORE_IMPORT)
    return "\n".join(lines)


def successor_precondition(profile, suffix):
    """Return the `instr_pre` premise that a successor block's entry owns."""
    entry = profile.qualified('Pilot' + suffix + 'Entries', 'fp_machineAt' + suffix)
    return 'instr_pre ' + profile.pc(suffix) + ' (' + entry + ' (args) (returnAddress) (K))%I'


def return_precondition(profile):
    """Return the `instr_pre` premise of the function-return package."""
    return ('instr_pre returnAddress ('
            + profile.qualified('FunctionReturnEntries', 'fp_machineReturn')
            + ' args returnAddress K)')


def render_block_caller(profile, block, preconditions, imports):
    """Render one block caller from its entry, its exit premises and the selected code.

    The statement is declarations data; the proof is always `zesu_block2.`.
    """
    pc = profile.pc(block)[2:]
    entry = profile.qualified('Pilot' + block + 'Entries', 'fp_machineAt' + block)
    premises = ''.join('  ' + premise + ' -∗\n' for premise in preconditions)
    return (''.join('Require Import ' + module + '.\n' for module in imports)
            + CORE_IMPORT + '\n'
            + 'Require Import isla.riscv64.riscv64.\n'
            + 'From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.\n'
            + 'Require Import stdpp.bitvector.definitions.\n'
            + ''.join(line + '\n' for line in profile['caller_contract_requires'])
            + profile.selected_import()
            + CORE_IMPORT + '\n'
            + 'Local Open Scope Z_scope.\n\n'
            + 'Definition DesignedEntry_' + pc + '\n'
            + '    `{!islaG Sigma} `{!threadG} (args : ' + profile.args_type
            + ') (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=\n'
            + '  ((' + entry + ' (args) (returnAddress) (K)) ∗\n'
            + '   True)%I.\n'
            + 'Global Instance : LithiumUnfold (@DesignedEntry_' + pc + ') := I.\n'
            + 'Global Typeclasses Opaque DesignedEntry_' + pc + '.\n\n'
            + 'Lemma DesignedBoundary_' + pc + ' `{!islaG Sigma} `{!threadG} (args : '
            + profile.args_type + ') (returnAddress : Z) (K : iProp Sigma)  :\n'
            + premises
            + '  ' + profile.selected_premise() + ' -∗\n'
            + '  instr_body 0x' + pc + '\n'
            + '    (DesignedEntry_' + pc + ' args returnAddress K).\n'
            + 'Proof.\n'
            + '  zesu_block2.\n'
            + 'Qed.\n\n'
            + 'Print Assumptions DesignedBoundary_' + pc + '.\n')


RESIDUALS = Path(__file__).resolve().parents[2] / "ZesuSsz/Residuals"


def residual_import(source, residuals=RESIDUALS):
    """Import the block's residual lemmas after the core import, when they exist.

    Import is not transitive, so the caller keeps its solver bindings; the
    residual module only adds its exact lemmas to the `zesu_residual` hints.
    """
    match = re.search(r"^Lemma DesignedBoundary_(800d[0-9a-f]{4})\b", source, re.M)
    if not match or not (Path(residuals) / ("Block" + match[1] + ".v")).is_file():
        return source
    line = "Require Import ZesuSsz.Residuals.Block" + match[1] + "."
    lines = source.split("\n")
    last = max(index for index, text in enumerate(lines) if text.startswith(("Require ", "From ")))
    if lines[last] != CORE_IMPORT:
        raise ValueError("A caller must end its imports with the core import.")
    # A return block's residual lemmas may use the pure lemmas behind its exit facts.
    if "FunctionReturnEntries.fp_machineReturn" in source:
        lines[last + 1:last + 1] = load_profile().get("return_requires", [])
        last += len(load_profile().get("return_requires", []))
    lines.insert(last + 1, line)
    return "\n".join(lines)


def render_caller(source, residuals=RESIDUALS):
    """Keep the canonical caller and select the second automation entry point."""
    if "::=" in source or "Ltac " in source:
        raise ValueError("A canonical caller cannot contain tactic overrides.")
    if source.count("Require Import ZesuSsz.Automation.All.") < 1:
        raise ValueError("A canonical caller lacks its automation import.")
    if source.count("  zesu_block.\nQed.") != 1:
        raise ValueError("A canonical caller lacks its plain block proof.")
    return residual_import(core_import_last(source.replace("Require Import ZesuSsz.Automation.All.",
                          CORE_IMPORT).replace(
                              "  zesu_block.\nQed.", "  zesu_block2.\nQed.")), residuals)


def render(inputs, output):
    design = json.loads(read_bound(inputs["design"]))
    callers = json.loads(read_bound(inputs["callers"]))
    declarations = json.loads(read_bound(inputs["declarations"]))
    source = read_bound(inputs["return_source"])
    profile = load_profile(inputs.get("function"))
    closed_cases = inputs["closed_cases"]
    count = profile.get("closed_cases_count", 0)
    if len(closed_cases) != count or len(set(closed_cases)) != count:
        raise ValueError("The preservation gate needs the distinct closed cases of the profile.")
    if not set(closed_cases) <= {row["case"] for row in callers["rows"]}:
        raise ValueError("A closed case has no authenticated caller statement.")
    returns = return_blocks(design)
    parameters = [
        {"name": "args", "type": profile.args_type},
        {"name": "returnAddress", "type": "Z"},
        {"name": "K", "type": "iProp Sigma"},
    ]
    symbol = "fp_machineReturn"
    definition, provenance = return_package(
        source, inputs["return_symbol"], symbol, parameters
    )
    definition = add_return_facts(definition, profile.get("return_facts", []))
    entries = {row["pc"]: row for row in declarations["cases"]}
    prepared = []
    for row in callers["rows"]:
        text = read_bound(row["caller"])
        pc = int(profile.pc(row["case"]), 16)
        name = "DesignedBoundary_" + format(pc, "x")
        original = caller_statement(text, name)
        application = (
            profile.qualified("FunctionReturnEntries", symbol) + " args returnAddress K"
        )
        changed = pc in returns
        rendered = (
            add_return_precondition(original, "returnAddress", application)
            if changed else original
        )
        if row["case"] in inputs["closed_cases"] and rendered != original:
            raise ValueError("A closed generated statement would change: " + row["case"])
        if hex(pc) not in entries:
            raise ValueError("A caller lacks its rendered FP301 entry: " + hex(pc))
        prepared.append((row, original, rendered, changed))

    # Validate every declaration binding before creating an output directory.
    for row in declarations["sources"]:
        read_bound(row)
    output = Path(output)
    output.mkdir(exist_ok=False)
    directory = output / "sources" / profile.generated_directory
    directory.mkdir(parents=True)
    header = return_header(profile)
    entry = directory / "FunctionReturnEntries.v"
    entry.write_text(header + "\n" + definition)
    structural = directory / "FunctionReturnStructural.v"
    structural.write_text(
        header
        + "Require Import " + profile.qualified("FunctionReturnEntries") + ".\n"
        + unfold_declaration(symbol, instance_name=symbol + "_unfold", locality="export")
        + definition_introduction_source(definition, symbol)
    )
    statements = output / "statements"
    statements.mkdir()
    rows = []
    caller_directory = output / "callers"
    caller_directory.mkdir()
    for row, original, rendered, changed in prepared:
        path = statements / (row["case"] + ".vpart")
        path.write_text(rendered)
        caller_source = read_bound(row["caller"]).replace(original, rendered, 1)
        if changed:
            caller_source = ("Require Import " + profile.qualified("FunctionReturnStructural")
                             + ".\n" + caller_source)
        caller = caller_directory / ("Caller" + row["case"] + ".v")
        caller.write_text(render_caller(caller_source))
        rows.append({
            "caller": binding(caller),
            "case": row["case"],
            "original_caller": row["caller"],
            "original_statement_sha256": hashlib.sha256(original.encode()).hexdigest(),
            "statement": binding(path),
            "changed": changed,
            "exit_kind": "function_return" if changed else "successor",
            "additional_imports": [
                profile.qualified("FunctionReturnStructural")
            ] if changed else [],
        })
    result = {
        "status": "SOURCE_DECLARATIONS_ONLY",
        "function": profile.name,
        "inputs": inputs,
        "function_return_blocks": [hex(pc) for pc in sorted(returns)],
        "return_preconditions": [
            {
                "entry_pc": hex(pc),
                "return_instruction_pc": returns[pc]["return_clause"]["return_instruction_pc"],
                "address": "returnAddress",
                "package": profile.qualified("FunctionReturnEntries", symbol)
                           + " args returnAddress K",
            }
            for pc in sorted(returns)
        ],
        "changed_blocks": [row["case"] for row in rows if row["changed"]],
        "closed_cases_unchanged": inputs["closed_cases"],
        "return_source_projection": provenance,
        "sources": [binding(entry), binding(structural)],
        "statements": rows,
        "existing_FP301_declarations_unchanged": declarations["sources"],
        "function_level_contract_changed": False,
        "proof_scripts_emitted": False,
    }
    (output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--inputs-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    options = parser.parse_args()
    inputs = json.loads(read_bound({
        "path": str(options.inputs), "sha256": options.inputs_sha256
    }))
    result = render(inputs, options.output)
    print(json.dumps({"changed_blocks": result["changed_blocks"],
                      "closed_cases_unchanged": result["closed_cases_unchanged"]}))


if __name__ == "__main__":
    main()
