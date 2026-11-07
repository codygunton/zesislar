"""Render FP301 return packages and caller statements from authenticated inputs."""

import argparse
import hashlib
import json
import re
from pathlib import Path

from production_modules import statement as caller_statement
from render_support import definition_introduction_source, unfold_declaration
from return_exit import add_return_precondition, return_blocks, return_package


LOOP_HEAD_FIXTURE = Path(__file__).resolve().parent / 'fixtures/fp301-loop-heads.json'


def render_loop_head(block, header, structural=False):
    """Keep the source classes and frame the existing caller continuation."""
    rows = json.loads(LOOP_HEAD_FIXTURE.read_text())['rows']
    row = next((item for item in rows if item['block'] == block), None)
    if row is None:
        raise ValueError('No authenticated loop head exists: ' + block)
    definitions = []
    authenticated_classes = {}
    for index, source in enumerate(row['classes']):
        original = 'generatedLoop' + block + 'Class' + str(index)
        name = 'fp_machineAt' + block + '_LoopClass' + str(index)
        assert source.startswith('Definition ' + original + ' ')
        assert source.count('(domain : DecodeItemArgs -> Prop)') == 1
        assert source.count('⌜domain args⌝') == 1
        source = source.replace(original, name).replace(
            ' (domain : DecodeItemArgs -> Prop)', '').replace(
            '⌜domain args⌝', '⌜' + row['domain'] + ' args⌝').replace(
            'ByteWindowFold.zesu_byte_window_fold',
            'ZesuSsz.Automation2.ByteWindowFold.zesu_byte_window_fold')
        authenticated_classes[name] = source
        definitions.append((name, grouped_class(source)))
    name = 'fp_machineAt' + block
    alternatives = ' ∨ '.join(symbol + ' args returnAddress' for symbol, _ in definitions)
    definitions.append((name,
        'Definition ' + name + ' `{!islaG Sigma} `{!threadG}'
        ' (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)'
        ' : iProp Sigma := ((' + alternatives + ') ∗ K)%I.\n'))
    extra = 'Require Import lithium.lvar.\nRequire Import ZesuSsz.Automation2.ByteWindowFold.\nRequire Import ZesuSsz.Contracts.LoopFoldStart.\n'
    output = header + extra
    if structural:
        output += 'Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot' + block + 'Entries.\n'
        for symbol, definition in definitions:
            output += unfold_declaration(symbol, instance_name=symbol + '_unfold', locality='export')
            output += (first_pass_registration(symbol, authenticated_classes[symbol])
                       if symbol in authenticated_classes else
                       definition_introduction_source(definition, symbol)) + '\n'
    else:
        output += '\n'.join(source for _, source in definitions)
    assert not re.search(r'\b(?:Proof|Qed|Admitted|Axiom|Ltac)\b', output)
    return output


def selected_loop_declaration(source, header):
    """Return a loop rendering only for its exact generated entry owner."""
    match = re.search(r'\bDefinition fp_machineAt(6a24|6ac4)(?:_|\s)', source)
    if match is None:
        match = re.search(r'\bInstance fp_machineAt(6a24|6ac4)(?:_|\s)', source)
    if match is None:
        return None
    return render_loop_head(match[1], header, structural='\nDefinition ' not in source)


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


def first_pass_registration(name, source):
    """Render a proof term from the shared start theorem and entailment lemma."""
    _, resources, facts = class_parts(source)
    guard = next(f for f in facts[6:] if 'decodeItemInputLength args' in f)
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
    base = '(decodeItemInputPointer args)'
    cursor = '(bv_add (Z_to_bv 64 ' + base + ') (BV 64 1))'
    endpoint = '(bv_add (Z_to_bv 64 ' + base + ') (bv_add ' + count + ' (BV 64 1)))'
    values = {'machine_x13': 'BV 64 0', 'machine_x15': cursor,
              'machine_x16': 'first_x16', 'machine_x11': endpoint,
              'i': '(0%Z : lvar "zesuLoopIndex" Z)'}
    initial = [facts[0], guard, '1 <= bv_unsigned ' + count] + facts[6:]
    initial_text = '(' + conjunction(initial) + ')%Z'
    invariant_text = '(' + conjunction(facts) + ')%Z'
    resource_text = '(' + ' ∗ '.join(resources) + ')%I'
    telescope = ' `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z)'
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
    derive = ('(fun Hinitial => let Hstart := @loop_fold_start_from_complete_source_domain args returnAddress '
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


def render_declaration(source, header):
    """Keep the bound declaration body and render its core-free header."""
    selected = selected_loop_declaration(source, header)
    if selected is not None:
        return selected
    boundary = "Local Open Scope Z_scope.\n"
    if source.count(boundary) != 1 or not header.endswith(boundary):
        raise ValueError("A generated declaration lacks its exact header boundary.")
    if "Automation.All." in header or "Automation2.All." in header:
        raise ValueError("A generated declaration cannot import a core.")
    return header + source.split(boundary, 1)[1]


def render_caller(source):
    """Keep the canonical caller and select the second automation entry point."""
    if "::=" in source or "Ltac " in source:
        raise ValueError("A canonical caller cannot contain tactic overrides.")
    if source.count("Require Import ZesuSsz.Automation.All.") < 1:
        raise ValueError("A canonical caller lacks its automation import.")
    if source.count("  zesu_block.\nQed.") != 1:
        raise ValueError("A canonical caller lacks its plain block proof.")
    return source.replace("Require Import ZesuSsz.Automation.All.",
                          "Require Import ZesuSsz.Automation2.All.").replace(
                              "  zesu_block.\nQed.", "  zesu_block2.\nQed.")


def render(inputs, output):
    design = json.loads(read_bound(inputs["design"]))
    callers = json.loads(read_bound(inputs["callers"]))
    declarations = json.loads(read_bound(inputs["declarations"]))
    source = read_bound(inputs["return_source"])
    closed_cases = inputs["closed_cases"]
    if len(closed_cases) != 10 or len(set(closed_cases)) != 10:
        raise ValueError("The preservation gate needs the ten distinct closed cases.")
    if not set(closed_cases) <= {row["case"] for row in callers["rows"]}:
        raise ValueError("A closed case has no authenticated caller statement.")
    returns = return_blocks(design)
    parameters = [
        {"name": "args", "type": "DecodeItemArgs"},
        {"name": "returnAddress", "type": "Z"},
        {"name": "K", "type": "iProp Sigma"},
    ]
    symbol = "fp_machineReturn"
    definition, provenance = return_package(
        source, inputs["return_symbol"], symbol, parameters
    )
    entries = {row["pc"]: row for row in declarations["cases"]}
    prepared = []
    for row in callers["rows"]:
        text = read_bound(row["caller"])
        pc = int("800d" + row["case"], 16)
        name = "DesignedBoundary_" + format(pc, "x")
        original = caller_statement(text, name)
        application = (
            "ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries."
            + symbol + " args returnAddress K"
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
    directory = output / "sources/ZesuSsz/Generated/DecodeItem/FP301"
    directory.mkdir(parents=True)
    header = """(* Generated from the authenticated function-return resource package. *)
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Export ZesuSsz.Contracts.DecodeItemDomainRanges.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require ZesuSsz.Automation.Hooks.
Local Open Scope Z_scope.
"""
    entry = directory / "FunctionReturnEntries.v"
    entry.write_text(header + "\n" + definition)
    structural = directory / "FunctionReturnStructural.v"
    structural.write_text(
        header
        + "Require Import ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries.\n"
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
            caller_source = ("Require Import ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnStructural.\n"
                             + caller_source)
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
                "ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnStructural"
            ] if changed else [],
        })
    result = {
        "status": "SOURCE_DECLARATIONS_ONLY",
        "inputs": inputs,
        "function_return_blocks": [hex(pc) for pc in sorted(returns)],
        "return_preconditions": [
            {
                "entry_pc": hex(pc),
                "return_instruction_pc": returns[pc]["return_clause"]["return_instruction_pc"],
                "address": "returnAddress",
                "package": "ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries."
                           + symbol + " args returnAddress K",
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
