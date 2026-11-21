"""Render FP301 loop-head classes, return packages and caller statements from profile data."""

import json
import re
from pathlib import Path

from render_support import definition_introduction_source, unfold_declaration
from return_exit import add_return_facts
from function_profiles import load_profile, return_alignment_fact, return_header
import entry_hist


ROOT = Path(__file__).resolve().parents[2]
LOOP_HIST_META = {}
# A loop class names the fold by its full path: `ByteWindowFold` alone is ambiguous between
# ZesuSsz.Automation and ZesuSsz.Automation2. A source already in the full spelling keeps it, so a
# profile fact written in that spelling reads the same in the loop class and at its source blocks.
SHORT_FOLD = re.compile(r'(?<![\w.])ByteWindowFold\.zesu_byte_window_fold')


def qualified_fold(text):
    """`text` with every short spelling of the fold qualified; the full spelling is kept."""
    return SHORT_FOLD.sub('ZesuSsz.Automation2.ByteWindowFold.zesu_byte_window_fold', text)


def render_loop_head(block, header, structural=False, profile=None, loop_heads=None):
    """Keep the source classes and frame the existing caller continuation.

    `loop_heads` is the loop-head file to read (default: the profile's committed fixture); a
    scratch render passes its own so the committed fixture is never rewritten."""
    profile = profile or load_profile()
    entry_hist.configure(profile)
    domain_binder = ' (domain : ' + profile.args_type + ' -> Prop)'
    rows = json.loads(Path(loop_heads or ROOT / profile['loop_head_fixture']).read_text())['rows']
    row = next((item for item in rows if item['block'] == block), None)
    if row is None:
        raise ValueError('No authenticated loop head exists: ' + block)
    definitions = []
    declarations = []
    authenticated_classes = {}
    for index, source in enumerate(row['classes']):
        # The authenticated class sources keep the names of their generation run.
        original = re.match(r'Definition (generatedLoop[0-9a-f]+Class' + str(index) + r') ', source)[1]
        name = 'fp_machineAt' + block + '_LoopClass' + str(index)
        assert source.count(domain_binder.strip()) == 1
        assert source.count('⌜domain args⌝') == 1
        domain = row.get('domain_component') or '⌜' + row['domain'] + ' args⌝'
        alignment = return_alignment_fact(profile)
        if alignment and alignment[1:-1] not in source:
            # The last component: a first-pass registration carries trailing facts from the entry.
            if not source.endswith(')%I.'):
                raise ValueError('A loop class does not end with its assertion: ' + original)
            source = source[:-len(')%I.')].rstrip(')') + ' ∗ ' + alignment + ')' * (
                len(source[:-len(')%I.')]) - len(source[:-len(')%I.')].rstrip(')'))) + ')%I.'
        source = qualified_fold(source.replace(original, name).replace(
            domain_binder, '').replace(
            '⌜domain args⌝', domain))
        authenticated_classes[name] = source
        # Hidden history and per-slot frame cells for the loop class (profile keys).
        design = next((item for item in profile.get('loop_designs', [])
                       if profile.pc(item['head']) == profile.pc(block)), {})
        binders_text, class_resources, class_facts = class_parts(source)
        changed = entry_hist.seal_class(
            name, source[:source.index(':=')], binders_text, class_resources, class_facts,
            [{'name': 'args', 'type': profile.args_type}, {'name': 'returnAddress', 'type': 'Z'}], design,
            visible=design.get('visible', []))
        if changed is None:
            LOOP_HIST_META.pop(name, None)  # an earlier render of this class in another shape
            definitions.append((name, grouped_class(source)))
        else:
            for symbol, text, kind in changed[0]:
                declarations.append((symbol, text, kind))
            definitions.append((name, changed[1]))
            LOOP_HIST_META[name] = changed[2]
    name = 'fp_machineAt' + block
    alternatives = ' ∨ '.join(symbol + ' args returnAddress' for symbol, _ in definitions)
    definitions.append((name,
        'Definition ' + name + profile.telescope() + ' (K : iProp Sigma)'
        ' : iProp Sigma := ((' + alternatives + ') ∗ K)%I.\n'))
    extra = 'Require Import lithium.lvar.\nRequire Import ZesuSsz.Automation2.ByteWindowFold.\nRequire Import ZesuSsz.Contracts.LoopFoldStart.\n'
    hist = any(kind == 'hist' for _, _, kind in declarations)   # an empty class history keeps the plain shape
    output = header + extra + (entry_hist.HIST_LIBRARY if hist else '')
    if structural:
        output += 'Require Import ' + profile.qualified('Pilot' + block + 'Entries') + '.\n'
        output += ''.join(entry_hist.structural_opacity(symbol, kind) for symbol, _, kind in declarations)
        for symbol, definition in definitions:
            output += unfold_declaration(symbol, instance_name=symbol + '_unfold', locality='export')
            # A first-pass registration needs the profile's start lemma; without
            # one, the class keeps its definition introduction.
            output += (first_pass_registration(symbol, authenticated_classes[symbol], profile)
                       if symbol in authenticated_classes and profile.get('loop_first_pass') else
                       definition_introduction_source(definition, symbol)) + '\n'
    else:
        output += '\n'.join([text for _, text, _ in declarations] + [source for _, source in definitions])
    assert not re.search(r'\b(?:Proof|Qed|Admitted|Axiom|Ltac)\b', output)
    return output


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
    meta = LOOP_HIST_META.get(name)
    invariant = conj_term(fields)
    if meta is not None and 'hidden' in meta:
        # A sealed class is `resources ∗ ⌜visible⌝ ∗ ⌜zesu_hist (Hist …)⌝`; the same
        # fields, split by the seal's classification, prove both parts.
        if meta['ghost']:
            raise ValueError('A sealed loop class with ghost binders has no first-pass registration: ' + name)
        hidden = {entry_hist.normal(fact) for fact in meta['hidden']}
        split = [entry_hist.normal(fact) in hidden for fact in facts]
        assert sum(split) == len(meta['hidden'])
        visible_fields = [field for field, sealed in zip(fields, split) if not sealed]
        hidden_fields = [field for field, sealed in zip(fields, split) if sealed]
        history = ('(' + meta['hist'] + ' args returnAddress'
                   + ''.join(' ' + binder['name'] for binder in meta['hist_live']) + ')')
        invariant = ('(conj ' + conj_term(visible_fields) + ' (zesu_hist_intro ' + history + ' '
                     + (conj_term(hidden_fields) if hidden_fields else 'I') + '))')
        visible_fun = ('(fun (machine_x13 machine_x15 machine_x16 machine_x11 : bv 64) (i : lvar "zesuLoopIndex" Z) => ('
                       + entry_hist.conjunction(meta['visible']) + '))')
        history_fun = ('(fun (machine_x13 machine_x15 machine_x16 machine_x11 : bv 64) (i : lvar "zesuLoopIndex" Z) => '
                       'zesu_hist ' + history + ')')
    derive = ('(fun Hinitial => let Hstart := @' + first_pass['start_lemma'] + ' args returnAddress '
              + cursor + ' ' + endpoint + ' ' + count + ' (BV 64 0) '
              + domain + ' eq_refl eq_refl ' + count_guard + ' ' + positive + ' eq_refl in '
              + 'match Hstart with conj Hzero (conj Hnonnegative (conj Hcursor (conj Hendpoint Hfold))) => '
              + invariant + ' end)')
    specialized_resource = substitute(resource_text, values)
    source_pred = '(fun first_x16 : bv 64 => (' + specialized_resource + ' ∗ ⌜' + initial_text + '⌝)%I)'
    target = '(' + name + ' args returnAddress)'
    if meta is not None and 'hidden' in meta:
        invariant_fun = visible_fun + ' ' + history_fun
    step = ('(@' + ('zesu_loop_first_pass_intro_sealed' if meta is not None and 'hidden' in meta
                    else 'zesu_loop_first_pass_intro') + ' Sigma (bv 64) (bv 64) (bv 64) (bv 64) '
            + '(lvar "zesuLoopIndex" Z) ' + resource_fun + ' ' + invariant_fun + ' '
            + initial_text + ' (BV 64 0) ' + cursor + ' first_x16 ' + endpoint
            + ' (0%Z : lvar "zesuLoopIndex" Z) ' + derive + ')')
    return ('#[export] Instance ' + name + '_first_pass_intro' + telescope + ' :\n'
            + '  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma ' + target
            + ' (∃ first_x16 : bv 64, ' + source_pred + ' first_x16)%I :=\n'
            + '  @bi.exist_elim (iPropI Sigma) (bv 64) ' + source_pred + ' ' + target
            + ' (fun first_x16 => ' + step + ').\n')


def render_return_package(profile):
    """Render the function-return package of a profile `return_package` design.

    The design names the package's existential binders, its owned resources and its pure
    facts; the profile's `return_facts` follow the facts. Returns the texts of
    `FunctionReturnEntries.v` and `FunctionReturnStructural.v` (declarations only)."""
    design = profile["return_package"]
    symbol = "fp_machineReturn"
    telescope = " ".join("(" + name + " : " + kind + ")" for name, kind in design["binders"])
    body = " ∗ ".join(list(design["resources"]) + ["⌜" + fact + "⌝" for fact in design["facts"]] + ["True"])
    definition = ("Definition " + symbol + profile.telescope() + " (K : iProp Sigma) : iProp Sigma :=\n"
                  + "  ((∃ " + telescope + ", (" + body + ")) ∗ K)%I.\n")
    definition = add_return_facts(definition, profile.get("return_facts", []))
    header = return_header(profile)
    structural = (header + "Require Import " + profile.qualified("FunctionReturnEntries") + ".\n"
                  + unfold_declaration(symbol, instance_name=symbol + "_unfold", locality="export")
                  + definition_introduction_source(definition, symbol))
    return header + "\n" + definition, structural


def render_entry_registers(source):
    """Render approved dead-register binders without changing other resources."""
    fixture = Path(__file__).resolve().parent / 'fixtures/fp301-entry-registers.json'
    for row in json.loads(fixture.read_text())['rows']:
        owner = re.escape(row['entry'])
        if not re.search(r'\b(?:Definition|Instance) ' + owner + r'(?:_intro)?\b', source):
            continue
        old, new = row['old_resource'], row['new_resource']
        if (old not in source and source.count(new) == 1
                and re.search(r'\(' + re.escape(row['binder']) + r' : ' + re.escape(row['type']) + r'\)', source)):
            continue  # A join already binds this register in the approved form.
        if source.count(old) != 1 or source.count('(∃ ') != 1:
            raise ValueError('The approved register declaration changed: ' + row['entry'])
        if re.search(r'\b' + re.escape(row['binder']) + r'\b', source):
            raise ValueError('The approved register binder already exists: ' + row['binder'])
        source = source.replace(old, new, 1).replace(
            '(∃ ', '(∃ (' + row['binder'] + ' : ' + row['type'] + ') ', 1)
    return source


CORE_IMPORT = "Require Import ZesuSsz.Automation2.All."


def slot_suffix(slot):
    """The name suffix of entry slot `slot` of a slot block; '' for a block with one entry."""
    return '' if slot is None else '_slot' + str(slot)


def successor_precondition(profile, suffix, slot=None, k='K'):
    """Return the `instr_pre` premise that a successor block's entry (or entry slot) owns."""
    entry = profile.qualified('Pilot' + suffix + 'Entries', 'fp_machineAt' + suffix + slot_suffix(slot))
    return 'instr_pre ' + profile.pc(suffix) + ' (' + entry + ' (args) (returnAddress) (' + k + '))%I'


def return_precondition(profile, suffix=''):
    """Return the `instr_pre` premise of a function-return package (one per return site)."""
    return ('instr_pre returnAddress ('
            + profile.qualified('FunctionReturn' + suffix + 'Entries', 'fp_machineReturn' + suffix)
            + ' args returnAddress K)')


def render_block_caller(profile, block, preconditions, imports, slot=None, continuation=None):
    """Render one block caller from its entry, its exit premises and the selected code.

    The statement is declarations data; the proof is always `zesu_block2.`.
    The caller makes the selected code transparent locally: a function's hint
    umbrella may declare it opaque (with its unfold marker), and an opaque code
    premise stops the block at its first instruction lookup. An entry slot's
    caller proves `instr_body` at the block's address for that slot's entry.
    With `continuation` (a block that runs through the function return), the
    statement has no K: the entry ends with that contract continuation.
    """
    address = profile.pc(block)[2:]
    pc = address + slot_suffix(slot)
    entry = profile.qualified('Pilot' + block + 'Entries', 'fp_machineAt' + block + slot_suffix(slot))
    premises = ''.join('  ' + premise + ' -∗\n' for premise in preconditions)
    return (''.join('Require Import ' + module + '.\n' for module in imports)
            + CORE_IMPORT + '\n'
            + 'Require Import isla.riscv64.riscv64.\n'
            + 'From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.\n'
            + 'Require Import stdpp.bitvector.definitions.\n'
            + ''.join(line + '\n' for line in profile['caller_contract_requires'])
            + profile.selected_import()
            + CORE_IMPORT + '\n'
            + 'Local Open Scope Z_scope.\n'
            + '#[local] Typeclasses Transparent ' + profile.selected_premise() + '.\n\n'
            + 'Definition DesignedEntry_' + pc + '\n'
            + '    `{!islaG Sigma} `{!threadG} (args : ' + profile.args_type
            + ') (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=\n'
            + '  ((' + entry + ' (args) (returnAddress) (K)) ∗\n'
            + '   True)%I.\n'
            + 'Global Instance : LithiumUnfold (@DesignedEntry_' + pc + ') := I.\n'
            + 'Global Typeclasses Opaque DesignedEntry_' + pc + '.\n\n'
            + 'Lemma DesignedBoundary_' + pc + ' `{!islaG Sigma} `{!threadG} (args : '
            + profile.args_type + ') (returnAddress : Z)' + ('' if continuation else ' (K : iProp Sigma)') + '  :\n'
            + premises
            + '  ' + profile.selected_premise() + ' -∗\n'
            + '  instr_body 0x' + address + '\n'
            + '    (DesignedEntry_' + pc + ' args returnAddress '
            + ('(' + continuation + ')' if continuation else 'K') + ').\n'
            + 'Proof.\n'
            + '  zesu_block2.\n'
            + 'Qed.\n\n'
            + 'Print Assumptions DesignedBoundary_' + pc + '.\n')


RESIDUALS = Path(__file__).resolve().parents[2] / "ZesuSsz/Residuals"


def residual_import(source, residuals=RESIDUALS, profile=None):
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
        requires = (profile or load_profile()).get("return_requires", [])
        lines[last + 1:last + 1] = requires
        last += len(requires)
    lines.insert(last + 1, line)
    return "\n".join(lines)
