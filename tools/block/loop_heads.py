"""Select authenticated existential loop heads for FP301 backedges."""
import json
from pathlib import Path
import re

from render_support import definition_introduction_source, unfold_declaration

FIXTURE = Path(__file__).resolve().parent / 'fixtures/fp301-loop-heads.json'


def render_loop_head(block, header, structural=False):
    """Keep the source classes and frame the existing caller continuation."""
    rows = json.loads(FIXTURE.read_text())['rows']
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
    """Render opacity next to each generated unfold declaration."""
    pattern = r'(\#\[export\] Instance (\w+)_unfold : LithiumUnfold \(@\2\) := I\.\n)'
    return re.sub(pattern, lambda match: match[1] + '#[export] Typeclasses Opaque ' + match[2] + '.\n', source)


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
