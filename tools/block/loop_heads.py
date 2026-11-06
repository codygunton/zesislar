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
        definitions.append((name, source + '\n'))
    name = 'fp_machineAt' + block
    alternatives = ' ∨ '.join(symbol + ' args returnAddress' for symbol, _ in definitions)
    definitions.append((name,
        'Definition ' + name + ' `{!islaG Sigma} `{!threadG}'
        ' (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)'
        ' : iProp Sigma := ((' + alternatives + ') ∗ K)%I.\n'))
    extra = 'Require Import lithium.lvar.\nRequire Import ZesuSsz.Automation2.ByteWindowFold.\n'
    output = header + extra
    if structural:
        output += 'Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot' + block + 'Entries.\n'
        for symbol, definition in definitions:
            output += unfold_declaration(symbol, instance_name=symbol + '_unfold', locality='export')
            output += definition_introduction_source(definition, symbol) + '\n'
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
