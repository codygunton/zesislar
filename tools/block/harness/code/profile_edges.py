"""Attach only inventory-derived edges that match helper path provenance."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path

try:
    from .generate_table import address, control, resolved_calls
except ImportError:
    from generate_table import address, control, resolved_calls


def _pc(value):
    return f'0x{value:08x}'


def _incoming(function):
    rows = {address(row['pc']): row for row in function['rows']}
    if len(rows) != len(function['rows']):
        raise ValueError('The inventory repeats an instruction address')
    blocks = {address(block['start']): block for block in function['blocks']}
    if len(blocks) != len(function['blocks']):
        raise ValueError('The inventory repeats a block address')
    incoming = {pc: [] for pc in blocks}
    calls = resolved_calls(function)
    backedges = {(address(edge['from']), address(edge['to']))
                 for loop in function['loops'] for edge in loop['backward_edges']}
    for pc, block in sorted(blocks.items()):
        instructions = sorted(at for at in rows if pc <= at < address(block['end']))
        if not instructions or instructions[0] != pc:
            raise ValueError('The inventory block has no first instruction')
        for index, at in enumerate(instructions):
            following = instructions[index + 1] if index + 1 < len(instructions) else address(block['end'])
            if at + rows[at]['size'] != following:
                raise ValueError('The inventory block has an instruction gap')
        tail = rows[instructions[-1]]
        kind, targets, conditions, _ = control(tail, calls)
        if set(targets) != {address(value) for value in block['successors']}:
            raise ValueError('The inventory successors differ from the instruction words')
        for target, condition in zip(targets, conditions):
            if target not in incoming:
                raise ValueError('The inventory edge leaves the declared blocks')
            edge_kind = ('loop_backedge' if (instructions[-1], target) in backedges else
                         'conditional' if kind == 'branch' else 'jump' if kind == 'jump' else
                         'call' if kind == 'call' else 'fallthrough')
            incoming[target].append({'from_block': _pc(pc), 'from_instruction': _pc(instructions[-1]),
                'source_terminator': tail['mnemonic'], 'kind': edge_kind, 'path_condition': condition})
    for pc, edges in incoming.items():
        edges.sort(key=lambda edge: (edge['from_block'], edge['from_instruction']))
        if pc == address(function['entry']):
            edges.insert(0, {'from_block': 'caller', 'from_instruction': None,
                            'kind': 'entry', 'path_condition': {'op': 'true'}})
    return incoming


def _unique(edges, label):
    encoded = [json.dumps(edge, sort_keys=True, separators=(',', ':')) for edge in edges]
    if len(encoded) != len(set(encoded)):
        raise ValueError('The ' + label + ' contains duplicate edges')
    return set(encoded)


def _path_origins(components):
    result = []
    for component in components:
        if component.get('kind') == 'pure':
            for term in component['terms']:
                origin = term.get('provenance', {})
                if origin.get('kind') == 'path':
                    if set(origin) != {'kind', 'from_block', 'from_instruction'}:
                        raise ValueError('The helper path provenance has unsupported fields')
                    result.append(origin)
        elif component.get('kind') == 'disjunction':
            result.extend(_path_origins(component['alternatives']))
    return result


def attach_helper_edges(profile, *, inventory_path, inventory_sha256, function_name, entry_pc):
    """Return a profile copy and an edge receipt. Keep the parent row exact."""
    payload = Path(inventory_path).read_bytes()
    if hashlib.sha256(payload).hexdigest() != inventory_sha256:
        raise ValueError('The inventory bytes differ from the bound hash')
    inventory = json.loads(payload)
    functions = [function for function in inventory['functions'] if function['name'] == function_name]
    if not functions:
        functions = [function for function in inventory['functions']
                     if function['name'].rsplit('.', 1)[-1] == function_name]
    if len(functions) != 1:
        raise ValueError('The inventory has no unique selected function')
    function = functions[0]
    if profile['function'] != function['name'] or profile['design']['function'] != function['name']:
        raise ValueError('The profile and bound inventory name different functions')
    incoming = _incoming(function)
    pc = address(entry_pc)
    matches = [(index, row) for index, row in enumerate(profile['design']['blocks'])
               if address(row['entry_pc']) == pc]
    if len(matches) != 1 or pc not in incoming:
        raise ValueError('The edge attachment needs one selected parent row')
    row_index, parent = matches[0]
    expected = incoming[pc]
    actual = parent.get('incoming_edges', [])
    expected_set, actual_set = _unique(expected, 'derived inventory'), _unique(actual, 'parent row')
    if actual_set - expected_set:
        raise ValueError('The parent row has conflicting CFG edges')
    if expected_set - actual_set:
        raise ValueError('The parent row is missing derived CFG edges')
    if actual != expected:
        raise ValueError('The parent CFG edge order differs from the bound inventory')
    additions = []
    for index, auxiliary in enumerate(parent['support']['additional_definitions']):
        helper = auxiliary['declaration']
        origins = _path_origins(helper['support']['components'])
        if not origins:
            continue
        selected = []
        for origin in origins:
            candidates = [edge for edge in expected if all(edge.get(key) == origin[key]
                          for key in ('from_block', 'from_instruction'))]
            if not candidates:
                raise ValueError('The helper has unmatched path provenance')
            if len(candidates) != 1:
                raise ValueError('The helper path provenance has ambiguous CFG matches')
            if candidates[0] not in selected:
                selected.append(candidates[0])
        selected = [edge for edge in expected if edge in selected]
        existing = helper.get('incoming_edges', [])
        _unique(existing, 'helper row')
        if existing and existing != selected:
            raise ValueError('The helper has conflicting existing CFG edges')
        additions.append((index, selected, origins))
    if not additions:
        raise ValueError('No selected helper has path provenance')
    result = deepcopy(profile)
    attachments = []
    for index, edges, origins in additions:
        helper = result['design']['blocks'][row_index]['support']['additional_definitions'][index]['declaration']
        helper['incoming_edges'] = deepcopy(edges)
        attachments.append({'helper': helper['entry_definition'],
            'profile_path': ['design', 'blocks', row_index, 'support', 'additional_definitions',
                             index, 'declaration', 'incoming_edges'],
            'edges': edges, 'path_provenance': origins})
    receipt = {'schema': 'helper-edge-attachment.v1', 'inventory_path': str(Path(inventory_path).resolve()),
        'inventory_sha256': inventory_sha256, 'function': function['name'], 'entry_pc': _pc(pc),
        'parent_incoming_edges': expected, 'attachments': attachments, 'resource_terms_changed': False,
        'conditions_changed': False, 'compact_author_changed': False, 'proof_ran': False}
    return result, receipt
