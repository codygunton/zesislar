"""Bind nextUint64's source-pass inputs: trace index, public seed, domain facts, system shapes.

The public seed is the Level 1 entry nextUint64ContractEntry
(NextUint64Contract.v): nextUint64BoundaryEntry instantiates
nextUint64EntryAt800d6274, whose register helper nextUint64Registers is
expanded. A register that the entry fixes by an equality conjunct takes that
value; every other register is an existential witness. The domain facts are
conjuncts of nextUint64BoundaryDomain. The decodeItem resource vocabulary is
reused unchanged. No proof runs.

Usage: nextuint64_inputs.py --output DIR --vocabulary VOCABULARY.json
"""
from pathlib import Path
import argparse, json, re, shutil, sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/block'))
sys.path.insert(0, str(ROOT / 'tools/block/functions'))
from entry_seed import definition_body
from forward_resources import load_resource_vocabulary, ownership_from_assertion_tree, parse_source_ownership
from source_domain import conjunctions
from symbolic_state import input_expr
from free_inputs import bind, system_shapes, trace_index

FUNCTION = 'rlp_decode.nextUint64'
BASE = '(nextUint64Base args)'
WITNESSES = ['x5', 'x6', 'x7', 'x12', 'x13', 'x14', 'x15', 'x16', 'x17', 'x28', 'x29', 'x30', 'x31']
# nextUint64BoundaryEntry's arguments of nextUint64EntryAt800d6274, and the
# equality conjuncts of that entry for its two argument registers.
FIXED = {'x1': '(Z_to_bv 64 (nextReturnAddress {b}))', 'x2': '(Z_to_bv 64 (nextStackPointer {b}))',
         'x8': '(nextSavedS0 {b})', 'x9': '(nextSavedS1 {b})',
         'x10': '(Z_to_bv 64 (nextResultPointer {b}))', 'x11': '(Z_to_bv 64 (nextSlicePointer {b}))',
         'x18': '(nextSavedS2 {b})', 'x19': '(nextSavedS3 {b})', 'x20': '(nextSavedS4 {b})',
         **{'x%d' % n: '(nextUint64SavedX%d args)' % n for n in range(21, 28)}}
LENGTH = 'Z.of_nat (length (nextInputBytes {b}))'


def entry_body(entries):
    """Flatten nextUint64ContractEntry into one owned assertion."""
    text = entries.read_text()
    boundary = definition_body(text, 'nextUint64BoundaryEntry')
    entry = definition_body(text, 'nextUint64EntryAt800d6274')
    registers = definition_body(text, 'nextUint64Registers')
    # Check the instantiation this flattening assumes.
    call = re.sub(r'\s+', ' ', boundary)
    if 'nextUint64EntryAt800d6274 params (Z_to_bv 64 (nextReturnAddress args)) (Z_to_bv 64 (nextStackPointer args))' not in call:
        raise ValueError('nextUint64BoundaryEntry changed its entry arguments.')
    flat = re.sub(r'\s+', ' ', entry)
    for clause in ('x10 = Z_to_bv 64 (nextResultPointer args)', 'x11 = Z_to_bv 64 (nextSlicePointer args)',
                   'inputBytes = nextInputBytes args',
                   'sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args)))'):
        if clause not in flat:
            raise ValueError('nextUint64EntryAt800d6274 lost the conjunct ' + clause)
    if len(re.findall(r'"x\d+" ↦ᵣ RVal_Bits x\d+', registers)) != 29:
        raise ValueError('nextUint64Registers changed.')
    b = BASE
    parts = ['reg_col (nextUint64SysRegs args)']
    for number in [1, 2] + list(range(5, 32)):
        register = 'x%d' % number
        value = register if register in WITNESSES else FIXED[register].format(b=b)
        parts.append('"%s" ↦ᵣ RVal_Bits %s' % (register, value))
    parts += ['nextInputPointer {b} ↦ₘ∗ nextInputBytes {b}'.format(b=b),
              'nextSlicePointer {b} ↦ₘ∗ nextUint64SliceImage (nextInputPointer {b}) ({l})'.format(
                  b=b, l=LENGTH.format(b=b)),
              'nextResultPointer {b} ↦ₘ? 16'.format(b=b),
              '(nextStackPointer {b} - 96) ↦ₘ? 96'.format(b=b),
              '(nextStackPointer {b} - 112) ↦ₘ? 16'.format(b=b),
              '⌜domain args⌝', 'True']
    return '∃ (' + ' '.join(WITNESSES) + ' : bv 64), ' + ' ∗ '.join(parts)


def public_seed(entries, contract):
    body = entry_body(entries)
    parsed = parse_source_ownership(body, provenance=bind(entries, declaration='nextUint64EntryAt800d6274'))
    binders = [{'name': name, 'type': 'bv 64', 'expression': input_expr(name, 64).to_dict()}
               for name in WITNESSES]
    components = []
    for row in parsed['components']:
        node = {'kind': row['kind'], 'id': row['id'], 'original_component': row['source']}
        if row['kind'] == 'register':
            value = row['value'][len('RVal_Bits '):].strip()
            node.update(register=row['name'], width=64, value_coq=value)
            if value in WITNESSES:
                node['symbolic_witness'] = value
        elif row['kind'] == 'byte_array':
            node.update(address_z=row['address_z'], byte_array_expr=input_expr(row['value'], None).to_dict(),
                        element_bits=8, length_original_coq='List.length (' + row['value'] + ')')
        elif row['kind'] == 'unknown_byte_array':
            node.update(kind='uninitialized_memory', address_z=row['address_z'],
                        length_original_coq=row['length'])
        else:
            node.update(coq=row['source'])
        components.append(node)
    tree = {'kind': 'exists', 'binders': binders, 'components': components}
    ownership_from_assertion_tree(tree, provenance={'binding': 'Level1 source'})
    return {'schema': 'h1-public-entry-seed.v1', 'function': FUNCTION, 'entry_pc': None,
            'source_bindings': [bind(entries), bind(contract)],
            'parameters': [{'name': 'args', 'type': 'NextUint64Args'}, {'name': 'returnAddress', 'type': 'Z'},
                           {'name': 'domain', 'type': 'NextUint64Args -> Prop'}],
            'domain_binding': {'source': 'NextUint64Contract.v', 'model': 'nextUint64ContractModel',
                               'actual_domain': 'nextReturnAddress (nextUint64Base args) = returnAddress /\\ '
                                                'nextUint64BoundaryDomain args',
                               'handling': 'nextUint64ContractEntry is nextUint64BoundaryEntry with the '
                                           'return link; both facts form the domain component.'},
            'assertion_tree': tree, 'BODY': body,
            'original_components': [row['source'] for row in parsed['components']],
            'source_facts_added': 0}


def resource_ids(seed):
    ids = {}
    for node in seed['assertion_tree']['components']:
        source = node['original_component']
        for key, marker in (('input', 'nextInputPointer'), ('slice', 'nextSlicePointer'),
                            ('result', 'nextResultPointer'), ('frame', '- 96)'), ('callee_frame', '- 112)')):
            if (node['kind'] in ('byte_array', 'uninitialized_memory') and marker in source
                    and (key != 'input' or 'nextInputBytes' in source.split('↦ₘ')[1])):
                ids.setdefault(key, node['id'])
    return ids


def domain(entries, layout_source, ids):
    text = entries.read_text()
    clauses = conjunctions(definition_body(text, 'nextUint64BoundaryDomain'))
    layout = conjunctions(definition_body(layout_source.read_text(), 'nextUint64EntryLayout'))
    origin = {'source': bind(entries, declaration='nextUint64BoundaryDomain')}

    def clause(rows, pattern, declaration):
        matches = [index for index, item in enumerate(rows) if re.sub(r'\s+', '', item) == re.sub(r'\s+', '', pattern)]
        if len(matches) != 1:
            raise ValueError('The domain clause is absent or ambiguous: ' + pattern)
        return {'source': bind(entries if declaration == 'nextUint64BoundaryDomain' else layout_source,
                               declaration=declaration),
                'conjunct_index': matches[0], 'source_clause': rows[matches[0]]}

    facts = []
    # nextUint64EntryLayout separations (its frame is the 96-byte caller frame).
    for left, right, pattern in [
            ('input', 'result', 'separateRanges inputPointer inputLength resultPointer 16'),
            ('input', 'frame', 'separateRanges inputPointer inputLength (stackPointer - nextUint64StackBytes) nextUint64StackBytes'),
            ('result', 'frame', 'separateRanges resultPointer 16 (stackPointer - nextUint64StackBytes) nextUint64StackBytes'),
            ('slice', 'result', 'separateRanges slicePointer 16 resultPointer 16'),
            ('slice', 'frame', 'separateRanges slicePointer 16 (stackPointer - nextUint64StackBytes) nextUint64StackBytes')]:
        facts.append({'fact_id': 'layout:%s-%s' % (left, right), 'kind': 'disjoint_ranges', 'status': 'supplied',
                      'terms': {'left': ids[left], 'right': ids[right], 'coq_statement': pattern},
                      'origin': {**clause(layout, pattern, 'nextUint64EntryLayout'),
                                 'instantiation': 'nextUint64EntryLayout of nextUint64BoundaryDomain'}})
    # The 112-byte separations cover the caller frame and the callee frame.
    for key, pattern in [('input', 'separateRanges (nextInputPointer args) inputLength (nextStackPointer args - 112) 112'),
                         ('slice', 'separateRanges (nextSlicePointer args) 16 (nextStackPointer args - 112) 112'),
                         ('result', 'separateRanges (nextResultPointer args) 16 (nextStackPointer args - 112) 112')]:
        facts.append({'fact_id': 'domain:%s-callee-frame' % key, 'kind': 'disjoint_ranges', 'status': 'supplied',
                      'terms': {'left': ids[key], 'right': ids['callee_frame'], 'coq_statement': pattern},
                      'origin': {**clause(clauses, pattern, 'nextUint64BoundaryDomain'),
                                 'derivation': '[sp-112, sp-96) lies inside [sp-112, sp).'}})
    slice_image = definition_body(text, 'nextUint64SliceImage')
    if re.sub(r'\s+', ' ', slice_image).strip() != 'word64Bytes pointer ++ word64Bytes length':
        raise ValueError('nextUint64SliceImage changed.')
    facts.append({'fact_id': 'definition:slice-length', 'kind': 'bounds', 'status': 'derived-by-pass',
                  'terms': {'resource_id': ids['slice'], 'index': 0, 'count': 16,
                            'coq_statement': 'length (nextUint64SliceImage p l) = 16%nat'},
                  'origin': {'source': bind(entries, declaration='nextUint64SliceImage'),
                             'derivation': 'word64Bytes returns 8 bytes; the image is two words.'}})
    # decodeItemEntryLayout at stackPointer - 96 gives RAM base + 16 <= sp - 96;
    # the domain bounds sp below the RAM end and aligns it to 16 bytes.
    ram_base, ram_end = 0xa0000000, 0xc0000000
    stack = input_expr('(Z_to_bv 64%N (nextStackPointer (nextUint64Base args)))', 64).to_dict()
    layout_clause = ('decodeItemEntryLayout (nextInputPointer args) inputLength (nextStackPointer args - 88) '
                     '(nextStackPointer args - 96) 0x800d62b8 (nextUint64InputEnd params)')
    facts.append({'fact_id': 'domain:stack-interval', 'kind': 'bounds', 'status': 'supplied',
                  'terms': {'unsigned_interval': {'expression': stack, 'minimum': ram_base + 16 + 96,
                                                  'maximum': ram_end - 1, 'ram_base': ram_base, 'ram_end': ram_end}},
                  'origin': {**clause(clauses, 'nextStackPointer args < machineRamEnd defaultMap',
                                      'nextUint64BoundaryDomain'),
                             'lower_bound': clause(clauses, layout_clause, 'nextUint64BoundaryDomain'),
                             'derivation': 'decodeItemEntryLayout bounds sp - 96 below by mapRamBase + '
                                           'decodeItemStackBytes; the domain bounds sp below machineRamEnd.'}})
    facts.append({'fact_id': 'domain:stack-alignment', 'kind': 'alignment', 'status': 'supplied',
                  'terms': {'alignment': {'expression': stack, 'modulus': 16, 'residue': 0}},
                  'origin': clause(clauses, '(16 | nextStackPointer args)', 'nextUint64BoundaryDomain')})
    facts.append({'fact_id': 'domain:slice-interval', 'kind': 'bounds', 'status': 'supplied',
                  'terms': {'unsigned_interval': {
                      'expression': input_expr('(Z_to_bv 64%N (nextSlicePointer (nextUint64Base args)))', 64).to_dict(),
                      'minimum': ram_base, 'maximum': ram_end - 16, 'ram_base': ram_base, 'ram_end': ram_end}},
                  'origin': {**clause(clauses, 'mapRamBase defaultMap <= nextSlicePointer args',
                                      'nextUint64BoundaryDomain'),
                             'upper_bound': clause(clauses, 'nextSlicePointer args + 16 <= machineRamEnd defaultMap',
                                                   'nextUint64BoundaryDomain')}})
    facts.append({'fact_id': 'domain:result-interval', 'kind': 'bounds', 'status': 'supplied',
                  'terms': {'unsigned_interval': {
                      'expression': input_expr('(Z_to_bv 64%N (nextResultPointer (nextUint64Base args)))', 64).to_dict(),
                      'minimum': ram_base, 'maximum': ram_end - 16, 'ram_base': ram_base, 'ram_end': ram_end}},
                  'origin': {**clause(clauses, 'mapRamBase defaultMap <= nextResultPointer args',
                                      'nextUint64BoundaryDomain'),
                             'upper_bound': clause(clauses, 'nextResultPointer args + 16 <= machineRamEnd defaultMap',
                                                   'nextUint64BoundaryDomain')}})
    return {'projection': {'facts': facts, 'original_wellformed_clauses': clauses,
                           'entry_assertion_changed': False, 'premises_added': []},
            'constants': {}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--vocabulary', type=Path, required=True)
    options = parser.parse_args()
    output = options.output.resolve()
    output.mkdir(exist_ok=False)
    entries = ROOT / 'ZesuSsz/Contracts/NextUint64BlockEntries.v'
    contract = ROOT / 'ZesuSsz/Contracts/NextUint64Contract.v'
    layout = ROOT / 'ZesuSsz/Contracts/ParentHeaderRootFacts.v'
    machine = ROOT / 'InstrSpecs/Machine.v'
    mapfile = ROOT / 'ZesuSsz/Contracts/Machine.v'
    vocabulary = output / 'VOCABULARY.json'
    shutil.copyfile(options.vocabulary, vocabulary)
    load_resource_vocabulary(vocabulary, bind(vocabulary)['sha256'])
    index, function = trace_index(output, FUNCTION, 'ZesuSsz.Stock.NextUint64')
    seed = public_seed(entries, contract)
    ids = resource_ids(seed)
    (output / 'DOMAIN.json').write_text(json.dumps(domain(entries, layout, ids), indent=2) + '\n')
    shapes = system_shapes(machine, mapfile)
    end, = [row for row in shapes['rows'] if row['key'] == 'zisk_input_end']
    # nextUint64SysRegs fixes zisk_input_end to the input end (decodeItemSysRegs of the callee base).
    end.update(shape='exact', value=input_expr('(Z_to_bv 64%N (nextUint64InputEnd args))', 64).to_dict())
    end.pop('symbol', None)
    (output / 'SYSTEM-SHAPES.json').write_text(json.dumps(shapes, indent=2) + '\n')
    seed['entry_pc'] = hex(function['entry'])
    seed['source_domain_binding'] = bind(output / 'DOMAIN.json')
    (output / 'SEED.json').write_text(json.dumps(seed, indent=2, ensure_ascii=False) + '\n')
    manifest = {'schema': 'fp301.seed-manifest.v1', 'function': FUNCTION,
                'domain': bind(output / 'DOMAIN.json'), 'seed': bind(output / 'SEED.json'),
                'trace_index': bind(index), 'generator': bind(Path(__file__))}
    (output / 'SEED-MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'seed_manifest': bind(output / 'SEED-MANIFEST.json'),
                      'instructions': len(function['rows']), 'blocks': len(function['blocks']),
                      'resources': ids}))


if __name__ == '__main__':
    main()
