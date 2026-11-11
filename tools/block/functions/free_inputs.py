"""Bind free's source-pass inputs: trace index, public seed, domain facts, system shapes.

Every value comes from a source declaration (AltFlFreeContract.v, AltFlFree.v,
InstrSpecs/Machine.v, MachineMap/Machine.v) or from the pinned CFG and traces.
The decodeItem resource vocabulary is reused unchanged; it names generic
memory and register helpers only. No fact is added beyond a conjunct of
freeArgsWellFormed, and no proof runs.

Usage: free_inputs.py --output DIR --vocabulary VOCABULARY.json
"""
from pathlib import Path
import argparse, hashlib, json, re, shutil, subprocess, sys

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(subprocess.run(['git', '-C', str(ROOT), 'rev-parse', '--path-format=absolute',
                            '--git-common-dir'], capture_output=True, text=True, check=True).stdout.strip()).parent
sys.path.insert(0, str(ROOT / 'tools/block'))
from entry_seed import definition_body
from forward_resources import (_strip_enclosure, _top_positions, load_resource_vocabulary,
                               ownership_from_assertion_tree, parse_source_ownership)
from source_domain import conjunctions, constant_from_source
from symbolic_state import Expr, bits, input_expr

FUNCTION = 'alt_fl_alloc.free'
ENTRY = 'freeEntryResources'
WELLFORMED = 'freeArgsWellFormed'
DOMAIN_APPLICATION = 'freeDomainAt returnAddress'
WORD = 2 ** 64


def bind(path, **more):
    path = Path(path)
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), **more}


def trace_index(output):
    cfg = BASE / 'build/stock-zisk/cfg.json'
    recipe = BASE / 'build/stock-zisk/build-recipe.json'
    traces = BASE / 'generated/isla-traces/stock-zisk/closure'
    function = next(row for row in json.loads(cfg.read_text())['functions'] if row['name'] == FUNCTION)
    elf = json.loads(recipe.read_text())['elf_sha256']
    coverage = json.loads((traces / 'coverage.json').read_text())
    if coverage.get('elf_sha256') not in (None, elf):
        raise ValueError('The trace coverage belongs to another ELF.')
    expected = {Path(key).name: value for key, value in coverage.get('files', {}).items()}
    rows = []
    for row in function['rows']:
        pair = {'pc': hex(row['pc']), 'word': row['word']}
        for kind, suffix in (('raw', '.isla'), ('rocq', '.v')):
            path = traces / ('a%x%s' % (row['pc'], suffix))
            pair[kind] = bind(path)
            if path.name in expected and expected[path.name] != pair[kind]['sha256']:
                raise ValueError('A trace differs from its coverage hash: ' + path.name)
        rows.append(pair)
    function_path = output / 'FUNCTION.json'
    function_path.write_text(json.dumps({'functions': [function], 'source': bind(cfg)}, indent=2) + '\n')
    index_path = output / 'TRACE-INDEX.json'
    index_path.write_text(json.dumps({
        'schema': 'source.instruction-trace-index.v1', 'namespace': 'ZesuSsz.Stock.Free',
        'ELF_sha256': elf, 'function': bind(function_path), 'coverage': bind(traces / 'coverage.json'),
        'recipe': bind(recipe), 'instruction_pairs': rows, 'proof_calls': 0}, indent=2) + '\n')
    return index_path, function


def constants(layout):
    result = {}
    for name in ('freeStackBytes', 'freeListsPointer', 'freeListCount'):
        result[name] = constant_from_source(bind(layout, declaration=name))
    count = result['freeListCount']['value']
    text = layout.read_text()
    body = re.search(r'Notation freeListsBytes := \(\((.*?)\) : Z\) \(only parsing\)\.', text)[1]
    if re.sub(r'\s+', '', body) != '8+8*freeListCount':
        raise ValueError('The list-head byte count changed in its source.')
    result['freeListsBytes'] = {'value': 8 + 8 * count, 'type': 'Z',
                                'origin': bind(layout, declaration='freeListsBytes',
                                               derivation='8 + 8 * freeListCount')}
    return result


def public_seed(contract, layout, machine):
    body = definition_body(contract.read_text(), ENTRY)
    parsed = parse_source_ownership(body, provenance=bind(contract, declaration=ENTRY))
    prefix, = parsed['existential_prefixes']
    match = re.fullmatch(r'∃\s*\(([^:]+):\s*([^()]+)\),', prefix)
    names, kind = match[1].split(), match[2].strip()
    binders = [{'name': name, 'type': kind, 'expression': input_expr(name, 64).to_dict()} for name in names]
    components = []
    for row in parsed['components']:
        node = {'kind': row['kind'], 'id': row['id'], 'original_component': row['source']}
        if row['kind'] == 'register':
            value = row['value'][len('RVal_Bits '):].strip()
            node.update(register=row['name'], width=64, value_coq=value)
            if value in names:
                node['symbolic_witness'] = value
        elif row['kind'] == 'byte_array':
            node.update(address_z=row['address_z'], byte_array_expr=input_expr(row['value'], None).to_dict(),
                        element_bits=8, length_original_coq='List.length (' + row['value'] + ')')
        elif row['kind'] == 'unknown_byte_array':
            node.update(kind='uninitialized_memory', address_z=row['address_z'],
                        length_original_coq=row['length'])
        elif row['source'] == '⌜' + WELLFORMED + ' args⌝':
            # The model entry adds the return link; freeDomainAt is exactly both facts.
            node.update(coq='⌜domain args⌝', original_component=row['source'])
        else:
            node.update(coq=row['source'])
        components.append(node)
    tree = {'kind': 'exists', 'binders': binders, 'components': components}
    ownership_from_assertion_tree(tree, provenance={'binding': 'Level1 source'})
    return {'schema': 'h1-public-entry-seed.v1', 'function': FUNCTION,
            'entry_pc': None,
            'source_bindings': [bind(contract), bind(layout), bind(machine)],
            'parameters': [{'name': 'args', 'type': 'FreeArgs'}, {'name': 'returnAddress', 'type': 'Z'},
                           {'name': 'domain', 'type': 'FreeArgs -> Prop'}],
            'domain_binding': {'source': 'AltFlFreeContract.v', 'model': 'freeModel',
                               'actual_domain': DOMAIN_APPLICATION,
                               'handling': 'freeModel entry is ⌜freeReturnAddress args = returnAddress⌝ ∗ '
                                           'freeEntryResources args; freeDomainAt returnAddress args is '
                                           'exactly the return link and freeArgsWellFormed args.'},
            'assertion_tree': tree, 'BODY': body,
            'original_components': [row['source'] for row in parsed['components']],
            'source_facts_added': 0}


def domain(contract, values):
    clauses = conjunctions(definition_body(contract.read_text(), WELLFORMED))
    origin = {'source': bind(contract, declaration=WELLFORMED)}

    def clause(text):
        matches = [index for index, item in enumerate(clauses) if re.sub(r'\s+', '', item) == re.sub(r'\s+', '', text)]
        if len(matches) != 1:
            raise ValueError('The wellformed clause is absent or ambiguous: ' + text)
        return {**origin, 'conjunct_index': matches[0], 'source_clause': clauses[matches[0]]}

    ram_base, ram_end = 0xa0000000, 0xc0000000
    range_text = definition_body(contract.read_text(), 'freeRange')
    if re.sub(r'\s+', '', range_text) != '0xa0000000<=pointer/\\0<=length/\\pointer+length<=0xc0000000':
        raise ValueError('The freeRange source changed.')
    stack = values['freeStackBytes']['value']
    lists = values['freeListsBytes']['value']
    facts = [
        {'fact_id': 'wellformed:buffer-minimum', 'kind': 'bounds', 'status': 'supplied',
         'terms': {'resource_id': 'resource_9', 'index': 0, 'count': 8,
                   'coq_statement': '8 <= Z.of_nat (length (freeBeforeBuffer args))'},
         'origin': clause('8 <= Z.of_nat (length (freeBeforeBuffer args))')},
        {'fact_id': 'wellformed:lists-length', 'kind': 'bounds', 'status': 'supplied',
         'terms': {'resource_id': 'resource_10', 'index': 0, 'count': lists,
                   'coq_statement': 'length (freeBeforeLists args) = 184%nat'},
         'origin': clause('length (freeBeforeLists args) = 184%nat')},
        {'fact_id': 'wellformed:stack-interval', 'kind': 'bounds', 'status': 'supplied',
         'terms': {'unsigned_interval': {
             'expression': input_expr('(Z_to_bv 64%N (freeStackPointer args))', 64).to_dict(),
             'minimum': ram_base + stack, 'maximum': ram_end, 'ram_base': ram_base, 'ram_end': ram_end}},
         'origin': {**clause('freeRange (freeStackPointer args - freeStackBytes) freeStackBytes'),
                    'definition': bind(contract, declaration='freeRange'),
                    'derivation': 'freeRange unfolded; closed addition of freeStackBytes.'}},
        {'fact_id': 'wellformed:stack-alignment', 'kind': 'alignment', 'status': 'supplied',
         'terms': {'alignment': {'expression': input_expr('(Z_to_bv 64%N (freeStackPointer args))', 64).to_dict(),
                                 'modulus': 16, 'residue': 0}},
         'origin': clause('freeStackPointer args mod 16 = 0')},
        {'fact_id': 'wellformed:return-alignment', 'kind': 'alignment', 'status': 'supplied',
         'terms': {'alignment': {'expression': input_expr('(Z_to_bv 64%N (freeReturnAddress args))', 64).to_dict(),
                                 'modulus': 4, 'residue': 0}},
         'origin': clause('freeReturnAddress args mod 4 = 0')},
    ]
    separations = [
        ('resource_9', 'resource_10', 'freeSeparate (freeBufferPointer args) (Z.of_nat (length (freeBeforeBuffer args))) freeListsPointer freeListsBytes'),
        ('resource_9', 'resource_11', 'freeSeparate (freeBufferPointer args) (Z.of_nat (length (freeBeforeBuffer args))) (freeStackPointer args - freeStackBytes) freeStackBytes'),
        ('resource_10', 'resource_11', 'freeSeparate freeListsPointer freeListsBytes (freeStackPointer args - freeStackBytes) freeStackBytes'),
    ]
    for index, (left, right, text) in enumerate(separations):
        facts.append({'fact_id': 'wellformed:separate-' + str(index), 'kind': 'disjoint_ranges',
                      'status': 'supplied', 'terms': {'left': left, 'right': right, 'coq_statement': text},
                      'origin': clause(text)})
    return {'projection': {'facts': facts, 'original_wellformed_clauses': clauses,
                           'entry_assertion_changed': False, 'premises_added': []},
            'constants': values}


def system_shapes(machine, mapfile):
    source = definition_body(mapfile.read_text(), 'defaultMap')
    origin = bind(mapfile, declaration='defaultMap')

    def map_value(field):
        value, = [item.strip() for item in re.findall(r'\b' + field + r'\s*:=\s*([^;|]+)', source)]
        if value in ('true', 'false'):
            return Expr('bool', value=value == 'true').to_dict()
        if re.fullmatch(r'"[A-Za-z_]+"%string', value):
            return Expr('enum', value=value.split('"')[1]).to_dict()
        return bits(constant_from_source({**origin, 'field': field})['value'], 64).to_dict()

    if map_value('mapZiskPlatform') != Expr('bool', value=True).to_dict():
        raise ValueError('The default map is not the ZisK platform.')
    body = definition_body(machine.read_text(), 'machine_static_sys_regs').strip()[1:-1]
    positions = [-1, *_top_positions(body, ';'), len(body)]
    bindings = [bind(machine, declaration='machine_sys_regs'), origin]
    rows = []
    for left, right in zip(positions, positions[1:]):
        item = _strip_enclosure(body[left + 1:right])
        name, shape = re.match(r'KindReg "([^"]+)",\s*(.*)', item, re.S).groups()
        row = {'key': name, 'collection_ownership_id': 'resource_0', 'source_bindings': bindings,
               'original_shape': shape}
        if shape.startswith('ExactShape'):
            row['shape'] = 'exact'
            if 'RVal_Bool' in shape or 'RVal_Enum' in shape:
                field = re.search(r'\((map\w+) machine\)', shape)[1]
                row.update(sort='bool' if 'RVal_Bool' in shape else 'enum', width=None, value=map_value(field))
            else:
                if 'RegVal_Struct' in shape:
                    row['key'] = name + '.bits'
                match = re.search(r'Z_to_bv 64\s+(?:\((map\w+) machine\)|(0))', shape)
                row.update(sort='bits', width=64, value=map_value(match[1]) if match[1] else bits(0, 64).to_dict())
        elif 'MaskShape' in shape:
            match = re.search(r'MaskShape 64\s+\((map\w+) machine\)\s+\((map\w+) machine\)', shape)
            row.update(key=name + '.bits', shape='mask', sort='bits', width=64,
                       symbol=input_expr('fp_seed_' + name + '_bits', 64).to_dict(),
                       mask=map_value(match[1]), expected=map_value(match[2]))
        elif re.fullmatch(r'BitsShape 64', shape):
            row.update(shape='bits', sort='bits', width=64, symbol=input_expr('fp_seed_' + name, 64).to_dict())
        else:
            raise ValueError('Unsupported source shape: ' + shape)
        rows.append(row)
    tail = definition_body(machine.read_text(), 'machine_sys_regs')
    for name in re.findall(r'KindReg "(zisk_\w+)", BitsShape 64', tail):
        rows.append({'key': name, 'shape': 'bits', 'sort': 'bits', 'width': 64,
                     'symbol': input_expr('fp_seed_' + name, 64).to_dict(),
                     'collection_ownership_id': 'resource_0', 'source_bindings': bindings,
                     'original_shape': 'BitsShape 64'})
    return {'rows': rows, 'collection_ownership_id': 'resource_0', 'created_ownership': [], 'source_only': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--vocabulary', type=Path, required=True)
    options = parser.parse_args()
    output = options.output.resolve()
    output.mkdir(exist_ok=False)
    contract = ROOT / 'ZesuSsz/Contracts/AltFlFreeContract.v'
    layout = ROOT / 'ZesuSsz/Contracts/AltFlFree.v'
    machine = ROOT / 'InstrSpecs/Machine.v'
    mapfile = ROOT / 'ZesuSsz/Contracts/Machine.v'
    vocabulary = output / 'VOCABULARY.json'
    shutil.copyfile(options.vocabulary, vocabulary)
    load_resource_vocabulary(vocabulary, bind(vocabulary)['sha256'])
    index, function = trace_index(output)
    values = constants(layout)
    (output / 'DOMAIN.json').write_text(json.dumps(domain(contract, values), indent=2) + '\n')
    (output / 'SYSTEM-SHAPES.json').write_text(json.dumps(system_shapes(machine, mapfile), indent=2) + '\n')
    seed = public_seed(contract, layout, machine)
    seed['entry_pc'] = hex(function['entry'])
    seed['source_domain_binding'] = bind(output / 'DOMAIN.json')
    (output / 'SEED.json').write_text(json.dumps(seed, indent=2, ensure_ascii=False) + '\n')
    manifest = {'schema': 'fp301.seed-manifest.v1', 'function': FUNCTION,
                'domain': bind(output / 'DOMAIN.json'), 'seed': bind(output / 'SEED.json'),
                'trace_index': bind(index), 'generator': bind(Path(__file__))}
    (output / 'SEED-MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'seed_manifest': bind(output / 'SEED-MANIFEST.json'),
                      'instructions': len(function['rows']), 'blocks': len(function['blocks'])}))


if __name__ == '__main__':
    main()
