"""Generic source-pass input helpers shared by the per-function input builders.

bind: path and SHA-256 binding. trace_index: a function's CFG row and its
pinned raw and Rocq traces. system_shapes: the source system-register rows of
the selected machine map. No proof runs.
"""
from pathlib import Path
import hashlib, json, re, subprocess, sys

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(subprocess.run(['git', '-C', str(ROOT), 'rev-parse', '--path-format=absolute',
                            '--git-common-dir'], capture_output=True, text=True, check=True).stdout.strip()).parent
sys.path.insert(0, str(ROOT / 'tools/block'))
from entry_seed import definition_body
from forward_resources import _strip_enclosure, _top_positions
from source_domain import constant_from_source
from symbolic_state import Expr, bits, input_expr


def bind(path, **more):
    path = Path(path)
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), **more}


def trace_index(output, name, namespace):
    cfg = BASE / 'build/stock-zisk/cfg.json'
    recipe = BASE / 'build/stock-zisk/build-recipe.json'
    traces = BASE / 'generated/isla-traces/stock-zisk/closure'
    function = next(row for row in json.loads(cfg.read_text())['functions'] if row['name'] == name)
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
        'schema': 'source.instruction-trace-index.v1', 'namespace': namespace,
        'ELF_sha256': elf, 'function': bind(function_path), 'coverage': bind(traces / 'coverage.json'),
        'recipe': bind(recipe), 'instruction_pairs': rows, 'proof_calls': 0}, indent=2) + '\n')
    return index_path, function


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
