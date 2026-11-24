"""Bind decodeItem's source-pass inputs from its frozen seed (render_function.sh INPUTS).

decodeItem's profile is hand-written and has no `entry_interface` row: its public seed, domain
facts, system shapes and resource vocabulary are the frozen FP-20261102 inputs its generated tree
was rendered from, committed under `decodeItem.inputs/`. This tool copies them and binds the
function's CFG row and pinned traces of this checkout (function_inputs.trace_index: the
`closure` traces, which `make stock-native-indexes` writes). No proof runs.

Usage: decodeitem_inputs.py --output DIR
"""
from pathlib import Path
import argparse, json, shutil, sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from function_inputs import bind, trace_index

FROZEN = HERE / 'decodeItem.inputs'
FILES = ('DOMAIN.json', 'SEED.json', 'SYSTEM-SHAPES.json', 'VOCABULARY.json')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    output = parser.parse_args().output.resolve()
    output.mkdir(exist_ok=False)
    for name in FILES:
        shutil.copyfile(FROZEN / name, output / name)
    index, function = trace_index(output, 'rlp.decodeItem', 'ZesuSsz.Stock.DecodeItem', root=HERE.parents[2])
    manifest = {'schema': 'fp301.seed-manifest.v1', 'function': 'rlp.decodeItem',
                'domain': bind(output / 'DOMAIN.json'), 'seed': bind(output / 'SEED.json'),
                'trace_index': bind(index), 'generator': bind(Path(__file__))}
    (output / 'SEED-MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'seed_manifest': bind(output / 'SEED-MANIFEST.json'),
                      'instructions': len(function['rows']), 'blocks': len(function['blocks'])}))


if __name__ == '__main__':
    main()
