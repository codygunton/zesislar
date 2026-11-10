"""Render block callers from the design table.

A design caller states the block's entry, one `instr_pre` premise for each
exit, and the selected code. A block with successors gets the entry of each
successor, in design-table order; a block with a return clause gets the
function-return package. The statement comes from render_block_caller and the
proof is always `zesu_block2.`; this renderer writes declarations only. A block
that has a residual module imports it, as render_caller does.

The fixture binds the design table by sha256 and stores one sha256 for each
rendered caller. --check renders again and compares the design hash, the
caller hashes and the committed files. --compare renders other blocks and
reports, without writing, whether a committed caller is byte-identical or
statement-identical to the design rendering.

Usage: render_design_callers.py [--function NAME] (--write | --check | --compare CASE...)

The block list, the fixture and the design table come from the function
profile (`design_callers` in tools/block/functions/NAME.json).
"""
from pathlib import Path
import argparse, hashlib, json, sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/block'))
from function_profiles import load_profile
from production_modules import statement
from render_fp301_statements import (render_block_caller, residual_import, return_precondition,
                                     successor_precondition)
from return_exit import return_blocks

SCHEMA = 'fp301-design-callers.v1'
RENDERER = 'tools/block/render_design_callers.py'


def sha256(text):
    return hashlib.sha256(text.encode()).hexdigest()


def design_binding(profile):
    path = profile['design_callers']['design']
    return {'path': path, 'sha256': hashlib.sha256((ROOT / path).read_bytes()).hexdigest()}


def load_design(profile):
    return json.loads((ROOT / profile['design_callers']['design']).read_text())


def suffix(profile, pc):
    prefix = profile['pc_prefix']
    if not pc.startswith(prefix):
        raise ValueError('A design address lies outside the function: ' + pc)
    return pc[len(prefix):]


def exits(profile, design, block):
    """Return (premises, imports) of one block's exits, from the design table."""
    pc = int(profile.pc(block), 16)
    rows = [row for row in design['blocks'] if int(row['entry_pc'], 0) == pc]
    if len(rows) != 1:
        raise ValueError('The design table lacks one row for block ' + block)
    own = [profile.qualified('Pilot' + block + kind) for kind in ('Entries', 'Structural')]
    if pc in return_blocks(design):
        return [return_precondition(profile)], own + [profile.qualified('FunctionReturnStructural')]
    premises, imports = [], list(own)
    for successor in rows[0]['successor_pcs']:
        name = suffix(profile, successor)
        premises.append(successor_precondition(profile, name))
        imports += [profile.qualified('Pilot' + name + kind) for kind in ('Entries', 'Structural')]
    return premises, list(dict.fromkeys(imports))


def caller_source(profile, design, block):
    premises, imports = exits(profile, design, block)
    return residual_import(render_block_caller(profile, block, premises, imports))


def output_path(profile, block):
    return profile['callers_directory'] + '/Caller' + block + '.v'


def lemma(profile, block):
    return 'DesignedBoundary_' + profile.pc(block)[2:]


def render_rows(profile):
    design = load_design(profile)
    rows = []
    for block in profile['design_callers']['blocks']:
        source = caller_source(profile, design, block)
        premises, imports = exits(profile, design, block)
        rows.append({'case': block, 'output': output_path(profile, block), 'premises': premises,
                     'imports': imports, 'statement_sha256': sha256(statement(source, lemma(profile, block))),
                     'sha256': sha256(source), 'source': source})
    return rows


def fixture_record(profile, rows):
    return {'schema': SCHEMA, 'renderer': RENDERER, 'design': design_binding(profile),
            'callers': [{key: value for key, value in row.items() if key != 'source'} for row in rows]}


def check(profile):
    """Return the list of mismatches between the fixture, the renderer and the committed files."""
    fixture = json.loads((ROOT / profile['design_callers']['fixture']).read_text())
    rows = render_rows(profile)
    errors = []
    if fixture.get('schema') != SCHEMA:
        errors.append('The fixture schema is not ' + SCHEMA + '.')
    if fixture.get('design') != design_binding(profile):
        errors.append('The design table changed since the callers were rendered.')
    if fixture.get('callers') != fixture_record(profile, rows)['callers']:
        errors.append('The fixture caller rows differ from the renderer.')
    for row in rows:
        path = ROOT / row['output']
        if not path.is_file() or path.read_text() != row['source']:
            errors.append('The committed caller differs from the renderer: ' + row['output'])
    return errors


def compare(profile, blocks):
    """Compare committed callers of other blocks with the design rendering."""
    design = load_design(profile)
    result = []
    for block in blocks:
        source = caller_source(profile, design, block)
        committed = (ROOT / output_path(profile, block)).read_text()
        name = lemma(profile, block)
        result.append({'case': block, 'byte_identical': committed == source,
                       'statement_identical': statement(committed, name) == statement(source, name)})
    return result


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write', action='store_true')
    group.add_argument('--check', action='store_true')
    group.add_argument('--compare', nargs='+', metavar='CASE')
    parser.add_argument('--function', default=None, help='function profile (default: decodeItem)')
    options = parser.parse_args()
    profile = load_profile(options.function)
    if options.compare:
        for row in compare(profile, options.compare):
            print(json.dumps(row))
        return 0
    if options.check:
        errors = check(profile)
        for error in errors:
            print(error)
        if errors:
            return 1
        print('Design callers match the design table.')
        return 0
    rows = render_rows(profile)
    for row in rows:
        (ROOT / row['output']).write_text(row['source'])
    (ROOT / profile['design_callers']['fixture']).write_text(
        json.dumps(fixture_record(profile, rows), indent=2, ensure_ascii=False) + '\n')
    print('Rendered', len(rows), 'design callers.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
