"""Prepare simultaneous entry replacements and their affected native block set."""

import argparse
from copy import deepcopy
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import sys
import tempfile
import traceback

from entry_chain_plan import derive
from entry_pilot_checker import install_inline, strict_loads, validate_inline

ROOT = Path(__file__).resolve().parents[4]


def digest(path):
    from binding_cache import digest as checked_digest
    return checked_digest(path)


def binding(path):
    path = Path(path).resolve()
    return {'path': str(path), 'sha256': digest(path)}


def read_bound(row):
    path = Path(row['path'])
    payload = path.read_bytes()
    if hashlib.sha256(payload).hexdigest() != row['sha256']:
        raise ValueError('A chain input changed: ' + str(path))
    return strict_loads(payload.decode())


def check_bindings(rows):
    from binding_cache import resolve_input
    seen = set(); parents = {}
    for row in rows:
        path = resolve_input(row['path'], parents)
        if path in seen:
            raise ValueError('A chain input binding repeats: ' + str(path))
        seen.add(path)
        if digest(path) != row['sha256']:
            raise ValueError('A chain input changed: ' + str(path))


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temp = tempfile.mkstemp(prefix='.entry-chain-', dir=path.parent)
    try:
        with os.fdopen(fd, 'w') as stream:
            json.dump(value, stream, indent=2, ensure_ascii=False, allow_nan=False)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temp, path)
    finally:
        if os.path.exists(temp):
            os.unlink(temp)


def relative(name):
    path = PurePosixPath(name)
    if (not isinstance(name, str) or path.is_absolute() or '..' in path.parts
            or str(path) != name or '\\' in name):
        raise ValueError('A chain output path is not contained.')
    return Path(name)


def install_answers(author, answer_set, mappings):
    """Validate every answer first. Mutate only a private author copy."""
    if not isinstance(answer_set, dict) or set(answer_set) != {'schema', 'entries'}:
        raise ValueError('The answer set has unsupported fields.')
    if answer_set['schema'] != 'entry-pilot.answer-set.v1':
        raise ValueError('The answer set has another schema.')
    entries = answer_set['entries']
    if not isinstance(entries, list) or not entries:
        raise ValueError('The answer set needs at least one entry.')
    by_case = {}
    for row in mappings:
        case = row['checker_case']
        if case['case_id'] in by_case:
            raise ValueError('The route repeats a case identifier.')
        by_case[case['case_id']] = case
    selected, targets, cases = set(), set(), []
    for response in entries:
        if not isinstance(response, dict):
            raise ValueError('An answer must be an object.')
        case_id = response.get('case_id')
        if not isinstance(case_id, str) or case_id not in by_case or case_id in selected:
            raise ValueError('An answer names an unknown or repeated case.')
        case = by_case[case_id]
        if case['eligible'] is not True or any(case['natural_cut_flags'].values()):
            raise ValueError('A replacement changes a protected cut.')
        validate_inline(response, case)
        target = int(case['target_pc'], 0)
        if target in targets:
            raise ValueError('The answer set repeats a target entry.')
        selected.add(case_id)
        targets.add(target)
        cases.append(case)
    result = deepcopy(author)
    for case, response in zip(cases, entries):
        result = install_inline(result, case, response)
    return result, cases


def selected_function(inventory, name):
    matches = [row for row in inventory['functions']
               if row['name'] == name or row['name'].rsplit('.', 1)[-1] == name]
    if len(matches) != 1:
        raise ValueError('The CFG does not name one function.')
    return matches[0]


def check_stage(before, after, receipt, field):
    """Reject changes outside the recorded helper metadata field."""
    restored = deepcopy(after)
    for addition in receipt['attachments']:
        path = addition['profile_path']
        if (len(path) != (9 if field == 'source_hashes' else 8)
                or path[:2] != ['design', 'blocks']
                or path[3:5] != ['support', 'additional_definitions']
                or path[6:8] != ['declaration', field]):
            raise ValueError('A helper stage reports another metadata path.')
        current, original = restored, before
        for key in path[:-1]:
            current, original = current[key], original[key]
        key = path[-1]
        if key in original:
            current[key] = deepcopy(original[key])
        else:
            del current[key]
    if restored != before:
        raise ValueError('A helper stage changed terms or unrelated metadata.')


def attach_metadata(profile, cases, metadata, source_root, attach_source, attach_edges):
    result, receipts = profile, []
    for case in cases:
        pc = case['target_pc']
        sources = [metadata['source_binding']] + [row['binding']
                   for row in metadata['data_source_bindings'] if row['target_pc'] == pc]
        for source in sources:
            changed, receipt = attach_source(result, entry_pc=pc, workspace=source_root, **source)
            check_stage(result, changed, receipt, 'source_hashes')
            result = changed
            receipts.append(receipt)
        changed, receipt = attach_edges(result, inventory_path=metadata['inventory']['path'],
            inventory_sha256=metadata['inventory']['sha256'],
            function_name=metadata['function'], entry_pc=pc)
        check_stage(result, changed, receipt, 'incoming_edges')
        result = changed
        receipts.append(receipt)
    return result, receipts


def check_interfaces(profile, cases, interfaces):
    expected = {row['pc']: row for row in interfaces['rows']}
    actual = {row['entry_pc']: row for row in profile['design']['blocks']}
    if len(actual) != len(profile['design']['blocks']):
        raise ValueError('The profile repeats an entry.')
    for case in cases:
        pc = case['target_pc']
        row, prior = actual[pc], expected[pc]
        if row['binders'] != prior['parent_binders'] or row['arguments'] != prior['parent_arguments']:
            raise ValueError('Simultaneous construction changed the accepted parent ABI: ' + pc)
        helpers = row['support']['additional_definitions']
        if len(helpers) != len(prior['helpers']):
            raise ValueError('Simultaneous construction changed the helper count: ' + pc)
        for helper, previous in zip(helpers, prior['helpers']):
            declaration = helper['declaration']
            if (declaration['entry_definition'] != previous['declaration']
                    or declaration['binders'] != previous['binders']
                    or declaration['arguments'] != previous['arguments']):
                raise ValueError('Simultaneous construction changed the accepted helper ABI: ' + pc)


def load_constructor(path):
    spec = importlib.util.spec_from_file_location('entry_chain_constructor', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def prepare(config, answer_path, output):
    """Render one coherent snapshot. This function cannot execute a proof."""
    output = Path(output).resolve()
    if output == ROOT or (output.is_relative_to(ROOT) and not output.is_relative_to(ROOT/'_build')):
        raise ValueError('The output directory must not modify the source tree.')
    output.mkdir(parents=True, exist_ok=False)
    stage = 'bindings'
    try:
        check_bindings(config['bindings'])
        if config['operation'] != 'prepare':
            raise ValueError('The source preparation route cannot launch native jobs.')
        metadata = read_bound(config['metadata'])
        if str(Path(answer_path).resolve()) != str(Path(metadata['answer_set']['path']).resolve()):
            raise ValueError('The answer path differs from the bound answer set.')
        answers = read_bound(metadata['answer_set'])
        author = read_bound(config['author'])
        inventory = read_bound(metadata['inventory'])
        interfaces = read_bound(metadata['interfaces'])
        stage = 'install_all'
        installed, cases = install_answers(author, answers, metadata['ordered_case_mapping'])
        function = selected_function(inventory, metadata['function'])
        module_map = {row['pc']: row['module'] for row in config['native_modules']}
        affected = derive(function['blocks'], [int(row['target_pc'], 0) for row in cases], module_map)
        save(output/'AUTHOR.json', installed)
        save(output/'AFFECTED-BLOCKS.json', affected)
        stage = 'construct_once'
        constructor = load_constructor(config['constructor'])
        profile = constructor.construct_profile(inventory, metadata['function'], installed,
            root=Path(config['source_root']), source_closure=read_bound(config['closure']),
            notation_choices=read_bound(config['notation']), registry_evidence=read_bound(config['registry']))
        save(output/'PROFILE-RAW.json', profile)
        stage = 'interfaces'
        check_interfaces(profile, cases, interfaces)
        stage = 'helper_metadata'
        from profile_sources import attach_helper_source
        from profile_edges import attach_helper_edges
        profile, receipts = attach_metadata(profile, cases, metadata, config['source_root'],
                                            attach_helper_source, attach_helper_edges)
        save(output/'PROFILE.json', profile)
        save(output/'HELPER-METADATA-STAGES.json', receipts)
        stage = 'build'
        design = constructor.build(inventory, metadata['function'], profile,
            root=Path(config['source_root']), generator=Path(config['constructor']))
        save(output/'DESIGN.json', design)
        stage = 'render'
        from render_support import render_support
        outputs = render_support(design, Path(config['source_root']), name_prefix=config['name_prefix'])
        if set(map(str, outputs)) != set(config['generated_outputs']):
            raise ValueError('The chain renderer changed its output set.')
        rendered = []
        for name, text in outputs.items():
            path = output/'rendered'/relative(str(name))
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            rendered.append(binding(path))
        check_bindings(config['bindings'])
        result = {'schema': 'entry-chain.preparation-result.v1', 'status': 'prepared',
                  'replacement_count': len(cases), 'affected_block_count': len(affected),
                  'constructor_calls': 1, 'render_calls': 1, 'outputs': rendered,
                  'answer_set': metadata['answer_set'], 'metadata': config['metadata'],
                  'profile': binding(output/'PROFILE.json'), 'design': binding(output/'DESIGN.json'),
                  'proof_ran': False, 'compiler_ran': False, 'claims_created': False,
                  'native_success': None}
        save(output/'RESULT.json', result)
        return result
    except Exception as error:
        save(output/'FIRST-FAILURE.json', {'stage': stage, 'exception': type(error).__name__,
             'error': str(error), 'traceback': traceback.format_exc(),
             'proof_ran': False, 'compiler_ran': False})
        raise


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('answer_set', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args(argv)
    config_path = Path(os.environ.get('CHECK_ENTRY_CHAIN_CONFIG', ROOT/'_build/check-entry-chain/CONFIG.json'))
    config = strict_loads(config_path.read_text())
    if config.get('schema')=='entry-chain.execution-runtime.v1':
        expected=config['identity']['answer_set']
        if digest(args.answer_set)!=expected['sha256']:
            raise ValueError('The chain answer set differs from the bound runtime.')
        if args.output.resolve()!=Path(config['scheduler_output']).resolve():
            raise ValueError('The chain output differs from the bound runtime.')
        os.execv(sys.executable,[sys.executable,str(ROOT/'tools/block/entry_chain_scheduler.py'),
                                str(config_path.resolve()),digest(config_path)])
    if config['schema'] != 'entry-chain.runtime.v1':
        raise ValueError('The chain route has another schema.')
    result = prepare(config, args.answer_set, args.output)
    print(json.dumps({key: result[key] for key in ['status', 'replacement_count', 'affected_block_count',
                                                 'constructor_calls', 'render_calls', 'proof_ran']}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
