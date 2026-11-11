#!/usr/bin/env python3
"""Move the stock recipe to a rebuilt ELF and rebind its derived files.

`build.py` writes a fresh recipe for a new build directory, but that recipe
lacks the platform, machine-map, trace and generated-file records, and no
tool merged the trace fragments back. These commands keep every recipe key:

  rebase --built DIR   take the ELF and its build records from a build.py output
  rehash               re-record changed inputs; invalidate bindings on a new identity
  merge-traces GROUP   bind regenerated trace groups from their manifest fragments
  rebind               bind the remaining derived files to the current identity

`regenerate.py` runs them with the generators in order.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/stock_zisk'))
import manifest  # noqa: E402

BUILD = ROOT / 'build/stock-zisk'
TRACES = ROOT / 'generated/isla-traces/stock-zisk'
PINS = [ROOT / 'Makefile', ROOT / 'tools/test_function_preparation.py']
# Fields that build.py derives from one build of the ELF.
BUILD_FIELDS = ['elf_sha256', 'runtime_library_sha256', 'linker_script_sha256', 'adapters',
                'link_without_exit_adapter', 'measurements', 'runtime_provenance',
                'object_command', 'link_command', 'build_dir', 'jobs']
BUILD_INPUTS = ['runtime', 'linker', 'guest/Makefile', 'guest/build.zig', 'guest/build.zig.zon',
                'guest/src/zisk_host.zig']
NATIVE_GROUPS = {'decodeItem', 'closure'}


def read(build):
    # The repository omits the disassembly; every refresh hashes it.
    for name, command in manifest.REPORTS.items():
        if not (build / name).exists():
            (build / name).write_text(manifest.normalized_report(command, build / 'zesu-zisk.elf'))
    return json.loads((build / 'build-recipe.json').read_text())


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def symbols(build):
    result = {}
    for row in (build / 'symbols.txt').read_text().splitlines():
        fields = row.split()
        if len(fields) >= 8 and fields[0].endswith(':') and fields[0][:-1].isdigit():
            result[fields[7]] = int(fields[1], 16)
    return result


def extents(recipe):
    loads = [s for s in recipe['elf_layout']['segments'] if s['p_type'] == 'PT_LOAD']
    text = next(s for s in loads if s['p_flags'] == 1)
    rodata = next(s for s in loads if s['p_flags'] == 4)
    return [text['p_vaddr'] + text['p_memsz'], rodata['p_vaddr'], rodata['p_vaddr'] + rodata['p_memsz']]


def rebase(build, built, keep_object=False, root=ROOT, pins=PINS):
    """Replace the ELF and its build records; keep every other recipe key."""
    recipe, fresh = read(build), json.loads((built / 'build-recipe.json').read_text())
    if manifest.digest(built / 'zesu-zisk.elf') != fresh['elf_sha256']:
        raise ValueError('The built ELF differs from its recipe.')
    # The build may have run in another checkout; its project paths name this checkout's files.
    built_root = Path(fresh['inputs']['builder/build.py']['path']).resolve().parents[2]
    relative = lambda value: manifest.relative_project_paths(  # noqa: E731
        manifest.relative_project_paths(value, built_root), root)
    old_sha, old_extents, old_symbols = recipe['elf_sha256'], extents(recipe), symbols(build)
    shutil.copyfile(built / 'zesu-zisk.elf', build / 'zesu-zisk.elf')
    for name, command in manifest.REPORTS.items():
        (build / name).write_text(manifest.normalized_report(command, build / 'zesu-zisk.elf'))
    for key in BUILD_FIELDS:
        recipe[key] = relative(fresh[key])
    for name in BUILD_INPUTS + ([] if keep_object else ['object']):
        recipe['inputs'][name] = relative(fresh['inputs'][name])
    if not keep_object:
        recipe['stock_object_sha256'] = fresh['stock_object_sha256']
    recipe['elf_layout'] = manifest.elf_layout(build / 'zesu-zisk.elf')
    new_sha, new_symbols = recipe['elf_sha256'], symbols(build)
    # Documents and trace-input descriptors name the ELF, its extents and memcpy.
    substitutions = {old_sha: new_sha}
    substitutions.update({hex(a): hex(b) for a, b in zip(old_extents, extents(recipe)) if a != b})
    if old_symbols.get('memcpy') != new_symbols.get('memcpy'):
        substitutions[hex(old_symbols['memcpy'])] = hex(new_symbols['memcpy'])
    for name in ['PLATFORM.md', 'RUNTIME.md']:
        path = build / name
        if path.exists():
            text = path.read_text()
            for old, new in substitutions.items():
                text = text.replace(old, new)
            path.write_text(text)
    for path in build.glob('*-trace-input.json'):
        descriptor = json.loads(path.read_text())
        if descriptor.get('schema') == 'stock-zisk.eql-trace-input.v1':
            descriptor['elf_sha256'] = new_sha
            write_json(path, descriptor)
    pin_changes = {}
    for path in build.glob('*-policy/PATH-MAP.json'):
        source_map = json.loads(path.read_text())
        elf = source_map.get('input_files', {}).get('elf')
        if elf and elf['sha256'] != new_sha:
            before = manifest.digest(path)
            elf['sha256'] = new_sha
            write_json(path, source_map)
            pin_changes[before] = manifest.digest(path)
    for path in pins:
        text = path.read_text()
        for old, new in pin_changes.items():
            text = text.replace(old, new)
        path.write_text(text)
    recipe['rebased_from'] = {'elf_sha256': old_sha, 'artifact_identity': recipe['artifact_identity']}
    invalidate(recipe)
    recipe['project_derived'], recipe['traces'] = {}, {}
    manifest.refresh(build, recipe)
    return recipe


def invalidate(recipe):
    recipe['invalidated_derived'] = sorted(set(recipe.get('invalidated_derived', [])) | set(recipe.get('derived', {})))
    recipe['derived'] = {}


def rehash(build, root=ROOT):
    """Re-record every changed input file; a new identity invalidates the bindings."""
    recipe = read(build)
    changed = []
    for name, record in recipe['inputs'].items():
        path = Path(record.get('path', ''))
        path = path if path.is_absolute() else root / path
        if 'path' in record and path.is_file() and manifest.digest(path) != record['sha256']:
            record['sha256'] = manifest.digest(path)
            changed.append(name)
    identity = manifest.artifact_identity(recipe)
    if identity != recipe['artifact_identity']:
        invalidate(recipe)
        for record in recipe.get('project_derived', {}).values():
            record['artifact_identity'] = identity
    manifest.refresh(build, recipe)
    return changed


def update_group_inputs(inputs, group, fragment_inputs, root=ROOT):
    """Update the recipe rows of one trace-only group from its fragment.

    The trace record's input_hashes bind every generation input. Recipe rows
    exist for some groups only, keyed by input name or by path; update those
    rows, keep their fields, and add none."""
    for name, row in fragment_inputs.items():
        row = manifest.relative_project_paths(row, root)
        key = next((key for key, old in inputs.items() if key.startswith(group + '/')
                    and (key == group + '/' + name or old.get('path') == row['path'])), None)
        if key is not None:
            inputs[key] = {field: row.get(field, value) for field, value in inputs[key].items()}


def trace_record(old, fragment):
    """Keep the existing keys and their order; the fragment's values win; the binding is complete."""
    return {**old, **fragment, 'manifest_binding_pending': False}


def merge_traces(build, groups, traces=TRACES, root=ROOT):
    """Bind each group's fragment: project files, trace record and trace-only inputs."""
    recipe = read(build)
    identity = recipe['artifact_identity']
    for group in groups:
        fragment = json.loads((traces / group / 'manifest-fragment.json').read_text())
        names = list(fragment['derived'])
        names += [str((traces / extra).relative_to(root)) for extra in
                  (group + '.selected.dump', group + '.frontend.dune') if (traces / extra).exists()]
        prefix = str((traces / group).relative_to(root)) + '/'
        records = {name: {'path': name, 'sha256': manifest.digest(root / name),
                          'schema_version': 1, 'artifact_identity': identity} for name in names}
        old = [name for name in recipe['project_derived']
               if name.startswith(prefix) or name.startswith(prefix[:-1] + '.')]
        if set(old) != set(records):
            # A changed file set moves the group to the end; an equal set keeps its order.
            for name in old:
                del recipe['project_derived'][name]
        recipe['project_derived'].update(records)
        record = trace_record(recipe['traces'].get(group, {}), fragment['traces'])
        if record.get('kind') == 'trace_only':
            update_group_inputs(recipe['inputs'], group, fragment['inputs'], root)
        recipe['traces'][group] = record
        measurement = traces / group / 'generation-measurement.json'
        if group in NATIVE_GROUPS and measurement.exists():
            shutil.copyfile(measurement, build / 'traces' / (group + '-generation.json'))
    after = manifest.artifact_identity(recipe)
    if after != identity:
        invalidate(recipe)
        for record in recipe['project_derived'].values():
            record['artifact_identity'] = after
    manifest.refresh(build, recipe)
    return after


COVERAGE = ['elf_sha256', 'instruction_count', 'generated_count', 'full_closure_coverage',
            'unsupported_runtime_boundaries', 'instruction_modules_validated', 'manifest_binding_pending']


def summarize_traces(path, recipe):
    """closure.py writes the static verification report; add the bound native trace coverage."""
    native = {group: recipe['traces'][group] for group in ('decodeItem', 'closure') if group in recipe['traces']}
    if len(native) != 2 or not path.exists():
        return
    report = json.loads(path.read_text())
    decode, closure = native['decodeItem'], native['closure']
    report['trace_generation'] = (
        f"{decode['generated_count']}/{decode['instruction_count']} decodeItem traces; "
        f"{closure['generated_count']}/{closure['instruction_count']} closure traces"
        + ('; CSR 0x813 remains unmodeled' if closure['unsupported_runtime_boundaries'] else ''))
    report['trace_coverage'] = {group: dict({key: record[key] for key in COVERAGE},
                                            bound_artifact_identity=recipe['artifact_identity'])
                                for group, record in native.items()}
    write_json(path, report)


def rebind(build):
    """Bind every invalidated file that has no generator; the audit names the identity."""
    recipe = read(build)
    identity = recipe['artifact_identity']
    audit_path = build / 'platform-audit.json'
    audit = json.loads(audit_path.read_text())
    if audit.get('artifact_identity') != identity:
        audit['artifact_identity'] = identity
        write_json(audit_path, audit)
    summarize_traces(build / 'verification.json', recipe)
    for name in recipe.get('invalidated_derived', []):
        if (build / name).exists():
            recipe['derived'][name] = {'artifact_identity': identity, 'schema_version': 1}
    missing = [name for name in recipe.get('invalidated_derived', []) if not (build / name).exists()]
    recipe['invalidated_derived'] = missing
    manifest.refresh(build, recipe)
    return missing


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--build', type=Path, default=BUILD)
    commands = parser.add_subparsers(dest='command', required=True)
    command = commands.add_parser('rebase')
    command.add_argument('--built', type=Path, required=True)
    command.add_argument('--keep-object', action='store_true',
                         help='keep the recorded object when it links to the same ELF')
    commands.add_parser('rehash')
    command = commands.add_parser('merge-traces')
    command.add_argument('groups', nargs='+')
    commands.add_parser('rebind')
    args = parser.parse_args()
    build = args.build.resolve()
    if args.command == 'rebase':
        print('rebased to', rebase(build, args.built.resolve(), args.keep_object)['elf_sha256'])
    elif args.command == 'rehash':
        print('rehashed', rehash(build))
    elif args.command == 'merge-traces':
        print('identity', merge_traces(build, args.groups))
    else:
        missing = rebind(build)
        if missing:
            sys.exit(f'Derived files without output: {missing}')
        print('rebound', read(build)['artifact_identity'])


if __name__ == '__main__':
    main()
