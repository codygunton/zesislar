"""Require declaration and resource lookup checks before a native launch."""
import argparse
import asyncio
import json
from pathlib import Path

import launch_entries as declarations
import launch_resources as resources


def prepare_rows(rows, workspace, function):
    if not isinstance(rows, list) or not rows:
        raise ValueError('The launch preflight needs selected entries and resources.')
    if any(not isinstance(row, dict) or set(row) != {'entry', 'resource'} for row in rows):
        raise ValueError('The launch preflight row has invalid fields.')
    declarations.prepare_entries([row['entry'] for row in rows], workspace, function)
    return [resources.make_plan(row['entry'], row['resource'], workspace, function) for row in rows]


def read_manifest(path):
    path = Path(path).resolve(strict=True)
    manifest = json.loads(path.read_bytes())
    if (not isinstance(manifest, dict) or set(manifest) != {'schema', 'workspace', 'function', 'rows'}
            or type(manifest['schema']) is not int or manifest['schema'] != 1
            or not isinstance(manifest['workspace'], str) or not isinstance(manifest['function'], str)
            or not manifest['function']):
        raise ValueError('The launch manifest has an invalid schema.')
    workspace = Path(manifest['workspace']).resolve(strict=True)
    checked = declarations.checked_file(declarations.file_reference(path), workspace)
    return manifest, checked, workspace


async def check_launch(manifest_path, output, session_factory):
    """Keep both stages separate and release only the complete selected set."""
    manifest, manifest_input, workspace = read_manifest(manifest_path)
    rows, function = manifest['rows'], manifest['function']
    output = Path(output).resolve()
    if not output.is_relative_to(workspace) or output.exists():
        raise ValueError('The launch preflight needs a fresh workspace output.')
    prepare_rows(rows, workspace, function)
    output.mkdir(parents=True)
    entry_result = await declarations.check_entries([row['entry'] for row in rows], workspace,
        function, output / 'declarations', session_factory)
    lookup_result = None
    if entry_result['passed'] is True:
        lookup_result = await resources.check_resources(rows,
            declarations.file_reference(output / 'declarations/REPORT.json'), workspace, function,
            output / 'resources', session_factory)
    declarations.unchanged_file(manifest_input)
    result = {'schema': 2, 'function': function, 'workspace': str(workspace), 'manifest': manifest_input,
              'passed': (entry_result['passed'] is True
                                     and lookup_result is not None and lookup_result['passed'] is True),
              'selected_entries': entry_result['selected_entries'],
              'checked_entries': entry_result['checked_entries'], 'entries': entry_result['entries'],
              'declarations': declarations.file_reference(output / 'declarations/REPORT.json'),
              'resources': declarations.file_reference(output / 'resources/REPORT.json') if lookup_result else None,
              'primary_calls': 0, 'scope': 'Declaration, loaded objects, and exact instruction lookup only.'}
    (output / 'REPORT.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def verify_release(binding, workspace, resource_specs):
    """Check both receipts and every retained source before worker admission."""
    workspace = Path(workspace).resolve(strict=True)
    checked = declarations.checked_file(binding, workspace)
    value = json.loads(Path(checked['resolved']).read_bytes())
    if (type(value.get('schema')) is not int or value['schema'] != 2 or value.get('passed') is not True
            or type(value.get('selected_entries')) is not int or value['selected_entries'] <= 0
            or type(value.get('checked_entries')) is not int
            or value['checked_entries'] != value['selected_entries']
            or not isinstance(value.get('entries'), list)
            or len(value['entries']) != value['selected_entries']
            or not isinstance(resource_specs, dict) or len(resource_specs) != value['selected_entries']):
        raise ValueError('The launch receipt does not prove both checks for every entry.')
    declarations.unchanged_file(value['manifest'])
    manifest, manifest_input, manifest_workspace = read_manifest(value['manifest']['binding']['path'])
    if (manifest_input != value['manifest'] or manifest_workspace != workspace
            or value.get('workspace') != str(workspace) or value.get('function') != manifest['function']):
        raise ValueError('The launch receipt substituted its manifest or function.')
    prepare_rows(manifest['rows'], workspace, manifest['function'])
    expected_entries = {row['entry']['id']: row['entry'] for row in manifest['rows']}
    if {row['entry']['id']: row['resource'] for row in manifest['rows']} != resource_specs:
        raise ValueError('The launch receipt differs from its manifest resources.')
    children = {}
    for name in ('declarations', 'resources'):
        child = declarations.checked_file(value.get(name), workspace)
        record = json.loads(Path(child['resolved']).read_bytes())
        if (type(record.get('schema')) is not int or record['schema'] != 1
                or record.get('input_error') is not None
                or record.get('passed') is not True or type(record.get('selected_entries')) is not int
                or record['selected_entries'] != value['selected_entries']
                or type(record.get('checked_entries')) is not int
                or record['checked_entries'] != value['selected_entries']
                or not isinstance(record.get('entries'), list)
                or len(record['entries']) != value['selected_entries']):
            raise ValueError('A launch stage is incomplete or refused.')
        children[name] = record
    if children['declarations']['entries'] != value['entries']:
        raise ValueError('The launch receipt substituted its declaration entries.')
    resource_declarations = children['resources'].get('declarations', {}).get('binding')
    if resource_declarations != value['declarations']:
        raise ValueError('The resource receipt refers to different declarations.')
    seen = set()
    for entry, lookup in zip(value['entries'], children['resources']['entries']):
        name = entry.get('id')
        if (not isinstance(name, str) or name in seen or name not in resource_specs
                or entry.get('passed') is not True or lookup.get('passed') is not True
                or entry.get('normal_context_closure') is not True
                or entry.get('owned_pet_exited') is not True
                or entry.get('journal', {}).get('retention_failed') is not False
                or lookup.get('resource_checked') is not True
                or lookup.get('id') != name or lookup.get('original_source') != entry.get('source')
                or lookup.get('resource') != resource_specs[name]
                or lookup.get('normal_context_closure') is not True
                or lookup.get('owned_pet_exited') is not True
                or lookup.get('journal', {}).get('retention_failed') is not False):
            raise ValueError('The launch resource association differs or lacks owned closure.')
        expected_entry = expected_entries[name]
        if (entry['source']['binding'] != expected_entry['source']
                or {module: artifact['binding'] for module, artifact in entry['artifacts'].items()}
                    != expected_entry['artifacts']):
            raise ValueError('The launch receipt differs from its manifest entry.')
        seen.add(name)
        declarations.unchanged_file(entry['source'])
        declarations.unchanged_file(lookup['source'])
        index = declarations.checked_file(resource_specs[name]['index_source'], workspace)
        declarations.unchanged_file(lookup['index_source'])
        if lookup['index_source'] != index:
            raise ValueError('The resource receipt substituted its instruction-map source.')
        expected = resources.instruction_entry(Path(index['resolved']).read_text(),
            resource_specs[name]['index_module'], int(resource_specs[name]['pc'], 16))
        if lookup.get('expected_instruction') != expected:
            raise ValueError('The resource receipt selected a different instruction.')
        for artifact in entry['artifacts'].values():
            declarations.unchanged_file(artifact)
        if not isinstance(lookup.get('exports'), list) or not lookup['exports']:
            raise ValueError('The resource receipt lacks its complete exports.')
        stages = ['entry', 'environment', 'map-entry', 'registration', 'opening', 'resources',
                  'lookup', 'lookup-bound', 'selected', 'closed']
        if [row.get('stage') for row in lookup['exports']] != stages:
            raise ValueError('The resource receipt omits a required structural stage.')
        for exported in lookup['exports']:
            declarations.unchanged_file(exported['export'])
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--mcp-command', required=True)
    args = parser.parse_args()
    manifest, _, workspace = read_manifest(args.manifest)
    result = asyncio.run(check_launch(args.manifest, args.output,
                                      declarations.owned_sessions(args.mcp_command, workspace)))
    if result['passed']:
        verify_release(declarations.file_reference(args.output / 'REPORT.json'), workspace,
                       {row['entry']['id']: row['resource'] for row in manifest['rows']})
    print(json.dumps({'passed': result['passed'], 'report': declarations.file_reference(args.output / 'REPORT.json'),
                      'primary_calls': 0}))
    return 0 if result['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
