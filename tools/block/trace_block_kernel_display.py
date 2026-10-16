"""Validate bounded displays against pinned reload and membership evidence.

The caller binds the reader, toolchain, plan, and argv from its sealed runtime.
Python verifies identities and record associations. It does not run Marshal.
"""
import json
from collections.abc import Mapping, Sequence
from trace_block_text import StreamText
from pathlib import Path, PurePosixPath
import re

from trace_block_kernel import artifact as _artifact, _hash, _integer, _json

LIMITS = {'depth': 60, 'nodes': 20000, 'text_bytes_per_mode': 1048576}
PRINT_STATUSES = {'primary-accepted', 'fallback-placeholder-typecheck', 'fallback-display-budget'}
MARKER_REASONS = {'depth-limit', 'shared-reference', 'node-budget', 'evar-reference'}
RELOAD_CHECKS = {'hash', 'bytes', 'schema', 'toolchain', 'context', 'evar_references',
                 'remarshal_bytes', 'trailing_bytes_absent'}
MEMBERSHIP_CHECKS = {'root-membership', 'binder-context', 'catalog-association',
                     'subtree-marshal-bytes', 'evar-reference'}
HOLE = re.compile(r'\belided_[0-9a-f]{8}_(?:0|[1-9][0-9]*)\b')


class MetadataEvidence:
    """Bind an open ArtifactReader to this validator without changing raw evidence."""
    def __init__(self, reader):
        self.reader = reader

    def __fspath__(self):
        return str(self.reader.root)


def _array(value):
    return isinstance(value, Sequence) and not isinstance(value, (str, bytes))


def _fields(value, names):
    if not isinstance(value, Mapping) or set(value) != set(names.split()):
        raise ValueError('The kernel evidence has unsupported fields.')


def artifact(root, reference):
    _fields(reference, 'path sha256 bytes')
    return _artifact(root, {key: reference[key] for key in reference})


def _identity(reference):
    _fields(reference, 'path sha256 bytes')
    return (reference['path'], reference['sha256'], reference['bytes'])


def _bounded_text(value):
    if isinstance(value, str):
        parts = (value,)
    elif isinstance(value, StreamText):
        parts = value.iter_text()
    else:
        raise ValueError('The bounded display text is not a text value.')
    fragments, size = [], 0
    for part in parts:
        size += len(part.encode('utf-8'))
        if size > LIMITS['text_bytes_per_mode']:
            raise ValueError('The bounded display text exceeds its exact byte limit.')
        fragments.append(part)
    return ''.join(fragments)


def _schema(record, kind=None):
    if type(record.get('schema')) is not int or record['schema'] != 1:
        raise ValueError('The bounded display evidence has an unsupported schema.')
    if kind is not None and record.get('kind') != kind:
        raise ValueError('The bounded display evidence has an unsupported kind.')


def _name(value):
    if not isinstance(value, str) or not value:
        raise ValueError('The bounded display root identity is invalid.')
    return value


def _node(value):
    _fields(value, 'root_id child_path')
    _name(value['root_id'])
    if not _array(value['child_path']):
        raise ValueError('The subtree path is not an ordered integer list.')
    for part in value['child_path']:
        _integer(part)


def _read(root, reference):
    return root.reader.read(reference) if isinstance(root, MetadataEvidence) else _json(artifact(root, reference))


def _exact(left, right):
    if isinstance(left, Mapping) or isinstance(right, Mapping):
        return (isinstance(left, Mapping) and isinstance(right, Mapping) and set(left) == set(right)
                and all(_exact(left[key], right[key]) for key in left))
    if _array(left) or _array(right):
        return _array(left) and _array(right) and len(left) == len(right) and all(_exact(a,b) for a,b in zip(left,right))
    if isinstance(left, StreamText) or isinstance(right, StreamText):
        return isinstance(left, (str, StreamText)) and isinstance(right, (str, StreamText)) and left == right
    return type(left) is type(right) and left == right


def _same(value, field, expected):
    if field not in value or not _exact(value[field], expected):
        raise ValueError('The bounded display evidence has a different ' + field + ' binding.')


def _references(root, value, fields):
    for field in fields:
        artifact(root, value[field])


def _marker(root, reference, expected_toolchain_ref):
    value = _read(root, reference)
    special = value.get('reason') == 'evar-reference'
    _fields(value, 'schema kind reason depth sha256 bytes hash_scope size_unit sidecar context_ref '
                   'evar_catalog_ref toolchain_ref node_ref' + (' source_evar' if special else ''))
    _schema(value, 'kernel-elision')
    if not isinstance(value['reason'], str) or value['reason'] not in MARKER_REASONS:
        raise ValueError('The bounded display marker has an unsupported reason.')
    _integer(value['depth'])
    if value['depth'] > LIMITS['depth']:
        raise ValueError('The bounded display marker exceeds its depth limit.')
    _integer(value['bytes'])
    _hash(value['sha256'])
    if value['hash_scope'] != 'pinned-marshal-bytes' or value['size_unit'] != 'bytes':
        raise ValueError('The bounded display marker has an unsupported hash or size meaning.')
    _same(value, 'toolchain_ref', expected_toolchain_ref)
    _references(root, value, ('sidecar', 'context_ref', 'evar_catalog_ref', 'toolchain_ref'))
    if value['sha256'] != value['sidecar']['sha256'] or value['bytes'] != value['sidecar']['bytes']:
        raise ValueError('The bounded display marker differs from its subtree artifact.')
    _node(value['node_ref'])
    if special:
        _integer(value['source_evar'])
    return value


def _reload(root, reference, display, expected_reader):
    from trace_block_compact_catalog import catalog_header, receipt_check
    receipt = _read(root, reference)
    catalog = _read(root, display['evar_catalog_ref'])
    catalog_version = catalog.get('schema')
    if type(catalog_version) is not int or catalog_version not in (1, 2):
        raise ValueError('The reload catalog schema is unsupported.')
    if catalog_version == 2:
        context = _read(root, display['context_ref'])
        _fields(context, 'schema kind complete_sidecar goals shelf given_up')
        _same(context, 'schema', 1)
        _same(context, 'kind', 'kernel-snapshot-context')
        _same(context, 'complete_sidecar', display['complete_sidecar'])
        catalog_header(catalog, display['complete_sidecar'], context)
    _fields(receipt, 'schema kind sidecar context_ref evar_catalog_ref toolchain_ref reader '
                     'accepted checks kernel_typecheck error unique_kernel_nodes' +
                     (' catalog_check' if catalog_version == 2 else ''))
    if catalog_version == 2:
        receipt_check(receipt['catalog_check'], catalog)
    _schema(receipt, 'kernel-marshal-reload')
    _integer(receipt['unique_kernel_nodes'])
    for field, expected in [('sidecar', display['complete_sidecar']),
                            ('reader', expected_reader), *[(name, display[name]) for name in
                            ('context_ref', 'evar_catalog_ref', 'toolchain_ref')]]:
        _same(receipt, field, expected)
    if (receipt['accepted'] is not True or receipt['error'] is not None
            or receipt['kernel_typecheck'] != 'not-attempted'
            or not isinstance(receipt['checks'], Mapping) or set(receipt['checks']) != RELOAD_CHECKS
            or any(value is not True for value in receipt['checks'].values())):
        raise ValueError('The root reload receipt lacks complete serialization checks.')
    return receipt


def _membership(root, reference, marker_ref, marker, display, expected_reader, owners):
    receipt = _read(root, reference)
    special = marker['reason'] == 'evar-reference'
    _fields(receipt, 'schema kind marker_ref node_ref complete_sidecar resolved_sidecar context_ref '
                     'evar_catalog_ref toolchain_ref reader accepted error checks owner_root_id display_ref' +
                     (' source_evar' if special else ''))
    _schema(receipt, 'kernel-node-membership')
    expected = {'marker_ref': marker_ref, 'node_ref': marker['node_ref'],
                'complete_sidecar': display['complete_sidecar'], 'resolved_sidecar': marker['sidecar'],
                'reader': expected_reader, **{field: marker[field] for field in
                    ('context_ref', 'evar_catalog_ref', 'toolchain_ref')}}
    owner = owners.get(marker['node_ref']['root_id'])
    expected['owner_root_id'] = owner['root_id'] if owner else marker['node_ref']['root_id']
    expected['display_ref'] = owner['display_ref'] if owner else None
    if special:
        expected['source_evar'] = marker['source_evar']
    for field, value in expected.items():
        _same(receipt, field, value)
    checks = receipt['checks']
    if (receipt['accepted'] is not True or receipt['error'] is not None
            or not _array(checks) or len(checks) != len(MEMBERSHIP_CHECKS)
            or any(not isinstance(check, str) for check in checks) or set(checks) != MEMBERSHIP_CHECKS):
        raise ValueError('The subtree membership receipt lacks complete checked associations.')
    return receipt


def _root_receipt(root, reference, entry, plan, expected_reader, inputs):
    value = _read(root, reference)
    _fields(value, 'schema kind display_ref root_id node_ref complete_sidecar resolved_sidecar '
                   'context_ref evar_catalog_ref toolchain_ref reader accepted error context_roots')
    _schema(value, 'kernel-root-membership')
    expected = {'display_ref': entry['display_ref'], 'root_id': entry['root_id'],
                'node_ref': entry['node_ref'], 'context_ref': entry['context_ref'],
                'complete_sidecar': plan['complete_sidecar'], 'evar_catalog_ref': plan['evar_catalog_ref'],
                'toolchain_ref': plan['toolchain_ref'], 'reader': expected_reader,
                'context_roots': inputs[entry['root_id']]['context_roots']}
    for field, item in expected.items():
        _same(value, field, item)
    artifact(root, value['resolved_sidecar'])
    if value['accepted'] is not True or value['error'] is not None:
        raise ValueError('The root membership receipt does not accept the exact selected root.')
    return value


def verify_kernel_capture_reload(root, capture, *, expected_toolchain_ref, expected_reader,
                                 expected_marker_plan, expected_arguments):
    """Check schema2 complete reload without requiring a printed display root."""
    evidence = capture['reload_evidence']
    _fields(evidence, 'receipt invocation')
    artifact(root, expected_reader)
    plan = _read(root, expected_marker_plan)
    _fields(plan, 'schema complete_sidecar markers displays context_ref evar_catalog_ref toolchain_ref reader receipt_prefix')
    _schema(plan)
    for field, expected in [('complete_sidecar', capture['complete_sidecar']),
                            ('evar_catalog_ref', capture['evar_catalog_ref']),
                            ('toolchain_ref', expected_toolchain_ref), ('reader', expected_reader)]:
        _same(plan, field, expected)
    _references(root, plan, ('complete_sidecar', 'context_ref', 'evar_catalog_ref', 'toolchain_ref'))
    prefix = plan['receipt_prefix']
    if (not isinstance(prefix, str) or not prefix or PurePosixPath(prefix).is_absolute()
            or any(part in ('', '.', '..') for part in prefix.split('/'))):
        raise ValueError('The capture reload plan lacks a safe receipt prefix.')
    for field in ('displays', 'markers'):
        if not _array(plan[field]):
            raise ValueError('The capture reload plan lacks its exact ordered lists.')
    if not capture['displays'] and (plan['displays'] or plan['markers']):
        raise ValueError('A zero-display capture has nonempty planned displays or markers.')
    invocation = _read(root, evidence['invocation'])
    _fields(invocation, 'schema kind reader arguments sidecar toolchain_ref marker_plan exit_code receipt '
                        'membership_receipts root_receipts stdout stderr')
    _schema(invocation, 'kernel-reader-invocation')
    for field, expected in [('reader', expected_reader), ('sidecar', capture['complete_sidecar']),
                            ('toolchain_ref', expected_toolchain_ref), ('marker_plan', expected_marker_plan),
                            ('receipt', evidence['receipt']), ('arguments', expected_arguments)]:
        _same(invocation, field, expected)
    if (type(invocation['exit_code']) is not int or invocation['exit_code'] != 0
            or not _array(expected_arguments) or not expected_arguments
            or any(not isinstance(value, str) for value in expected_arguments)
            or expected_arguments[-1] != '--result-ref'):
        raise ValueError('The capture lacks its exact successful reader invocation.')
    _references(root, invocation, ('stdout', 'stderr'))
    for field, entries in [('root_receipts', plan['displays']), ('membership_receipts', plan['markers'])]:
        if not _array(invocation[field]) or len(invocation[field]) != len(entries):
            raise ValueError('The capture reader lacks its exact receipt counts.')
    receipts = [evidence['receipt'], *invocation['root_receipts'], *invocation['membership_receipts']]
    seen = set()
    for reference in receipts:
        identity = _identity(reference)
        if identity in seen:
            raise ValueError('The capture reader repeats a receipt.')
        seen.add(identity)
        artifact(root, reference)
        if not reference['path'].startswith(prefix + '/'):
            raise ValueError('A capture reader receipt leaves its planned output prefix.')
    output = _read(root, invocation['stdout'])
    _fields(output, 'result')
    result = _read(root, output['result'])
    _fields(result, 'schema accepted receipt membership_receipts root_receipts')
    _schema(result)
    _same(result, 'accepted', True)
    for field in ('receipt', 'membership_receipts', 'root_receipts'):
        _same(result, field, invocation[field])
    _reload(root, evidence['receipt'], plan, expected_reader)
    return plan


DISPLAY_INPUT_FIELDS = ('schema root_id node_ref surface surface_nonotation limits goal goal_nonotation '
    'complete_sidecar context_ref evar_catalog_ref toolchain_ref omitted_subtrees display_holes print_check displayed_nodes context_roots')


def verify_kernel_display(root, display, *, expected_toolchain_ref, expected_reader,
                          expected_marker_plan, expected_arguments):
    """Require exact acyclic composition, complete reload, and checked root/subtree membership."""
    _fields(display, DISPLAY_INPUT_FIELDS + ' display_input_ref reload_evidence root_reload_evidence')
    _schema(display)
    _name(display['root_id'])
    _node(display['node_ref'])
    if display['node_ref'] != {'root_id': display['root_id'], 'child_path': []}:
        raise ValueError('The display does not identify its exact root node.')
    source = _read(root, display['display_input_ref'])
    _fields(source, DISPLAY_INPUT_FIELDS)
    if not _exact(source, {key: display[key] for key in DISPLAY_INPUT_FIELDS.split()}):
        raise ValueError('The final display differs from its immutable pre-evidence input.')
    _integer(display['displayed_nodes'])
    if display['displayed_nodes'] > LIMITS['nodes']:
        raise ValueError('The bounded display exceeds its constructor-visit budget.')
    if display['limits'] != LIMITS or any(type(value) is not int for value in display['limits'].values()):
        raise ValueError('The bounded display limits differ from the approved limits.')
    _same(display, 'toolchain_ref', expected_toolchain_ref)
    _references(root, display, ('complete_sidecar', 'context_ref', 'evar_catalog_ref', 'toolchain_ref'))
    artifact(root, expected_reader)
    plan = _read(root, expected_marker_plan)
    _fields(plan, 'schema complete_sidecar markers displays context_ref evar_catalog_ref toolchain_ref reader receipt_prefix')
    _schema(plan)
    for field in ('complete_sidecar', 'evar_catalog_ref', 'toolchain_ref'):
        _same(plan, field, display[field])
    _references(root, plan, ('complete_sidecar', 'context_ref', 'evar_catalog_ref', 'toolchain_ref'))
    _same(plan, 'reader', expected_reader)
    prefix = plan['receipt_prefix']
    if (not isinstance(prefix, str) or not prefix or PurePosixPath(prefix).is_absolute()
            or any(part in ('', '.', '..') for part in prefix.split('/'))):
        raise ValueError('The bounded display plan lacks a safe receipt prefix.')
    entries = plan['displays']
    if not _array(entries) or not entries:
        raise ValueError('The bounded display plan lacks its exact root list.')
    roots = set()
    owners = {}
    inputs = {}
    selected = None
    for entry in entries:
        _fields(entry, 'display_ref root_id node_ref context_ref')
        _name(entry['root_id'])
        _node(entry['node_ref'])
        if entry['root_id'] in roots or entry['node_ref'] != {'root_id': entry['root_id'], 'child_path': []}:
            raise ValueError('The bounded display plan repeats or changes a root identity.')
        roots.add(entry['root_id'])
        input_record = _read(root, entry['display_ref'])
        _fields(input_record, DISPLAY_INPUT_FIELDS)
        for field in ('root_id', 'node_ref', 'context_ref'):
            _same(input_record, field, entry[field])
        for field in ('complete_sidecar', 'evar_catalog_ref', 'toolchain_ref'):
            _same(input_record, field, plan[field])
        artifact(root, entry['context_ref'])
        inputs[entry['root_id']] = input_record
        context_roots = input_record['context_roots']
        if not _array(context_roots):
            raise ValueError('The display lacks its ordered context roots.')
        node_roots = [input_record['node_ref'], *context_roots]
        for node in node_roots:
            _node(node)
            if node['child_path'] or node['root_id'] in owners:
                raise ValueError('The display repeats or changes context ownership.')
            if node['root_id'] != entry['root_id']:
                match = re.fullmatch(re.escape(entry['root_id']) + r'@(named|rel):(0|[1-9][0-9]*):(type|body)', node['root_id'])
                if match is None:
                    raise ValueError('A context root lacks its exact declaration-field identity.')
            owners[node['root_id']] = entry
        if entry['display_ref'] == display['display_input_ref']:
            selected = entry
    if selected is None or selected['root_id'] != display['root_id']:
        raise ValueError('The plan does not bind this exact immutable display input.')
    _fields(display['print_check'], 'status reason')
    status, reason = display['print_check']['status'], display['print_check']['reason']
    if not isinstance(status, str) or status not in PRINT_STATUSES:
        raise ValueError('The bounded display printer status is unsupported.')
    if status == 'primary-accepted':
        if display['surface'] != 'rocq-notation' or display['surface_nonotation'] != 'rocq-no-notation' or reason is not None:
            raise ValueError('The primary display has inconsistent printer evidence.')
    elif (display['surface'] != 'kernel-constructor' or display['surface_nonotation'] != 'kernel-constructor'
          or not isinstance(reason, str) or not reason):
        raise ValueError('The fallback display lacks its exact permitted failure.')
    found = set()
    for field in ('goal', 'goal_nonotation'):
        text = _bounded_text(display[field])
        found.update(HOLE.findall(text))
    plan_markers = plan['markers']
    if not _array(plan_markers) or len(plan_markers) > LIMITS['nodes']:
        raise ValueError('The bounded display plan has an invalid marker count.')
    all_markers = []
    seen = set()
    for reference in plan_markers:
        identity = _identity(reference)
        if identity in seen:
            raise ValueError('The bounded display plan repeats a marker.')
        seen.add(identity)
        marker = _marker(root, reference, expected_toolchain_ref)
        all_markers.append((reference, marker))
    loaded = [(reference, marker) for reference, marker in all_markers
              if owners.get(marker['node_ref']['root_id']) is selected]
    markers, holes = display['omitted_subtrees'], display['display_holes']
    if (not _array(markers) or not _array(holes) or len(markers) != len(holes)
            or markers != [reference for reference, marker in loaded]):
        raise ValueError('The bounded display lacks its exact ordered marker plan.')
    names = set()
    term_names = set()
    display_evars = set()
    for (reference, marker), hole in zip(loaded, holes):
        _fields(hole, 'name marker_sha256 marker_ref display_evar scope')
        _integer(hole['display_evar'])
        if hole['display_evar'] in display_evars:
            raise ValueError('The bounded display repeats a detached hole identity.')
        display_evars.add(hole['display_evar'])
        name = hole['name']
        expected_scope = 'term' if marker['node_ref']['root_id'] == display['root_id'] else 'context'
        if hole['scope'] != expected_scope:
            raise ValueError('The display hole differs from its checked term or context ownership.')
        if (not isinstance(name, str) or HOLE.fullmatch(name) is None
                or not name.startswith('elided_' + marker['sha256'][:8] + '_')
                or name in names or (expected_scope == 'term' and name not in found) or hole['marker_ref'] != reference
                or hole['marker_sha256'] != marker['sha256']):
            raise ValueError('The bounded display hole differs from its exact marker.')
        names.add(name)
        if expected_scope == 'term':
            term_names.add(name)
    if found != term_names:
        raise ValueError('The bounded display contains an undeclared hash hole.')
    evidence, root_evidence = display['reload_evidence'], display['root_reload_evidence']
    _fields(evidence, 'receipt invocation')
    _fields(root_evidence, 'receipt invocation')
    if root_evidence['invocation'] != evidence['invocation']:
        raise ValueError('The root and complete reload use different reader invocations.')
    invocation = _read(root, evidence['invocation'])
    _fields(invocation, 'schema kind reader arguments sidecar toolchain_ref marker_plan exit_code receipt '
                        'membership_receipts root_receipts stdout stderr')
    _schema(invocation, 'kernel-reader-invocation')
    for field, expected in [('reader', expected_reader), ('sidecar', display['complete_sidecar']),
                            ('toolchain_ref', expected_toolchain_ref), ('marker_plan', expected_marker_plan),
                            ('receipt', evidence['receipt']), ('arguments', expected_arguments)]:
        _same(invocation, field, expected)
    if (type(invocation['exit_code']) is not int or invocation['exit_code'] != 0
            or not _array(expected_arguments) or not expected_arguments
            or any(not isinstance(value, str) for value in expected_arguments)):
        raise ValueError('The bounded display lacks its exact successful reader invocation.')
    _references(root, invocation, ('stdout', 'stderr'))
    receipts, root_receipts = invocation['membership_receipts'], invocation['root_receipts']
    if (not _array(receipts) or len(receipts) != len(all_markers)
            or not _array(root_receipts) or len(root_receipts) != len(entries)):
        raise ValueError('The reader invocation lacks its exact root or subtree receipts.')
    all_receipts = [evidence['receipt'], *root_receipts, *receipts]
    seen = set()
    for reference in all_receipts:
        identity = _identity(reference)
        if identity in seen:
            raise ValueError('The reader invocation repeats a receipt.')
        seen.add(identity)
        artifact(root, reference)
        if not reference['path'].startswith(prefix + '/'):
            raise ValueError('A reader receipt leaves its planned output prefix.')
    receipt = _reload(root, evidence['receipt'], plan, expected_reader)
    matched_root = None
    for reference, entry in zip(root_receipts, entries):
        _root_receipt(root, reference, entry, plan, expected_reader, inputs)
        if _exact(entry['display_ref'], selected['display_ref']):
            matched_root = reference
    if matched_root != root_evidence['receipt']:
        raise ValueError('The final display does not bind its exact root receipt.')
    for reference, (marker_ref, marker) in zip(receipts, all_markers):
        _membership(root, reference, marker_ref, marker, plan, expected_reader, owners)
    return {'display_availability': 'bounded', 'root_id': display['root_id'],
            'kernel_artifact': 'reload-and-membership-verified', 'markers': len(loaded),
            'surface': display['surface'], 'surface_nonotation': display['surface_nonotation'],
            'kernel_typecheck': receipt['kernel_typecheck'],
            'reload_evidence': {key: dict(evidence[key]) for key in ('receipt', 'invocation')},
            'root_reload_evidence': {key: dict(root_evidence[key]) for key in ('receipt', 'invocation')},
            'limit': 'Byte preservation and membership do not establish kernel typechecking or semantic equality.'}
