"""Seal bounded outputs with their complete, unchanged raw evidence."""
import json
import sys
from pathlib import Path

from trace_block import logical_session_id
from trace_block_capture import validate_capture, write_raw_seal
from trace_block_seal import file_sha256, verify_root_seal
from trace_block_stream import json_document
from trace_block_text import StreamText


def _reference(path):
    return {'path': str(path), 'sha256': file_sha256(path), 'bytes': path.stat().st_size}


def _text(value):
    if isinstance(value, StreamText):
        yield from value.iter_text()
    elif isinstance(value, str):
        yield value
    else:
        raise ValueError('The bounded renderer requires exact text.')


def _goal(record):
    if record['goal'] is None:
        if record.get('goal_availability') != {
                'availability': 'unavailable',
                'reason': 'Evd erases the conclusion of a defined evar'}:
            raise ValueError('The bounded renderer lacks an exact conclusion availability record.')
        yield 'The raw group member is defined. Its erased conclusion is unavailable.\n\n'
        yield 'The complete body uses its checked artifact reference.\n\n'
    else:
        yield '```rocq\n'
        yield from _text(record['goal'])
        yield '\n```\n\n'


def markdown(trace):
    yield '# Bounded native trace\n\n'
    yield 'Printed terms use bounded displays. Complete terms use checked Marshal artifacts.\n\n'
    yield 'Coverage: ' + ('complete' if trace['completion']['trace_complete'] else 'incomplete') + '.\n\n'
    if not trace['points']:
        yield 'The retained stream contains no selected trigger snapshot.\n\n'
    for number, point in enumerate(trace['points']):
        trigger = point['trigger']
        yield '## Trigger %d: %s\n\n' % (number + 1, trigger['rule'])
        yield from _goal(point)
        for trial in point['hand_call']:
            yield 'Trial ' + trial['clause'] + ': ' + trial['outcome'] + '.\n\n'
            yield '```rocq\n' + trial['command'] + '\n```\n\n'
            if 'message' in trial:
                yield '```text\n'
                yield from _text(trial['message'])
                yield '\n```\n\n'
    residual = trace['residual']
    if residual is not None:
        yield '## First residual leaf\n\n'
        yield 'The selected leaf does not expose hidden peer goals.\n\n'
        yield from _goal(residual)
    for reason in trace['completion']['reasons']:
        yield '- ' + reason + '\n'


def write_bundle(request, out_dir, raw_root, manifest, *, operation_bindings=None):
    """Check every raw file before and after streaming output."""
    from trace_block_bounded_projection import ProjectionView
    from trace_block_bounded_aliases import (AliasProjection, AliasDocument, write_alias_map,
        verify_aliases, verify_alias_files)
    retained, paths = validate_capture(request, raw_root, manifest)
    directory = Path(out_dir).absolute()
    root = Path(raw_root).resolve(strict=True)
    if directory.resolve().is_relative_to(root):
        raise ValueError('The bounded output must remain outside its raw evidence.')
    directory.mkdir(parents=True, exist_ok=True)
    session_id = logical_session_id(retained)
    raw_seal = write_raw_seal(root, directory / 'RAW-SEAL.json', session_id)
    before = verify_root_seal(paths['session'].parent, session_id, Path(raw_seal['path']))
    with ProjectionView(retained, paths['session'].parent, index_dir=directory / 'projection-index',
                        operation_bindings=operation_bindings, raw_seal_reference=_reference(Path(raw_seal['path']))) as view:
        raw_trace = view.trace
        trace = raw_trace
        if manifest.get('admission_exit_status') not in (None, 0):
            trace['completion']['trace_complete'] = False
            trace['coverage']['required_complete'] = False
            trace['completion']['reasons'].append('The admitted capture controller reports a nonzero exit status.')
        index = directory / 'raw/INDEX.json'
        index.parent.mkdir(parents=True, exist_ok=True)
        view.write_raw_index(index)
        aliases = AliasProjection(raw_trace, paths['session'].parent)
        alias_directory = directory / 'aliases'
        alias_binding = write_alias_map(alias_directory, aliases.mapping,
            index_dir=directory / 'projection-index/alias-write', writer_reference=retained['chunk_writer'])
        trace = aliases.stable
        with AliasDocument(alias_directory, alias_binding['artifact'],
                           index_dir=directory / 'projection-index/alias-read') as alias_map:
            alias_verification = verify_aliases(trace, alias_map, raw_trace, paths['session'].parent)
        for name, chunks in (('TRACE.json', json_document(trace)), ('TRACE.md', markdown(raw_trace))):
            with (directory / name).open('x') as stream:
                for part in chunks:
                    stream.write(part)
        after = verify_root_seal(paths['session'].parent, session_id, Path(raw_seal['path']))
        if before != after:
            raise ValueError('The raw evidence changed during bounded projection.')
        link = directory / 'evidence'
        if link.exists() or link.is_symlink():
            raise ValueError('The bounded output already contains an evidence path.')
        link.symlink_to(paths['session'].parent, target_is_directory=True)
        verify_alias_files(alias_directory, alias_binding['files'])
        sources = {}
        for module in tuple(sys.modules.values()):
            name = getattr(module, '__file__', None)
            if name is not None:
                path = Path(name)
                if path.suffix == '.py' and path.parent.resolve() == Path(__file__).parent.resolve():
                    sources[path.name] = _reference(path)
        mapping = {'schema': 1, 'surface_policy': 'bounded-kernel-v1', 'session': session_id,
            'raw_root': str(root), 'raw_seal': _reference(Path(raw_seal['path'])),
            'raw_verification': before, 'request': _reference(paths['request']),
            'runtime_session': _reference(paths['session']), 'evidence_link': str(link),
            'evidence_target': str(link.resolve(strict=True)), 'raw_index': _reference(index),
            'outputs': {name: _reference(directory / name) for name in ('TRACE.json', 'TRACE.md')},
            'projection_sources': sources, 'alias_directory': str(alias_directory),
            'alias_binding': alias_binding, 'alias_verification': alias_verification,
            'limits': ['Printed text is bounded. Complete terms require every checked Marshal receipt.',
                'A missing event-to-operation range remains unavailable.',
                'The raw seal binds all process streams. The index names only the owned interactive stream.']}
        if mapping['outputs']['TRACE.json']['sha256'] != alias_verification['trace_sha256']:
            raise ValueError('The stable TRACE differs from its verified alias projection.')
        if alias_binding['logical_sha256'] != alias_verification['alias_map_sha256']:
            raise ValueError('The alias artifact differs from its verified logical map.')
        with (directory / 'EVIDENCE-MAP.json').open('x') as stream:
            for part in json_document(mapping):
                stream.write(part)
        return {key: raw_trace[key] for key in ('completion', 'verdict', 'coverage', 'session')}
