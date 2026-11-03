"""Authenticate private compiler outputs before serialized canonical publication."""
from pathlib import Path
from contextlib import contextmanager
import fcntl
import os
import re
import stat
import uuid

from entry_chain import binding, read_bound
from source_context import compilation


SCHEMA = 'entry-chain.declaration-publication.v1'
GIB = 1024 ** 3


@contextmanager
def publication_lock(snapshot_reference, *, exclusive=False):
    """Prevent compiler validation from observing a partially published pair."""
    from compiler_snapshot import _read_snapshot
    snapshot = _read_snapshot(snapshot_reference)
    root = Path(snapshot['objects'])
    descriptor = os.open(root / 'PUBLICATION.lock', os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    try:
        info = os.fstat(descriptor)
        if (not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid() or
                stat.S_IMODE(info.st_mode) != 0o600 or info.st_nlink != 1):
            raise ValueError('The declaration publication lock lacks its private identity.')
        fcntl.flock(descriptor, fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH)
        yield
    finally:
        os.close(descriptor)


def private_target(runtime, source, target, workspace):
    """Keep each output outside every shared compiler load-path mapping."""
    admission = runtime.get('canonical_admission', {})
    if (runtime.get('phase') != 'prerequisites' or
            runtime.get('declaration_dag', {}).get('schema') != 'entry-chain.declaration-dag.v1' or
            type(runtime.get('declaration_dag', {}).get('claim_bytes')) is not int or
            not 0 < runtime['declaration_dag']['claim_bytes'] <= 64 * GIB or
            admission.get('minimum_claim_bytes') != runtime['declaration_dag']['claim_bytes'] or
            admission.get('physical_fence_bytes') != 64 * GIB or
            runtime.get('native_route') or runtime.get('control_session')):
        raise ValueError('Private declarations require the opt-in frontier booking and 64 GiB fence.')
    workspace = Path(workspace).resolve()
    target = Path(target).absolute()
    source = Path(source['path'])
    if (target != target.resolve() or not source.resolve().is_relative_to(workspace) or
            not target.is_relative_to(workspace / '.declaration-private') or
            len(target.relative_to(workspace / '.declaration-private').parts) != 2 or
            re.fullmatch('[0-9a-f]{32}', target.parent.name) is None or
            target.name != source.with_suffix('.vo').name):
        raise ValueError('A private declaration output has another source or namespace.')
    flags = runtime['physical_flags']
    for index, word in enumerate(flags):
        if word in {'-Q', '-R', '-I'}:
            root = Path(flags[index + 1]).resolve()
            if target.is_relative_to(root):
                raise ValueError('A private declaration output enters a compiler load path.')
    return target


def output_context(runtime, source, target, workspace):
    """Preserve the logical owner with one mapping private to this worker."""
    from compiler_snapshot import _namespace
    workspace = Path(workspace).resolve()
    target = private_target(runtime, source, target, workspace)
    owners = [name for name, relative in runtime['module_files'].items()
              if (workspace / relative).resolve() == Path(source['path']).resolve()]
    if len(owners) != 1 or owners[0].rsplit('.', 1)[-1] != Path(source['path']).stem:
        raise ValueError('The private output lacks its exact source-bound logical owner.')
    module = owners[0]
    parent = module.rpartition('.')[0]
    source_context = compilation(runtime['physical_flags'], source)
    mapping = ['-Q', str(target.parent), parent]
    return {'schema': 'entry-chain.declaration-output-context.v1', 'module': module,
            'source': source, 'source_context': source_context, 'output': str(target),
            'private_mapping': mapping, 'directory_namespace': _namespace(target.parent),
            'physical_flags': source_context['physical_flags'] + mapping}


def publication(reference, *, source, compiler, flags, snapshot, producer,
                physical_result, canonical_object):
    """Validate the immutable association without reading relocated old outputs."""
    from compiler_snapshot import _read_private
    value = _read_private(reference)
    required = {'schema', 'module', 'source', 'compiler', 'physical_flags', 'snapshot',
                'producer', 'physical_result', 'private_outputs', 'published_outputs',
                'private_globalization', 'published_globalization', 'output_context'}
    if (not isinstance(value, dict) or set(value) != required or value['schema'] != SCHEMA or
            value['source'] != source or value['compiler'] != compiler or
            value['physical_flags'] != list(flags) or value['snapshot'] != snapshot or
            value['producer'] != producer or value['physical_result'] != physical_result):
        raise ValueError('The declaration publication differs from its physical producer.')
    private, published = value['private_outputs'], value['published_outputs']
    context = value['output_context']
    expected_mapping = ['-Q', str(Path(private['object']['binding']['path']).parent),
                        value['module'].rpartition('.')[0]]
    if (not isinstance(context, dict) or
            context.get('schema') != 'entry-chain.declaration-output-context.v1' or
            context.get('module') != value['module'] or context.get('source') != source or
            context.get('output') != private['object']['binding']['path'] or
            context.get('source_context', {}).get('physical_flags') != list(flags) or
            context.get('private_mapping') != expected_mapping or
            context.get('physical_flags') != list(flags) + expected_mapping):
        raise ValueError('The declaration publication changed its private output mapping.')
    if (set(private) != {'object', 'sidecar', 'sidecar_status'} or
            set(published) != set(private) or private['sidecar_status'] != 'compiled_output' or
            published['sidecar_status'] != 'compiled_output' or
            published['object']['binding'] != canonical_object or
            canonical_object['path'] != str(Path(source['path']).with_suffix('.vo'))):
        raise ValueError('The declaration publication names another canonical output.')
    for key, suffix in [('object', '.vo'), ('sidecar', '.vos')]:
        left, right = private[key], published[key]
        if (left['binding']['sha256'] != right['binding']['sha256'] or
                right['binding']['path'] != str(Path(source['path']).with_suffix(suffix)) or
                left['binding']['path'] != str(Path(private['object']['binding']['path']).with_suffix(suffix))):
            raise ValueError('A published declaration differs from its private physical output.')
    if (value['private_globalization']['sha256'] != value['published_globalization']['sha256'] or
            value['private_globalization']['path'] != str(Path(private['object']['binding']['path']).with_suffix('.glob')) or
            value['published_globalization']['path'] != str(Path(source['path']).with_suffix('.glob'))):
        raise ValueError('The declaration globalization differs from its private output.')
    return value


def publish(manager, module, source, physical_result, private_object, tool_result, *, workspace):
    """Copy absent outputs and seal their receipt on the provider's single thread."""
    return _publish_outputs(manager, module, source, physical_result, private_object,
                            tool_result, workspace=workspace)


def _publish_outputs(manager, module, source, physical_result, private_object, tool_result, *, workspace):
    from clone_copy import copy2
    from compiler_snapshot import (_identity, _namespace, _physical_record, _publish,
                                   compiler_outputs, output_artifact, producer)
    source = Path(source).resolve()
    if producer() != manager.snapshot['producer']:
        raise ValueError('Another producer cannot publish a private declaration.')
    if tool_result.get('success') is not True:
        raise ValueError('A failed compilation cannot publish a private declaration.')
    runtime = read_bound(manager.snapshot['runtime'])
    workspace = Path(workspace).resolve()
    owners = [name for name, relative in runtime['module_files'].items()
              if (workspace / relative).resolve() == source]
    if owners != [module]:
        raise ValueError('The private declaration lacks its exact canonical module.')
    source_binding = binding(source)
    flags = compilation(runtime['physical_flags'], source_binding)['physical_flags']
    compiler = runtime['physical_compiler']
    private_object = private_target(runtime, source_binding, private_object, workspace)
    private_outputs, before, _, _ = _physical_record(
        physical_result, manager.snapshot, manager.reference, source_binding, compiler,
        flags, binding(private_object), manager.rows, private_output=True)
    if before['state'] != 'absent':
        raise ValueError('A private declaration reused an existing sidecar.')
    private_glob = private_object.with_suffix('.glob')
    if '\nF' + module + '\n' not in private_glob.read_text():
        raise ValueError('The private declaration has another logical owner.')
    # Authenticate the private record before the exclusive lock. The locked copy
    # rechecks the source and the private outputs before it seals the receipt.
    with publication_lock(manager.reference, exclusive=True):
        destinations = [source.with_suffix(suffix) for suffix in ['.vo', '.vos', '.glob']]
        if any(path.exists() or path.is_symlink() for path in destinations):
            raise ValueError('A declaration publication would replace an existing output.')
        source_identity, source_namespace = _identity(source), _namespace(source)
        private_glob_binding = binding(private_glob)
        for source_path, destination in zip(
                [private_object, private_object.with_suffix('.vos'), private_glob], destinations):
            temporary = destination.with_name('.' + destination.name + '.publication-' + uuid.uuid4().hex)
            try:
                copy2(source_path, temporary)
                # Link the new private clone without replacing an existing output.
                os.link(temporary, destination, follow_symlinks=False)
            finally:
                temporary.unlink(missing_ok=True)
        published = {'object': output_artifact(destinations[0]),
                     'sidecar': output_artifact(destinations[1]), 'sidecar_status': 'compiled_output'}
        if (_identity(source) != source_identity or _namespace(source) != source_namespace or
                binding(source) != source_binding or
                compiler_outputs(private_object, before) != private_outputs):
            raise ValueError('A declaration input or private output changed during publication.')
        value = {'schema': SCHEMA, 'module': module, 'source': source_binding,
                 'compiler': compiler, 'physical_flags': flags, 'snapshot': manager.reference,
                 'producer': manager.snapshot['producer'], 'physical_result': physical_result,
                 'private_outputs': private_outputs, 'published_outputs': published,
                 'output_context': output_context(runtime, source_binding, private_object, workspace),
                 'private_globalization': private_glob_binding,
                 'published_globalization': binding(destinations[2])}
        reference = _publish(Path(physical_result['path']).parent / 'PUBLICATION.json', value)
        publication(reference, source=source_binding, compiler=compiler, flags=flags,
                    snapshot=manager.reference, producer=manager.snapshot['producer'],
                    physical_result=physical_result, canonical_object=binding(destinations[0]))
        return manager.accept(source, destinations[0], compiler['path'], runtime['physical_flags'],
                              tool_result, physical_result=physical_result, publication=reference)
