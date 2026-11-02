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
    from compiler_snapshot import _read_private
    snapshot = _read_private(snapshot_reference)
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
    """Keep every worker output outside all compiler load-path mappings."""
    admission = runtime.get('canonical_admission', {})
    if (runtime.get('phase') != 'prerequisites' or
            runtime.get('declaration_dag', {}).get('schema') != 'entry-chain.declaration-dag.v1' or
            admission.get('minimum_claim_bytes') != 64 * GIB or
            admission.get('physical_fence_bytes') != 64 * GIB or
            runtime.get('native_route') or runtime.get('control_session')):
        raise ValueError('Private declarations require an opt-in 64/64 GiB prerequisite job.')
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


def publication(reference, *, source, compiler, flags, snapshot, producer,
                physical_result, canonical_object):
    """Validate the immutable association without reading relocated old outputs."""
    from compiler_snapshot import _read_private
    value = _read_private(reference)
    required = {'schema', 'module', 'source', 'compiler', 'physical_flags', 'snapshot',
                'producer', 'physical_result', 'private_outputs', 'published_outputs',
                'private_globalization', 'published_globalization'}
    if (not isinstance(value, dict) or set(value) != required or value['schema'] != SCHEMA or
            value['source'] != source or value['compiler'] != compiler or
            value['physical_flags'] != list(flags) or value['snapshot'] != snapshot or
            value['producer'] != producer or value['physical_result'] != physical_result):
        raise ValueError('The declaration publication differs from its physical producer.')
    private, published = value['private_outputs'], value['published_outputs']
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
    with publication_lock(manager.reference, exclusive=True):
        return _publish_outputs(manager, module, source, physical_result, private_object,
                                tool_result, workspace=workspace)


def _publish_outputs(manager, module, source, physical_result, private_object, tool_result, *, workspace):
    from clone_copy import copy2
    from compiler_snapshot import (_identity, _namespace, _physical_record, _publish,
                                   compiler_outputs, output_artifact)
    source = Path(source).resolve()
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
             'private_globalization': private_glob_binding,
             'published_globalization': binding(destinations[2])}
    reference = _publish(Path(physical_result['path']).parent / 'PUBLICATION.json', value)
    publication(reference, source=source_binding, compiler=compiler, flags=flags,
                snapshot=manager.reference, producer=manager.snapshot['producer'],
                physical_result=physical_result, canonical_object=binding(destinations[0]))
    return manager.accept(source, destinations[0], compiler['path'], runtime['physical_flags'],
                          tool_result, physical_result=physical_result, publication=reference)
