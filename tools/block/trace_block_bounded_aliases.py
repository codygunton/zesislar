"""Keep runtime artifact identities outside the stable bounded trace body."""
from collections.abc import Mapping, Sequence
import hashlib
import json
from pathlib import Path, PurePosixPath

from trace_block_kernel_display import artifact
from trace_block_stream import json_document
from trace_block_text import StreamText


def _escape(value):
    return str(value).replace('~', '~0').replace('/', '~1')


def _digest(value):
    digest = hashlib.sha256()
    for part in json_document(value):
        digest.update(part.encode('utf-8'))
    return digest.hexdigest()


class _Map(Mapping):
    def __init__(self, projection, value):
        self.projection, self.value = projection, value

    def __iter__(self):
        return iter(self.value)

    def __len__(self):
        return len(self.value)

    def __getitem__(self, key):
        return self.projection._wrap(self.value[key])


class _Array(Sequence):
    def __init__(self, projection, value):
        self.projection, self.value = projection, value

    def __len__(self):
        return len(self.value)

    def __getitem__(self, index):
        if isinstance(index, slice):
            raise TypeError('The stable alias sequence does not support slicing.')
        return self.projection._wrap(self.value[index])


class AliasProjection:
    """Assign logical artifact names by deterministic traversal of checked data.

    This projection does not validate term semantics. Its caller supplies the
    complete bounded projection after all raw captures and receipts pass.
    """
    def __init__(self, raw_trace, evidence_root):
        if not isinstance(raw_trace, Mapping) or 'artifacts' in raw_trace:
            raise ValueError('The bounded source already uses the reserved artifact namespace.')
        self.root = Path(evidence_root).resolve(strict=True)
        self.raw_trace = raw_trace
        self.by_target = {}
        self.by_path = {}
        self.aliases = []
        self._scan(raw_trace, '#')
        self.mapping = {'schema': 1, 'session': raw_trace['session']['id'], 'aliases': self.aliases}
        descriptors = {row['name']: {'kind': 'verified-raw-artifact'} for row in self.aliases}
        self.stable = _Map(self, dict(raw_trace, artifacts=descriptors))

    def _reference(self, value):
        if not isinstance(value, Mapping) or set(value) not in (
                {'path', 'sha256', 'bytes'}, {'path', 'sha256'}):
            return None
        name = value['path']
        if not isinstance(name, str):
            raise ValueError('An artifact alias requires an exact path string.')
        path = Path(name)
        if path.is_absolute():
            try:
                name = path.relative_to(self.root).as_posix()
            except ValueError:
                raise ValueError('An artifact alias points outside the owned raw evidence.') from None
        else:
            parts = PurePosixPath(name)
            if any(part in ('.', '..', '') for part in name.split('/')):
                raise ValueError('An artifact alias has an unsupported path component.')
            # The original source-prefix binding remains part of stable scope identity.
            if set(value) == {'path', 'sha256'} and not (self.root / name).is_file():
                return None
        size = value['bytes'] if 'bytes' in value else (self.root / name).stat().st_size
        result = {'path': name, 'sha256': value['sha256'], 'bytes': size}
        return result

    def _scan(self, value, pointer):
        reference = self._reference(value)
        if reference is not None:
            key = (reference['path'], reference['sha256'], reference['bytes'])
            existing = self.by_path.get(reference['path'])
            if existing is not None and existing != key:
                raise ValueError('An artifact path has conflicting alias identities.')
            self.by_path[reference['path']] = key
            if key not in self.by_target:
                artifact(self.root, reference)
                row = {'name': 'artifact-%08d' % (len(self.aliases) + 1),
                       'reference': reference, 'first_use': pointer, 'occurrences': 0}
                self.by_target[key] = row
                self.aliases.append(row)
            self.by_target[key]['occurrences'] += 1
            return
        if isinstance(value, Mapping):
            if set(value) == {'artifact'}:
                raise ValueError('The source uses a reserved logical artifact reference.')
            for key in sorted(value):
                if not isinstance(key, str):
                    raise ValueError('A bounded source map key is not text.')
                self._scan(value[key], pointer + '/' + _escape(key))
        elif isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray, StreamText)):
            for index, item in enumerate(value):
                self._scan(item, pointer + '/' + str(index))

    def _wrap(self, value):
        reference = self._reference(value)
        if reference is not None:
            key = (reference['path'], reference['sha256'], reference['bytes'])
            if key not in self.by_target:
                raise ValueError('The source introduced an artifact after alias indexing.')
            return {'artifact': '#/artifacts/' + self.by_target[key]['name']}
        if isinstance(value, Mapping):
            return _Map(self, value)
        if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray, StreamText)):
            return _Array(self, value)
        return value


def verify_aliases(stable_trace, mapping, expected_raw_trace, evidence_root):
    """Reject substitutions by comparison with the independently checked source.

    The bundle seal must additionally bind the exact serialized alias map and
    stable TRACE bytes. This function does not replace raw capture validation.
    """
    if not isinstance(mapping, Mapping) or set(mapping) != {'schema', 'session', 'aliases'}:
        raise ValueError('The artifact alias map has unsupported fields.')
    if type(mapping['schema']) is not int or mapping['schema'] != 1:
        raise ValueError('The artifact alias map schema is unsupported.')
    rows = mapping['aliases']
    if not isinstance(rows, Sequence) or isinstance(rows, (str, bytes)):
        raise ValueError('The artifact alias rows are not an ordered array.')
    names, targets = set(), set()
    for row in rows:
        if not isinstance(row, Mapping) or set(row) != {'name', 'reference', 'first_use', 'occurrences'}:
            raise ValueError('An artifact alias row has unsupported fields.')
        if row['name'] in names:
            raise ValueError('The artifact alias map repeats a logical name.')
        names.add(row['name'])
        reference = row['reference']
        artifact(evidence_root, reference)
        key = (reference['path'], reference['sha256'], reference['bytes'])
        if key in targets:
            raise ValueError('The artifact alias map repeats a physical target.')
        targets.add(key)
    expected = AliasProjection(expected_raw_trace, evidence_root)
    if _digest(mapping) != _digest(expected.mapping):
        raise ValueError('The artifact alias map differs from the checked source associations.')
    if _digest(stable_trace) != _digest(expected.stable):
        raise ValueError('The stable trace differs from its exact logical artifact projection.')
    return {'schema': 1, 'session': expected.mapping['session'], 'verified_aliases': len(expected.aliases),
            'trace_sha256': _digest(stable_trace), 'alias_map_sha256': _digest(mapping),
            'scope': 'Exact projection of the supplied checked raw trace. No cross-session identity claim.'}


def write_alias_map(directory, mapping, *, index_dir, writer_reference=None):
    """Keep every published alias artifact within the existing physical limit."""
    import subprocess
    from trace_block_chunks import MAX_RECORD_BYTES
    from trace_block_kernel_runtime import checked_reference
    directory, index_dir = Path(directory).absolute(), Path(index_dir).absolute()
    if index_dir.resolve().is_relative_to(directory.resolve()):
        raise ValueError('Alias indexes must remain outside the sealed alias directory.')
    directory.mkdir(parents=True, exist_ok=True)
    index_dir.mkdir(parents=True, exist_ok=True)
    logical = index_dir / 'ALIAS-INPUT.json'
    with logical.open('x') as stream:
        for part in json_document(mapping):
            stream.write(part)
    logical_hash = hashlib.sha256()
    with logical.open('rb') as stream:
        for data in iter(lambda: stream.read(65536), b''):
            logical_hash.update(data)
    target = directory / 'ALIASES.json'
    if target.exists() or target.is_symlink():
        raise ValueError('The output already contains an alias artifact.')
    if logical.stat().st_size <= MAX_RECORD_BYTES:
        with logical.open('rb') as source, target.open('xb') as destination:
            for data in iter(lambda: source.read(65536), b''):
                destination.write(data)
    else:
        if not isinstance(writer_reference, Mapping) or set(writer_reference) != {'path', 'sha256'}:
            raise ValueError('Oversized alias metadata requires its exact bound writer.')
        executable = Path(writer_reference['path'])
        checked_reference(dict(writer_reference, bytes=executable.stat().st_size))
        process = subprocess.run([str(executable), str(directory), str(logical), 'chunks/aliases',
                                  'kernel-json/ALIASES.json'], check=True, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE)
        if len(process.stdout) > MAX_RECORD_BYTES:
            raise ValueError('The alias writer returned an oversized envelope.')
        envelope = json.loads(process.stdout)
        wrapper = {'schema': 2, 'kind': 'kernel-json-artifact', 'logical_event': 'kernel-json/ALIASES.json',
                   'logical_sha256': logical_hash.hexdigest(), 'payload': envelope}
        payload = (json.dumps(wrapper, separators=(',', ':')) + '\n').encode()
        if len(payload) > MAX_RECORD_BYTES:
            raise ValueError('The alias metadata wrapper exceeds its physical limit.')
        target.write_bytes(payload)
    from trace_block_seal import file_sha256
    references = []
    for path in sorted(directory.rglob('*')):
        if path.is_symlink():
            raise ValueError('The sealed alias directory cannot contain a symlink.')
        if path.is_file():
            if path.stat().st_size > MAX_RECORD_BYTES:
                raise ValueError('An alias artifact exceeds the physical record limit.')
            references.append({'path': path.relative_to(directory).as_posix(),
                               'sha256': file_sha256(path), 'bytes': path.stat().st_size})
    return {'artifact': {'path': 'ALIASES.json', 'sha256': file_sha256(target), 'bytes': target.stat().st_size},
            'logical_sha256': logical_hash.hexdigest(), 'files': references}


class AliasDocument:
    """Expose inline and chunked aliases through the accepted lazy metadata reader."""
    def __init__(self, directory, reference, *, index_dir):
        from trace_block_kernel_artifacts import ArtifactReader
        self.reader = ArtifactReader(directory, index_dir)
        try:
            self.mapping = self.reader.read(reference)
        except BaseException:
            self.reader.close()
            raise

    def __enter__(self):
        return self.mapping

    def __exit__(self, *arguments):
        self.reader.close()


def verify_alias_files(directory, references):
    """Reject missing, changed, duplicate, or additional physical alias artifacts."""
    directory = Path(directory).resolve(strict=True)
    names = set()
    for reference in references:
        if reference['path'] in names:
            raise ValueError('The alias artifact seal repeats a path.')
        names.add(reference['path'])
        artifact(directory, reference)
    actual = set()
    for path in directory.rglob('*'):
        if path.is_symlink():
            raise ValueError('The alias artifact directory contains a symlink.')
        if path.is_file():
            actual.add(path.relative_to(directory).as_posix())
    if names != actual:
        raise ValueError('The alias artifact set differs from its complete seal.')
