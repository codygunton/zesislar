"""Retain released shell records in immutable, authenticated documents."""
import hashlib
import json
import os
import re
from pathlib import Path
import stat
import tempfile

FIELDS = ('shell_claim_owners', 'shell_releases', 'shell_admissions')


def document_path(directory, key, reference=None):
    name = hashlib.sha256(key.encode()).hexdigest()
    if reference is not None:
        if not isinstance(reference, str) or not re.fullmatch(r'[0-9a-f]{64}', reference):
            raise ValueError('The released shell archive identity changed.')
        name += '.' + reference
    return Path(directory) / (name + '.json')


def archive_record(data, key, reader):
    import admission_memory as memory
    ledger = memory.active_ledger() or os.environ.get('ZESU_CANONICAL_LEDGER', memory.DEFAULT_LEDGER)
    reference = memory.archived_shell_digest(data, key, ledger)
    if reference is None:
        raise KeyError(key)
    path = document_path(data['shell_archive_directory'], key, reference)
    if not os.path.lexists(path):
        path = document_path(data['shell_archive_directory'], key)
    before = reader.file_identity(path.lstat())
    value = reader.read(path)
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if (reader.file_identity(path.lstat()) != before or digest != reference
            or value.get('claim_key') != key or value.get('schema') != 'zesu.shell-archive.v1'):
        raise ValueError('The released shell archive identity changed.')
    return value['records']


def released_records(data, key, reader):
    """Prefer ledger records. Authenticate the archive only after removal."""
    owners, releases = data.get('shell_claim_owners', {}), data.get('shell_releases', {})
    if key in owners or key in releases:
        if key not in owners or key not in releases:
            raise ValueError('The ledger lacks exact closed and released shell ownership.')
        return owners[key], releases[key]
    records = archive_record(data, key, reader)
    return records['shell_claim_owners'], records['shell_releases']


def publish(directory, key, records):
    directory = Path(directory)
    directory.mkdir(mode=0o700, parents=True, exist_ok=True)
    info = directory.lstat()
    if (directory != directory.resolve() or not stat.S_ISDIR(info.st_mode)
            or info.st_uid != os.getuid() or info.st_mode & 0o022):
        raise ValueError('The shell archive directory is not private.')
    raw = (json.dumps({'schema': 'zesu.shell-archive.v1', 'claim_key': key,
                       'records': records}, separators=(',', ':')) + '\n').encode()
    digest = hashlib.sha256(raw).hexdigest()
    path = document_path(directory, key, digest)
    descriptor, temporary = tempfile.mkstemp(prefix='.pending-', dir=directory)
    try:
        with os.fdopen(descriptor, 'wb') as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        try:
            os.link(temporary, path)
        except FileExistsError:
            info = path.lstat()
            if (not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid()
                    or info.st_mode & 0o022 or path.read_bytes() != raw):
                raise ValueError('An existing shell archive differs from its release.')
        descriptor = os.open(directory, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    finally:
        Path(temporary).unlink(missing_ok=True)
    return digest


def _archive_released_record(data, key, directory):
    """Stage storage after the caller authenticates release under the ledger lock.

    The caller commits this index with the release. The existing token cleanup
    can then consult the archive if that commit precedes marker removal.
    """
    directory = str(Path(directory).absolute())
    if data.get('shell_archive_directory', directory) != directory:
        raise ValueError('The shell archive directory changed.')
    owner = data['shell_claim_owners'][key]
    release = data['shell_releases'][key]
    if (data['fixed_claims'].get(key) != 0 or release.get('owner') != owner['owner']
            or release.get('marker') != owner['marker']):
        raise ValueError('The shell archive lacks exact released ownership.')
    records = {field: data[field][key] for field in FIELDS if key in data.get(field, {})}
    growth = [row for row in data.get('shell_growth', []) if row.get('claim_key') == key]
    if growth:
        records['shell_growth'] = growth
    digest = publish(directory, key, records)
    data['shell_archive_directory'] = directory
    data.setdefault('shell_archive', {})[key] = digest
    for field in FIELDS:
        data.get(field, {}).pop(key, None)
    if growth:
        data['shell_growth'] = [row for row in data['shell_growth'] if row.get('claim_key') != key]
    return digest



def compact_released_shells(data, directory, reader):
    """Stage exact closed releases; retain every ineligible record."""
    import admission_memory as memory
    archived = []
    for key, owner in list(data.get('shell_claim_owners', {}).items()):
        release = data.get('shell_releases', {}).get(key)
        try:
            if (data['fixed_claims'].get(key) != 0 or release is None
                    or release.get('owner') != owner.get('owner')
                    or release.get('marker') != owner.get('marker')
                    or not owner.get('marker') or os.path.lexists(owner['marker'])
                    or not memory.ended_process(reader, owner['owner'])
                    or owner.get('leaf') and not memory.leaf_closed(reader, owner['leaf'])):
                continue
        except ValueError:
            # A changed actor or leaf stays authoritative in the ledger.
            continue
        _archive_released_record(data, key, directory)
        archived.append(key)
    return archived

def archive_released_shells(ledger, directory, *, reader=None):
    """Archive exact releases under the ledger lock. Never invoke on live data implicitly."""
    import admission_memory as memory
    reader = memory.ScopeReader() if reader is None else reader
    directory = str(Path(directory).absolute())
    with memory.ledger_transaction(ledger) as data:
        if data.get('shell_archive_directory', directory) != directory:
            raise ValueError('The shell archive directory changed.')
        archived = []
        for key, owner in list(data.get('shell_claim_owners', {}).items()):
            release = data.get('shell_releases', {}).get(key)
            if data['fixed_claims'].get(key) != 0 or release is None:
                continue
            if (release.get('owner') != owner['owner'] or release.get('marker') != owner['marker']
                    or os.path.lexists(owner['marker']) or not memory.ended_process(reader, owner['owner'])
                    or owner.get('leaf') and not memory.leaf_closed(reader, owner['leaf'])):
                raise ValueError('The shell archive lacks exact release and closure.')
            _archive_released_record(data, key, directory)
            archived.append(key)
        if archived:
            memory.write_ledger(ledger, data)
        return archived
