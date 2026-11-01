"""Seal validated producer history. Keep current inputs independently checked.

This source API does not enable compaction in existing launches. A caller must
review the returned projection before writing a successor runtime.
Later-produced objects keep the existing compiler-snapshot receipt checks.
"""
from copy import deepcopy
import fcntl
import hashlib
import json
import os
import re
from pathlib import Path
import stat
import tempfile

SCHEMA = 'scratch.validated-lineage.v1'
LEDGER = Path('/home/cody/zesislar/_build/agents/worker-build-2/native-region-release-v1/LEDGER.json')
LOCK = LEDGER.with_name('LEDGER.lock')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def stamp(info):
    return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns,
            info.st_ctime_ns, info.st_mode)


def raw_bound(reference, *, private=False):
    from binding_cache import identity
    require(isinstance(reference, dict) and set(reference) == {'path', 'sha256'}
            and isinstance(reference['path'], str) and
            isinstance(reference['sha256'], str) and
            re.fullmatch(r'[0-9a-f]{64}', reference['sha256']),
            'The sealed input binding is invalid.')
    path = Path(reference['path'])
    require(path.is_absolute() and '..' not in path.parts,
            'The sealed input path is not absolute and normalized.')

    def check_private():
        info = path.lstat()
        require(path == path.resolve() and stat.S_ISREG(info.st_mode)
                and info.st_uid == os.getuid() and info.st_nlink == 1
                and stat.S_IMODE(info.st_mode) == 0o400,
                'The sealed receipt is not a protected owned file.')

    if private:
        check_private()
    before = identity(path)
    with path.open('rb') as stream:
        require(stamp(os.fstat(stream.fileno())) == before[1],
                'A sealed input changed before reading.')
        data = stream.read()
        require(stamp(os.fstat(stream.fileno())) == before[1],
                'A sealed input changed while reading.')
    require(identity(path) == before, 'A sealed input changed after reading.')
    if private:
        check_private()
    require(hashlib.sha256(data).hexdigest() == reference['sha256'], 'A sealed input hash differs.')
    return data


def read(reference, *, private=False):
    return json.loads(raw_bound(reference, private=private))


def binding(path):
    from binding_cache import digest, force_hashing
    with force_hashing(True):
        return {'path': str(Path(path).absolute()), 'sha256': digest(path)}


def write_once(path, value):
    """Publish one complete, read-only receipt. Never replace a prior receipt."""
    path = Path(path)
    descriptor, temporary = tempfile.mkstemp(prefix='.sealed-lineage-', dir=path.parent)
    try:
        with os.fdopen(descriptor, 'w') as stream:
            json.dump(value, stream, separators=(',', ':'), allow_nan=False)
            stream.flush()
            os.fchmod(stream.fileno(), 0o400)
            os.fsync(stream.fileno())
        os.link(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)
    descriptor = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    return binding(path)


def _canonical_release(closed, released):
    require(LOCK == LEDGER.with_name('LEDGER.lock'), 'The release lock is not canonical.')
    with LOCK.open('rb') as stream:
        fcntl.flock(stream, fcntl.LOCK_SH)
        raw = LEDGER.read_bytes()
        data = json.loads(raw)
        key = closed['claim_key']
        require(key in data['fixed_claims'] and data['fixed_claims'][key] == 0,
                'The producer claim remains live or unknown.')
        recorded = data.get('entry_pilot_outside_releases', {}).get(key)
        require(isinstance(recorded, dict) and recorded.get('bytes') == released['bytes']
                and recorded.get('owner') == closed.get('owner')
                and recorded.get('closure') == released['closure_binding'],
                'The canonical release names another producer, closure, or amount.')
    return {'claim_key': key, 'bytes': recorded['bytes'], 'owner': recorded['owner'],
            'closure': recorded['closure'], 'ledger_sha256_at_publication': hashlib.sha256(raw).hexdigest()}


def _current_files(compiler, flags, environment, extra=()):
    """Include every regular load-path file. Do not filter by extension."""
    from compiler_snapshot import load_roots, physical_context
    context = physical_context(compiler, flags, environment)
    paths = {Path(compiler).absolute(), *(Path(path).absolute() for path in extra)}
    for root in load_roots(compiler, flags, environment):
        if not root.exists():
            continue
        require(root.is_dir(), 'A physical load root is not a directory.')
        for path in root.rglob('*'):
            if path.is_symlink() and path.is_dir():
                raise ValueError('A load path contains an unclassified directory alias.')
            if path.is_file():
                paths.add(path.absolute())
    from binding_cache import identity
    identities = {path: identity(path) for path in paths}
    rows = [binding(path) for path in sorted(paths)]
    after = {Path(compiler).absolute(), *(Path(path).absolute() for path in extra)}
    for root in load_roots(compiler, flags, environment):
        if not root.exists():
            continue
        for path in root.rglob('*'):
            if path.is_symlink() and path.is_dir():
                raise ValueError('A load path contains an unclassified directory alias.')
            if path.is_file():
                after.add(path.absolute())
    require(paths == after and all(identity(path) == prior for path, prior in identities.items())
            and context == physical_context(compiler, flags, environment),
            'The physical load-path namespace changed during publication.')
    return rows, context


def _mapped_inputs(runtime, workspace):
    paths = set()
    for name in runtime['proof_runtime']['module_files'].values():
        source = (workspace / name).absolute()
        require(source.is_file(), 'A mapped source is absent from the current bank.')
        paths.add(source)
        for suffix in ['.vo', '.vos']:
            path = source.with_suffix(suffix)
            if path.is_file():
                paths.add(path)
    return sorted(paths)


def _relative_context(flags, environment):
    paths = [flags[index + 1] for index, word in enumerate(flags[:-1])
             if word in {'-Q', '-R', '-I', '-coqlib'}]
    for name in ['OCAMLPATH', 'CAML_LD_LIBRARY_PATH', 'COQPATH']:
        paths.extend(part for part in environment.get(name, '').split(':') if part)
    return any(not Path(path).is_absolute() for path in paths)


def publish(supplier_reference, output):
    """Validate a closed supplier fully before exporting and sealing history."""
    from binding_cache import force_hashing
    from proof_bindings import check_proof_bindings
    from compiler_snapshot import binding_rows
    import supplier_ready
    from end_run_cleanup import closed_job
    from harness_commit import check
    from coqc_findlib import compiler_environment
    import clone_copy

    requested = Path(output).absolute()
    output = requested.resolve()
    require(not output.exists(), 'The sealed bank output already exists.')
    with force_hashing(True):
        supplier = supplier_ready.validate(supplier_reference)
        ready = supplier['ready']
        require(ready.get('harness') is not None, 'The producer lacks its Git tool identity.')
        check(ready['harness'])
        check_proof_bindings(ready, force_full=True)
        original = Path(ready['prepared_workspace']).resolve()
        job = next(job for job in ready['jobs'] if job['phase'] == 'prerequisites')
        require(job.get('key') == 'prerequisites', 'The producer job has another key.')
        lifecycle = closed_job(job, Path(job['output']).parent.parent)
        require(lifecycle is not None, 'The producer lifecycle is not closed.')
        closed, released = read(lifecycle['closure']), read(lifecycle['release'])
        require(read(lifecycle['result']).get('success') is True and
                released.get('bytes') == job['claim_bytes'] and released['bytes'] > 0,
                'The producer compilation or exact release failed.')
        canonical = _canonical_release(closed, dict(released, closure_binding=lifecycle['closure']))
        environment = dict(os.environ,
            OCAMLPATH=ready['proof_runtime'].get('ocamlpath', '').replace('{workspace}', str(original)))
        environment = compiler_environment(original, environment)
        actual = read(supplier['packet']['runtime'])
        require(actual.get('harness') == ready['harness'],
                'The compiled job names another producer tool pin.')
        compiler = ready['effective_compiler_version']['compiler']
        require(binding(compiler['path']) == compiler, 'The producer compiler changed.')
        direct, context = _current_files(compiler['path'], ready['physical_flags'], environment,
                                         _mapped_inputs(ready, original))
        historical = deepcopy(binding_rows(ready))
        # No path or byte from the producer is changed by this export.
        for path in original.rglob('*'):
            if path.is_symlink():
                require(not Path(os.readlink(path)).is_absolute() and path.resolve().is_relative_to(original),
                        'A source bank alias cannot be exported safely.')
        output.mkdir(parents=True, mode=0o700)
        exported = output / 'bank'
        clone_copy.copytree(original, exported, symlinks=True)
        exports, aliases = [], []
        for path in sorted(exported.rglob('*')):
            relative = path.relative_to(exported)
            source = original / relative
            if path.is_symlink():
                require(os.readlink(source) == os.readlink(path) and path.resolve().is_relative_to(exported),
                        'An exported alias differs or escapes.')
                aliases.append({'relative': str(relative), 'target': os.readlink(path)})
            elif path.is_file():
                before, after = binding(source), binding(path)
                require(before['sha256'] == after['sha256'] and
                        (source.stat().st_dev, source.stat().st_ino) != (path.stat().st_dev, path.stat().st_ino),
                        'An exported input differs or shares the producer inode.')
                with path.open('rb') as stream:
                    os.fsync(stream.fileno())
                exports.append({'relative': str(relative), 'sha256': after['sha256'],
                                'source': before, 'mode': stat.S_IMODE(path.stat().st_mode)})
        evidence = {}
        directory = output / 'evidence'
        directory.mkdir(mode=0o700)
        originals = {'job_result': lifecycle['result'], 'closure': lifecycle['closure'],
                     'release': lifecycle['release'], 'supplier': supplier_reference}
        originals.update({name: row for name, row in supplier['packet'].items()
                          if isinstance(row, dict) and set(row) == {'path', 'sha256'}})
        for name, row in originals.items():
            data = raw_bound(row)
            target = directory / (name + '.json')
            with target.open('xb') as stream:
                stream.write(data); stream.flush(); os.fsync(stream.fileno())
            target.chmod(0o400)
            evidence[name] = binding(target)
        check_proof_bindings(ready, force_full=True)
        require(supplier_ready.validate(supplier_reference)['ready'] == ready,
                'The producer evidence changed during durable export.')
        final_release = _canonical_release(closed, dict(released, closure_binding=lifecycle['closure']))
        require(all(final_release[key] == canonical[key]
                    for key in ['claim_key', 'bytes', 'owner', 'closure']),
                'The canonical release changed during durable export.')
        require(direct == _current_files(compiler['path'], ready['physical_flags'], environment,
                                         _mapped_inputs(ready, original))[0],
                'A current physical input changed during durable export.')
        archive = write_once(output / 'HISTORICAL-ROWS.json', {'rows': historical})
        inventory = write_once(output / 'EXPORTED-FILES.json', {'workspace': str(exported),
            'files': exports, 'symlinks': aliases})
        value = {'schema': SCHEMA, 'requested_output': str(requested), 'resolved_output': str(output),
            'producer_ready': supplier['packet']['ready'], 'producer_harness': ready['harness'],
            'producer_evidence': evidence, 'producer_originals': originals,
            'canonical_release': canonical,
            'compiler': compiler, 'producer_workspace': str(original), 'physical_context': context,
            'current_load_files': direct, 'working_directory': os.getcwd(),
            'relative_context': _relative_context(ready['physical_flags'], environment),
            'physical_flags': ready['physical_flags'],
            'expected_mcp_flags': ready['expected_mcp_flags'], 'exported_inventory': inventory,
            'historical_inventory': archive, 'historical_row_count': len(historical),
            'validation': {'supplier_ready': True, 'forced_full_bindings': True,
                           'closure': True, 'exact_release': True, 'durable_exports': True},
            'scope': 'Past producer validation only. Current coqc inputs always require direct hashes.'}
        return write_once(output / 'RECEIPT.json', value)


def _inside(root, path):
    require(path.is_absolute() and path == path.resolve() and path.is_relative_to(root),
            'A sealed evidence path leaves its durable root.')
    return path


def validate(reference):
    """Authenticate past validation. Do not assert that current files are unchanged."""
    value = read(reference, private=True)
    require(value.get('schema') == SCHEMA and value.get('validation') == {
        'supplier_ready': True, 'forced_full_bindings': True, 'closure': True,
        'exact_release': True, 'durable_exports': True}, 'The lineage validation record differs.')
    root = Path(value['resolved_output'])
    require(root.is_absolute() and root == root.resolve() and
            Path(reference['path']) == root / 'RECEIPT.json',
            'The receipt names another durable bank.')
    evidence, originals = value['producer_evidence'], value['producer_originals']
    require(set(evidence) == set(originals) and
            {'supplier', 'ready', 'source_packet', 'import_graph', 'runtime',
             'verification', 'calls', 'result', 'job_result', 'closure', 'release'} <= set(evidence),
            'The durable producer evidence is incomplete.')
    values = {}
    for name, row in evidence.items():
        require(Path(row['path']) == root / 'evidence' / (name + '.json') and
                row['sha256'] == originals[name]['sha256'],
                'A durable producer payload differs from its original.')
        _inside(root, Path(row['path']))
        values[name] = read(row, private=True)
    closed, released = values['closure'], values['release']
    record = value['canonical_release']
    require(closed.get('all_owned_actors_closed') is True and closed.get('actors') and
            all(row.get('ended') is True for row in closed['actors']) and
            released.get('released') is True and released.get('bytes') == record['bytes'] > 0 and
            released.get('claim_key') == record['claim_key'] == closed.get('claim_key') and
            record['owner'] == closed.get('owner'), 'The producer closure or exact release differs.')
    require(record['closure'] == originals['closure'] and
            values['ready'].get('harness') == values['runtime'].get('harness')
                == value['producer_harness'] and
            values['result'].get('success') is True and
            values['job_result'].get('success') is True and
            values['result'].get('prerequisites') == originals['job_result'],
            'The durable producer identity differs.')
    # All these original payloads passed supplier_ready.validate at publication.
    # Their hashes remain identical; validation never follows their historical paths.
    for name, row in values['supplier'].items():
        if isinstance(row, dict) and set(row) == {'path', 'sha256'}:
            require(originals.get(name) == row, 'A supplier payload names another original.')
    _inside(root, Path(value['exported_inventory']['path']))
    _inside(root, Path(value['historical_inventory']['path']))
    inventory = read(value['exported_inventory'], private=True)
    exported = root / 'bank'
    require(inventory.get('workspace') == str(exported), 'The durable export root differs.')
    names = set()
    for row in inventory['files'] + inventory['symlinks']:
        name = Path(row['relative'])
        require(not name.is_absolute() and name.parts and '..' not in name.parts and
                str(name) == row['relative'] and str(name) not in names,
                'An exported file escapes or repeats.')
        names.add(str(name))
    return dict(receipt=value, inventory=inventory)


def verify_exports(reference):
    """Hash every exported input before adoption or any producer-workspace deletion."""
    sealed = validate(reference)
    inventory = sealed['inventory']
    root = Path(inventory['workspace'])
    from binding_cache import identity
    result, identities = [], {}
    for row in inventory['files']:
        path = _inside(root, root / row['relative'])
        require(path.is_file() and not path.is_symlink() and
                stat.S_IMODE(path.stat().st_mode) == row['mode'],
                'An exported file identity or mode changed.')
        require(path.stat().st_uid == os.getuid() and path.stat().st_nlink == 1,
                'An exported input is not one owned file.')
        identities[path] = identity(path)
        actual = binding(path)
        require(actual['sha256'] == row['sha256'], 'An exported input hash differs.')
        result.append(actual)
    for row in inventory['symlinks']:
        path = root / row['relative']
        require(path.is_symlink() and os.readlink(path) == row['target'] and
                path.resolve().is_relative_to(root), 'An exported alias changed or escaped.')
    # Also refuse additions. A new plugin or object cannot enter through an export.
    actual = {str(path.relative_to(root)) for path in root.rglob('*')
              if path.is_file() or path.is_symlink()}
    require(actual == {row['relative'] for row in inventory['files'] + inventory['symlinks']},
            'The exported input inventory changed.')
    require(all(identity(path) == before for path, before in identities.items()),
            'An exported input changed during verification.')
    return result


def _active_paths(runtime, rows):
    """Keep all named inputs, including paths in currently consumed JSON payloads."""
    by_path = {row['path']: row for row in rows}
    active, visited = set(), set()

    def visit(value):
        if isinstance(value, dict):
            if isinstance(value.get('path'), str) and isinstance(value.get('sha256'), str):
                row = {'path': value['path'], 'sha256': value['sha256']}
                prior = by_path.get(row['path'])
                require(prior is None or prior['sha256'] == row['sha256'],
                        'A current metadata binding conflicts with a retained row.')
                by_path[row['path']] = row
            # The flat list is historical lineage. Every other runtime field
            # remains current, including producer-input declarations.
            for key, item in value.items():
                if key not in {'bindings', 'binding_inventory'}:
                    visit(item)
        elif isinstance(value, list):
            for item in value:
                visit(item)
        elif isinstance(value, str) and Path(value).is_absolute():
            path = Path(value)
            active.add(str(path)); active.add(str(path.resolve()))
            row = by_path.get(str(path))
            require(not (row is None and path.suffix == '.json' and path.is_file()),
                    'An unclassified current JSON input requires legacy validation.')
            if row is not None and path.suffix == '.json' and str(path) not in visited:
                visited.add(str(path))
                # These bytes remain actual inputs. Do not hide a transitive
                # configuration dependency behind the producer receipt.
                payload = read(row)
                visit(payload)
                # A nested runtime can still be consumed by a legacy route.
                # Keep its entire row list conservatively until that route has
                # its own checked receipt integration.
                if isinstance(payload, dict) and 'bindings' in payload:
                    visit(payload['bindings'])

    visit({key: value for key, value in runtime.items()
           if key not in {'bindings', 'binding_inventory'}})
    return active


def project(runtime, reference, *, environment=None):
    """Propose a row projection only. Existing launch routes do not consume it."""
    from compiler_snapshot import binding_rows, load_roots
    from coqc_findlib import compiler_environment
    sealed = validate(reference)
    receipt = sealed['receipt']
    original = read(receipt['historical_inventory'], private=True)['rows']
    covered = {(row['path'], row['sha256']) for row in original}
    current = Path(runtime['prepared_workspace']).resolve()
    compiler = runtime['effective_compiler_version']['compiler']
    require(compiler == receipt['compiler'], 'The current compiler differs from the sealed producer.')
    from supplier_ready import flags
    for field in ['physical_flags', 'expected_mcp_flags']:
        require(flags(runtime[field], current) == flags(receipt[field], receipt['producer_workspace']),
                'The current compiler flag context differs from the sealed producer.')
    environment = dict(os.environ if environment is None else environment)
    environment['OCAMLPATH'] = runtime['proof_runtime'].get('ocamlpath', '').replace('{workspace}', str(current))
    environment = compiler_environment(current, environment)
    require(not (receipt['relative_context'] or _relative_context(runtime['physical_flags'], environment))
            or os.getcwd() == receipt['working_directory'],
            'A relative compiler context requires legacy validation after a directory change.')
    # This always hashes all regular current load-path files, with no extension
    # filter. The receipt never substitutes for current compiler input hashing.
    direct, context = _current_files(compiler['path'], runtime['physical_flags'], environment,
                                     _mapped_inputs(runtime, current))
    roots = [current, *(path.resolve() for path in load_roots(compiler['path'], runtime['physical_flags'], environment))]
    rows = binding_rows(runtime)
    # Initial installed inputs remain authenticated by the producer's full seal.
    # Current/new explicit bindings take precedence only when hashes agree.
    expected = {}
    for row in receipt['current_load_files']:
        path = Path(row['path'])
        producer = Path(receipt['producer_workspace'])
        if path.is_relative_to(producer):
            path = current / path.relative_to(producer)
        expected[str(path.resolve())] = row['sha256']
    for row in rows:
        name = str(Path(row['path']).resolve())
        if name in expected and expected[name] != row['sha256']:
            raise ValueError('A current input disagrees with the sealed producer.')
        expected[name] = row['sha256']
    for row in direct:
        require(expected.get(str(Path(row['path']).resolve())) == row['sha256'],
                'A current compiler input is new, unbound, or changed.')
    named = _active_paths(runtime, rows)
    retained, encapsulated = [], []
    for row in rows:
        path = Path(row['path']).resolve()
        needed = row['path'] in named or str(path) in named or any(path.is_relative_to(root) for root in roots)
        if needed or (row['path'], row['sha256']) not in covered:
            retained.append(deepcopy(row))
        else:
            encapsulated.append(deepcopy(row))
    require(len(retained) + len(encapsulated) == len(rows), 'The lineage projection lost an input.')
    return {'encapsulated_rows': encapsulated, 'retained_rows': retained,
        'historical_inventory': receipt['historical_inventory'], 'receipt': reference,
        'current_direct_hashes': direct, 'current_physical_context': context,
        'remaining_external_inputs': [row for row in retained
             if not Path(row['path']).resolve().is_relative_to(current)],
        'scope': 'Source-only proposal. No launch runtime or file is modified.',
        'cleanup_qualification': 'Still-referenced legacy inputs remain active until public relocation checks pass.'}
