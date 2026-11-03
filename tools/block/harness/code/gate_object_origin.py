"""Authenticate objects from one explicitly accepted stock-gate build.

This origin grants no READY, physical-compilation receipt, or cache claim.
The normal inspector and target-bank import comparisons remain mandatory.
"""
import hashlib
from pathlib import Path
import stat
import subprocess

from entry_chain import binding
from binding_cache import identity

KIND = 'accepted-correctness-gate-objects'
LABEL = 'individual-object-from-accepted-correctness-gate'
SCHEMA = 'entry-chain.correctness-gate-origin.v1'
BUILD_RECORDS = {'dune-build-dir.json', 'trace.csexp',
                 '.digest-db', '.db', 'log.jsonl', '.filesystem-clock'}


def file_identity(path):
    return [list(row) for row in identity(Path(path))]


def tree(workspace):
    """Read Git without refreshing its index or changing its worktree."""
    command = ['git', '--no-optional-locks', '-C', str(workspace)]
    head = subprocess.check_output(command + ['rev-parse', 'HEAD'], text=True).strip()
    root = subprocess.check_output(command + ['rev-parse', 'HEAD^{tree}'], text=True).strip()
    listing = subprocess.check_output(command + ['ls-tree', '-r', 'HEAD'])
    clean = subprocess.run(command + ['diff', '--quiet', 'HEAD', '--'], check=False).returncode == 0
    return {'commit': head, 'tree': root, 'sha256': hashlib.sha256(listing).hexdigest(), 'clean': clean}


def sealed(reference, expected_identity, completed_ns):
    path = Path(reference['path'])
    info = path.lstat()
    actual = file_identity(path)
    stable = lambda value: [row[:4] + row[5:] for row in value]
    if (not stat.S_ISREG(info.st_mode) or path.is_symlink() or
            stable(actual) != stable(expected_identity) or
            info.st_mtime_ns > completed_ns or
            binding(path) != reference):
        raise ValueError('A gate object, source, or build record changed after the gate.')
    if actual != expected_identity:
        return {'path': str(path), 'expected_ctime_ns': expected_identity[0][4],
                'actual_ctime_ns': actual[0][4], 'SHA256_unchanged': True,
                'identity_except_ctime_unchanged': True}
    return None


def normalize_flags(flags, workspace):
    """Translate only Dune's exact default/install layout into the owned layout."""
    prefix = str(Path(workspace).resolve())
    return [word.replace(prefix + '/artifacts/', '{workspace}/artifacts/')
            .replace(prefix + '/default', '{workspace}/artifacts/default')
            .replace(prefix + '/install', '{workspace}/artifacts/install')
            .replace(prefix, '{workspace}') for word in flags]


def context(authority, reference, read):
    if authority.get('kind') != KIND or authority.get('binding') != reference:
        raise ValueError('The correctness-gate origin is not authorized.')
    publication = read(reference)
    if (publication.get('schema') != SCHEMA or publication.get('kind') != KIND or
            publication.get('gate_final') != authority.get('gate_final')):
        raise ValueError('The correctness-gate origin schema or accepted gate differs.')
    final = read(publication['gate_final'])
    gates = [row for row in final['gates'] if row['target'] == 'check-iris']
    if (final.get('success') is not True or final.get('source_clean_and_unchanged') is not True or
            len(gates) != 1 or gates[0].get('accepted') is not True):
        raise ValueError('The correctness gate lacks accepted unchanged source.')
    gate = gates[0]
    for key, name in [('result', 'RESULT'), ('request', 'REQUEST'),
                      ('closure', 'CLOSURE'), ('release', 'RELEASE')]:
        if publication[key] != gate['receipts'][name]:
            raise ValueError('A gate receipt differs from the accepted final packet.')
    result, request = read(publication['result']), read(publication['request'])
    closure, release = read(publication['closure']), read(publication['release'])
    completed = result['completed_ns']
    if (result.get('target') != 'check-iris' or result.get('success') is not True or
            result.get('exit_code') != 0 or request.get('target') != 'check-iris' or
            gate.get('all_owned_actors_closed') is not True or
            gate.get('outer_actors_closed') is not True or
            gate.get('kernel_aggregate_absent') is not True or gate.get('claim_value') != 0 or
            release.get('released') is not True or
            closure.get('all_owned_actors_closed') is not True or
            release.get('claim_key') != request['policy']['claim_key'] or
            release.get('bytes') != request['policy']['claim_bytes'] or
            release.get('owner') != request['owner'] or
            release.get('closure') != publication['closure']['path'] or
            any(Path(path).exists() for path in closure['batch']['aggregate_paths'])):
        raise ValueError('The correctness gate lacks exact successful closure and release.')
    for actor in [request['owner'], *closure['batch']['actors']]:
        try:
            fields = (Path('/proc') / str(actor['pid']) / 'stat').read_text().rsplit(')', 1)[1].split()
            if int(fields[19]) == actor['startticks'] and fields[0] not in ['Z', 'X']:
                raise ValueError('A correctness-gate actor is still active.')
        except FileNotFoundError:
            pass
    workspace = Path(publication['source_workspace']).resolve()
    build = Path(publication['build_root']).resolve()
    if (str(workspace) != request['workspace'] or str(build) != request['build'] or
            final['source_boundary']['workspace'] != str(workspace) or
            final['source_boundary']['commit'] != publication['source_tree']['commit'] or
            tree(workspace) != publication['source_tree'] or not publication['source_tree']['clean']):
        raise ValueError('The gate source tree or exact build directory changed.')
    if file_identity(build) != publication['build_identity'] or not build.is_dir():
        raise ValueError('The exact Dune build identity changed.')
    directories = publication['build_directories']
    if len(directories) != 1 or directories[0]['path'] != str(build / '.action-trace'):
        raise ValueError('The gate lacks its exact Dune action directory.')
    action = build / '.action-trace'
    if (action.is_symlink() or not action.is_dir() or list(action.iterdir()) or
            file_identity(action) != directories[0]['identity'] or
            action.stat().st_ctime_ns > completed or action.stat().st_mtime_ns > completed):
        raise ValueError('The Dune action directory changed after the gate.')
    records = publication['build_records']
    if (len(records) != len(BUILD_RECORDS) or
            {Path(row['binding']['path']).name for row in records} != BUILD_RECORDS):
        raise ValueError('The gate lacks its complete sealed Dune build records.')
    build_observations = []
    for row in records:
        if not Path(row['binding']['path']).is_relative_to(build):
            raise ValueError('A Dune build record leaves its exact build.')
        observation = sealed(row['binding'], row['identity'], completed)
        if observation:
            build_observations.append(observation)
    layout = read(publication['dune_build_directory'])
    if (layout['workspace'] != str(workspace) or layout['physical_directory'] != str(build) or
            publication['dune_build_directory'] not in [row['binding'] for row in publication['build_records']]):
        raise ValueError('The Dune build marker names another build.')
    for tool in ['compiler', 'coqdep']:
        if binding(publication[tool]['path']) != publication[tool]:
            raise ValueError('The gate compiler installation changed.')
    if publication['compiler']['path'] not in (build / 'trace.csexp').read_text():
        raise ValueError('The gate trace does not identify its bound compiler.')
    rows = publication['modules']
    selected = {row['module']: row for row in rows}
    if (len(selected) != len(rows) or
            {name: row['object'] for name, row in selected.items()} != authority.get('module_objects')):
        raise ValueError('The gate object selection differs from its exact authority.')
    runtime = read(publication['resolution_runtime'])
    target = Path(runtime['prepared_workspace']).resolve()
    mapping = runtime['proof_runtime']['module_files']
    observations = {}
    for name, row in selected.items():
        relative = Path(mapping[name])
        if (relative.parts[:2] != ('artifacts', 'default') or
                row['target_relative'] != str(relative) or '..' in relative.parts):
            raise ValueError('A gate module changes its exact owned module mapping.')
        source = build / Path(*relative.parts[1:])
        if row['source']['path'] != str(source) or row['object']['path'] != str(source.with_suffix('.vo')):
            raise ValueError('A gate module leaves its exact Dune mapping.')
        observations[name] = [value for value in
            [sealed(row['source'], row['source_identity'], completed),
             sealed(row['object'], row['object_identity'], completed)] if value is not None]
        if binding(target / relative)['sha256'] != row['source']['sha256']:
            raise ValueError('The gate source differs from the authorized target source.')
    flags = [word.replace(str(target) + '/artifacts', str(build))
             .replace(str(target), str(build)) for word in runtime['physical_flags']]
    if normalize_flags(flags, build) != normalize_flags(runtime['physical_flags'], target):
        raise ValueError('The gate resolution context changes the owned flags.')
    config = {'prepared_workspace': str(build),
              'proof_runtime': {'module_files': {name: str(Path(*Path(row['target_relative']).parts[1:]))
                                               for name, row in selected.items()}},
              'bindings': [publication['compiler'], publication['coqdep']], 'physical_flags': flags,
              'gate_identity_observations': observations,
              'gate_build_observations': build_observations}
    return config, publication, selected


def selected_origin(authority, reference, module, source, obj, compiler, flags, workspace, read):
    config, publication, rows = context(authority, reference, read)
    if module not in rows:
        raise ValueError('The module lacks an authorized gate object.')
    row = rows[module]
    source, obj, workspace = Path(source).resolve(), Path(obj).resolve(), Path(workspace).resolve()
    original = Path(row['source']['path'])
    expected = original if workspace == Path(config['prepared_workspace']) else workspace / row['target_relative']
    if (source != expected or obj != expected.with_suffix('.vo') or
            binding(source)['sha256'] != row['source']['sha256'] or
            binding(obj)['sha256'] != row['object']['sha256'] or compiler != publication['compiler']):
        raise ValueError('The selected gate source, object, compiler, or owned mapping differs.')
    from source_context import compilation
    effective = compilation(flags, binding(source))['physical_flags']
    if normalize_flags(effective, workspace) != normalize_flags(config['physical_flags'], config['prepared_workspace']):
        raise ValueError('The selected gate object has another resolution context.')
    return {'kind': LABEL, 'publication': reference, 'gate_final': publication['gate_final'],
            'resolution_runtime': publication['resolution_runtime']}, effective


def relocate(publication, module, path, workspace):
    """Relocate one inspected gate dependency by its bound logical-module mapping."""
    build = Path(publication['build_root']).resolve()
    path, workspace = Path(path).resolve(), Path(workspace).resolve()
    if not path.is_relative_to(build):
        return path
    from object_import_migration import bound_record
    runtime = bound_record(publication['resolution_runtime'])
    relative = Path(runtime['proof_runtime']['module_files'][module])
    if path != (build / Path(*relative.parts[1:])).with_suffix('.vo'):
        raise ValueError('A gate dependency differs from its bound module mapping.')
    return (workspace / relative).with_suffix('.vo')
