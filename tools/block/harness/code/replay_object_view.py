"""Create one exact replay view without changing either source bank."""
from pathlib import Path

import clone_copy
from entry_chain import binding, read_bound, save
from object_imports import _record
from object_import_migration import inspector
from installed_mappings import InstalledMappings, MissingLibraryObject

REPLAY_SHA = 'f1e02ad7f032a29f35d538a67f070ec7b12e89b6a1612595a50c68075643dd94'
MODULE = 'ZesuSsz.Compliance.DecodeItemHints'
SOURCE_SHA = '20e90ffbfb2e89274ec818641f9b0f890375ddd00bbe8dd1948e634bcbc8ec38'


def ordinary_umbrella(ready_reference, receipt_reference):
    ready = read_bound(ready_reference)
    if Path(ready_reference['path']).name != 'READY-RUNTIME.json':
        raise ValueError('The replay view requires the published declaration READY.')
    if ready.get('declarations_only') is not True or ready.get('control_session'):
        raise ValueError('The replay umbrella did not use the declaration-only route.')
    readiness = read_bound(ready['readiness'])
    result = read_bound(readiness['prerequisite_result'])
    job = next(row for row in ready['jobs'] if row['phase'] == 'prerequisites')
    directory = Path(job['output'])
    closed=read_bound(binding(directory / 'CLOSURE.json'))
    released=read_bound(binding(directory / 'RELEASE.json'))
    outer=read_bound(binding(Path(ready_reference['path']).parent / 'RESULT.json'))
    if (outer.get('status')!='declarations_passed' or outer.get('success') is not True or
            outer.get('prerequisites')!=readiness['prerequisite_result'] or
            result.get('success') is not True or readiness.get('all_required_compiles_passed') is not True or
            readiness['prerequisite_result'] != binding(directory / 'RESULT.json') or
            closed.get('all_owned_actors_closed') is not True or released.get('released') is not True or
            closed.get('claim_key')!=released.get('claim_key') or
            released.get('bytes')!=job.get('claim_bytes') or released.get('bytes',0)<=0 or
            ready.get('object_imports', {}).get(MODULE) != receipt_reference):
        raise ValueError('The replay umbrella lacks its closed accepted declaration result.')
    receipt = read_bound(receipt_reference)
    if receipt.get('schema') == 'entry-chain.object-import-migration.v1':
        raise ValueError('The new umbrella requires its ordinary compiler receipt.')
    read_bytes(receipt['source']);read_bytes(receipt['object'])
    source, obj = Path(receipt['source']['path']), Path(receipt['object']['path'])
    if receipt['source']['sha256'] != SOURCE_SHA:
        raise ValueError('The replay umbrella source changed.')
    workspace = Path(receipt['import_provenance']['owned_workspace']).resolve()
    flags = receipt.get('compiler_context', {}).get('base_flags', receipt['normalized_flags'])
    imports, recorded_workspace = _record(receipt_reference, MODULE, source, obj,
                                          receipt['compiler'], flags, workspace)
    if recorded_workspace.resolve() != workspace:
        raise ValueError('The ordinary umbrella workspace changed.')
    return ready, receipt, imports, workspace


def select_closure(roots, resolve_original, donor_imports, inspect):
    """Prefer original imports. Refuse a mismatch instead of replacing it."""
    selected = dict(roots)
    pending = list(roots)
    checks = []
    while pending:
        name = pending.pop(0)
        owner = selected[name]
        summary = inspect([owner['object']['path']], [])['objects']
        if len(summary) != 1 or summary[0]['module'] != name:
            raise ValueError('A replay object has another canonical module name: ' + name)
        names = [row['module'] for row in summary[0]['imports']]
        if len(names) != len(set(names)):
            raise ValueError('A replay object repeats an imported module.')
        for dependency in names:
            if dependency not in selected:
                candidate = resolve_original(dependency)
                if candidate is None:
                    candidate = donor_imports.get(dependency)
                if candidate is None:
                    raise ValueError('The replay view lacks an imported object: ' + dependency)
                selected[dependency] = candidate
                pending.append(dependency)
            checks.append({'owner': owner['object']['path'], 'module': dependency,
                           'object': selected[dependency]['object']['path']})
    result = inspect([row['object']['path'] for row in selected.values()], checks)
    if (len(result['checks']) != len(checks) or any(row.get('compatible') is not True for row in result['checks']) or
            any({key: row[key] for key in ['owner', 'module', 'object']} != expected
                for row, expected in zip(result['checks'], checks))):
        raise ValueError('A replay object has a missing or mismatched md_deps import.')
    return selected, result


def create(spec_reference, output):
    spec = read_bound(spec_reference)
    original_reference = spec['original_replay']
    if original_reference['sha256'] != REPLAY_SHA:
        raise ValueError('The replay authority changed.')
    original = read_bound(original_reference)
    for reference in original['projects']:
        read_bytes(reference)
    old = Path(original['physical_workspace']).resolve()
    original_ready = read_bound(original['support_READY'])
    ready, receipt, imports, donor = ordinary_umbrella(spec['umbrella_READY'], spec['umbrella_receipt'])
    compiler = receipt['compiler']
    expected_compiler = original_ready['effective_compiler_version']['compiler']
    if compiler != expected_compiler or binding(compiler['path']) != compiler:
        raise ValueError('The replay view compiler differs from its original authority.')
    coqdep = Path(compiler['path']).with_name('coqdep')
    coqdep_reference = next(row for row in original_ready['bindings'] if Path(row['path']) == coqdep)
    if binding(coqdep) != {key: coqdep_reference[key] for key in ['path', 'sha256']}:
        raise ValueError('The replay coqdep binding changed.')
    policy = read_bound(binding(Path(__file__).resolve().parents[1] / 'policies/OBJECT-IMPORT-MIGRATION-ORIGINS.json'))
    flags = [word.replace(str(Path(original_ready['prepared_workspace'])), str(old))
             for word in original_ready['physical_flags']]
    resolver = InstalledMappings(flags, coqdep=coqdep)
    roots = {}
    for row in original['source_object_bindings']:
        read_bytes(row['source']); read_bytes(row['object'])
        roots[row['module']] = dict(row, bank='original')
    extra = read_bound(original['compatible_extra_compiles'])
    if extra.get('health_success') is not True or extra.get('normal_close') is not True:
        raise ValueError('The original extra declarations lack their accepted closure.')
    for row in extra['compiles']:
        if Path(row['source']['path']).name == 'ResourceGroups308.v':
            read_bytes(row['source']); read_bytes(row['object'])
            roots['ZesuSsz.Automation.ResourceGroups308'] = dict(row, bank='original')
    roots[MODULE] = {'source': receipt['source'], 'object': receipt['object'], 'bank': 'umbrella'}
    modules = read_bound(receipt['runtime'])['module_files']
    donor_rows = {}
    for name, obj in imports.items():
        source = donor / modules[name]
        donor_rows[name] = {'source': binding(source), 'object': obj, 'bank': 'umbrella'}

    def resolve(name):
        try:
            resolved = resolver.resolution(name)
        except MissingLibraryObject as error:
            # Ambiguous resolution and changed tools never permit a fallback.
            if Path(error.path).exists():raise
            return None
        if resolved['canonical'] != name:
            raise ValueError('The original replay import uses another module alias: ' + name)
        obj = Path(resolved['object'])
        source = obj.with_suffix('.v')
        return {'object': binding(obj), 'source': binding(source) if source.is_file() else None,
                'bank': 'original' if obj.resolve().is_relative_to(old) else 'installed'}

    selected, compared = select_closure(roots, resolve, donor_rows,
                                        lambda objects, checks: inspector(policy, objects, checks))
    output = Path(output).absolute()
    if output.exists() or output.is_symlink() or output.is_relative_to(old) or output.is_relative_to(donor):
        raise ValueError('The replay view must use a fresh path outside both banks.')
    # Finish all authentication before creating the owned output.
    for row in selected.values():
        read_bytes(row['object'])
        if row.get('source') is not None:read_bytes(row['source'])
        if row['bank']!='installed':
            bank=old if row['bank']=='original' else donor
            relative=Path(row['object']['path']).resolve().relative_to(bank)
            if relative.parts[0]=='default':relative=Path('artifacts')/relative
            if relative.parts[:2]!=('artifacts','default'):
                raise ValueError('A replay object leaves the owned artifact mapping.')
    output.mkdir(parents=True)
    copied = []
    for name, row in selected.items():
        if row['bank'] == 'installed':
            continue
        bank = old if row['bank'] == 'original' else donor
        for key in ['source', 'object']:
            reference = row.get(key)
            if reference is None:continue
            source = Path(reference['path']).resolve()
            relative = source.relative_to(bank)
            if relative.parts[0]=='default':relative=Path('artifacts')/relative
            if relative.parts[:2] != ('artifacts', 'default'):
                raise ValueError('A replay object leaves the owned artifact mapping.')
            target = output / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            clone_copy.copy2(source, target)
            if binding(target)['sha256'] != reference['sha256'] or target.stat().st_ino == source.stat().st_ino:
                raise ValueError('A replay reflink differs from its authenticated input.')
            copied.append({'module': name, 'kind': key, 'original': reference, 'owned': binding(target)})
    for reference in original['projects']:
        clone_copy.copy2(reference['path'], output / Path(reference['path']).name)
    # Preserve the existing plugin view. No source bank changes.
    install = old / 'artifacts/install'
    if install.exists():(output / 'artifacts/install').symlink_to(install, target_is_directory=True)
    for reference in original['projects']:
        for line in Path(reference['path']).read_text().splitlines():
            if line.startswith('-I default/'):
                relative = Path('artifacts') / line.split()[1]
                target = output / relative
                if target.is_symlink() and target.resolve()==(old/relative).resolve():continue
                if target.exists() or target.is_symlink():
                    raise ValueError('A plugin mapping overlaps a selected replay object.')
                target.parent.mkdir(parents=True, exist_ok=True)
                target.symlink_to(old / relative, target_is_directory=True)
    for row in selected.values():
        read_bytes(row['object'])
        if row.get('source') is not None:read_bytes(row['source'])
    adopted={name:row['object']['path'] for name,row in selected.items()}
    for row in copied:
        if row['kind']=='object':adopted[row['module']]=row['owned']['path']
    paths={row['object']['path']:adopted[name] for name,row in selected.items()}
    actual_checks=[dict(row,owner=paths[row['owner']],object=paths[row['object']])
        for row in compared['checks']]
    actual_checks=[{key:row[key] for key in ['owner','module','object']} for row in actual_checks]
    actual=inspector(policy,list(adopted.values()),actual_checks)
    if len(actual['checks'])!=len(actual_checks) or any(row.get('compatible') is not True for row in actual['checks']):
        raise ValueError('The installed replay view has an incompatible imported object.')
    value = {'schema': 'entry-chain.exact-replay-view.v1', 'spec': spec_reference,
             'workspace': str(output), 'objects': selected, 'copies': copied,
             'import_comparison': compared, 'installed_comparison':actual, 'banks_changed': False,
             'READY_granted': False, 'proof_acceptance': False}
    save(output / 'OBJECT-VIEW.json', value)
    return binding(output / 'OBJECT-VIEW.json')


def read_bytes(reference):
    if binding(reference['path']) != {key: reference[key] for key in ['path', 'sha256']}:
        raise ValueError('A replay view input changed: ' + reference['path'])
    return Path(reference['path']).read_bytes()
