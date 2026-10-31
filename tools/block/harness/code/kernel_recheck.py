"""Prepare a recursive kernel check in the current private workspace."""
import clone_copy
import hashlib
from pathlib import Path
import shutil
import tempfile


def digest(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(chunk)
    return value.hexdigest()


def checker_arguments(flags):
    """Preserve kernel flags. Record compile-only flags separately."""
    result, omitted = [], []
    index = 0
    while index < len(flags):
        word = flags[index]
        if word in {'-Q', '-R'}:
            if index + 2 >= len(flags):
                raise ValueError('A kernel load-path mapping is incomplete.')
            result.extend(flags[index:index + 3])
            index += 3
        elif word == '-coqlib':
            if index + 1 >= len(flags):
                raise ValueError('The kernel standard-library mapping is incomplete.')
            result.extend(flags[index:index + 2])
            index += 2
        elif word in {'-boot', '-impredicative-set', '-indices-matter'}:
            result.append(word)
            index += 1
        elif word in {'-q'}:
            omitted.append([word])
            index += 1
        elif word in {'-I', '-w', '-native-compiler'}:
            if index + 1 >= len(flags):
                raise ValueError('A compile-only flag is incomplete.')
            if word == '-native-compiler' and flags[index + 1] not in {'ondemand', 'no', 'yes'}:
                raise ValueError('The native-compiler policy is unknown.')
            omitted.append(flags[index:index + 2])
            index += 2
        else:
            raise ValueError('An unmapped compiler flag prevents the kernel check: ' + word)
    if not any(word in {'-Q', '-R'} for word in result):
        raise ValueError('The kernel check has no current dependency mappings.')
    return result, omitted


def verify(cached, current, launch):
    """Use a stock admitted launch callback. Never execute a proof tactic.

    launch(argv) must retain physical limits, costs, actor closure, and claim
    release. It returns {returncode,all_owned_actors_closed,claim_released,...}.
    The caller records a false result as a cache defect before fresh execution.
    """
    installed = False
    target = None
    check_directory = None
    physical = None
    report = {'success': False, 'search_calls': 0, 'method': 'coqchk-recursive',
              'current_dependencies_used': True, 'object_reuse_authorized': False}
    try:
        result = cached['result']
        receipt = result['native_receipts']['block']
        if not result.get('success') or result.get('status') != 'passed':
            raise ValueError('The cached verdict is not closed.')
        if receipt.get('compile_file_success') is not True or receipt.get('verification_method') != 'module_m' or receipt.get('assumptions') != []:
            raise ValueError('The cached closed verdict lacks exact kernel evidence.')
        if receipt['statement_sha256'] != current['statement_sha256']:
            raise ValueError('The cached theorem statement differs from the current statement.')
        statement = hashlib.sha256(receipt['statement'].encode()).hexdigest()
        if statement != current['statement_sha256']:
            raise ValueError('The cached theorem text differs from its statement hash.')
        source, cached_source = Path(current['source']['path']), Path(receipt['source'])
        expected = current['source']['sha256']
        if receipt['source_sha256'] != expected or digest(source) != expected or digest(cached_source) != expected:
            raise ValueError('The cached source differs from the current proof source.')
        obj = Path(receipt['object'])
        if digest(obj) != receipt['object_sha256']:
            raise ValueError('The cached object changed.')
        workspace = Path(current['workspace']).resolve()
        parent_namespace=current['module'].rsplit('.',1)[0]
        if parent_namespace==current['module'] or any(name.startswith(parent_namespace+'.') and name!=current['module'] for name in current['dependency_modules']):
            raise ValueError('The target-only kernel mapping would affect another dependency.')
        check_directory=Path(tempfile.mkdtemp(prefix='.cached-kernel-',dir=workspace))
        target = check_directory / source.with_suffix('.vo').name
        if not source.resolve().is_relative_to(workspace) or not target.resolve().is_relative_to(workspace):
            raise ValueError('The kernel-check object leaves the private workspace.')
        checker = Path(current['checker']['path'])
        if digest(checker) != current['checker']['sha256']:
            raise ValueError('The pinned kernel checker changed.')
        mappings, omitted = checker_arguments(current['physical_flags'])
        dependency_mappings=list(mappings)
        mappings.extend(['-Q',str(check_directory),parent_namespace])
        clone_copy.copy2(obj, target)
        installed = True
        if digest(target) != receipt['object_sha256'] or (target.stat().st_dev, target.stat().st_ino) == (obj.stat().st_dev, obj.stat().st_ino):
            raise ValueError('The cached object copy differs or shares its source inode.')
        candidates = []
        for index, word in enumerate(mappings):
            if word in {'-Q', '-R'}:
                root, prefix = Path(mappings[index + 1]), mappings[index + 2]
                if current['module'].startswith(prefix + '.'):
                    path = root / Path(*current['module'][len(prefix) + 1:].split('.'))
                    path = path.with_suffix('.vo')
                    if path.is_file():
                        candidates.append((len(prefix.split('.')),path.resolve()))
        longest=max((length for length,_ in candidates),default=-1)
        if {path for length,path in candidates if length==longest} != {target.resolve()}:
            raise ValueError('The cached module has an ambiguous or different current object mapping.')
        argv = [str(checker), '-silent', *mappings, current['module']]
        physical = launch(argv)
        report.update(command=argv, unchanged_dependency_mappings=dependency_mappings, target_only_mapping=['-Q',str(check_directory),parent_namespace], compile_only_flags_omitted=omitted, physical_receipt=physical,
                      cached_object_sha256=receipt['object_sha256'], statement_sha256=statement)
        if physical['returncode'] != 0:
            raise ValueError('The current kernel check refused the cached object.')
        if not physical['all_owned_actors_closed'] or not physical['claim_released']:
            raise ValueError('The kernel-check actors or claim remain open.')
        if physical.get('CPU') is None or 'claim_key' not in physical or 'released_bytes' not in physical:
            raise ValueError('The kernel-check costs or release receipt are missing.')
        report.update(success=True, method='coqchk', checked_key=cached['key'],
                      recursive=True, admitted_modules=[])
    except (ValueError, OSError, KeyError) as error:
        report['defect'] = str(error)
    finally:
        # A check never installs a proof object for a later consumer. The
        # immutable cached artifact remains available with its evidence.
        if check_directory is not None:
            if physical is not None and not physical.get('all_owned_actors_closed'):
                report['retained_kernel_directory']=str(check_directory)
            else:
                shutil.rmtree(check_directory)
    return report
