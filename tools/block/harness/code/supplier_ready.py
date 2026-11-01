"""Check published supplier data against the existing closed declaration run."""
from pathlib import Path
import hashlib
import json
from collections import OrderedDict
from contextvars import ContextVar
from copy import deepcopy
import os
import stat
import threading

from binding_cache import identity, _FORCE

_TRACKER = ContextVar("supplier_validation_files", default=None)
_MEMO = OrderedDict()
_MEMO_PID = os.getpid()
_MEMO_LOCK = threading.RLock()
_MEMO_LIMIT = 4


def _file_identity(path, namespace=False):
    try:
        value = identity(path)
        # Ancestor directories need identity checks, not content-list checks.
        if namespace and stat.S_ISDIR(value[0][-1]):
            value = tuple((row[0], row[1], row[-1]) for row in value)
        if stat.S_ISLNK(path.lstat().st_mode):
            return value, str(path.resolve())
        return value
    except FileNotFoundError:
        return None


class _ConsultedFiles:
    def __init__(self):
        self.rows = {}
        self.stable = True

    def note(self, path, namespace=False):
        path = Path(path).absolute()
        key = (str(path), namespace)
        if key not in self.rows:
            self.rows[key] = _file_identity(path, namespace)

    def path(self, path, *, contents=True):
        path = Path(path).absolute()
        for parent in path.parents:
            self.note(parent, namespace=True)
        if contents or path.is_symlink():
            self.note(path)
        if not contents:
            # Adding a previously absent binding can change index resolution.
            self.note(path.parent)

    def unchanged(self):
        return self.stable and all(_file_identity(Path(path), namespace) == value
                                   for (path, namespace), value in self.rows.items())


def _observe(path, *, contents=True):
    tracker = _TRACKER.get()
    if tracker is not None:
        tracker.path(path, contents=contents)


def _resolved(path):
    path = Path(path)
    _observe(path, contents=False)
    return path.resolve()


def validate(binding):
    """Reuse successful validation only while every consulted identity is exact."""
    global _MEMO_PID, _MEMO_LOCK
    if _MEMO_PID != os.getpid():
        # A child must not acquire an inherited lock or reuse a parent entry.
        _MEMO.clear()
        _MEMO_LOCK = threading.RLock()
        _MEMO_PID = os.getpid()
    require(isinstance(binding, dict) and set(binding) == {"path", "sha256"},
            "binding is invalid")
    key = (binding["path"], binding["sha256"], os.getcwd())
    with _MEMO_LOCK:
        cached = _MEMO.pop(key, None)
        if cached is not None and not _FORCE.get():
            tracker, value = cached
            if tracker.unchanged():
                result = deepcopy(value)
                if tracker.unchanged():
                    _MEMO[key] = cached
                    return result
        tracker = _ConsultedFiles()
        token = _TRACKER.set(tracker)
        try:
            result = _validate(binding)
        finally:
            _TRACKER.reset(token)
        if tracker.unchanged():
            _MEMO[key] = (tracker, deepcopy(result))
            while len(_MEMO) > _MEMO_LIMIT:
                _MEMO.popitem(last=False)
        return result

ROOTS = frozenset({'ZesuSsz.Automation.All', 'ZesuSsz.Automation.Hooks',
                   'ZesuSsz.Automation.Finish'})
FIELDS = frozenset({'ready', 'source_packet', 'modules', 'import_graph',
                    'expected_mcp_flags', 'physical_flags', 'effective_compiler_version',
                    'verification', 'calls', 'result', 'runtime', 'closure', 'release'})


def require(condition, message):
    if not condition:
        raise ValueError('The PORT supplier ' + message + '.')


def bound(row):
    require(isinstance(row, dict) and set(row) == {'path', 'sha256'}, 'binding is invalid')
    path = Path(row['path'])
    _observe(path)
    before = identity(path) if path.is_file() else None
    require(path.is_absolute() and path.is_file(), 'input is absent')
    require(hashlib.sha256(path.read_bytes()).hexdigest() == row['sha256'],
            'input changed: ' + str(path))
    require(identity(path) == before, 'input changed during validation: ' + str(path))
    _observe(path)
    return path


def read(row):
    path = bound(row)
    before = identity(path)
    value = json.loads(path.read_text())
    require(identity(path) == before, 'input changed during reading: ' + str(path))
    _observe(path)
    return value


def closure(graph):
    edges = graph['import_edges']
    require(isinstance(edges, list) and all(isinstance(row, dict) and
            set(row) == {'from', 'to'} and all(isinstance(value, str) for value in row.values())
            for row in edges), 'import graph is invalid')
    adjacent = {}
    for row in edges:
        adjacent.setdefault(row['from'], set()).add(row['to'])
    seen, pending = set(), list(ROOTS)
    while pending:
        name = pending.pop()
        if name not in seen:
            seen.add(name)
            pending.extend(adjacent.get(name, ()))
    return seen, {(row['from'], row['to']) for row in edges if row['from'] in seen}


def owned(workspace, relative):
    path = _resolved(workspace / relative)
    require(path.is_relative_to(_resolved(workspace)), 'module leaves its owned workspace')
    return path


def installation(index, compiler, physical_flags, supplier=None):
    """Use the existing resolver inventory and its bound executable identity."""
    from installed_mappings import InstalledMappings
    tool = Path(compiler['compiler']['path']).parent / 'coqdep'
    row = index.get(str(_resolved(tool)))
    require(row is not None, 'installation resolver lacks its binding')
    bound(row)
    for index, word in enumerate(physical_flags[:-1]):
        if word in {'-Q', '-R', '-I', '-coqlib'}:
            _observe(Path(physical_flags[index + 1]))
    selected = InstalledMappings(physical_flags, coqdep=tool, supplier=supplier)
    for root in selected.roots:
        path = Path(root['root'])
        _observe(path)
        for directory in path.rglob('*'):
            if directory.is_dir():
                _observe(directory)
    for entry in selected.entries:
        _observe(entry['source'])
        _observe(entry['object'])
    require(selected.tool_sha256 == row['sha256'], 'installation resolver changed')
    return selected, row


def installed_module(module, relative, installed):
    from seed_bindings import installation_path
    path = Path(relative)
    require(path.is_absolute() and '..' not in path.parts and
            installation_path(path) and installation_path(path.with_suffix('.vo')),
            'external module is outside the installed roots')
    resolved = installed.resolution(module)
    require(resolved['source'] == path and resolved['object'] == path.with_suffix('.vo'),
            'installed module mapping differs: ' + module)
    mappings = [entry['mapping'] for entry in installed.entries
                if entry['canonical'] == resolved['canonical'] and
                entry['source'] == resolved['source'] and entry['object'] == resolved['object']]
    require(mappings, 'resolved installation mapping is absent: ' + module)
    return dict(canonical=resolved['canonical'], source=str(path),
                object=str(path.with_suffix('.vo')), mappings=mappings)


def response(call):
    from verification_supplement import response as checked_response
    return checked_response(call)


def _validate(binding):
    packet = read(binding)
    require(isinstance(packet, dict) and FIELDS <= set(packet) and
            set(packet) - FIELDS <= {'hooks_compile', 'installation_qualification'},
            'manifest fields differ')
    if 'installation_qualification' in packet:
        require(packet['installation_qualification'] == 'publication_time_identity_only',
                'installation qualification differs')
    evidence = [binding]

    def load(row):
        value = read(row)
        evidence.append(row)
        return value

    ready = load(packet['ready'])
    require(Path(packet['ready']['path']).name == 'READY-RUNTIME.json', 'runtime is not READY')
    require(ready.get('declarations_only') is True and ready.get('control_session') is None,
            'run is not declaration-only')
    jobs = ready.get('jobs', [])
    prerequisites = [job for job in jobs if job.get('phase') == 'prerequisites']
    require(len(prerequisites) == 1, 'run lacks one prerequisite job')
    job = prerequisites[0]
    ordered = job.get('ordered_modules')
    require(isinstance(ordered, list) and len(ordered) == len(set(ordered)) and ordered,
            'compile order is invalid')
    output = Path(job['output'])
    workspace = Path(ready['prepared_workspace'])
    mapping = ready['proof_runtime']['module_files']
    readiness = load(ready['readiness'])
    require(readiness.get('schema') == 'entry-chain.prerequisite-readiness.v1' and
            readiness.get('all_required_compiles_passed') is True,
            'readiness is incomplete')
    require(Path(readiness['prerequisite_result']['path']) == output / 'RESULT.json',
            'readiness names another job')
    result = load(readiness['prerequisite_result'])
    require(result.get('success') is True and result.get('status') == 'passed' and
            result.get('returncode') == 0 and not any(result.get(key) for key in
            ['resource_reason', 'shared_infrastructure_failure', 'observer_failure']),
            'declaration job did not pass')
    outer = load(packet['result'])
    require(Path(packet['result']['path']).parent == Path(packet['ready']['path']).parent and
            outer.get('prerequisites') == readiness['prerequisite_result'] and
            outer.get('success') is True and outer.get('status') == 'declarations_passed' and
            outer.get('native_calls') == 0, 'outer result differs or is incomplete')

    for field, relative in [('runtime', 'RUNTIME.json'), ('calls', 'native/CALLS.json'),
                            ('verification', 'native/CONTROL-VERIFICATION.json'),
                            ('closure', 'CLOSURE.json'), ('release', 'RELEASE.json')]:
        require(Path(packet[field]['path']) == output / relative,
                field + ' names another job')
    calls = load(packet['calls'])
    require(isinstance(calls, list) and len(calls) >= 2 and
            calls[0].get('tool') == calls[-1].get('tool') == 'rocq_health',
            'health boundaries are absent')
    require(all(call.get('tool') in {'rocq_health', 'rocq_compile_file', 'rocq_verify'}
                for call in calls), 'declaration run contains another proof operation')
    require(sum(call.get('tool') == 'rocq_compile_file' for call in calls) ==
            len(ordered) - int('hooks_compile' in packet),
            'compile call count differs')
    for call in [calls[0], calls[-1]]:
        health = response(call)
        require(health.get('success') is True and health.get('ok') is True,
                'health check failed')
    checks = ready.get('declaration_checks')
    verified = load(packet['verification'])
    require(isinstance(checks, list) and checks and isinstance(verified, list) and
            len(verified) == len(checks) and outer.get('exact_statement_checks') == packet['verification']
            and outer.get('exact_statement_check_count') == len(checks),
            'verification is unfinished')
    verification_calls = [call for call in calls if call.get('tool') == 'rocq_verify']
    require(len(verification_calls) == len(checks), 'verification call count differs')
    for specification, receipt, call in zip(checks, verified, verification_calls):
        arguments = dict(call['arguments'])
        require(isinstance(arguments.pop('workspace', None), str) and
                type(arguments.pop('timeout', None)) is int, 'verification transport is invalid')
        value = response(call)
        require(arguments == specification == receipt.get('specification') and
                value == receipt.get('result') and value.get('success') is True and
                value.get('verification_method') == 'module_m' and value.get('assumptions') == [],
                'exact verification differs or failed')
    closed, released = load(packet['closure']), load(packet['release'])
    require(closed.get('all_owned_actors_closed') is True and closed.get('actors') and
            all(actor.get('ended') is True for actor in closed['actors']) and
            released.get('released') is True and released.get('bytes') == job.get('claim_bytes') and
            released.get('bytes', 0) > 0 and closed.get('claim_key') == released.get('claim_key'),
            'closure or claim release is incomplete')

    require(packet['import_graph'] == ready.get('cache_import_graph'), 'graph binding differs')
    graph = load(packet['import_graph'])
    names, edges = closure(graph)
    require(ROOTS <= set(ordered) | {row['module'] for row in packet['modules']},
            'root module is absent')
    for field in ['expected_mcp_flags', 'physical_flags', 'effective_compiler_version']:
        require(packet[field] == ready.get(field), field + ' differs')
    runtime = load(packet['runtime'])
    require(runtime.get('phase') == 'prerequisites' and runtime.get('job_output') == str(output)
            and runtime.get('ordered_modules') == ordered and
            runtime.get('declaration_checks') == checks,
            'actual prerequisite runtime differs')
    inner_workspace = Path(runtime.get('prepared_workspace', output / 'workspace'))
    for field in ['expected_mcp_flags', 'physical_flags']:
        require(flags(runtime[field], inner_workspace) == flags(packet[field], workspace),
                'actual compiler flags differ')
    compiler = packet['effective_compiler_version']
    require(isinstance(compiler.get('text'), str) and compiler['text'], 'compiler version is absent')
    require(all(response(call).get('toolchain', {}).get('coqc', {}).get('version') == compiler['text']
                for call in [calls[0], calls[-1]]), 'health compiler version differs')
    for field in ['compiler', 'evidence']:
        bound(compiler[field])
        evidence.append(compiler[field])

    index = {}
    for row in ready['bindings']:
        key = str(_resolved(row['path']))
        require(key not in index or index[key]['sha256'] == row['sha256'],
                'runtime repeats conflicting bindings')
        index[key] = {'path': row['path'], 'sha256': row['sha256']}
    for row in readiness['objects']:
        bound(row)
        index[str(_resolved(row['path']))] = row
    libraries = [row for row in index.values()
                 if Path(row['path']).suffix in {'.cmxs', '.cma', '.cmxa', '.so'}]
    for row in libraries:
        bound(row)
        evidence.append(row)
    declared = packet['modules']
    require(isinstance(declared, list) and len({row['module'] for row in declared}) == len(declared),
            'module inventory repeats')
    selected = {row['module']: row for row in declared}
    require(ROOTS <= set(selected) and set(selected) <= set(mapping), 'root inventory differs')
    modules = []
    installed = None
    resolver = None
    fallback_used = False
    publication_only_installed = []
    for name in sorted(names | set(selected) | set(ordered)):
        require(name in mapping, 'dependency lacks a module mapping: ' + name)
        original = Path(mapping[name])
        source = _resolved(workspace / original)
        external = not source.is_relative_to(_resolved(workspace))
        if external:
            require(name not in ROOTS and name not in ordered, 'production root or compile leaves its owned workspace')
            if installed is None:
                installed, resolver = installation(index, compiler, packet['physical_flags'], binding)
                evidence.append(resolver)
            physical_mapping = installed_module(name, original, installed)
            source = original
        else:
            source = owned(workspace, mapping[name])
        pair = {}
        for kind, path in [('source', source), ('object', source.with_suffix('.vo'))]:
            row = index.get(str(path))
            if row is None and external:
                require(packet.get('installation_qualification') == 'publication_time_identity_only',
                        'new installed capture lacks its publication-time qualification')
                require(name in selected and kind in selected[name] and
                        selected[name][kind].get('path') == str(path),
                        'new installed capture lacks its exact manifest row: ' + name)
                row = selected[name][kind]
                publication_only_installed.append((name, kind))
            require(row is not None, 'dependency lacks a bound ' + kind + ': ' + name)
            bound(row)
            evidence.append(row)
            pair[kind] = row
        if name in selected:
            require(all(selected[name][kind] == pair[kind] for kind in pair),
                    'published module differs: ' + name)
        if name in ordered:
            receipt_path = output / 'native' / ('dependency-' + name + '.json')
            row = {'path': str(receipt_path),
                   'sha256': hashlib.sha256(receipt_path.read_bytes()).hexdigest()}
            receipt = load(row)
            require(receipt.get('result', {}).get('success') is True and
                    all(receipt[kind + '_sha256'] == pair[kind]['sha256'] for kind in pair),
                    'compile receipt differs: ' + name)
            matching = [call for call in calls if call.get('tool') == 'rocq_compile_file' and
                        call.get('arguments', {}).get('file') == receipt.get('source')]
            require(Path(receipt['object']) == Path(receipt['source']).with_suffix('.vo'),
                    'compile object path differs: ' + name)
            if len(matching) == 1:
                require(response(matching[0]) == receipt['result'], 'compile call differs: ' + name)
            else:
                require(not matching and name == 'ZesuSsz.Automation.Hooks' and
                        'hooks_compile' in packet, 'compile call differs: ' + name)
                require(Path(packet['hooks_compile']['path']) == output / 'native/HOOKS-COMPILE.json',
                        'Hooks fallback leaves its exact job')
                fallback = load(packet['hooks_compile'])
                wrapper = owned(inner_workspace, runtime['coqc_wrapper'])
                inner_bindings = {str(_resolved(row['path'])): row for row in runtime['bindings']}
                wrapper_row = inner_bindings.get(str(wrapper))
                prepared_wrapper = index.get(str(owned(workspace, runtime['coqc_wrapper'])))
                require(wrapper_row is not None and prepared_wrapper is not None and
                        wrapper_row['sha256'] == prepared_wrapper['sha256'],
                        'Hooks wrapper lacks its exact tool binding')
                bound(wrapper_row)
                evidence.append(wrapper_row)
                declarations = [line.strip() for line in source.read_text().splitlines()
                                if line.strip().startswith('Declare ML Module')]
                require(declarations == ['Declare ML Module "zesu-signature-gates.plugin".'] and
                        fallback == receipt['result'] and fallback.get('success') is True and
                        fallback.get('returncode') == 0 and
                        fallback.get('method') == 'stock-guarded-dependency-build' and
                        fallback.get('MCP_refusal') == 'Forbidden command Declare ML Module' and
                        fallback.get('source') == {'path': receipt['source'], 'sha256': pair['source']['sha256']} and
                        fallback.get('argv') == [str(wrapper), *runtime['expected_mcp_flags'], receipt['source']],
                        'Hooks fallback differs from its existing guarded build')
                for stream in ['stdout', 'stderr']:
                    require(Path(fallback[stream]['path']) == output / 'native' / ('HOOKS-COMPILE.' + stream),
                            'Hooks output leaves its exact job')
                    bound(fallback[stream])
                    evidence.append(fallback[stream])
                fallback_used = True
        modules.append(dict(module=name, installed_mapping=physical_mapping if external else None,
                            **pair))
    source_packet = load(packet['source_packet'])
    sources = source_packet.get('all_sources')
    require(isinstance(sources, list) and ROOTS <= {row['module'] for row in sources},
            'source packet omits a root')
    by_module = {row['module']: row for row in modules}
    for row in sources:
        bound({'path': row['path'], 'sha256': row['sha256']})
        require(row['module'] in by_module and
                row['sha256'] == by_module[row['module']]['source']['sha256'],
                'source packet differs from the compiled source')
        evidence.append({'path': row['path'], 'sha256': row['sha256']})
    require(fallback_used == ('hooks_compile' in packet), 'Hooks fallback was not consumed')
    return dict(packet=packet, ready=ready, modules=modules, names=names, edges=edges,
                libraries=libraries, installation_resolver=resolver,
                publication_only_installed=publication_only_installed, bindings=evidence)


def flags(words, workspace):
    prefix = str(Path(workspace).resolve())
    return ['{workspace}' + word[len(prefix):]
            if word == prefix or word.startswith(prefix + '/') else word for word in words]


def staged(supplier, config):
    """Require the exact compiled closure, with owned-path relocation only."""
    packet = supplier['packet']
    root = Path(config['prepared_workspace'])
    flag_root = config.get('supplier_flag_workspace', root)
    for field in ['expected_mcp_flags', 'physical_flags']:
        require(flags(config[field], flag_root) ==
                flags(packet[field], supplier['ready']['prepared_workspace']),
                'staged ' + field + ' differs')
    require(config['effective_compiler_version'] == packet['effective_compiler_version'],
            'staged compiler differs')
    graph = read(config['cache_import_graph'])
    names, edges = closure(graph)
    require(names == supplier['names'] and edges == supplier['edges'], 'staged import closure differs')
    mapping = config['proof_runtime']['module_files']
    installed = None
    supplier_root = Path(supplier['ready']['prepared_workspace']).resolve()
    for row in supplier['libraries']:
        original = _resolved(row['path'])
        path = Path(flag_root) / original.relative_to(supplier_root) if original.is_relative_to(supplier_root) else original
        bound({'path': str(path), 'sha256': row['sha256']})
    sources = []
    for row in supplier['modules']:
        if row['module'] not in supplier['names']:
            continue
        require(row['module'] in mapping, 'staged dependency mapping is absent')
        if row['installed_mapping'] is not None:
            require(mapping[row['module']] == supplier['ready']['proof_runtime']['module_files'][row['module']],
                    'staged installed source path differs')
            if installed is None:
                from installed_mappings import InstalledMappings
                resolver = supplier['installation_resolver']
                bound(resolver)
                installed = InstalledMappings(config['physical_flags'], coqdep=resolver['path'],
                                              supplier=supplier['bindings'][0])
                require(installed.tool_sha256 == resolver['sha256'], 'staged installation resolver differs')
            actual_mapping = installed_module(row['module'], mapping[row['module']], installed)
            require(actual_mapping == row['installed_mapping'], 'staged installation identity differs')
            source = Path(mapping[row['module']])
        else:
            source = root / mapping[row['module']]
        for kind, path in [('source', source), ('object', source.with_suffix('.vo'))]:
            bound({'path': str(path), 'sha256': row[kind]['sha256']})
        sources.append(dict(module=row['module'], path=str(source), sha256=row['source']['sha256']))
    return sources
