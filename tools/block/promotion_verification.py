"""Compile every generated module and check its exact exported statements."""
import argparse
import asyncio
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from successor_entailment import _result
from function_names import FunctionNames

HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def launcher_bindings(workspace, mcp_launcher=None, compiler_launcher=None):
    """Bind explicit executable paths without replacing virtual-environment paths."""
    selected = {
        'mcp': mcp_launcher if mcp_launcher is not None else Path(workspace) / 'tools/rocq_mcp_guarded.sh',
        'compiler': compiler_launcher if compiler_launcher is not None else Path(workspace) / 'tools/rocq_coqc_guarded.sh',
    }
    result = {}
    for label, value in selected.items():
        path = Path(value).absolute()
        if not path.is_file() or not os.access(path, os.X_OK):
            raise ValueError('The selected ' + label + ' launcher is missing or not executable: ' + str(path))
        result[label] = dict(path=str(path), resolved_path=str(path.resolve()), sha256=digest(path))
    return result


def unchanged_launchers(bindings):
    for label, record in bindings.items():
        path = Path(record['path'])
        if (not path.is_file() or not os.access(path, os.X_OK) or
                str(path.resolve()) != record['resolved_path'] or digest(path) != record['sha256']):
            raise ValueError('The selected ' + label + ' launcher changed during verification.')


def prepare_protected_expectations(workspace, sources, records):
    """Bind literal baseline expectations before starting any transport."""
    workspace = Path(workspace).resolve()
    if records is None:
        return {}
    if not isinstance(records, list) or not records:
        raise ValueError('Protected expectations must be a nonempty list.')
    required = {'candidate_source', 'candidate_source_sha256', 'name',
                'baseline_workspace', 'baseline_commit', 'baseline_build_dir',
                'baseline_source', 'baseline_source_sha256',
                'baseline_object', 'baseline_object_sha256',
                'statement', 'statement_sha256'}
    selected = {Path(source).resolve() for source in sources}
    result = {}
    for row in records:
        if (not isinstance(row, dict) or set(row) != required or
                any(not isinstance(value, str) or not value for value in row.values())):
            raise ValueError('A protected expectation has missing or invalid fields.')
        if any(not Path(row[name]).is_absolute() for name in ('candidate_source', 'baseline_workspace',
                   'baseline_build_dir', 'baseline_source', 'baseline_object')):
            raise ValueError('Protected expectation paths must be absolute.')
        candidate = Path(row['candidate_source']).resolve(strict=True)
        if candidate not in selected or not candidate.is_relative_to(workspace):
            raise ValueError('A protected expectation names an unused candidate source.')
        key = (str(candidate), row['name'])
        if key in result:
            raise ValueError('The protected expectations repeat a source and name.')
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", row['name']):
            raise ValueError('A protected expectation needs an exact declaration name.')
        for name in ('candidate_source_sha256', 'baseline_source_sha256',
                     'baseline_object_sha256', 'statement_sha256'):
            if not re.fullmatch(r'[0-9a-f]{64}', row[name]):
                raise ValueError('A protected expectation needs exact SHA256 values.')
        if not re.fullmatch(r'[0-9a-f]{40}', row['baseline_commit']):
            raise ValueError('A protected expectation needs an exact baseline commit.')
        baseline = Path(row['baseline_workspace']).resolve(strict=True)
        source = Path(row['baseline_source']).resolve(strict=True)
        build = Path(row['baseline_build_dir']).resolve(strict=True)
        artifact = Path(row['baseline_object']).resolve(strict=True)
        if (not source.is_relative_to(baseline) or not build.is_relative_to(baseline) or
                source.suffix != '.v' or artifact.suffix != '.vo'):
            raise ValueError('A protected expectation leaves its baseline workspace.')
        relative = candidate.relative_to(workspace)
        if source.relative_to(baseline) != relative or artifact != build / 'default' / relative.with_suffix('.vo'):
            raise ValueError('A protected baseline source/object mapping differs.')
        head = subprocess.check_output(['git', '-C', str(baseline), 'rev-parse', 'HEAD'], text=True).strip()
        if head != row['baseline_commit']:
            raise ValueError('The protected baseline commit differs.')
        committed = subprocess.check_output(['git', '-C', str(baseline), 'show', head + ':' + relative.as_posix()])
        copied = build / 'default' / relative
        if not copied.resolve().is_relative_to(baseline):
            raise ValueError('A protected baseline source copy leaves its workspace.')
        if (hashlib.sha256(committed).hexdigest() != row['baseline_source_sha256'] or
                digest(source) != row['baseline_source_sha256'] or
                not copied.is_file() or digest(copied) != row['baseline_source_sha256'] or
                digest(artifact) != row['baseline_object_sha256'] or
                digest(candidate) != row['candidate_source_sha256']):
            raise ValueError('A protected source or object differs from its binding.')
        # Source mode supports literal global declarations. A Section needs a
        # separately retained baseline kernel type, never a candidate type query.
        matches = [statement for name, statement, _ in statements(committed.decode(), 0)
                   if name == row['name']]
        if len(matches) != 1 or matches[0] != row['statement']:
            raise ValueError('The protected statement differs from its baseline source.')
        if hashlib.sha256(row['statement'].encode()).hexdigest() != row['statement_sha256']:
            raise ValueError('The protected statement hash differs.')
        candidate_names = [name for name, _, _ in statements(candidate.read_text(), 0,
                           '.'.join(relative.with_suffix('').parts))]
        if candidate_names.count(row['name']) != 1:
            raise ValueError('A protected expectation names an unused declaration.')
        result[key] = {**row, 'baseline_workspace': str(baseline),
                       'baseline_source': str(source), 'baseline_object': str(artifact),
                       'baseline_source_copy': str(copied), 'candidate_source': str(candidate),
                       'origin': 'literal baseline source'}
    return result


def unchanged_protected_expectations(records):
    for row in records.values():
        head = subprocess.check_output(['git', '-C', row['baseline_workspace'],
                                        'rev-parse', 'HEAD'], text=True).strip()
        if head != row['baseline_commit']:
            raise ValueError('The protected baseline commit changed during verification.')
        for path, expected in ((row['candidate_source'], row['candidate_source_sha256']),
                               (row['baseline_source'], row['baseline_source_sha256']),
                               (row['baseline_source_copy'], row['baseline_source_sha256']),
                               (row['baseline_object'], row['baseline_object_sha256'])):
            if digest(path) != expected:
                raise ValueError('A protected expectation input changed during verification.')


def prepare_verification_imports(workspace, protected, records):
    """Adapt explicit imports without changing a protected declaration or its hash."""
    if records is None:
        return {}
    if not isinstance(records, list) or not records:
        raise ValueError('Verification imports must be a nonempty list.')
    workspace = Path(workspace).resolve()
    required = {'candidate_source', 'name', 'statement_sha256',
                'verification_statement_sha256', 'imports'}
    result = {}
    module_pattern = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+"
    for row in records:
        if not isinstance(row, dict) or set(row) != required:
            raise ValueError('A verification-import adapter has missing or invalid fields.')
        if not isinstance(row['candidate_source'], str) or not Path(row['candidate_source']).is_absolute():
            raise ValueError('A verification-import adapter needs an absolute candidate source.')
        key = (str(Path(row['candidate_source']).resolve()), row['name'])
        if key not in protected:
            raise ValueError('A verification-import adapter names an unused expectation.')
        if key in result:
            raise ValueError('The verification-import adapters repeat an expectation.')
        expected = protected[key]
        if row['statement_sha256'] != expected['statement_sha256']:
            raise ValueError('A verification-import adapter changes its baseline statement binding.')
        if not isinstance(row['imports'], list) or not row['imports']:
            raise ValueError('A verification-import adapter needs explicit imports.')
        statement = expected['statement']
        # Only import commands before the selected declaration can change.
        declaration = re.search(r'^Lemma\s+' + re.escape(row['name']) + r'\b', statement, re.M)
        if declaration is None:
            raise ValueError('A verification-import adapter has no literal declaration.')
        prefix, declaration_text = statement[:declaration.start()], statement[declaration.start():]
        seen = set()
        for item in row['imports']:
            if not isinstance(item, dict) or set(item) != {'old_module', 'new_module', 'source_sha256'}:
                raise ValueError('A verification import has missing or invalid fields.')
            old, new = item['old_module'], item['new_module']
            if (not isinstance(old, str) or not isinstance(new, str) or
                    not re.fullmatch(module_pattern, old) or not re.fullmatch(module_pattern, new) or old == new):
                raise ValueError('A verification adapter may replace only a qualified import.')
            if old in seen:
                raise ValueError('A verification-import adapter repeats an import.')
            seen.add(old)
            before, after = 'Require Import ' + old + '.\n', 'Require Import ' + new + '.\n'
            pattern = r'^' + re.escape(before)
            if len(re.findall(pattern, prefix, re.M)) != 1:
                raise ValueError('A verification import is missing, ambiguous, or unused.')
            source = workspace / (new.replace('.', '/') + '.v')
            if (not source.is_file() or not source.resolve().is_relative_to(workspace) or
                    digest(source) != item['source_sha256']):
                raise ValueError('A verification-import source differs from its binding.')
            prefix = re.sub(pattern, lambda _: after, prefix, count=1, flags=re.M)
        adapted = prefix + declaration_text
        if hashlib.sha256(adapted.encode()).hexdigest() != row['verification_statement_sha256']:
            raise ValueError('The verification statement hash differs.')
        result[key] = {**row, 'candidate_source': key[0], 'verification_statement': adapted}
    return result


def unchanged_verification_imports(workspace, records):
    for row in records.values():
        for item in row['imports']:
            source = Path(workspace) / (item['new_module'].replace('.', '/') + '.v')
            if (not source.is_file() or not source.resolve().is_relative_to(Path(workspace).resolve()) or
                    digest(source) != item['source_sha256']):
                raise ValueError('A verification-import source changed during verification.')


def retained_compile_result(source, artifact, retained):
    if (retained['source'] != str(source) or
            Path(retained['private_artifact']).resolve() != artifact.resolve() or
            retained['source_sha256'] != digest(source) or
            retained['compile_file'].get('success') is not True or
            digest(artifact) != retained['private_artifact_sha256']):
        raise ValueError('The retained compilation identity differs.')
    return retained['compile_file']


def compilation_sources(workspace, sources):
    """Refresh project prerequisites that import a changed generated module."""
    workspace = Path(workspace).resolve()
    changed = {Path(source).resolve() for source in sources}
    dependencies = {}

    def inspect(source):
        if source in dependencies:
            return
        dependencies[source] = []
        for imports in re.findall(r'^Require Import\s+([^\n]+)\.', source.read_text(), re.M):
            for module in imports.split():
                dependency = workspace / (module.replace('.', '/') + '.v')
                if dependency.is_file():
                    dependencies[source].append(dependency)
                    inspect(dependency)

    for source in sources:
        inspect(Path(source).resolve())
    affected, visiting = {}, set()

    def needs_refresh(source):
        if source in affected:
            return affected[source]
        if source in visiting:
            raise ValueError('The project import graph contains a cycle.')
        visiting.add(source)
        results = [needs_refresh(dependency) for dependency in dependencies[source]]
        visiting.remove(source)
        affected[source] = source in changed or any(results)
        return affected[source]

    for source in dependencies:
        needs_refresh(source)
    ordered, emitted = [], set()

    def emit(source):
        if source in emitted:
            return
        for dependency in dependencies[source]:
            emit(dependency)
        emitted.add(source)
        if affected[source]:
            ordered.append(source)

    for source in sources:
        emit(Path(source).resolve())
    return ordered


def restated_statement(source, match, end, module=None):
    """Use the compiled constant's kernel type outside an active Section."""
    sections = []
    for command in re.finditer(r'^(Section|End)\s+([A-Za-z_][A-Za-z0-9_\']*)\.',
                               source[:match.start()], re.M):
        if command[1] == 'Section':
            sections.append(command[2])
        elif sections and sections[-1] == command[2]:
            sections.pop()
    if not sections:
        return source[:end]
    if module is None or not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_\']*(?:\.[A-Za-z_][A-Za-z0-9_\']*)*', module):
        raise ValueError('A Section statement needs its compiled logical module.')
    return (f'Require Import {module}.\n'
            f'Lemma {match[1]} :\n'
            f'  ltac:(let statement := type of @{module}.{match[1]} in exact statement).\n')


def statements(source, pc, module=None, *, name_prefix="decodeItem"):
    """Retain exact declarations, including earlier definitions and scopes."""
    result = []
    for match in re.finditer(r'^Lemma\s+([A-Za-z_][A-Za-z0-9_\']*)\b', source, re.M):
        opening = re.search(r'\bProof(?:\s+using\b[^.]*?)?\s*\.', source[match.end():])
        if opening is None:
            raise ValueError('The named lemma has no supported proof opening: ' + match[1])
        end = match.end() + opening.start()
        statement = restated_statement(source, match, end, module)
        proof = source
        if statement != source[:end]:
            # The verifier bridge uses the constant without an explicit @.
            proof += f'\nArguments {match[1]} : clear implicits.\n'
        result.append((match[1], statement, proof))
    # PromotedBodies exports typed definitions inside an Iris section.
    name = f'{FunctionNames(name_prefix).prefix}PromotedBody{pc:x}'
    match = re.search(r'Definition ' + name + r'\s*:\s*(.*?)\s*:=', source, re.S)
    if match:
        imports = source.split('Section promoted_block_bodies.', 1)[0]
        declaration = f'Lemma promotion_{pc:x} `{{!islaG Sigma}} `{{!threadG}} :\n  {match[1]}.\n'
        proof = source + '\n' + declaration + f'Proof. exact {name}. Qed.\n'
        result.append((f'promotion_{pc:x}', imports + declaration, proof))
    if not result and not assumption_audit_only(source):
        raise ValueError('The generated module has no supported statement check.')
    return result


def assumption_audit_only(source):
    """Audit leaves compile queries, but declare no proposition to verify."""
    from check_data_only_lemmas import rocq_commands
    identifier = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+"
    imports, queries = set(), set()
    for command in rocq_commands(source):
        values = [token for token, _ in command]
        if (values[:2] == ['Require', 'Import'] and len(values) > 2 and
                all(re.fullmatch(identifier, name) for name in values[2:])):
            imports.update(values[2:])
            continue
        if (values[:2] == ['Print', 'Assumptions'] and len(values) == 3 and
                re.fullmatch(identifier, values[2])):
            target = values[2]
            if target in queries or target.rsplit('.', 1)[0] not in imports:
                return False
            queries.add(target)
            continue
        return False
    return bool(queries)


def source_artifacts(source):
    source = Path(source)
    return [source.with_suffix(s) for s in ('.vo', '.vos', '.vok', '.glob')] + [
        source.with_name('.' + source.stem + '.aux')]


def require_clean_source(source):
    present = [str(p) for p in source_artifacts(source) if p.exists()]
    if present:
        raise ValueError('Compiler artifacts exist in the source tree: ' + repr(present))


def live(identity):
    if not identity:
        return False
    try:
        fields = (Path('/proc') / str(identity['pid']) / 'stat').read_text().rsplit(')', 1)[1].split()
        return fields[0] not in ('Z', 'X') and int(fields[19]) == identity['start_ticks']
    except FileNotFoundError:
        return False


def owned_pet(health, owner):
    pet = health.get('pet', {})
    if not pet.get('running'):
        return None
    pid = pet['pid']
    fields = (Path('/proc') / str(pid) / 'stat').read_text().rsplit(')', 1)[1].split()
    if int(fields[1]) != owner['pid'] or not live(owner):
        raise ValueError('The Pet identity does not belong to this transport.')
    return {'pid': pid, 'start_ticks': int(fields[19])}


async def verify(workspace, sources, pc, directory, timeout=600, *, compiled_checks=None,
                 name_prefix="decodeItem", mcp_launcher=None, compiler_launcher=None,
                 protected_expectations=None, verification_imports=None, operation_observer=None):
    workspace = Path(workspace).resolve()
    launchers = launcher_bindings(workspace, mcp_launcher, compiler_launcher)
    protected = prepare_protected_expectations(workspace, sources, protected_expectations)
    import_adapters = prepare_verification_imports(workspace, protected, verification_imports)
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    private = (workspace / '_build/default').resolve()
    if not private.is_dir() or not private.is_relative_to(workspace.resolve()):
        raise ValueError('The owned private artifact directory is unavailable.')
    report = {'private_artifact_directory': str(private), 'launchers': launchers, 'protected_expectations': list(protected.values()), 'verification_imports': list(import_adapters.values()), 'success': False, 'calls': [], 'closures': [], 'sources': [], 'checks': []}

    def save():
        (directory / 'RESULT.json').write_text(json.dumps(report, indent=2) + '\n')

    async def operation(label, tool, arguments):
        owner = pet = None
        normal = False
        unchanged_launchers(launchers)
        unchanged_protected_expectations(protected)
        unchanged_verification_imports(workspace, import_adapters)
        env = dict(os.environ)
        env.update(ROCQ_WORKSPACE=str(workspace), ROCQ_DUNE_BUILD='1',
                   AGENT_BUILD_DIR=str(private.parent),
                   ZESU_ROCQ_COQC_WRAPPER=launchers['compiler']['path'])
        # The existing compiler wrapper supplies normal guarded admission.
        command = directory / (label + '.sh')
        command.write_text('#!/bin/sh\nset -eu\nexec "$ZESU_MCP_PYTHON" "$ZESU_PROMOTION_SERVER"\n')
        command.chmod(0o755)
        env.update(ZESU_MCP_PYTHON=sys.executable,
                   ZESU_PROMOTION_SERVER=str(HERE / 'promotion_verify_server.py'),
                   ZESU_ROCQ_MCP_BINARY=str(command))
        parameters = StdioServerParameters(command=launchers['mcp']['path'], env=env)
        result = None
        try:
            async with stdio_client(parameters) as streams:
                async with ClientSession(*streams) as session:
                    await session.initialize()

                    async def call(name, args):
                        record = {'tool': name, 'arguments': args,
                                  'request_UTC': datetime.now(timezone.utc).isoformat()}
                        report['calls'].append(record); save()
                        try:
                            response = await session.call_tool(name, args)
                            record['raw_response'] = response.model_dump(mode='json')
                            record['result'] = _result(response); save()
                        except BaseException as error:
                            record['error'] = dict(type=type(error).__name__, message=str(error)); save()
                            raise
                        return record['result']

                    health = await call('rocq_health', {})
                    if not health.get('ok'):
                        raise ValueError('Rocq MCP health failed.')
                    if mcp_launcher is not None or compiler_launcher is not None:
                        actual = health.get('toolchain', {}).get('coqc', {}).get('path')
                        if not isinstance(actual, str) or str(Path(actual).absolute()) != launchers['compiler']['path']:
                            raise ValueError('MCP health reports a different compiler launcher.')
                    owner = await call('rocq_promotion_owner', {})
                    if not owner.get('success') or not live(owner):
                        raise ValueError('The MCP server identity is unavailable.')
                    if health.get('pet', {}).get('running'):
                        raise ValueError('A fresh compilation transport has an active Pet.')
                    try:
                        token = await operation_observer.start(label, owner, tool, arguments) if operation_observer else None
                        try:
                            result = await call(tool, arguments)
                        finally:
                            if operation_observer:
                                await operation_observer.finish(token, result)
                    finally:
                        pet = owned_pet(await call('rocq_health', {}), owner)
            normal = True
        finally:
            for _ in range(50):
                if not live(owner) and not live(pet):
                    break
                await asyncio.sleep(.1)
            closure = {'operation': label, 'owner': owner, 'owned_pet': pet,
                       'transport_closed_normally': normal,
                       'server_exited': owner is not None and not live(owner),
                       'owned_Pet_absent': not live(pet)}
            report['closures'].append(closure); save()
        if not all(closure[k] for k in ('transport_closed_normally', 'server_exited', 'owned_Pet_absent')):
            raise ValueError('The owned verification transport did not close normally.')
        if not result or not result.get('success'):
            raise ValueError(f'{tool} failed. Inspect {directory / "RESULT.json"}.')
        return result

    try:
        used_protected = set()
        report['requested_sources'] = list(map(str, sources))
        for index, source in enumerate(compilation_sources(workspace, sources)):
            source = Path(source)
            require_clean_source(source)
            copy = directory / f'{index:02d}-{source.name}'
            copy.write_bytes(source.read_bytes())
            report['sources'].append({'path': str(source), 'sha256': digest(source),
                                      'snapshot': str(copy), 'snapshot_sha256': digest(copy)})
            retained = (compiled_checks or {}).get(str(source))
            artifact = private / source.relative_to(workspace).with_suffix('.vo')
            if retained is not None:
                compiled = retained_compile_result(source, artifact, retained)
                report.setdefault('reused_compilations', []).append(retained)
            else:
                compiled = await operation(f'compile-{index}', 'rocq_compile_file',
                    {'workspace': str(workspace), 'file': str(source), 'timeout': timeout, 'timing': True, 'keep_vo': True})
            require_clean_source(source)
            if not artifact.is_file():
                raise ValueError('The compiler did not retain the private module artifact.')
            report['checks'].append({'source': str(source), 'compile_file': compiled,
                                    'private_artifact': str(artifact), 'private_artifact_sha256': digest(artifact),
                                    'source_tree_clean': True, 'statements': []})
            for number, (name, statement, proof) in enumerate(statements(
                    copy.read_text(), pc, '.'.join(source.relative_to(workspace).with_suffix('').parts),
                    name_prefix=name_prefix)):
                key = (str(source.resolve()), name)
                if key in protected:
                    statement = protected[key]['statement']
                    used_protected.add(key)
                verification_statement = import_adapters[key]['verification_statement'] if key in import_adapters else statement
                checked = await operation(f'verify-{index}-{number}', 'rocq_verify',
                    {'workspace': str(workspace), 'problem_statement': verification_statement,
                     'proof': proof, 'problem_name': name, 'timeout': timeout})
                if checked.get('verification_method') != 'module_m':
                    raise ValueError('The generated statement lacks exact module_m verification.')
                if checked.get('assumptions') != []:
                    raise ValueError('The generated statement has assumptions or unavailable assumptions.')
                report['checks'][-1]['statements'].append(
                    {'name': name, 'exact_statement': statement,
                     'verification_statement': verification_statement,
                     'verification_statement_sha256': hashlib.sha256(verification_statement.encode()).hexdigest(),
                     'expectation_origin': 'baseline' if key in protected else 'candidate',
                     'verification': checked})
                save()
            if digest(source) != report['sources'][-1]['sha256']:
                raise ValueError('A generated source changed during verification.')
        if used_protected != set(protected):
            raise ValueError('A protected expectation was unused during verification.')
        unchanged_protected_expectations(protected)
        unchanged_verification_imports(workspace, import_adapters)
        report['success'] = True
        save()
        return report
    except BaseException as error:
        report['error'] = {'type': type(error).__name__, 'message': str(error)}
        save()
        raise


def verify_generated(workspace, sources, pc, directory, python=None, *, name_prefix="decodeItem",
                     mcp_launcher=None, compiler_launcher=None, protected_expectations=None,
                     verification_imports=None):
    """Use the pinned MCP Python, never a shell compiler fallback."""
    if not os.environ.get('OPAM_SWITCH_PREFIX') or not shutil.which('pet'):
        raise ValueError('Run complete promotion under the pinned opam environment with pet on PATH.')
    python = python or os.environ.get('ZESU_MCP_PYTHON') or sys.executable
    manifest = Path(str(directory) + '.inputs.json')
    manifest.parent.mkdir(parents=True, exist_ok=True)
    if manifest.exists() or Path(directory).exists():
        raise ValueError('The verification output already exists. Preserve that attempt.')
    FunctionNames(name_prefix)
    manifest.write_text(json.dumps({'workspace': str(workspace), 'sources': list(map(str, sources)),
                                    'pc': pc, 'directory': str(directory),
                                    'name_prefix': name_prefix,
                                    'protected_expectations': protected_expectations,
                                    'verification_imports': verification_imports,
                                    'mcp_launcher': str(mcp_launcher) if mcp_launcher is not None else None,
                                    'compiler_launcher': str(compiler_launcher) if compiler_launcher is not None else None}, indent=2) + '\n')
    subprocess.run([python, str(Path(__file__).resolve()), '--inputs', str(manifest)], check=True)
    result = json.loads((Path(directory) / 'RESULT.json').read_text())
    if result.get('success') is not True:
        raise ValueError('The generated promotion failed verification.')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs', type=Path, required=True)
    args = parser.parse_args()
    inputs = json.loads(args.inputs.read_text())
    asyncio.run(verify(Path(inputs['workspace']), inputs['sources'], inputs['pc'], inputs['directory'],
                       name_prefix=inputs.get('name_prefix', 'decodeItem'),
                       mcp_launcher=inputs.get('mcp_launcher'),
                       compiler_launcher=inputs.get('compiler_launcher'),
                       protected_expectations=inputs.get('protected_expectations'),
                       verification_imports=inputs.get('verification_imports')))
