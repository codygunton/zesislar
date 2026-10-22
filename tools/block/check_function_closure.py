"""Compile native decodeItem theorems and verify protected baseline statements."""
import argparse
import asyncio
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coqc_findlib import active_build, check_record
from lithium_metrics import Commit, block_counts, count_commit
from launch_imports import function_hints
from promotion_verification import (digest, launcher_bindings, prepare_protected_expectations,
                                    unchanged_launchers, unchanged_protected_expectations, verify)
from closure_receipts import ClosureObserver, ObjectBindings, validate_physical_receipt
from residual.modules import parse_module


PUBLIC = {
    'decodeItemSelectedCompliance': 'ZesuSsz/Compliance/DecodeItemCompliance.v',
    'decodeItemSelectedComplianceRegisters': 'ZesuSsz/Compliance/DecodeItemCompositionalCompliance.v',
    'decodeItemSelectedComplianceCompositional': 'ZesuSsz/Compliance/DecodeItemCompositionalCompliance.v',
    'decodeItemSlotBody800d698c': 'ZesuSsz/Proofs/DecodeItem/TableSlots/Adapter800d698c.v',
}
# These modules fix the claim and its signature. Entry modules may change.
PUBLIC_CONTEXTS = (
    'ZesuSsz/Contracts/Level1.v',
    'ZesuSsz/Contracts/RlpDecodeItemContract.v',
    'ZesuSsz/Compliance/KnownBugs.v',
    'ZesuSsz/Evidence/SignatureGates.v',
)


def native_rows(commit):
    """Keep 24 CFG PCs separate from 25 production theorem rows."""
    rows = []
    with tempfile.TemporaryDirectory(prefix='function-closure-') as directory:
        blocks, paths = block_counts(commit, directory)
        if len(blocks) != 24:
            raise ValueError('The candidate needs exactly 24 CFG PCs.')
        for block in blocks:
            for branch in block.get('branches', [block]):
                path = branch['path']
                if branch['status'] != 'native':
                    raise ValueError('A production theorem has a hand body: ' + path)
                data = commit.read(path)
                source = Path(directory) / Path(path).name
                source.write_bytes(data)
                name = 'DesignedBoundary_' + Path(path).stem.removeprefix('Block')
                proofs = [proof for proof in parse_module(source) if proof.name == name]
                if len(proofs) != 1:
                    raise ValueError('The source needs its exact boundary theorem: ' + path)
                proof = proofs[0]
                lines = data.decode().splitlines()
                if not re.search(r'\bQed\.\s*$', lines[proof.terminator_line]):
                    raise ValueError('A production theorem must end with Qed: ' + path)
                if not proof.automation_only or not proof.body:
                    raise ValueError('A production theorem needs native automation: ' + path)
                statement = '\n'.join(lines[proof.declaration_line:proof.proof_line]) + '\n'
                rows.append(dict(pc=block['pc'], source=path, theorem=name,
                                 module='.'.join(Path(path).with_suffix('').parts),
                                 source_sha256=hashlib.sha256(data).hexdigest(),
                                 statement=statement,
                                 statement_sha256=hashlib.sha256(statement.encode()).hexdigest()))
    if len(rows) != 25 or len({row['theorem'] for row in rows}) != 25:
        raise ValueError('The candidate needs 25 distinct native theorem rows.')
    split = {row['theorem'] for row in rows if row['pc'] == '800d698c'}
    if split != {'DesignedBoundary_800d698cLiteral', 'DesignedBoundary_800d698cShortString'}:
        raise ValueError('Both exact 698c branches are required.')
    return dict(cfg_pcs=24, native_theorem_rows=25, rows=rows,
                umbrellas=sorted(paths - {row['source'] for row in rows}))


def bound_json(record, workspace=None):
    if not isinstance(record, dict) or set(record) != {'path', 'sha256'}:
        raise ValueError('A JSON binding needs its path and SHA256.')
    path = Path(record['path'])
    if not path.is_absolute() or (workspace is not None and not path.resolve().is_relative_to(workspace)):
        raise ValueError('A JSON binding leaves its workspace.')
    if digest(path) != record['sha256']:
        raise ValueError('A JSON binding differs from its hash.')
    return json.loads(path.read_text())


def arm_binding(arm, *, require_active=True):
    if not isinstance(arm, dict) or set(arm) != {'workspace', 'commit', 'build_dir', 'recipe', 'findlib'}:
        raise ValueError('A closure arm has missing or unused fields.')
    for key in ('workspace', 'build_dir'):
        if not isinstance(arm[key], str) or not Path(arm[key]).is_absolute():
            raise ValueError('Closure arm paths must be absolute.')
    root, build = Path(arm['workspace']).resolve(), Path(arm['build_dir']).resolve()
    if (not build.is_relative_to(root) or not (build / 'default').is_dir() or
            (require_active and active_build(root) != build)):
        raise ValueError('The closure arm needs its contained active build.')
    commit = Commit(root, 'HEAD')
    if commit.sha != arm['commit']:
        raise ValueError('The closure arm HEAD differs from its exact commit.')
    if commit.git('status', '--porcelain', '--untracked-files=no').strip():
        raise ValueError('The closure arm has tracked changes.')
    recipe = bound_json(arm['recipe'], root)
    if (not isinstance(recipe, dict) or set(recipe) != {'command', 'working_dir'} or
            not isinstance(recipe['command'], list) or not recipe['command'] or
            any(not isinstance(arg, str) or not arg for arg in recipe['command']) or
            not isinstance(recipe['working_dir'], str) or
            Path(recipe['working_dir']).resolve() != build / 'default'):
        raise ValueError('The recipe does not bind the private compiler cwd.')
    findlib = bound_json(arm['findlib'], root)
    ocamlpath = check_record(findlib, root, build)
    sources = []
    for relative in sorted(commit.paths):
        if not relative.endswith('.v'):
            continue
        expected = hashlib.sha256(commit.read(relative)).hexdigest()
        path = root / relative
        if not path.resolve().is_relative_to(root) or digest(path) != expected:
            raise ValueError('A tracked proof source differs: ' + relative)
        sources.append(dict(path=str(path), sha256=expected))
    objects = []
    for path in sorted((build / 'default').rglob('*.vo')):
        if not path.resolve().is_relative_to(root):
            raise ValueError('A private object leaves its workspace: ' + str(path))
        objects.append(dict(path=str(path), sha256=digest(path)))
    if not objects:
        raise ValueError('The closure arm has no private proof objects.')
    return dict(**arm, tree=commit.git('rev-parse', 'HEAD^{tree}').strip(),
                OCAMLPATH=ocamlpath, command=recipe['command'], cwd=recipe['working_dir'],
                sources=sources, objects=objects), commit


def public_mapping(workspace, baseline, records):
    """Require every public declaration exactly once before any MCP operation."""
    if not isinstance(records, list):
        raise ValueError('The coordinator requires all protected expectations.')
    expected = {(str(workspace / path), name) for name, path in PUBLIC.items()}
    checked = prepare_protected_expectations(workspace,
        [workspace / path for path in sorted(set(PUBLIC.values()))], records)
    if set(checked) != expected:
        raise ValueError('The protected public declaration inventory differs.')
    for row in checked.values():
        if (Path(row['baseline_workspace']).resolve() != Path(baseline['workspace']).resolve() or
                row['baseline_commit'] != baseline['commit'] or
                Path(row['baseline_build_dir']).resolve() != Path(baseline['build_dir']).resolve()):
            raise ValueError('A protected expectation names a different baseline arm.')
    return checked


def physical_mapping(executable, admission, launchers):
    if (not isinstance(executable, dict) or set(executable) != {'path', 'sha256'} or
            not Path(executable['path']).is_absolute() or
            str(Path(executable['path']).resolve()) != executable['path'] or
            digest(executable['path']) != executable['sha256']):
        raise ValueError('The physical compiler needs its exact executable binding.')
    receipt = bound_json(admission)
    if receipt.get('success') is not True or not receipt.get('observed_compilers'):
        raise ValueError('The launcher admission has no physical compiler receipt.')
    policy = bound_json(receipt['launcher_receipt'])
    if (policy['server'] != launchers['mcp']['path'] or
            policy['compiler'] != launchers['compiler']['path']):
        raise ValueError('The admission receipt names different launchers.')
    for path, expected in policy['bound_sources'].items():
        if digest(path) != expected:
            raise ValueError('A launcher admission input changed.')
    for observed in receipt['observed_compilers']:
        if policy['bound_sources'].get(observed['executable']) != executable['sha256']:
            raise ValueError('The admission compiler hash differs.')
        row = {**observed, 'executable_sha256': executable['sha256'],
               'cpu_quota_controls': observed['cpu_quota']['controls']}
        validate_physical_receipt(row, executable, require_context=False)
    if not all(receipt['closure'].get(key) is True for key in
               ('transport_closed_normally', 'server_exited', 'owned_pet_absent')):
        raise ValueError('The launcher admission did not close normally.')


def baseline_verification(record, baseline, protected, executable):
    receipt = bound_json(record)
    if receipt.get('success') is not True or receipt.get('scope') != 'protected-baseline-only':
        raise ValueError('The protected baseline has no completed exact verification.')
    if receipt['baseline']['commit'] != baseline['commit']:
        raise ValueError('The verified baseline commit differs.')
    for key in ('commit', 'tree', 'objects'):
        if receipt['baseline'][key] != baseline[key]:
            raise ValueError('The verified baseline source/object identity differs.')
    fields = ('baseline_commit', 'baseline_source_sha256', 'baseline_object_sha256', 'statement_sha256')
    prior = {row['name']: tuple(row[field] for field in fields) for row in receipt['protected_expectations']}
    expected = {row['name']: tuple(row[field] for field in fields) for row in protected.values()}
    if prior != expected:
        raise ValueError('The protected baseline expectations differ from their verification.')
    checked = set()
    for verification in receipt['verifications']:
        result = bound_json(dict(path=verification['result'], sha256=verification['sha256']))
        if result.get('success') is not True:
            raise ValueError('A baseline module failed exact verification.')
        for check in result['checks']:
            for statement in check['statements']:
                outcome = statement['verification']
                if (outcome.get('success') is not True or outcome.get('verification_method') != 'module_m'
                        or outcome.get('assumptions') != []):
                    raise ValueError('A baseline statement lacks exact module_m verification.')
                if statement.get('expectation_origin') == 'baseline':
                    checked.add(statement['name'])
    if checked != set(PUBLIC):
        raise ValueError('The baseline verification omits protected declarations.')
    operations = []
    for binding in receipt['physical_receipts']:
        operation = bound_json(binding)
        if operation.get('limits_validated') is not True or operation.get('observer_error_count') != 0:
            raise ValueError('A baseline compiler receipt has an observer failure.')
        for row in operation['observed_compilers']:
            validate_physical_receipt(row, executable)
        if operation['tool'] == 'rocq_verify' and not operation['observed_compilers']:
            raise ValueError('A baseline statement has no physical compiler receipt.')
        operations.append(operation)
    if not operations:
        raise ValueError('The protected baseline has no compiler receipts.')


def prepare(inputs, *, protected_baseline_only=False):
    if (not isinstance(inputs, dict) or set(inputs) != {'schema_version', 'function', 'baseline',
            'candidate', 'protected_expectations', 'freshness', 'mcp_launcher',
            'compiler_launcher', 'rpc_timeout', 'physical_compiler', 'physical_admission',
            'baseline_verification'} or type(inputs['schema_version']) is not int or inputs['schema_version'] != 1 or
            inputs['function'] != 'decodeItem'):
        raise ValueError('The closure input mapping is incomplete or unsupported.')
    timeout = inputs['rpc_timeout']
    if type(timeout) is not int or timeout <= 0:
        raise ValueError('The closure mapping needs an explicit positive RPC timeout.')
    baseline, baseline_commit = arm_binding(inputs['baseline'], require_active=False)
    candidate, commit = arm_binding(inputs['candidate'])
    root = Path(candidate['workspace']).resolve()
    function_hints('decodeItem', root)  # Preserve inventory-only and umbrella refusals.
    coverage = native_rows(commit)
    protected = public_mapping(root, baseline, inputs['protected_expectations'])
    contexts = []
    for relative in PUBLIC_CONTEXTS:
        old, new = baseline_commit.read(relative), commit.read(relative)
        if old != new:
            raise ValueError('A protected claim/signature source differs: ' + relative)
        contexts.append(dict(source=relative, baseline_sha256=hashlib.sha256(old).hexdigest(),
                             candidate_sha256=hashlib.sha256(new).hexdigest()))
    freshness = None
    if inputs['freshness'] is not None:
        freshness = bound_json(inputs['freshness'], root)
    metrics = count_commit(commit, 'decodeItem', freshness)
    if any(row.get('freshness') == 'unchecked' for row in metrics['files']):
        raise ValueError('Generated support lacks a successful freshness binding.')
    if protected_baseline_only and candidate['commit'] != baseline['commit']:
        raise ValueError('Protected baseline verification needs the exact baseline commit.')
    modules = {}
    if not protected_baseline_only:
        for row in coverage['rows']:
            modules.setdefault(row['source'], []).append(row['theorem'])
    for name, source in PUBLIC.items():
        modules.setdefault(source, []).append(name)
    selected = []
    for source, names in sorted(modules.items()):
        path = root / source
        copied = Path(candidate['build_dir']) / 'default' / source
        artifact = copied.with_suffix('.vo')
        if (not copied.resolve().is_relative_to(root) or not artifact.resolve().is_relative_to(root) or
                not copied.is_file() or digest(copied) != digest(path) or not artifact.is_file()):
            raise ValueError('A selected source/object mapping is unavailable: ' + source)
        selected.append(dict(source=str(path), source_sha256=digest(path),
                             private_source=str(copied), private_artifact=str(artifact),
                             private_artifact_sha256=digest(artifact), required_statements=names))
    launchers = launcher_bindings(root, inputs['mcp_launcher'], inputs['compiler_launcher'])
    physical_mapping(inputs['physical_compiler'], inputs['physical_admission'], launchers)
    if not protected_baseline_only:
        baseline_verification(inputs['baseline_verification'], baseline, protected, inputs['physical_compiler'])
    return dict(schema_version=1, function='decodeItem', baseline=baseline, candidate=candidate,
                scope='protected-baseline-only' if protected_baseline_only else 'native-and-compliance',
                coverage=coverage, selected=selected, protected_expectations=list(protected.values()),
                public_contexts=contexts, metrics=metrics, launchers=launchers,
                freshness=inputs['freshness'],
                physical_compiler=inputs['physical_compiler'], physical_admission=inputs['physical_admission'],
                baseline_verification=inputs['baseline_verification'],
                rpc_timeout=timeout, rpc_timeout_scope='MCP operation; not a physical CPU limit',
                proof_execution=False, success=False)


def unchanged_preparation(report):
    ObjectBindings(report['baseline'], report['candidate']).check()
    unchanged_launchers(report['launchers'])
    for arm in ('baseline', 'candidate'):
        bound = report[arm]
        commit = Commit(bound['workspace'], 'HEAD')
        if (commit.sha != bound['commit'] or (arm == 'candidate' and
                active_build(bound['workspace']) != Path(bound['build_dir']).resolve())):
            raise ValueError('A closure arm identity changed after preparation.')
        for row in bound['sources']:
            if digest(row['path']) != row['sha256']:
                raise ValueError('A closure source changed after preparation.')
        for label in ('recipe', 'findlib'):
            bound_json(bound[label], Path(bound['workspace']).resolve())
    protected = {(row['candidate_source'], row['name']): row for row in report['protected_expectations']}
    unchanged_protected_expectations(protected)
    metrics = report['metrics']
    root = Path(report['candidate']['workspace'])
    for row in [metrics['manifest'], *metrics['files']]:
        if digest(root / row['path']) != row['sha256']:
            raise ValueError('A metrics/freshness input changed after preparation.')
    if report['freshness'] is not None:
        bound_json(report['freshness'], root)
    bound_json(report['physical_admission'])
    if digest(report['physical_compiler']['path']) != report['physical_compiler']['sha256']:
        raise ValueError('The bound physical compiler changed.')
    if report['baseline_verification'] is not None:
        bound_json(report['baseline_verification'])


async def run(inputs, directory, *, prepare_only=False, protected_baseline_only=False):
    """Use existing owned MCP verification; keep failed results in fresh directories."""
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    report = {'success': False, 'proof_execution': False}
    objects = None
    def save():
        if objects is not None:
            report['object_transitions'] = objects.transitions
            report['physical_receipts'] = [dict(path=str(path), sha256=digest(path))
                for path in sorted((directory / 'physical-compilers').glob('*.json'))]
        (directory / 'RESULT.json').write_text(json.dumps(report, indent=2) + '\n')
    try:
        report = prepare(inputs, protected_baseline_only=protected_baseline_only)
        (directory / 'PREPARED.json').write_text(json.dumps(report, indent=2) + '\n')
        save()
        if prepare_only:
            return report
        root = Path(report['candidate']['workspace'])
        if os.environ.get('OCAMLPATH') != report['candidate']['OCAMLPATH']:
            raise ValueError('The active findlib path differs from the candidate record.')
        report['proof_execution'] = True
        report['verifications'] = []
        objects = ObjectBindings(report['baseline'], report['candidate'])
        observer = ClosureObserver(objects, report['physical_compiler'], directory / 'physical-compilers')
        for index, selected in enumerate(report['selected']):
            unchanged_preparation(report)
            rows = [row for row in inputs['protected_expectations']
                    if str(Path(row['candidate_source']).resolve()) == selected['source']]
            result_directory = directory / f'verify-{index:02d}'
            result = await verify(root, [Path(selected['source'])], 0, result_directory,
                timeout=report['rpc_timeout'], mcp_launcher=inputs['mcp_launcher'],
                compiler_launcher=inputs['compiler_launcher'], protected_expectations=rows or None,
                operation_observer=observer)
            if result.get('success') is not True:
                raise ValueError('The selected module has no successful verification result.')
            for check in result['checks']:
                for statement in check['statements']:
                    outcome = statement['verification']
                    if (outcome.get('success') is not True or
                            outcome.get('verification_method') != 'module_m' or
                            outcome.get('assumptions') != []):
                        raise ValueError('A returned statement lacks exact module_m verification.')
            checked = {statement['name'] for check in result['checks']
                       if check['source'] == selected['source'] for statement in check['statements']
                       if statement['verification'].get('success') is True and
                       statement['verification'].get('verification_method') == 'module_m' and
                       statement['verification'].get('assumptions') == []}
            if not set(selected['required_statements']).issubset(checked):
                raise ValueError('A required native/public statement has no exact verification.')
            report['verifications'].append(dict(source=selected['source'], checked=sorted(checked),
                result=str(result_directory / 'RESULT.json'), sha256=digest(result_directory / 'RESULT.json')))
            save()
        unchanged_preparation(report)
        report['success'] = True
        save()
        return report
    except BaseException as error:
        report['error'] = dict(type=type(error).__name__, message=str(error))
        save()
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--protected-baseline-only', action='store_true')
    args = parser.parse_args()
    asyncio.run(run(json.loads(args.inputs.read_text()), args.output, prepare_only=args.prepare_only,
                    protected_baseline_only=args.protected_baseline_only))


if __name__ == '__main__':
    main()
