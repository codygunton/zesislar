#!/usr/bin/env python3
"""Build and independently check the protected PUBLIC compliance closure."""
import argparse
import asyncio
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import uuid

sys.path.insert(0, str(Path(__file__).parent / 'block'))
import promotion_verification as verification
from check_function_closure import PUBLIC, PUBLIC_CONTEXTS
from coqc_findlib import check_record
from gate_workspace import prepare as prepare_sources

BASELINE = '0140e68747d7f3f0c4ac8ff44609f42ba9da65b4'
PLUGINS = (
    '_dune-cache/install/default/lib/zesu-signature-gates/plugin/signature_gates_plugin.cmxs',
    '_dune-cache/install/default/lib/zesu-signature-gates/trace-observer/trace_block_plugin.cmxs',
)
# Each gate compile may run this long once the guard admits it.
COMPILE_SECONDS = 600
WRAPPERS = '''Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Compliance.DecodeItemCompliance.
Require Import ZesuSsz.Compliance.DecodeItemCompositionalCompliance.
Require Import ZesuSsz.Compliance.DecodeItemComplianceGenerated.

Definition certified_selected :
  forall returnAddress,
    ZesuSsz.Contracts.Level1.IslarisContractCorrect
      ZesuSsz.Contracts.RlpDecodeItem.decodeItemEntry returnAddress
      (ZesuSsz.Contracts.DecodeItemSelected.decodeItemSelectedModel returnAddress) :=
  ZesuSsz.Compliance.DecodeItemCompliance.decodeItemSelectedCompliance.

Definition certified_registers :
  forall returnAddress,
    ZesuSsz.Contracts.Level1.IslarisContractCorrect
      ZesuSsz.Contracts.RlpDecodeItem.decodeItemEntry returnAddress
      (ZesuSsz.Contracts.DecodeItemCompositional.decodeItemSelectedModelRegisters returnAddress) :=
  ZesuSsz.Compliance.DecodeItemCompositionalCompliance.decodeItemSelectedComplianceRegisters.

Definition certified_compositional :
  forall returnAddress,
    ZesuSsz.Contracts.Level1.IslarisContractCorrect
      ZesuSsz.Contracts.RlpDecodeItem.decodeItemEntry returnAddress
      (ZesuSsz.Contracts.DecodeItemCompositional.decodeItemSelectedModelCompositional returnAddress) :=
  ZesuSsz.Compliance.DecodeItemCompositionalCompliance.decodeItemSelectedComplianceCompositional.

Lemma certified_generated :
  forall returnAddress,
    ZesuSsz.Contracts.Level1.IslarisContractCorrect
      ZesuSsz.Contracts.RlpDecodeItem.decodeItemEntry returnAddress
      (ZesuSsz.Contracts.DecodeItemSelected.decodeItemSelectedModel returnAddress).
Proof.
  exact ZesuSsz.Compliance.DecodeItemComplianceGenerated.decodeItemGeneratedCompliance.
Qed.

Set Printing Fully Qualified.
Print Assumptions certified_selected.
Print Assumptions certified_registers.
Print Assumptions certified_compositional.
Print Assumptions certified_generated.
'''


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def binding(path):
    return {'path': str(path), 'sha256': digest(path)}


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def git(workspace, *args):
    return subprocess.check_output(['git', '-C', str(workspace), *args])


def clone(source, target):
    """Use the required copy mode, including for source-only staging."""
    target.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(['cp', '--reflink=always', '--preserve=all', '--', str(source), str(target)], check=True)
    if source.samefile(target) or digest(source) != digest(target):
        raise ValueError('A staged file lost its exact, independent identity.')


def kernel_flags(recipe, workspace, build):
    cwd = workspace / recipe['working_dir']
    if cwd.resolve() != build / 'default':
        raise ValueError('The compiler recipe names another build.')
    flags, args, index = [], recipe['command'][1:], 0
    while index < len(args):
        flag = args[index]
        if flag in {'-Q', '-R', '-coqlib'}:
            path = Path(args[index + 1])
            path = path if path.is_absolute() else cwd / path
            flags += [flag, str(path.resolve())]
            index += 2
            if flag != '-coqlib':
                flags.append(args[index]); index += 1
        elif flag == '-boot':
            flags.append(flag); index += 1
        else:
            index += 1
    return flags


def wrapper_paths(workspace, out, build):
    """Keep checker input outside the production tree, with the normal MCP mapping."""
    source = out / 'scratch/SoundnessGateWrappers.v'
    artifact = build / 'default' / source.relative_to(workspace).with_suffix('.vo')
    return source, artifact


def control_sources():
    """Each candidate compiles before the checker tests its own expectation."""
    return {
        'admitted': 'Lemma challenge : False. Admitted.\n',
        'extra_axiom': 'Axiom extra : False.\nLemma challenge : False. Proof. exact extra. Qed.\n',
        'admit_axiom': ('Require Import Coq.Compat.AdmitAxiom.\n'
                        'Lemma challenge : False. Proof. exact proof_admitted. Qed.\n'),
        'wrong_statement': 'Lemma challenge : True. Proof. exact I. Qed.\n',
        'doctored_statement': ('Definition expected := True.\n'
                               'Lemma challenge : expected. Proof. exact I. Qed.\n'),
    }


def unchanged_inputs(config):
    for row in config['bindings']:
        if digest(row['path']) != row['sha256']:
            raise ValueError('A frozen gate input changed: ' + row['path'])


def rejected_control(name, compiled, outcome):
    if compiled.get('success') is not True or outcome.get('success') is not False:
        raise ValueError('A negative control did not compile and then refuse.')
    if name in {'admitted', 'extra_axiom', 'admit_axiom'}:
        if (outcome.get('verification_method') != 'module_m' or
                outcome.get('reason') != 'axiom_dependency' or not outcome.get('assumptions')):
            raise ValueError('The negative control did not reject an assumption.')
    elif 'Unable to unify' not in outcome.get('error', '') or 'False' not in outcome['error']:
        raise ValueError('The negative control did not reject the checker-owned type.')


def stage_traces(workspace, origin):
    recipe = json.loads((workspace / 'build/stock-zisk/build-recipe.json').read_text())
    rows = []
    for relative, record in sorted(recipe['project_derived'].items()):
        if not relative.startswith('generated/isla-traces/'):
            continue
        target = workspace / relative
        if not target.resolve().is_relative_to(workspace) or target.suffix in {'.vo', '.vos', '.vok'}:
            raise ValueError('The trace manifest must name contained source inputs only.')
        if not target.exists():
            if origin is None:
                raise ValueError('Missing trace source; supply --trace-source: ' + relative)
            source = origin / relative
            if digest(source) != record['sha256']:
                raise ValueError('The trace source differs from the pinned manifest: ' + relative)
            clone(source, target)
        if digest(target) != record['sha256']:
            raise ValueError('The trace source differs: ' + relative)
        rows.append(binding(target))
    return rows


def public_records(workspace, baseline, build):
    """Use the reviewed Git source as authority, never a candidate type query."""
    records = []
    authority = baseline / '_build/authority'
    for name, relative in PUBLIC.items():
        source, original = workspace / relative, baseline / relative
        # A baseline object may be reused only for identical complete source bytes.
        if digest(source) != digest(original):
            raise ValueError('Protected PUBLIC source changed; review its baseline: ' + relative)
        for src, dst in [(original, authority / 'default' / relative),
                         (build / 'default' / Path(relative).with_suffix('.vo'),
                          authority / 'default' / Path(relative).with_suffix('.vo'))]:
            if not dst.exists():
                clone(src, dst)
        matches = [s for n, s, _ in verification.statements(original.read_text(), 0) if n == name]
        if len(matches) != 1:
            raise ValueError('A protected PUBLIC declaration is absent or ambiguous.')
        statement = matches[0]
        records.append(dict(candidate_source=str(source), candidate_source_sha256=digest(source), name=name,
            baseline_workspace=str(baseline), baseline_commit=BASELINE, baseline_build_dir=str(authority),
            baseline_source=str(original), baseline_source_sha256=digest(original),
            baseline_object=str(authority / 'default' / Path(relative).with_suffix('.vo')),
            baseline_object_sha256=digest(authority / 'default' / Path(relative).with_suffix('.vo')),
            statement=statement, statement_sha256=hashlib.sha256(statement.encode()).hexdigest()))
    return records


async def negative_checks(config):
    """Use the existing guarded MCP server and its module_m checker."""
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client
    from successor_entailment import _result
    workspace, out, build = map(Path, (config['workspace'], config['output'], config['build']))
    binary = out / 'mcp-server.sh'
    binary.write_text('#!/bin/sh\nexec "$ZESU_MCP_PYTHON" "$ZESU_PROMOTION_SERVER"\n')
    binary.chmod(0o700)
    for name, text in control_sources().items():
        directory = out / 'negative' / name
        directory.mkdir(parents=True)
        source = directory / 'Control.v'
        source.write_text(text + 'Print Assumptions challenge.\n')
        report = {'success': False, 'calls': [], 'source': binding(source), 'allowed_axioms': []}
        owner = pet = None
        normal = False
        env = dict(os.environ, ROCQ_WORKSPACE=str(workspace), ROCQ_DUNE_BUILD='1',
                   AGENT_BUILD_DIR=str(build), ZESU_MCP_PYTHON=config['mcp_python'],
                   ZESU_PROMOTION_SERVER=str(workspace / 'tools/block/promotion_verify_server.py'),
                   ZESU_ROCQ_MCP_BINARY=str(binary),
                   ZESU_ROCQ_COQC_WRAPPER=str(workspace / 'tools/rocq_coqc_guarded.sh'),
                   ZESU_COMPILE_SECONDS=str(COMPILE_SECONDS))
        try:
            async with stdio_client(StdioServerParameters(
                    command=str(workspace / 'tools/rocq_mcp_guarded.sh'), env=env)) as streams:
                async with ClientSession(*streams) as session:
                    await session.initialize()
                    async def call(tool, arguments):
                        row = {'tool': tool, 'arguments': arguments}
                        report['calls'].append(row); save(directory / 'RESULT.json', report)
                        response = await session.call_tool(tool, arguments)
                        row.update(raw_response=response.model_dump(mode='json'), result=_result(response))
                        save(directory / 'RESULT.json', report)
                        return row['result']
                    health = await call('rocq_health', {})
                    if not health.get('ok') or health.get('pet', {}).get('running'):
                        raise ValueError('The fresh negative-control transport is unhealthy.')
                    owner = await call('rocq_promotion_owner', {})
                    if not owner.get('success') or not verification.live(owner):
                        raise ValueError('The MCP owner identity is unavailable.')
                    try:
                        # Each compile gets COMPILE_SECONDS after guard admission;
                        # a long admission wait is logged and retried.
                        compiled = await verification.call_with_admission(call, 'rocq_compile_file',
                            dict(workspace=str(workspace), file=str(source), timing=True, keep_vo=True),
                            COMPILE_SECONDS)
                        if compiled.get('success') is not True:
                            raise ValueError('A negative fixture failed to compile; inspect its first error.')
                        outcome = await verification.call_with_admission(call, 'rocq_verify', dict(
                            workspace=str(workspace), problem_statement='Lemma challenge : False.\n',
                            proof=source.read_text(), problem_name='challenge'), COMPILE_SECONDS)
                        rejected_control(name, compiled, outcome)
                        report.update(success=True, expected_rejection=outcome,
                                      Print_Assumptions=compiled.get('output', ''))
                    finally:
                        pet = verification.owned_pet(await call('rocq_health', {}), owner)
            normal = True
        finally:
            for _ in range(50):
                if not verification.live(owner) and not verification.live(pet):
                    break
                await asyncio.sleep(.1)
            report['closure'] = dict(transport_closed_normally=normal,
                server_exited=owner is not None and not verification.live(owner),
                owned_Pet_absent=not verification.live(pet))
            save(directory / 'RESULT.json', report)
        if not all(report['closure'].values()):
            raise ValueError('The negative-control transport did not close.')


def project_graph(build):
    """Direct project dependencies of each ZesuSsz object, from Dune's coqdep output."""
    graph = {}
    text = (build / 'default/ZesuSsz/.ZesuSsz.theory.d').read_text().replace('\\\n', ' ')
    for line in text.splitlines():
        if ':' not in line:
            continue
        left, right = line.split(':', 1)
        target = left.split()[0]
        if target.endswith('.vo'):
            rows = []
            for dependency in right.split():
                if not dependency.endswith('.vo'):
                    continue
                if os.path.isabs(dependency):
                    if not Path(dependency).is_relative_to(build / 'default'):
                        continue  # An installed library is not a project target.
                    dependency = str(Path(dependency).relative_to(build / 'default'))
                else:
                    dependency = os.path.normpath('ZesuSsz/' + dependency)
                rows.append(dependency)
            graph['ZesuSsz/' + target] = rows
    return graph


def dependency_closure(graph, roots):
    """The roots and every project object they need (objects of other theories end the walk)."""
    missing = set(roots) - graph.keys()
    if missing:
        raise ValueError('The dependency file lacks a module: ' + ', '.join(sorted(missing)))
    seen, pending = set(), list(roots)
    while pending:
        target = pending.pop()
        if target not in seen:
            seen.add(target)
            pending.extend(graph.get(target, ()))
    return seen


def fresh_dependencies(graph, fresh):
    """Objects the fresh set needs that need no fresh-set member.

    An object above a fresh member is left to the fresh step: built in the
    closure step, it would bring the fresh member in from the cache first.
    """
    fresh = set(fresh)
    needed = dependency_closure(graph, fresh) - fresh
    users = {}
    for target in needed:
        for dependency in graph.get(target, ()):
            users.setdefault(dependency, set()).add(target)
    above, pending = set(), list(fresh)
    while pending:
        for user in users.get(pending.pop(), ()):
            if user not in above:
                above.add(user)
                pending.append(user)
    return sorted(needed - above)


def csexp(data):
    """Parse a stream of canonical S-expressions (the Dune trace format)."""
    stack, items, index = [], [], 0
    while index < len(data):
        byte = data[index]
        if byte == 0x28:
            stack.append([]); index += 1
        elif byte == 0x29:
            done = stack.pop(); index += 1
            (stack[-1] if stack else items).append(done)
        else:
            colon = data.index(b':', index)
            size = int(data[index:colon])
            atom = data[colon + 1:colon + 1 + size].decode('utf-8', 'replace')
            index = colon + 1 + size
            (stack[-1] if stack else items).append(atom)
    if stack:
        raise ValueError('The Dune trace ends inside an expression.')
    return items


def field(event, name):
    return next((row[1:] for row in event if isinstance(row, list) and row and row[0] == name), None)


def fresh_compiler_runs(trace, fresh):
    """Each fresh object needs a coqc run in this Dune invocation that exited 0."""
    runs = {}
    for event in csexp(trace.read_bytes()):
        if event[:2] != ['process', 'finish']:
            continue
        program, arguments = field(event, 'prog'), field(event, 'process_args')
        exit_code, targets = field(event, 'exit'), field(event, 'target_files')
        if not program or Path(program[0]).name != 'coqc' or exit_code != ['0'] or not arguments or not targets:
            continue
        for target in fresh:
            source = str(Path(target).with_suffix('.v'))
            if arguments[0][-1] == source and any(name.endswith('/default/' + target) for name in targets[0]):
                runs[target] = {'source': source, 'pid': field(event, 'pid')[0], 'exit': 0}
    missing = sorted(set(fresh) - runs.keys())
    if missing:
        raise ValueError('The Dune trace shows no fresh coqc run for: ' + ', '.join(missing))
    return runs


def public_fresh_receipt(build, fresh, captured, started):
    """The fresh object and the object that Dune linked into _build must be equal."""
    runs = fresh_compiler_runs(build / 'trace.csexp', fresh)
    rows = []
    for target in fresh:
        produced, linked = captured / target, build / 'default' / target
        if not produced.is_file() or not linked.is_file():
            raise ValueError('A fresh object is missing: ' + target)
        if produced.stat().st_mtime_ns < started:
            raise ValueError('A captured object predates the fresh compile: ' + target)
        if digest(produced) != digest(linked):
            raise ValueError('The object in _build differs from the fresh compile: ' + target)
        rows.append({'target': target, 'compiler_run': runs[target], 'fresh': binding(produced),
                     'linked': binding(linked), 'equal': True})
    return {'schema': 'soundness.public-fresh.v2', 'started_ns': started, 'fresh_objects': rows,
            'policy': 'Dependency objects may come from the Dune cache; recursive coqchk re-checks them. '
                      'Each fresh object comes from a coqc rerun and equals the object in _build.'}


def stage(config, name):
    unchanged_inputs(config)
    workspace, out, build = map(Path, (config['workspace'], config['output'], config['build']))
    if name == 'source':
        public = sorted({str(Path(p).with_suffix('.vo')) for p in PUBLIC.values()})

        def dune(label, targets, **environment):
            # Every step keeps the cache enabled: Dune reruns every rule when the mode changes.
            subprocess.run([sys.executable, '-B', 'tools/build_record.py', '--build-dir', str(build),
                '--target', 'soundness-' + label, '--', shutil.which('dune'), 'build', '--root', str(workspace),
                '--build-dir', str(build), '--cache=enabled', '-j2', '--display', 'short', *targets],
                cwd=workspace, env=dict(os.environ, DUNE_CACHE='enabled', **environment), check=True)
        # The plugins come from the cache too. A native OCaml compile records its
        # worktree path, so a fresh plugin changed every Coq rule digest outside
        # the worktree that filled the cache. A plugin acts only at elaboration:
        # recursive coqchk and the statement checks cover what it produced.
        dune('plugins', PLUGINS)
        dune('dependencies', ['ZesuSsz/.ZesuSsz.theory.d'])
        graph = project_graph(build)
        # Optionally the trust-context files that the PUBLIC closure contains
        # also compile fresh; a context outside it cannot define a PUBLIC term.
        closure = dependency_closure(graph, public)
        contexts = sorted(str(Path(p).with_suffix('.vo')) for p in PUBLIC_CONTEXTS) if config.get('fresh_contexts') else []
        fresh = sorted(set(public) | {c for c in contexts if c in closure})
        # The dependency closure may come from the Dune cache: recursive coqchk
        # re-checks every object, cached or fresh.
        dependencies = fresh_dependencies(graph, fresh)
        if dependencies:  # Dune builds its default alias without targets.
            dune('closure', dependencies)
        if any((build / 'default' / target).exists() for target in fresh):
            raise ValueError('A fresh-set object exists before its fresh compile.')
        # The fresh set always reruns coqc. The compiler route keeps each new
        # object before Dune links the target to an equal cache entry.
        captured = Path(config['output']) / 'fresh-objects'
        started = time.time_ns()
        dune('fresh', fresh, DUNE_CACHE_CHECK_PROBABILITY='1', ZESU_FRESH_OBJECT_DIR=str(captured))
        receipt = public_fresh_receipt(build, fresh, captured, started)
        receipt.update(contexts_outside_closure=[c for c in contexts if c not in closure],
                       rebuilt_above_fresh=len(closure) - len(dependencies) - len(fresh))
        save(Path(config['output']) / 'PUBLIC-FRESH.json', receipt)
    elif name == 'negative':
        asyncio.run(negative_checks(config))
    elif name == 'wrappers':
        baseline = Path(config['baseline'])
        records = public_records(workspace, baseline, build)
        wrapper, artifact = wrapper_paths(workspace, out, build)
        if wrapper.exists():
            raise ValueError('The checker-owned wrapper already exists.')
        wrapper.parent.mkdir(parents=True)
        wrapper.write_text(WRAPPERS)
        save(out / 'protected-statements.json', records)
        reports = []
        # Selecting sources independently avoids treating generated dependencies as proof targets.
        for index, source in enumerate([workspace / p for p in sorted(set(PUBLIC.values()))] + [wrapper]):
            protected = [r for r in records if r['candidate_source'] == str(source)]
            result = asyncio.run(verification.verify(workspace, [source], 0, out / f'verify-{index}',
                timeout=COMPILE_SECONDS, admission_seconds=verification.ADMISSION_WAIT_SECONDS,
                protected_expectations=protected or None,
                mcp_launcher=workspace / 'tools/rocq_mcp_guarded.sh',
                compiler_launcher=workspace / 'tools/rocq_coqc_guarded.sh'))
            reports.append(result)
        compiled = reports[-1]['checks'][0]['compile_file']
        if compiled.get('output', '').splitlines() != ['Closed under the global context'] * 4:
            raise ValueError('The four typed wrappers lack empty assumption certificates.')
        retained = reports[-1]['checks'][0]
        if (Path(retained['private_artifact']) != artifact or
                digest(artifact) != retained['private_artifact_sha256']):
            raise ValueError('The scratch wrapper object differs from the checked mapping.')
        save(out / 'WRAPPERS.json', {'success': True, 'allowed_axioms': [], 'source': binding(wrapper),
             'object': binding(artifact), 'module': 'SoundnessGateWrappers',
             'Print_Assumptions': compiled['output'], 'verification_results': [binding(out / f'verify-{i}/RESULT.json') for i in range(4)]})
    elif name == 'coqchk':
        before = [binding(p) for p in sorted((build / 'default').rglob('*.vo'))]
        save(out / 'OBJECTS.json', before)
        recipe = json.loads((out / 'source-frozen/coqc_recipe.json').read_text())
        modules = sorted({'.'.join(Path(p).with_suffix('').parts) for p in PUBLIC.values()})
        wrapper, artifact = wrapper_paths(workspace, out, build)
        receipt = json.loads((out / 'WRAPPERS.json').read_text())
        if receipt['source'] != binding(wrapper) or receipt['object'] != binding(artifact):
            raise ValueError('The scratch wrapper changed before kernel checking.')
        argv = [shutil.which('coqchk'), *kernel_flags(recipe, workspace, build),
                '-Q', str(artifact.parent), '', *modules, 'SoundnessGateWrappers']
        save(out / 'COQCHK-ARGV.json', argv)
        with (out / 'coqchk.stdout').open('w') as stdout, (out / 'coqchk.stderr').open('w') as stderr:
            subprocess.run([str(workspace / 'tools/resource_guard.sh'), 'scope', 'soundness-coqchk', '--', *argv],
                           cwd=build / 'default', stdout=stdout, stderr=stderr, check=True)
        if [binding(p) for p in sorted((build / 'default').rglob('*.vo'))] != before:
            raise ValueError('A project object changed during coqchk.')
        save(out / 'COQCHK.json', {'success': True, 'unchanged_objects': len(before),
             'command': argv, 'stdout': binding(out / 'coqchk.stdout'), 'stderr': binding(out / 'coqchk.stderr')})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workspace', type=Path, default=Path.cwd())
    parser.add_argument('--output', type=Path, help='New directory below the workspace _build/agents.')
    parser.add_argument('--trace-source', type=Path, help='Optional source for exact manifest-bound traces.')
    parser.add_argument('--source-workspace', type=Path, help='Pinned external source checkout owner.')
    parser.add_argument('--fresh-contexts', action='store_true',
                        help='Also compile the four PUBLIC trust-context files without the Dune cache.')
    parser.add_argument('--stage', choices=('source', 'negative', 'wrappers', 'coqchk'), help=argparse.SUPPRESS)
    parser.add_argument('--config', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.stage:
        if not os.environ.get('ZESU_RUN_ID'):
            raise ValueError('A soundness stage requires its registered guard run.')
        stage(json.loads(args.config.read_text()), args.stage)
        return
    workspace = args.workspace.resolve()
    token = uuid.uuid4().hex
    out = (args.output or workspace / '_build/agents' / ('soundness-' + token)).resolve()
    if not out.is_relative_to(workspace / '_build/agents') or out.exists():
        raise ValueError('The output must be a fresh owned directory below _build/agents.')
    if not str(out).startswith('/home/'):
        raise ValueError('This gate requires an owned /home TMPDIR.')
    if git(workspace, 'status', '--porcelain', '--untracked-files=no').strip():
        raise ValueError('Commit the reviewed candidate before the release gate.')
    for tool in ('dune', 'coqc', 'coqchk', 'pet'):
        if not shutil.which(tool):
            raise ValueError('The pinned opam environment lacks ' + tool)
    for module in ('mcp', 'rocq_mcp', 'pytanque'):
        if importlib.util.find_spec(module) is None:
            raise ValueError('Use the MCP Python interpreter; missing module: ' + module)
    out.mkdir(parents=True, mode=0o700); (out / 'tmp').mkdir(mode=0o700)
    os.environ.update(TMPDIR=str(out / 'tmp'), PYTHONDONTWRITEBYTECODE='1',
        PYTHONHASHSEED='0',
        ZESU_PROOF_CACHE='off', DUNE_CACHE='disabled', ZESU_GATE_LIMIT='64G', ZESU_BATCH_LIMIT='64G',
        ZESU_GATE_MODULE_LIMIT_GIB='8', ZESU_MODULE_LIMIT_GIB='8')
    baseline = out / 'baseline'
    subprocess.run(['git', '-C', str(workspace), 'worktree', 'add', '--detach', str(baseline), BASELINE], check=True)
    for relative in (*PUBLIC_CONTEXTS, *set(PUBLIC.values())):
        if digest(workspace / relative) != digest(baseline / relative):
            raise ValueError('Protected source changed; review the trust boundary: ' + relative)
    prepare_sources(workspace, source_workspace=args.source_workspace)
    save(out / 'TRACE-INPUTS.json', stage_traces(workspace, args.trace_source))
    subprocess.run([sys.executable, '-B', 'tools/stock_zisk/selected/bind_traces.py', '--out',
                    'generated/isla-traces/stock-zisk/closure', '--function', 'alt_fl_alloc.free', '--trace-name', 'free'],
                   cwd=workspace, check=True)
    build = out / 'build'
    # Freeze the existing helpers and this script before the first admitted stage.
    frozen_tools = out / 'command-tools'
    subprocess.run(['cp', '-a', '--reflink=always', '--', str(workspace / 'tools'), str(frozen_tools)], check=True)
    frozen_script = frozen_tools / Path(__file__).name
    bindings = [binding(p) for p in sorted(frozen_tools.rglob('*'))
                if p.is_file() and p.suffix in {'.py', '.sh'}]
    bindings += [binding(workspace / p) for p in git(workspace, 'ls-files', '*.v').decode().splitlines()]
    bindings += [binding(workspace / 'tools' / p) for p in
                 ('correctness_gate.py', 'resource_guard.sh', 'rocq_mcp_guarded.sh', 'rocq_coqc_guarded.sh')]
    bindings += [binding(Path(shutil.which(p))) for p in ('dune', 'coqc', 'coqchk', 'pet')]
    config = dict(workspace=str(workspace), output=str(out), baseline=str(baseline), build=str(build),
                  mcp_python=sys.executable, token=token, bindings=bindings, fresh_contexts=args.fresh_contexts,
                  commit=git(workspace, 'rev-parse', 'HEAD').decode().strip())
    save(out / 'INPUTS.json', config)
    costs = {}
    try:
        for name in ('source', 'negative', 'wrappers', 'coqchk'):
            # Bookings come from measured peaks; the fence caps a compile and books an
            # unmeasured one. The closure has callers that peak at 10.9 GiB; the
            # negative and wrapper compiles peak at most 1.25 GiB.
            limit = {'source': '16', 'coqchk': '24'}.get(name, '8')
            os.environ.update(ZESU_GATE_MODULE_LIMIT_GIB=limit, ZESU_MODULE_LIMIT_GIB=limit)
            run_id = 'soundness-' + token + '-' + name
            command = [sys.executable, '-B', str(workspace / 'tools/run_registry.py'), 'run', '--id', run_id,
                '--kind', 'correctness-gate', '--owner', os.environ.get('COORD_AGENT', 'soundness'), '--',
                sys.executable, '-B', str(workspace / 'tools/correctness_gate.py'), 'run', '--target', 'check-iris',
                '--build-dir', str(build), '--', sys.executable, '-B', str(frozen_script),
                '--stage', name, '--config', str(out / 'INPUTS.json')]
            save(out / (name + '-COMMAND.json'), command)
            completed = subprocess.run(command, cwd=workspace)
            run = workspace / '_build/agents/correctness-gates' / run_id
            costs[name] = json.loads((run / 'RESULT.json').read_text())
            if not json.loads((run / 'CLOSURE.json').read_text())['all_owned_actors_closed'] or not json.loads((run / 'RELEASE.json').read_text())['released']:
                raise ValueError('A gate stage did not close and release.')
            for item in run.glob('*.json'):
                clone(item, out / (name + '-lifecycle') / item.name)
            completed.check_returncode()
            if name == 'source':
                for item in ('trace.csexp', 'coqc_recipe.json', 'coqc-ocamlpath.json', 'log.jsonl'):
                    clone(build / item, out / 'source-frozen' / item)
                os.environ['OCAMLPATH'] = check_record(json.loads((build / 'coqc-ocamlpath.json').read_text()), workspace, build)
                alias = workspace / '_build/default'
                if alias.is_symlink() and alias.resolve() == build / 'default':
                    pass
                elif not alias.exists() and not alias.is_symlink():
                    alias.symlink_to(os.path.relpath(build / 'default', alias.parent))
                else:
                    raise ValueError('Another private build owns _build/default.')
        save(out / 'RESULT.json', dict(success=True, scope='PUBLIC closure; not full check-iris',
            allowed_axioms=[], costs=costs, inputs=binding(out / 'INPUTS.json')))
    except BaseException as error:
        save(out / 'RESULT.json', dict(success=False, error=str(error), costs=costs))
        raise
    print(json.dumps(binding(out / 'RESULT.json')))


if __name__ == '__main__':
    main()
