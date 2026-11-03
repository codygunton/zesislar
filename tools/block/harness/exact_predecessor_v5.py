"""Validate the two released normalization controls before public admission.

This authority permits metadata-gated diagnostic execution only. It grants no
proof acceptance, supplier compatibility, or authority for another subject.
The caller retains the public registry, batch, scope, and lifecycle checks.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

POLICY = Path(__file__).parent / 'policies/EXACT-NORMALIZATION-PREDECESSOR-v5.json'
POLICY_SHA = 'f5327c2480c9dac297d4027bd6f3fd1433c817a180c3941001da1b81f4b71abe'
BASE = Path('/home/cody/zesislar')
PYTHON = '/home/cody/.local/share/uv/tools/rocq-mcp/bin/python'


def binding(path):
    path = Path(path).resolve()
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def read(reference):
    if binding(reference['path'])['sha256'] != reference['sha256']:
        raise ValueError('An exact control input changed: ' + reference['path'])
    return json.loads(Path(reference['path']).read_text())


def validate(case, output):
    authority = read({'path': str(POLICY), 'sha256': POLICY_SHA})
    if not authority['execution_enabled'] or case not in authority['cases']:
        raise ValueError('The exact control is not released.')
    row = authority['cases'][case]
    spec = read(row['spec'])
    for reference in [authority['client'], *spec['bindings']]:
        if binding(reference['path'])['sha256'] != reference['sha256']:
            raise ValueError('An exact control input changed: ' + reference['path'])
    for key in ['claim_bytes', 'physical_fence_bytes', 'subject', 'helper', 'identity']:
        if spec[key] != row[key]:
            raise ValueError('The exact control boundary differs: ' + key)
    if spec['client'] != authority['client'] or spec['CPU_policy'] != 'unlimited':
        raise ValueError('The exact control client or CPU policy differs.')
    support = read(spec['support_READY'])
    compiler = support['effective_compiler_version']['compiler']
    toolchain = [compiler, *[ref for ref in support['bindings']
                            if ref['path'] == '/home/cody/islaris/_opam/bin/coqdep']]
    if len(toolchain) != 2 or compiler['path'] != '/home/cody/islaris/_opam/bin/coqc':
        raise ValueError('The exact control compiler boundary differs.')
    for reference in toolchain:
        if binding(reference['path']) != reference:
            raise ValueError('An exact control toolchain input changed.')
    original = read(spec['original_export'])
    goals = original['kernel_groups']['goals']
    selected = goals[1 if case == 'predecessor' else 0]
    identity = spec['identity']
    target = hashlib.sha256(selected['ty'].encode()).hexdigest()
    context = hashlib.sha256(json.dumps(selected['hyps'], sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    if (target != identity['kernel_target_sha256'] or
            context != identity['ordered_kernel_hypotheses_sha256'] or
            len(selected['hyps']) != identity['context_entries'] or
            len(goals) != spec['original_groups']['active'] or
            any(original[key] for key in ['stack', 'shelf', 'given_up'])):
        raise ValueError('The original kernel identity differs.')
    if case == 'predecessor':
        if spec['prefix'] or spec['identity_from'] != 'start' or len(goals) != 2:
            raise ValueError('The predecessor must preserve its initial identity gate.')
        packet = read(spec['replay_packet'])
        def references(value):
            if isinstance(value, dict):
                if set(value) >= {'path', 'sha256'}:
                    yield value
                for child in value.values():
                    yield from references(child)
            elif isinstance(value, list):
                for child in value:
                    yield from references(child)
        for reference in references(packet):
            if binding(reference['path'])['sha256'] != reference['sha256']:
                raise ValueError('A replay dependency changed.')
    else:
        prefix = read(spec['preserved_prefix'])
        if spec['prefix'] != prefix['steps'] or len(spec['prefix']) != 10:
            raise ValueError('The exact ten-step prefix differs.')
    output = Path(output).absolute()
    if output.exists() or output.is_symlink():
        raise ValueError('The exact control output already exists.')
    if output.parent.resolve() != Path(row['spec']['path']).parent.resolve():
        raise ValueError('The output leaves the released control directory.')
    client = [PYTHON, '-B', authority['client']['path'], '--spec', row['spec']['path'],
              '--spec-sha256', row['spec']['sha256'], '--output', str(output)]
    tools = BASE / '.worktrees' / ('shared-block-' + row['public_guard_pin']) / 'tools'
    for path in [tools / 'run_registry.py', tools / 'resource_guard.sh']:
        if not path.is_file():
            raise ValueError('The released public guard is absent.')
    argv = [PYTHON, '-B', str(tools / 'run_registry.py'), 'run', '--id', row['registry_id'],
            '--kind', 'diagnostic', '--owner', 'worker-build-2', '--',
            str(tools / 'resource_guard.sh'), 'batch', row['guard_name'], '--',
            str(tools / 'resource_guard.sh'), 'scope', row['guard_name'], '--',
            PYTHON, '-B', str(Path(__file__).resolve()), '--case', case,
            '--output', str(output), '--inside-guard']
    return {'schema': 'scratch.exact-normalization-command.v1', 'case': case,
            'authority': binding(POLICY), 'validator': binding(__file__),
            'spec': row['spec'], 'client': authority['client'], 'client_argv': client,
            'toolchain': toolchain,
            'argv': argv, 'environment': row['environment'],
            'claim_bytes': row['claim_bytes'], 'physical_fence_bytes': row['physical_fence_bytes'],
            'fresh_canonical_projection_required': True,
            'final_acceptance_requires': row['final_acceptance_requires'], 'proof_acceptance': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', required=True, choices=['predecessor', 'resource023'])
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--inside-guard', action='store_true')
    args = parser.parse_args()
    command = validate(args.case, args.output)
    if not args.inside_guard:
        print(json.dumps(command, indent=2))
        return 0
    if any(os.environ.get(key) != value for key, value in command['environment'].items()):
        raise ValueError('The admitted exact control environment differs.')
    code = subprocess.run(command['client_argv'], check=False).returncode
    # The public guard and registry close actors and release claims after this return.
    # This record binds execution inputs only. It does not assert their closure.
    result = {'command': command, 'client_returncode': code, 'proof_acceptance': False,
              'lifecycle_acceptance_pending': True}
    for key in ['authority', 'validator', 'spec', 'client']:
        if binding(command[key]['path']) != command[key]:
            raise ValueError('A final exact control input changed.')
    for reference in command['toolchain']:
        if binding(reference['path']) != reference:
            raise ValueError('A final exact control toolchain input changed.')
    if args.output.is_dir():
        (args.output / 'AUTHORITY-BINDING.json').write_text(json.dumps(result, indent=2) + '\n')
    return code


if __name__ == '__main__':
    raise SystemExit(main())
