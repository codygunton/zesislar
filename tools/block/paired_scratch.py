#!/usr/bin/env python3
"""Compare scratch compiler CPU with interleaved samples under normal load.

The original eleven entries keep their sampling rule. Promotion entries use
three samples per arm, except 6960, which uses five interleaved pairs. Both
698c branches require explicit Literal or ShortString selectors. R4 adds the
remaining eight hand blocks. Promotion A/A floors require a completed matching
comparison with baseline CPU below 300 seconds. Longer entries use a 10% limit.
"""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import statistics
import subprocess
import time

import scratch_block


LARGE_BLOCKS = {'6974', '6a08', '6aa8'}
PROMOTED_ENTRIES = {'6960', '6a38', '6ad8', '698cliteral', '698cshortstring', '697c'}
# These entries join the timing set with R4, not with earlier releases.
R4_ENTRIES = {'69e8', '69b0', '6ae0', '6a40', '6b08', '6a78', '6a24', '6ac4'}


def entry_id(pc):
    match = re.fullmatch(r'(?:0x)?(?:800d)?([0-9a-f]{4}(?:literal|shortstring)?)', pc.lower())
    if not match:
        raise ValueError('Use a decodeItem PC, optionally followed by Literal or ShortString.')
    return match[1]


def sample_count(pc):
    entry = entry_id(pc)
    return 3 if entry in LARGE_BLOCKS | (PROMOTED_ENTRIES - {'6960'}) | R4_ENTRIES else 5



def promotion_policy(pc, baseline_cpu):
    """Retain the new timing rule without changing the original eleven-entry rule."""
    entry = entry_id(pc)
    if entry not in PROMOTED_ENTRIES | R4_ENTRIES:
        return None
    short = baseline_cpu < 300
    return dict(first_release=('R4' if entry in R4_ENTRIES | {'6960'} else
                              'R1' if entry in {'6a38', '6ad8'} else 'R2-R3'),
                aa_floor_required=short, cpu_boundary_seconds=300,
                limit_rule='max(10%, twice the A/A floor)' if short else '10%',
                fixed_limit=None if short else .1,
                closure_check='required project gates; this run adds timing')


def check_noise_reference(pcs, reference, sources, setup):
    """Refuse new-entry floors without a matching sub-300-second baseline."""
    for pc in pcs:
        if entry_id(pc) not in PROMOTED_ENTRIES | R4_ENTRIES:
            continue
        if reference is None or reference.get('status') != 'complete' or reference.get('mode') != 'compare':
            raise ValueError('Promotion noise requires a completed comparison reference.')
        block = reference.get('blocks', {}).get(pc, {})
        cpu = block.get('median_cpu_A')
        if not isinstance(cpu, (int, float)) or not math.isfinite(cpu) or not 0 < cpu < 300:
            raise ValueError('Promotion A/A floors require baseline CPU below 300 seconds: ' + pc)
        old_source = reference.get('sources', {}).get(pc, {})
        for key in ('statement_sha256', 'source_A_sha256'):
            if old_source.get(key) != sources[pc][key]:
                raise ValueError('The noise reference uses a different baseline source: ' + pc)
        if reference.get('compiler_setups', {}).get('A') != setup:
            raise ValueError('The noise reference uses a different baseline compiler setup.')

def ratios(pairs):
    values = [pair['B']['cpu_seconds'] / pair['A']['cpu_seconds'] for pair in pairs]
    median_a = statistics.median(pair['A']['cpu_seconds'] for pair in pairs)
    median_b = statistics.median(pair['B']['cpu_seconds'] for pair in pairs)
    return dict(paired_ratios=values, median_ratio=statistics.median(values),
                median_cpu_A=median_a, median_cpu_B=median_b, median_cpu_ratio=median_b / median_a,
                median_absolute_deviation=statistics.median(abs(value - 1) for value in values),
                absolute_median_deviation=abs(statistics.median(values) - 1))


def statement(module):
    name = 'DesignedBoundary_' + module.stem.removeprefix('Block')
    proofs = [proof for proof in scratch_block.parse_module(module) if proof.name == name]
    if len(proofs) != 1:
        raise ValueError('The source must contain one selected boundary statement.')
    proof = proofs[0]
    return ''.join(module.read_text().splitlines(keepends=True)[proof.declaration_line:proof.proof_line])


def source_scope(args):
    rows = {}
    for pc in args.pcs:
        original = scratch_block.find_block(args.workspace, pc)
        changed = scratch_block.find_block(args.changed_workspace, pc)
        declaration = statement(original)
        if declaration != statement(changed):
            raise ValueError('The two arms have different boundary statements: ' + pc)
        rows[pc] = dict(statement_sha256=hashlib.sha256(declaration.encode()).hexdigest(),
                        source_A=str(original), source_B=str(changed),
                        source_A_sha256=hashlib.sha256(original.read_bytes()).hexdigest(),
                        source_B_sha256=hashlib.sha256(changed.read_bytes()).hexdigest())
    return rows


def compiler_setup(build, recipe_path=None, ocamlpath=None):
    recipe_path = (recipe_path or build / 'coqc_recipe.json').resolve()
    data = recipe_path.read_bytes()
    recipe = json.loads(data)
    working = Path(recipe['working_dir'])
    if not working.is_absolute() or not working.is_dir():
        raise ValueError('The compiler working directory must exist and be absolute.')
    command = recipe['command']
    project = []
    for index, flag in enumerate(command[:-2]):
        if flag in ('-R', '-Q') and command[index + 2] == 'ZesuSsz':
            path = Path(command[index + 1])
            project.append((path if path.is_absolute() else working / path).resolve())
    if len(project) != 1 or not project[0].is_dir():
        raise ValueError('The recipe requires one existing ZesuSsz object directory.')
    if ocamlpath is None:
        local = build / 'install/default/lib'
        if not local.is_dir():
            raise ValueError('This build requires an explicit OCAMLPATH.')
        ocamlpath = str(local) + ':/home/cody/islaris/_opam/lib'
    directories = ocamlpath.split(':')
    if any(not path or not Path(path).is_absolute() or not Path(path).is_dir() for path in directories):
        raise ValueError('Every OCAMLPATH directory must exist and be absolute.')
    if not any((Path(path) / 'zesu-signature-gates/plugin/signature_gates_plugin.cmxs').is_file()
               for path in directories):
        raise ValueError('OCAMLPATH does not contain the prepared signature plugin.')
    return dict(recipe=str(recipe_path), recipe_sha256=hashlib.sha256(data).hexdigest(),
                working_dir=str(working), project_objects=str(project[0]), ocamlpath=ocamlpath)


def run_pairs(pcs, sample, save, load=os.getloadavg):
    report = dict(status='running', load_policy='normal load; no quiet invalidation', blocks={})
    save(report)
    for pc in pcs:
        count = sample_count(pc)
        block = dict(samples_per_arm=count, pairs=[])
        report['blocks'][pc] = block
        for number in range(1, count + 1):
            pair = dict(number=number, load_average_start=list(load()), complete=False)
            block['pairs'].append(pair)
            save(report)
            for arm in ('A', 'B'):
                def retain(row):
                    pair[arm] = row
                    save(report)
                row = sample(pc, arm, number, retain)
                pair[arm] = row
                save(report)
                cpu = row.get('cpu_seconds')
                if (row['exit_code'] != 0 or not row['measurement_complete']
                        or not isinstance(cpu, (int, float)) or not math.isfinite(cpu) or cpu <= 0):
                    pair['load_average_end'] = list(load())
                    report['status'] = 'sample-failed'
                    save(report)
                    return report
            pair.update(load_average_end=list(load()), complete=True)
            save(report)
        block.update(ratios(block['pairs']))
        block['method'] = 'median CPU ratio' if count == 3 else 'median of paired ratios'
        block['comparison_ratio'] = block['median_cpu_ratio'] if count == 3 else block['median_ratio']
        policy = promotion_policy(pc, block['median_cpu_A'])
        if policy is not None:
            block['timing_policy'] = policy
        for arm in ('A', 'B'):
            block['all_' + arm + '_no_goals'] = all(pair[arm]['outcome'] == 'no goals' for pair in block['pairs'])
        save(report)
    report['status'] = 'complete'
    save(report)
    return report


def process_identity(pid):
    try:
        fields = (Path('/proc') / str(pid) / 'stat').read_text().rsplit(') ', 1)[1].split()
        return None if fields[0] == 'Z' else fields[19]
    except (FileNotFoundError, ProcessLookupError):
        return None


def watched_sample(pc, arm, number, retain, args):
    workspace = args.workspace if arm == 'A' else args.changed_workspace
    build = args.build_dir if arm == 'A' else args.changed_build_dir
    extra = args.extra if arm == 'B' and args.mode == 'compare' else None
    setup = args.compiler_setups[arm]
    for path, expected in args.tool_versions.items():
        if hashlib.sha256(Path(path).read_bytes()).hexdigest() != expected:
            raise ValueError('A frozen compiler helper changed before the sample.')
    module = scratch_block.find_block(workspace, pc)
    if hashlib.sha256(module.read_bytes()).hexdigest() != args.sources[pc]['source_' + arm + '_sha256']:
        raise ValueError('A selected source changed before the sample.')
    if args.extra and hashlib.sha256(args.extra.read_bytes()).hexdigest() != args.extra_hash:
        raise ValueError('The local additions changed before the sample.')
    if hashlib.sha256(Path(setup['recipe']).read_bytes()).hexdigest() != setup['recipe_sha256']:
        raise ValueError('A compiler recipe changed before the sample.')
    label = f'{args.writer_prefix}-{pc}-{arm}-{number}'
    command = ['ai-coord', 'watch', '--label', label, '--', 'opam', 'exec',
               '--switch=/home/cody/islaris', '--', 'env', 'ZESU_WRITER_ID=' + label,
               'AGENT_BUILD_DIR=' + str(build), 'OCAMLPATH=' + setup['ocamlpath'],
               'ZESU_SCRATCH_RECIPE=' + setup['recipe'],
               'ZESU_SCRATCH_RECIPE_SHA256=' + setup['recipe_sha256'],
               str(Path(__file__).with_name('scratch_block.sh').resolve()), pc]
    if extra:
        command.append(str(extra))
    command.extend(['--source-workspace', str(workspace)])
    launched = subprocess.check_output(command, cwd=workspace, text=True)
    match = re.search(r'\(runner pid (\d+)\); output: ([^\n]+)', launched)
    if not match:
        raise ValueError('The watcher did not return its process and log path.')
    pid, log = int(match[1]), Path(match[2])
    row = dict(log=str(log), writer=label, watcher_pid=pid, command=command,
               cpu_seconds=None, measurement_complete=False, exit_code=None)
    retain(row)
    start = process_identity(pid)
    while start is not None and process_identity(pid) == start:
        time.sleep(1)
    try:
        text = log.read_text()
        source = Path(next(line.split('=', 1)[1] for line in text.splitlines()
                           if line.startswith('scratch_source=')))
        row['source'] = str(source)
        if not source.resolve().is_relative_to((build / 'scratch-blocks').resolve()):
            raise ValueError('The scratch source is outside the selected build directory.')
        expected = scratch_block.scratch_source(module, extra.read_text() if extra else '')
        if source.read_text() != expected:
            raise ValueError('The scratch source changed the statement or native body.')
        compiler = source.parent / 'compiler.json'
        row['compiler'] = str(compiler)
        record = json.loads(compiler.read_text())
        row.update(cpu_seconds=record['cpu_seconds'], peak_rss_kib=record['peak_rss_kib'],
                   measurement_complete=record['measurement_complete'], exit_code=record['exit_code'],
                   outcome='no goals' if 'No more goals.' in text else 'residual')
    except (OSError, ValueError, StopIteration, KeyError) as error:
        row['error'] = str(error) or type(error).__name__
    return row


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('pcs', nargs='+')
    parser.add_argument('--mode', choices=('noise', 'compare'), required=True)
    parser.add_argument('--workspace', type=Path, required=True)
    parser.add_argument('--build-dir', type=Path, required=True)
    parser.add_argument('--changed-workspace', type=Path)
    parser.add_argument('--changed-build-dir', type=Path)
    parser.add_argument('--recipe', type=Path)
    parser.add_argument('--changed-recipe', type=Path)
    parser.add_argument('--ocamlpath')
    parser.add_argument('--changed-ocamlpath')
    parser.add_argument('--extra', type=Path)
    parser.add_argument('--prior-results', type=Path)
    parser.add_argument('--noise-reference', type=Path,
                        help='Completed comparison for promotion A/A floors below 300 CPU seconds.')
    parser.add_argument('--writer-prefix', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(argv)
    args.workspace = args.workspace.resolve()
    args.build_dir = args.build_dir.resolve()
    args.changed_workspace = (args.changed_workspace or args.workspace).resolve()
    args.changed_build_dir = (args.changed_build_dir or args.build_dir).resolve()
    if args.extra:
        args.extra = args.extra.resolve()
    if not re.fullmatch(r'[A-Za-z0-9._-]+', args.writer_prefix):
        parser.error('The writer prefix contains an invalid character.')
    if args.output.exists():
        parser.error('The result file already exists.')
    try:
        tools = Path(__file__).resolve().parents[1]
        args.tool_versions = {str(tools / path): hashlib.sha256((tools / path).read_bytes()).hexdigest()
                              for path in ['block/paired_scratch.py', 'block/scratch_block.py',
                                           'block/scratch_block.sh', 'block/coqc_primary.py',
                                           'coqc_scratch.sh', 'coqc_recipe.py']}
        for pc in args.pcs:
            entry_id(pc)
        if len({entry_id(pc) for pc in args.pcs}) != len(args.pcs):
            raise ValueError('The entry list contains a duplicate boundary.')
        args.sources = source_scope(args)
        args.extra_hash = hashlib.sha256(args.extra.read_bytes()).hexdigest() if args.extra else None
        args.compiler_setups = {'A': compiler_setup(args.build_dir, args.recipe, args.ocamlpath),
                                'B': compiler_setup(args.changed_build_dir, args.changed_recipe,
                                                    args.changed_ocamlpath or args.ocamlpath)}
        prior = json.loads(args.prior_results.read_text()) if args.prior_results else None
        noise_bytes = args.noise_reference.read_bytes() if args.noise_reference else None
        noise_reference = json.loads(noise_bytes) if noise_bytes else None
        if args.mode == 'noise':
            check_noise_reference(args.pcs, noise_reference, args.sources, args.compiler_setups['A'])
        elif args.noise_reference:
            raise ValueError('Use --noise-reference only for A/A floors.')
        heads = {arm: subprocess.check_output(['git', '-C', str(workspace), 'rev-parse', 'HEAD'], text=True).strip()
                 for arm, workspace in [('A', args.workspace), ('B', args.changed_workspace)]}
        if args.mode == 'noise' and (args.extra or args.workspace != args.changed_workspace
                                     or args.build_dir != args.changed_build_dir
                                     or args.compiler_setups['A'] != args.compiler_setups['B']):
            raise ValueError('Noise pairs require the same plain source, build, recipe, and findlib path.')
        if args.workspace != args.changed_workspace and (
                args.compiler_setups['A']['project_objects'] == args.compiler_setups['B']['project_objects']):
            raise ValueError('Different workspaces require distinct project object directories.')
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        parser.error(str(error))
    args.output.parent.mkdir(parents=True, exist_ok=True)

    def save(report):
        report.update(mode=args.mode, workspace_A=str(args.workspace), workspace_B=str(args.changed_workspace),
                      workspace_heads=heads, extra=str(args.extra) if args.extra else None,
                      extra_sha256=args.extra_hash, sources=args.sources, compiler_setups=args.compiler_setups,
                      prior_results=prior, floor_definition='median(abs(B/A - 1))',
                      tool_versions=args.tool_versions,
                      noise_reference=str(args.noise_reference) if args.noise_reference else None,
                      noise_reference_sha256=hashlib.sha256(noise_bytes).hexdigest() if noise_bytes else None)
        args.output.write_text(json.dumps(report, indent=2) + '\n')

    try:
        report = run_pairs(args.pcs, lambda *row: watched_sample(*row, args), save)
    except (OSError, ValueError, IndexError, subprocess.CalledProcessError, StopIteration) as error:
        report = json.loads(args.output.read_text())
        report.update(status='runner-error', error=str(error))
        save(report)
        return 1
    return 0 if report['status'] == 'complete' else 1


if __name__ == '__main__':
    raise SystemExit(main())
