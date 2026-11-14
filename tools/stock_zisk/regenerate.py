#!/usr/bin/env python3
"""Regenerate every ELF-bound stock artifact by one command.

Run from the checkout root after `build.py` built a new ELF into DIR, or with
no `--built` to verify that the current artifacts regenerate unchanged:

  python3 tools/stock_zisk/regenerate.py [--built DIR] [--keep-object]

Order: move the recipe to the ELF; render the layout constants; rebuild the
platform snapshot and its smoke traces; rerun the inventory generators;
render Machine.v and re-extract the region-policy windows; generate and bind
each missing trace group; repeat the generators until the artifact identity
is stable; re-pin the design callers to the inventory; run every check. A trace
group regenerates only when the recipe lacks it, and its output directory
must then be absent. The test-trace fixture check reports fixtures that need
a new address or new traces; this tool does not choose fixtures.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
BUILD = 'build/stock-zisk'
RECIPE = BUILD + '/build-recipe.json'
TRACES = 'generated/isla-traces/stock-zisk'
PY = sys.executable
TRACE_ONLY = {
    'eql': ('eql-trace-input.json', 'eql-policy', 'eql.raw.dump', 'ZesuSsz.Stock.Eql'),
    'decodeItemRegions': ('decodeItem-regions-trace-input.json', 'decodeItem-regions-policy',
                          'decodeItem.raw.dump', 'ZesuSsz.Stock.DecodeItemRegions'),
}


def run(label, command, **options):
    started = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, **options)
    print(f'[regenerate] {label}: exit {result.returncode} in {time.monotonic() - started:.1f} s', flush=True)
    if result.returncode:
        raise SystemExit(f'{label} failed')


def recipe():
    return json.loads((ROOT / RECIPE).read_text())


def generators():
    run('inventory', [PY, 'tools/stock_zisk/closure.py', '--elf', BUILD + '/zesu-zisk.elf', '--object',
                      recipe()['inputs']['object']['path'], '--manifest', RECIPE,
                      '--out', BUILD + '/inventory.json', '--publish'])
    run('runtime inventory', [PY, 'tools/stock_zisk/runtime_inventory.py', '--manifest', RECIPE,
                              '--out', BUILD + '/runtime-inventory.json'])
    run('static sites', [PY, 'tools/stock_zisk/static_sites/collect.py'])
    run('rebind', [PY, 'tools/stock_zisk/recipe.py', 'rebind'])


def sha(path):
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()


def trace_commands(group):
    if group == 'decodeItem':
        return [[PY, 'tools/stock_zisk/platform/traces.py', '--manifest', RECIPE, '--dump',
                 BUILD + '/decodeItem.raw.dump', '--out', TRACES + '/decodeItem',
                 '--coqdir', 'ZesuSsz.Stock.DecodeItem', '--jobs', '6']]
    if group == 'closure':
        return [[PY, 'tools/stock_zisk/platform/traces.py', '--closure', '--indexes', '--manifest', RECIPE,
                 '--out', TRACES + '/closure', '--coqdir', 'ZesuSsz.Stock.Closure', '--jobs', '6']]
    descriptor, policy, dump, coqdir = TRACE_ONLY[group]
    policy = BUILD + '/' + policy
    source_map = json.loads((ROOT / policy / 'PATH-MAP.json').read_text())
    guard = [str(ROOT / 'tools/resource_guard.sh'), 'batch', group + '-traces', '--']
    return [guard + [PY, 'tools/stock_zisk/platform/traces.py', '--trace-only',
                     '--manifest', BUILD + '/' + descriptor, '--dump', policy + '/' + dump,
                     '--out', TRACES + '/' + group, '--coqdir', coqdir, '--jobs', '6',
                     '--per-load-regions', policy + '/regions.json.gz', '--per-load-regions-sha256',
                     source_map['archives']['regions.json.gz']['payload_sha256'],
                     '--region-source-map', policy + '/PATH-MAP.json',
                     '--region-source-map-sha256', sha(policy + '/PATH-MAP.json')]]


def current_fragment(group, fragment):
    """A finished generation for this ELF and platform resumes without regenerating."""
    if fragment['traces'].get('elf_sha256') != recipe()['elf_sha256']:
        return False
    snapshot = sha(BUILD + '/platform/riscv64-zisk.ir')
    if group in TRACE_ONLY:
        return fragment['traces']['input_hashes'].get('platform_snapshot') == snapshot
    coverage = json.loads((ROOT / TRACES / group / 'coverage.json').read_text())
    return coverage.get('platform_snapshot_sha256') == snapshot


def traces():
    missing = [group for group in ('decodeItem', 'closure', *TRACE_ONLY) if group not in recipe()['traces']]
    for group in missing:
        fragment = ROOT / TRACES / group / 'manifest-fragment.json'
        if fragment.exists() and current_fragment(group, json.loads(fragment.read_text())):
            print(f'[regenerate] {group} traces match the selected ELF and platform; binding them', flush=True)
            continue
        if (ROOT / TRACES / group).exists():
            raise SystemExit(f'{TRACES}/{group} belongs to another recipe; move it aside to regenerate it.')
        for command in trace_commands(group):
            run(group + ' traces', command, env=dict(os.environ, ZESU_BATCH_LIMIT='8G'))
        run(group + ' fragment', [PY, 'tools/stock_zisk/platform/bind_traces.py', '--out',
                                  TRACES + '/' + group, '--trace-name', group])
    if missing:
        run('merge traces', [PY, 'tools/stock_zisk/recipe.py', 'merge-traces', *missing])
    return missing


def platform_current():
    """The platform build and smoke reports record timings; rerun them only for a changed input."""
    report = json.loads((ROOT / BUILD / 'platform/build-report.json').read_text())
    smoke = json.loads((ROOT / BUILD / 'platform/smoke/report.json').read_text())
    inputs = recipe()['inputs']
    return (report['adapter_source_sha256'] == sha('tools/stock_zisk/platform/adapter.sail')
            and report['snapshot_sha256'] == sha(BUILD + '/platform/riscv64-zisk.ir')
            and report['base_sha256'] == hashlib.sha256(Path(inputs['platform/base_snapshot']['path'])
                                                         .read_bytes()).hexdigest()
            and smoke['snapshot_sha256'] == report['snapshot_sha256']
            and smoke['config_sha256'] == sha('ZesuSsz/riscv64_zesu.toml')
            and inputs['platform/tools/stock_zisk/platform/smoke.py']['sha256']
            == sha('tools/stock_zisk/platform/smoke.py'))


def refresh_design_pins(design, before, after):
    """Block fixtures pin their control-flow source by hash; the pin follows the artifact identity."""
    if before == after:
        return
    for path in sorted((ROOT / 'tools/block/fixtures').glob('*.json')):
        fixture = json.loads(path.read_text())
        if isinstance(fixture, dict) and fixture.get('design') == {'path': design, 'sha256': before}:
            path.write_text(path.read_text().replace(before, after))
            print(f'[regenerate] {path.relative_to(ROOT)} pins the regenerated design table', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--built', type=Path, help='a build.py output directory with the new ELF')
    parser.add_argument('--keep-object', action='store_true')
    args = parser.parse_args()
    if args.built:
        rebase = [PY, 'tools/stock_zisk/recipe.py', 'rebase', '--built', str(args.built.resolve())]
        run('rebase', rebase + (['--keep-object'] if args.keep_object else []))
    inventory = BUILD + '/inventory.json'
    inventory_before = sha(inventory)
    run('layout', [PY, 'tools/stock_zisk/layout.py'])
    if platform_current():
        print('[regenerate] platform snapshot and smoke traces are current; their reports keep their measurements')
    else:
        run('platform', [PY, 'tools/stock_zisk/platform/build.py', '--out', BUILD + '/platform'])
        run('platform smoke', [PY, 'tools/stock_zisk/platform/smoke.py'])
        run('platform fragment', [PY, 'tools/stock_zisk/platform/fragment.py'])
    run('rehash', [PY, 'tools/stock_zisk/recipe.py', 'rehash'])
    generators()
    run('machine map', [PY, 'tools/stock_zisk/machine_map/generate.py', '--build', BUILD])
    run('region windows', [PY, 'tools/stock_zisk/platform/region_windows.py', '--write'])
    for _ in range(3):
        before = recipe()['artifact_identity']
        traces()
        run('rehash', [PY, 'tools/stock_zisk/recipe.py', 'rehash'])
        if recipe()['invalidated_derived']:
            generators()
        if recipe()['artifact_identity'] == before:
            break
    else:
        raise SystemExit('The artifact identity did not settle in three rounds.')
    run('selected free binding', [PY, 'tools/stock_zisk/selected/bind_traces.py', '--out',
                                  TRACES + '/closure', '--function', 'alt_fl_alloc.free', '--trace-name', 'free'])
    refresh_design_pins(inventory, inventory_before, sha(inventory))
    checks = [('stock check', [PY, 'tools/stock_zisk/build.py', '--check', '--out', BUILD]),
              ('machine map check', [PY, 'tools/stock_zisk/machine_map/generate.py', '--build', BUILD, '--check']),
              ('layout check', [PY, 'tools/stock_zisk/layout.py', '--check']),
              ('region windows check', [PY, 'tools/stock_zisk/platform/region_windows.py']),
              ('design callers check', [PY, 'tools/block/render_design_callers.py', '--check']),
              ('test-trace fixtures', [PY, 'tools/stock_zisk/check_test_traces.py'])]
    failed = []
    for label, command in checks:
        if subprocess.run(command, cwd=ROOT).returncode:
            failed.append(label)
    if failed:
        raise SystemExit('Regenerated, but these checks fail: ' + ', '.join(failed))
    print('[regenerate] every ELF-bound artifact regenerated and checked')


if __name__ == '__main__':
    main()
