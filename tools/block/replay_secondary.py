#!/usr/bin/env python3
"""Replay only diagnostics bound to immutable primary timeout evidence."""
import argparse
import asyncio
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path
import time

import native_diagnostics


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def jobs(primary, index):
    result = []
    for block in primary['blocks']:
        if 'automation-search-timeout' not in block['outcomes']:
            continue
        sources = []
        for previous in block['secondary_diagnostics']:
            source = Path(previous['source']).resolve()
            archived = next(record for name, record in index.items()
                            if Path(name).resolve() == source)
            if digest(source) != archived['sha256']:
                raise ValueError('The immutable primary source changed: ' + str(source))
            capture_path = source.with_suffix('.mcp.json')
            captured = next(record for name, record in index.items()
                            if Path(name).resolve() == capture_path)
            if digest(capture_path) != captured['sha256']:
                raise ValueError('The immutable primary capture changed')
            sources.append({'path': str(source), 'sha256': archived['sha256'],
                            'primary_capture': {'path': str(capture_path), 'sha256': captured['sha256']}})
        result.append({'entry': block['entry'], 'primary_outcomes': block['outcomes'], 'sources': sources})
    return result


async def run_block(job, options):
    rows = []
    for source in job['sources']:
        path = Path(source['path'])
        started = time.monotonic()
        diagnostic = await native_diagnostics.diagnose(path, options)
        if digest(path) != source['sha256'] or digest(source['primary_capture']['path']) != source['primary_capture']['sha256']:
            raise ValueError('The primary evidence changed during diagnosis')
        output = Path(options['out']) / (path.stem + '.json')
        output.write_text(json.dumps(diagnostic, indent=2) + '\n')
        rows.append({'source': source, 'diagnostic': str(output), 'sha256': digest(output),
                     'elapsed_seconds': time.monotonic() - started, 'stop': diagnostic.get('stop'),
                     'first_residual': diagnostic.get('first_residual'),
                     'last_successful_state': diagnostic.get('last_successful_state'),
                     'native_step_attempts': sum(row['label'] == 'zesu_liAStep' for row in diagnostic['steps']),
                     'pet_peak_mib': diagnostic.get('diagnostic', {}).get('memory', {}).get('peak_pet_rss_mb')})
    return {'entry': job['entry'], 'primary_outcomes': job['primary_outcomes'], 'diagnostics': rows}


def worker(arguments):
    job, options = arguments
    return asyncio.run(run_block(job, options))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--primary', type=Path, required=True)
    parser.add_argument('--archive-index', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--source', type=Path, action='append', default=[])
    parser.add_argument('--complete-goals', action='store_true')
    parser.add_argument('--jobs', type=int, default=6)
    parser.add_argument('--seconds', type=int, default=300)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 6 or not 1 <= args.seconds <= 300:
        parser.error('Diagnostics permit at most six workers and 300 seconds')
    primary = json.loads(args.primary.read_text())
    index = json.loads(args.archive_index.read_text())
    raw = primary['raw_report']
    if digest(raw['archive_path']) != raw['sha256']:
        raise ValueError('The immutable raw primary report changed')
    selected = jobs(primary, index)
    if args.source:
        requested = {str(p.resolve()) for p in args.source}
        for job in selected:
            job['sources'] = [source for source in job['sources'] if source['path'] in requested]
        selected = [job for job in selected if job['sources']]
        if {source['path'] for job in selected for source in job['sources']} != requested:
            raise ValueError('A requested source is not a frozen primary-timeout source')
    args.out.mkdir(parents=True, exist_ok=True)
    options = {'workspace': str(Path.cwd()), 'out': str(args.out.resolve()),
               'mcp_command': str(Path('tools/rocq_mcp_guarded.sh').resolve()), 'seconds': args.seconds, 'complete_goals': args.complete_goals}
    inputs = {str(args.primary): digest(args.primary), str(args.archive_index): digest(args.archive_index),
              str(Path(__file__).resolve()): digest(__file__),
              str(Path(native_diagnostics.__file__).resolve()): digest(native_diagnostics.__file__)}
    if args.complete_goals:
        for name in ('complete_goals_mcp.py', 'complete_goals_mcp.sh'):
            p = Path(__file__).with_name(name).resolve()
            inputs[str(p)] = digest(p)
        from rocq_mcp import server
        from rocq_mcp import interactive
        import pytanque.client, pytanque.protocol
        for module in (server, interactive, pytanque.client, pytanque.protocol):
            inputs[str(Path(module.__file__).resolve())] = digest(module.__file__)
    started = time.monotonic()
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        blocks = list(pool.map(worker, [(job, options) for job in selected]))
    report = {'label': 'Secondary first-goal diagnostics only; immutable primary outcomes retained',
              'inputs': inputs, 'raw_primary_report': raw, 'workers': args.jobs,
              'diagnostic_budget_seconds': args.seconds, 'memory_limit_gib': 6,
              'selector_policy': '1: zesu_liAStep.; record every returned goal',
              'elapsed_seconds': time.monotonic() - started, 'blocks': blocks,
              'instruction_closures': 0, 'contract_closures': 0}
    path = args.out/'report.json'
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'report': str(path), 'sha256': digest(path), 'blocks': len(blocks)}))


if __name__ == '__main__':
    main()
