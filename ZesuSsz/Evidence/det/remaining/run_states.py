#!/usr/bin/env python3
"""Prepare the 85 remaining states with the pinned entry choices.

Run from the repository root. Pass --entries with the canonical table.
The default prepares probes. --ingest-mcp reads MCP results from the build
directory. --infer runs entry probes through the guarded scratch compiler.
All records stay in the build directory. Sources remain under Evidence.
The script excludes the 17 writeOutput blocks assigned to worker-build-2.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'ZesuSsz/Evidence/det/blocks'))
import run_write_output as shared  # noqa: E402

gen_block, inference = shared.gen_block, shared.infer_boundary
STAGING = ROOT / 'ZesuSsz/Evidence/det/remaining'


def remaining_blocks(blocks: list[dict]) -> list[dict]:
    return [block for block in blocks
            if gen_block.address(block['start']) not in set(shared.LEADERS)]


def native_metadata(module: Path, lemma: str) -> dict:
    proof = inference.find_proof(module, lemma)
    header = []
    for line in module.read_text().splitlines()[proof.declaration_line:proof.proof_line]:
        header.append(line)
        if line.rstrip().endswith(':'):
            break
    declaration = ' '.join(line.strip() for line in header).rstrip(':').strip()
    return {'binders': re.sub(rf'^Lemma\s+{re.escape(lemma)}\b\s*', '', declaration),
            'imports': ['ZesuSsz.Proofs.WriteSuccess.' + module.stem,
                        *inference.native_imports(module)]}


def from_mcp(row: dict, measurement: dict, module: Path) -> dict:
    result = measurement['result']
    output = '\n'.join(output for _command, output in result.get('feedback', []))
    selected, details = inference.goal_record(output)
    target = row.get('stop', row['leader'])
    record = {**details, **native_metadata(module, row['lemma']),
              'module': module.name, 'lemma': row['lemma'],
              'exit': row.get('exit', row['leader']),
              'probe_entry': row['leader'], 'seconds': measurement['seconds'],
              'canonical_table_sha256': shared.TABLE_SHA256}
    record['parameter_types'] = {**row.get('parameter_types', {}),
                                 **record['parameter_types']}
    if not result.get('success'):
        record.update(outcome='error', error_lines=[result.get('error', 'MCP failed')])
        return record
    context, conclusion = inference.conclusion_text(selected)
    frame, points = inference.context_size(context)
    record.update(context=context, conclusion=conclusion, frame=frame, mapsto=points)
    if inference.reached_stop(output, target):
        if conclusion.strip() != inference.stop_name(target):
            record.update(outcome='error', error_lines=[
                'the selected context does not conclude the requested stop'])
            return record
        record.update(outcome='reached', state_entry=target)
    else:
        record.update(outcome='stalled')
    return record


def prepare_successors(manifest: list[dict], records_dir: Path) -> list[dict]:
    """Prepare stops from owned, recorded predecessor states only."""
    owned = {row['leader']: row for row in manifest}
    probes = []
    for target in manifest:
        if target['outcome'] != 'missing-entry':
            continue
        for address in target['predecessors']:
            row = {'leader': address, 'stop': target['leader'],
                   'canonical_table_sha256': shared.TABLE_SHA256}
            predecessor = owned.get(address)
            if predecessor is None:
                row['outcome'] = 'external-predecessor'
            elif predecessor['outcome'] != 'staged':
                row['outcome'] = 'missing-predecessor-state'
            else:
                row.update(module=predecessor['module'], lemma=predecessor['lemma'],
                           exit=predecessor['end'])
                entry = gen_block.address(address)
                record = json.loads((records_dir / f'entry_{entry:x}.jsonl').read_text())
                record['standard_call_frame'] = True
                row['parameter_types'] = {
                    **dict(gen_block.gen_boundary.sections(record['context'])[0]),
                    **record.get('parameter_types', {})}
                module = ROOT / 'ZesuSsz/Proofs/WriteSuccess' / (row['module'] + '.v')
                try:
                    source = inference.probe_source(
                        module, row['lemma'], predecessor['end'], [], shared.CALL_RULE,
                        stop=row['stop'], after_return=True,
                        entry_state=(gen_block.state_source(entry, record),
                                     gen_block.state_application(entry, record)))
                    name = f'remaining_stop_{entry:x}_{gen_block.address(row["stop"]):x}.v'
                    (records_dir / name).write_text(source)
                    row.update(source=name, outcome='prepared')
                except (ValueError, KeyError) as error:
                    row.update(outcome='residual', error=str(error))
            probes.append(row)
    return probes


def ingest_successors(probes: list[dict], records_dir: Path) -> list[dict]:
    results = []
    for probe in probes:
        row = dict(probe)
        if probe['outcome'] == 'prepared':
            entry, stop = map(gen_block.address, (probe['leader'], probe['stop']))
            path = records_dir / f'mcp_stop_{entry:x}_{stop:x}.json'
            if path.exists():
                try:
                    measurement = json.loads(path.read_text())
                    if any(measurement[key] != probe[key] for key in
                           ('leader', 'stop', 'module', 'lemma', 'canonical_table_sha256')):
                        raise ValueError('the MCP predecessor selection differs')
                    module = ROOT / 'ZesuSsz/Proofs/WriteSuccess' / (probe['module'] + '.v')
                    record = from_mcp(probe, measurement, module)
                    (records_dir / f'stop_{entry:x}_{stop:x}.jsonl').write_text(
                        json.dumps(record) + '\n')
                    row['outcome'] = record['outcome']
                    if record['outcome'] == 'reached':
                        record['standard_call_frame'] = True
                        (STAGING / 'States' / f'State_{stop:x}.v').write_text(
                            gen_block.state_source(stop, record))
                        row['outcome'] = 'staged'
                except (ValueError, KeyError) as error:
                    row.update(outcome='residual', error=str(error))
        results.append(row)
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--entries', type=Path, required=True)
    parser.add_argument('--build-dir', type=Path,
                        default=ROOT / '_build/agents/writer-generator')
    parser.add_argument('--leader', action='append', default=[])
    parser.add_argument('--prepare-successors', action='store_true')
    action = parser.add_mutually_exclusive_group()
    action.add_argument('--infer', action='store_true')
    action.add_argument('--ingest-mcp', action='store_true')
    parser.add_argument('--seconds', type=int, default=300)
    args = parser.parse_args()
    if Path.cwd().resolve() != ROOT:
        parser.error('run this script from the repository root')
    raw = args.entries.read_bytes()
    if hashlib.sha256(raw).hexdigest() != shared.TABLE_SHA256:
        parser.error('the canonical entry table digest differs')
    entries = json.loads(raw)
    if len(entries) != 87:
        parser.error('the canonical entry table must contain 87 rows')
    args.build_dir = args.build_dir.resolve()
    records_dir = args.build_dir / 'wp2-remaining'
    records_dir.mkdir(parents=True, exist_ok=True)
    for name in ('ARISTOTLE_API_KEY', 'OPEN_ROUTER_API_KEY', 'PROVER_API_KEY'):
        os.environ.pop(name, None)
    cfg = json.loads((ROOT / 'build/endpoint-cfg/zesu-cfg.json').read_text())
    blocks = next(function['blocks'] for function in cfg['functions']
                  if gen_block.address(function['start']) == 0x14d30)
    remaining = remaining_blocks(blocks)
    if len(remaining) != 85:
        parser.error('the pinned CFG must contain 85 remaining blocks')
    leaders = {gen_block.address(value) for value in args.leader}
    if leaders - {gen_block.address(block['start']) for block in remaining}:
        parser.error('a requested leader is outside the 85 remaining blocks')
    (STAGING / 'States').mkdir(parents=True, exist_ok=True)
    (STAGING / 'dune').write_text('(data_only_dirs States)\n')
    manifest = []
    for block in remaining:
        leader = gen_block.address(block['start'])
        if leaders and leader not in leaders:
            continue
        address = hex(leader)
        row = {'leader': address, 'end': hex(gen_block.address(block['end'])),
               'successors': block['successors'], 'canonical_table_sha256': shared.TABLE_SHA256}
        selected = entries.get(address)
        if selected is None:
            row.update(outcome='missing-entry', predecessors=[
                hex(gen_block.address(previous['start'])) for previous in blocks
                if address in previous['successors']])
        else:
            row.update(selected)
            module = ROOT / 'ZesuSsz/Proofs/WriteSuccess' / (selected['module'] + '.v')
            try:
                source, actual = inference.entry_source(module, selected['lemma'])
                if actual != address:
                    raise ValueError(f'the selected entry is {actual}, expected {address}')
                name = f'remaining_entry_{leader:x}.v'
                (records_dir / name).write_text(source)
                row.update(source=name, outcome='prepared')
                record = None
                if args.ingest_mcp:
                    path = records_dir / f'mcp_entry_{leader:x}.json'
                    if path.exists():
                        measurement = json.loads(path.read_text())
                        if any(measurement[key] != row[key] for key in
                               ('leader', 'module', 'lemma', 'canonical_table_sha256')):
                            raise ValueError('the MCP probe selection differs')
                        record = from_mcp(row, measurement, module)
                elif args.infer:
                    record = inference.infer(module, selected['lemma'], address,
                        args.build_dir, [], args.seconds, entry_only=True)
                    record.update(canonical_table_sha256=shared.TABLE_SHA256, probe_entry=address)
                if record is not None:
                    (records_dir / f'entry_{leader:x}.jsonl').write_text(json.dumps(record) + '\n')
                    row['outcome'] = record['outcome']
                    if record['outcome'] == 'reached':
                        record['standard_call_frame'] = True
                        (STAGING / 'States' / f'State_{leader:x}.v').write_text(
                            gen_block.state_source(leader, record))
                        row['outcome'] = 'staged'
            except (ValueError, KeyError) as error:
                row.update(outcome='residual', error=str(error))
        manifest.append(row)
        print(f"{address}: {row['outcome']}" + (f" {row['error']}" if 'error' in row else ''),
              flush=True)
    (records_dir / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    if args.prepare_successors:
        successors = prepare_successors(manifest, records_dir)
        if args.ingest_mcp:
            successors = ingest_successors(successors, records_dir)
        (records_dir / 'successors.json').write_text(json.dumps(successors, indent=2) + '\n')
        for row in successors:
            print(f"{row['leader']} -> {row['stop']}: {row['outcome']}", flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
