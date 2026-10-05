#!/usr/bin/env python3
"""Validate exact entry schemas and type-check their ordered applications."""
import argparse
import asyncio
import hashlib
import json
import os
from pathlib import Path
import time

from entry_bindings import application_source, validate_design
from entry_schema import FIELDS


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def structured(value):
    if not isinstance(value.structuredContent, dict):
        raise ValueError('Rocq MCP returned no structured result')
    return value.structuredContent


async def compile_queries(workspace, source, timeout):
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client
    env = dict(os.environ)
    env['ZESU_ROCQ_COQC_WRAPPER'] = str(workspace/'tools/block/entry_check_coqc.sh')
    env['ROCQ_DUNE_BUILD'] = '0'
    parameters = StdioServerParameters(command=str(workspace/'tools/rocq_mcp_guarded.sh'), env=env)
    async with stdio_client(parameters) as streams:
        async with ClientSession(*streams) as session:
            await session.initialize()
            health = structured(await session.call_tool('rocq_health', {}))
            if not health.get('ok'):
                raise ValueError('Rocq MCP health failed')
            result = structured(await session.call_tool('rocq_compile_file', {
                'workspace': str(workspace), 'file': str(source), 'timeout': timeout,
                'mode': 'full', 'timing': True, 'include_warnings': False}))
            return health, result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--design', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--seconds', type=int, default=60)
    args = parser.parse_args()
    if not 1 <= args.seconds <= 60:
        parser.error('Application checks permit at most 60 seconds')
    workspace = Path.cwd()
    design = json.loads(args.design.read_text())
    count = validate_design(design, workspace)
    args.out.mkdir(parents=True, exist_ok=True)
    source = (args.out/'ApplicationChecks.v').resolve()
    source.write_text(application_source(design))
    started = time.monotonic()
    health, result = asyncio.run(compile_queries(workspace, source, args.seconds))
    inputs = {str(args.design): digest(args.design)}
    for row in design['blocks']:
        for path, expected in row['source_hashes'].items():
            inputs[path] = digest(path)
            if inputs[path].lower() != expected.lower():
                raise ValueError('The bound source changed during validation')
    for path in (Path(__file__), Path(__file__).with_name('entry_bindings.py'),
                 Path(__file__).with_name('entry_schema.py'),
                 Path(__file__).with_name('trace_registers.py'),
                 workspace/'tools/rocq_mcp_guarded.sh',
                 workspace/'tools/block/entry_check_coqc.sh', workspace/'_CoqProject'):
        inputs[str(path.relative_to(workspace)) if path.is_absolute() else str(path)] = digest(path)
    report = {'schema': 1, 'label': 'Entry declaration and application validation; no proof completion claim',
              'fields': sorted(FIELDS), 'inputs': inputs, 'row_count': count,
              'source': {'path': str(source.relative_to(workspace)), 'sha256': digest(source)},
              'elapsed_seconds': time.monotonic()-started, 'health': health, 'result': result,
              'module_limit_seconds': args.seconds, 'module_limit_gib': 2, 'workers': 1,
              'argument_policy': 'JSON expression order is authoritative; same-type swaps require specification review'}
    path = args.out/'report.json'
    path.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'report': str(path), 'sha256': digest(path), 'success': result.get('success')}))
    return 0 if result.get('success') else 1




def validate_report(path, design_path, workspace):
    """Require successful typing of the current, complete query source."""
    report = json.loads(Path(path).read_text())
    design = json.loads(Path(design_path).read_text())
    validate_design(design, workspace)
    if report.get('result', {}).get('success') is not True or not report.get('health', {}).get('ok'):
        raise ValueError('The entry application report does not record successful typing')
    if report.get('row_count') != len(design['blocks']) or report.get('fields') != sorted(FIELDS):
        raise ValueError('The entry application report has different rows or fields')
    expected = hashlib.sha256(application_source(design).encode()).hexdigest()
    if report.get('source', {}).get('sha256') != expected:
        raise ValueError('The entry application report checked different ordered expressions')
    for name, expected in report['inputs'].items():
        if digest(Path(workspace)/name) != expected:
            raise ValueError('The entry application report has a changed input: ' + name)
    return digest(path)


if __name__ == '__main__':
    raise SystemExit(main())
