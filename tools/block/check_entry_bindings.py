#!/usr/bin/env python3
"""Validate exact entry schemas and type-check their ordered applications."""
import argparse
import asyncio
import hashlib
import json
import os
from pathlib import Path
import time

from entry_bindings import application_source, rendered_entry_views, validate_design
from entry_schema import FIELDS
from function_names import prefix_argument


SUPPORT_TOOLS = (
    'ZesuSsz/Evidence/generate_block_design.py',
    'tools/block/render_support.py', 'tools/block/check_data_only_lemmas.py',
    'tools/block/generate_table.py', 'tools/resource_guard.sh')
APPLICATION_TOOLS = (
    'tools/block/check_entry_bindings.py', 'tools/block/entry_bindings.py',
    'tools/block/entry_schema.py', 'tools/block/function_names.py',
    'tools/block/trace_registers.py', 'tools/rocq_mcp_guarded.sh',
    'tools/block/entry_check_coqc.sh', '_CoqProject')


def binding_record(views):
    return {key: views[key] for key in ('name_mapping', 'input_source_hashes',
            'output_source_hashes', 'primary_count', 'auxiliary_count')}


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
    parser.add_argument('--function', type=prefix_argument, default='decodeItem')
    parser.add_argument('--design', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--seconds', type=int, default=60)
    args = parser.parse_args()
    if not 1 <= args.seconds <= 60:
        parser.error('Application checks permit at most 60 seconds')
    workspace = Path.cwd()
    design = json.loads(args.design.read_text())
    views = rendered_entry_views(design, workspace, name_prefix=args.function)
    applications = views['application_design']
    count = validate_design(applications, workspace)
    args.out.mkdir(parents=True, exist_ok=True)
    source = (args.out/'ApplicationChecks.v').resolve()
    source.write_text(application_source(applications, name_prefix=args.function))
    inputs = {str(args.design): digest(args.design)}
    if args.function == 'decodeItem':
        contract = 'ZesuSsz/Contracts/RlpDecodeItemContract.v'
        inputs[contract] = digest(workspace/contract)
    for hashes in (views['input_source_hashes'], views['output_source_hashes']):
        for path, expected in hashes.items():
            inputs[path] = digest(workspace/path)
            if inputs[path].lower() != expected.lower():
                raise ValueError('The bound source changed during validation')
    inputs.update({path: digest(workspace/path) for path in APPLICATION_TOOLS})
    if views['name_mapping']:
        inputs.update({path: digest(workspace/path) for path in SUPPORT_TOOLS})
    source_hash = digest(source)
    started = time.monotonic()
    health, result = asyncio.run(compile_queries(workspace, source, args.seconds))
    for name, expected in inputs.items():
        if digest(workspace/name) != expected:
            raise ValueError('The bound input changed during validation: ' + name)
    if digest(source) != source_hash:
        raise ValueError('The application query changed during validation')
    report = {'schema': 1, 'label': 'Entry declaration and application validation; no proof completion claim',
              'fields': sorted(FIELDS), 'inputs': inputs, 'row_count': count,
              'source': {'path': str(source.relative_to(workspace)), 'sha256': source_hash},
              'elapsed_seconds': time.monotonic()-started, 'health': health, 'result': result,
              'module_limit_seconds': args.seconds, 'module_limit_gib': 2, 'workers': 1,
              'argument_policy': 'JSON expression order is authoritative; same-type swaps require specification review'}
    if views['name_mapping']:
        report['entry_bindings'] = binding_record(views)
        report['cfg_row_count'] = len(design['blocks'])
    if args.function != 'decodeItem':
        report['name_prefix'] = args.function
    path = args.out/'report.json'
    path.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'report': str(path), 'sha256': digest(path), 'success': result.get('success')}))
    return 0 if result.get('success') else 1




def validate_report(path, design_path, workspace):
    """Require successful typing of the current, complete query source."""
    report = json.loads(Path(path).read_text())
    design = json.loads(Path(design_path).read_text())
    views = rendered_entry_views(design, workspace, name_prefix=report.get('name_prefix', 'decodeItem'))
    applications = views['application_design']
    validate_design(applications, workspace)
    if report.get('result', {}).get('success') is not True or not report.get('health', {}).get('ok'):
        raise ValueError('The entry application report does not record successful typing')
    if report.get('row_count') != len(applications['blocks']) or report.get('fields') != sorted(FIELDS):
        raise ValueError('The entry application report has different rows or fields')
    if views['name_mapping']:
        if (report.get('entry_bindings') != binding_record(views) or
                report.get('cfg_row_count') != len(design['blocks'])):
            raise ValueError('The entry application report has different rendered bindings')
        required = dict(views['input_source_hashes'], **views['output_source_hashes'])
        required.update({name: digest(Path(workspace)/name)
                         for name in SUPPORT_TOOLS+APPLICATION_TOOLS})
        if report.get('name_prefix', 'decodeItem') == 'decodeItem':
            name = 'ZesuSsz/Contracts/RlpDecodeItemContract.v'
            required[name] = digest(Path(workspace)/name)
        for name, expected in required.items():
            if report.get('inputs', {}).get(name) != expected:
                raise ValueError('The entry application report omits a rendered input: ' + name)
    expected = hashlib.sha256(application_source(applications, name_prefix=report.get('name_prefix', 'decodeItem')).encode()).hexdigest()
    if report.get('source', {}).get('sha256') != expected:
        raise ValueError('The entry application report checked different ordered expressions')
    for name, expected in report['inputs'].items():
        if digest(Path(workspace)/name) != expected:
            raise ValueError('The entry application report has a changed input: ' + name)
    return digest(path)


if __name__ == '__main__':
    raise SystemExit(main())
