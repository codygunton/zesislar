"""Compile dependency levels through MCP and retain ordinary object receipts."""
import asyncio
import time
from aggregate_layout import aggregate_root
from contextlib import AsyncExitStack

from entry_chain import read_bound, save


def levels(ordered, edges, completed, protected=()):
    if len(ordered) != len(set(ordered)) or set(ordered) & set(completed):
        raise ValueError('The MCP declaration order repeats an accepted module.')
    pending, done, result = set(ordered), set(completed), []
    dependencies = {name: set() for name in ordered}
    for row in edges:
        if row['from'] in dependencies:
            dependencies[row['from']].add(row['to'])
    while pending:
        ready = [name for name in ordered if name in pending and dependencies[name] <= done]
        if not ready:
            raise ValueError('The MCP declaration graph has a cycle or an absent dependency.')
        batch = []
        for name in ready:
            if name in protected:
                if batch:result.append(batch);batch = []
                result.append([name])
            else:batch.append(name)
        if batch:result.append(batch)
        pending.difference_update(ready)
        done.update(ready)
    return result, dependencies


def session_limit(maximum, budget, controller_bytes, compiler_weights, client_bytes=0):
    if not compiler_weights:
        return 1
    if any(type(value) is not int or value <= 0 for value in [maximum, budget, controller_bytes, *compiler_weights]):
        raise ValueError('The MCP declaration booking is invalid.')
    if type(client_bytes) is not int or client_bytes < 0:
        raise ValueError('The MCP client booking is invalid.')
    width = min(maximum, (budget - client_bytes) // (controller_bytes + max(compiler_weights)))
    if width < 1:
        raise ValueError('The MCP controller and compiler do not fit the aggregate budget.')
    return width


async def run(runtime, output, main_session, open_session, compile_one, *, controller_bytes,
              client_bytes=0, normal_failure):
    spec = runtime['declaration_dag']
    graph = read_bound(spec['graph'])
    waves, dependencies = levels(runtime['ordered_modules'], graph['import_edges'], spec['completed_modules'], spec.get('protected_modules', ()))
    done, failures, blocked, receipts = set(spec['completed_modules']), {}, {}, {}
    depths = {name: depth for depth, wave in enumerate(waves, 1) for name in wave}
    width = session_limit(spec['maximum_workers'], runtime['canonical_admission']['physical_fence_bytes'],
                          controller_bytes, list(spec['weights'].values()), client_bytes)
    report = {'transport': 'MCP', 'dependency_depth': len(waves), 'maximum_sessions': width,
              'controller_claim_bytes': controller_bytes, 'client_claim_bytes': client_bytes,
              'compiler_weights': spec['weights'], 'sample': None,
              'receipts': receipts, 'failures': failures, 'blocked': blocked}

    def publish():
        report['completed_modules'] = len(receipts)
        save(output / 'MCP-DECLARATIONS.json', report)

    async def compile_selected(session, name):
        reference = await compile_one(session, name)
        receipts[name] = reference
        done.add(name)
        publish()
        return reference

    publish()
    # Measure the first ready declaration before independent dispatch.
    if waves:
        sample = waves[0][0]
        group = aggregate_root()
        def aggregate_cpu():
            values = dict(line.split() for line in (group / 'cpu.stat').read_text().splitlines())
            return int(values['usage_usec']) / 1000000
        before_cpu, before_wall = aggregate_cpu(), time.monotonic()
        reference = await compile_selected(main_session, sample)
        sample_cpu, sample_wall = aggregate_cpu() - before_cpu, time.monotonic() - before_wall
        receipt = read_bound(reference)
        physical = read_bound(receipt['physical_result'])
        report['sample'] = {'module': sample, 'depth': depths[sample], 'receipt': reference,
                            'physical_result': receipt['physical_result'],
                            'compiler_CPU_seconds': physical['user_CPU_seconds'] + physical['system_CPU_seconds'],
                            'physical_wall_seconds': physical['wall_seconds'],
                            'aggregate_CPU_seconds': sample_cpu, 'aggregate_wall_seconds': sample_wall,
                            'aggregate_scope': str(group),
                            'CPU_ratio': sample_cpu / (physical['user_CPU_seconds'] + physical['system_CPU_seconds']) if physical['user_CPU_seconds'] + physical['system_CPU_seconds'] else None}
        publish()
        if report['sample']['CPU_ratio'] is not None and report['sample']['CPU_ratio'] > 10:
            raise RuntimeError('The measured compiler ratio exceeds 10. Further dispatch requires a harness correction.')
    async with AsyncExitStack() as stack:
        sessions = [main_session]
        for index in range(1, width):
            sessions.append(await stack.enter_async_context(open_session(index)))
        for depth, wave in enumerate(waves, 1):
            ready = []
            for name in wave:
                if name in done:
                    continue
                missing = dependencies[name] - done
                if missing:
                    blocked[name] = sorted(missing)
                else:
                    ready.append(name)
            for offset in range(0, len(ready), width):
                names = ready[offset:offset + width]
                outcomes = await asyncio.gather(*(compile_selected(session, name)
                    for session, name in zip(sessions, names)), return_exceptions=True)
                fatal = None
                for name, outcome in zip(names, outcomes):
                    if isinstance(outcome, BaseException):
                        failures[name] = {'error': str(outcome), 'depth': depth}
                        if not normal_failure(outcome) or not spec.get('keep_going'):
                            fatal = fatal or outcome
                publish()
                if fatal is not None:
                    raise fatal
    if failures or blocked:
        raise RuntimeError('The MCP declaration levels contain failed or blocked modules.')
    return report
