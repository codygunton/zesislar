"""Record primary transactions and separate native-step diagnostics."""
import hashlib
import json
from datetime import datetime, timezone
import time


def goal_size(goals):
    if goals is None:
        return {'available': False}
    text = goals if isinstance(goals, str) else json.dumps(goals, sort_keys=True)
    encoded = text.encode()
    return {'available': True, 'utf8_bytes': len(encoded), 'lines': len(text.splitlines()),
            'sha256': hashlib.sha256(encoded).hexdigest(), 'format': 'MCP reported goals'}


def timed_result(label, started, timestamp, before, result):
    return {'label': label, 'started_utc': timestamp,
            'elapsed_seconds': time.monotonic() - started,
            'success': result.get('success'), 'from_state_id': result.get('from_state_id'),
            'state_id': result.get('state_id'), 'goals_before': goal_size(before),
            'goals_after': goal_size(result.get('goals')),
            'error': result.get('error'), 'reason': result.get('reason')}


async def measured_call(session, name, arguments, records, before=None, label=None):
    from discovery import data
    started = time.monotonic()
    stamp = datetime.now(timezone.utc).isoformat()
    try:
        result = data(await session.call_tool(name, arguments))
    except Exception as error:
        records.append(timed_result(label or name, started, stamp, before,
                                    {'success': False, 'error': str(error)}))
        raise
    records.append({**timed_result(label or name, started, stamp, before, result),
                    'tool': name, 'arguments': arguments})
    return result


async def native_step(session, state, timeout, records):
    return await measured_call(session, 'rocq_check', {
        'from_state': state['state_id'], 'body': '1: zesu_liAStep.', 'timeout': timeout},
        records, state.get('goals'), 'zesu_liAStep')


def is_primary_timeout(calls):
    return any(value.get('success') is False and value.get('error') == 'Coq: Timeout!'
               and value.get('reason') == 'tactic_failed' for value in calls)


async def _diagnose(path, options, report):
    """Use a fresh session. Never derive a primary outcome from this pass."""
    import os
    import sys
    from pathlib import Path
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client
    from discovery import data
    env = {**os.environ, 'ROCQ_WORKSPACE': options['workspace'],
           'ROCQ_PET_TIMEOUT': str(options['seconds'])}
    if options.get('complete_goals'):
        env.update(ZESU_ROCQ_MCP_BINARY=str(Path(__file__).with_name('complete_goals_mcp.sh').resolve()),
                   ZESU_MCP_PYTHON=sys.executable,
                   ZESU_COMPLETE_GOAL_DIR=str(Path(options['out'])/'complete'/path.stem))
    parameters = StdioServerParameters(command=options['mcp_command'], env=env)
    async with stdio_client(parameters) as streams:
        async with ClientSession(*streams) as session:
            await session.initialize()
            report['health'] = data(await session.call_tool('rocq_health', {}))
            opened = await measured_call(session, 'rocq_start', {
                'workspace': options['workspace'], 'file': str(path.resolve()),
                'theorem': 'infer_boundary', 'timeout': 60}, report['steps'], label='diagnostic-start')
            report['calls'].append(opened)
            if not opened.get('success'):
                report['stop'] = 'diagnostic-setup-failure'
                return report
            state = opened
            report['owned_session'] = data(await session.call_tool('rocq_diag', {}))
            report['complete_exports'] = []
            async def export_state(current):
                if options.get('complete_goals'):
                    result = data(await session.call_tool('rocq_complete_goals', {'from_state': current['state_id']}))
                    report['complete_exports'].append(result)
                    if not result.get('success'):
                        raise RuntimeError('The read-only goal export failed: ' + str(result.get('error')))
            await export_state(state)
            report['last_successful_state'] = state
            deadline = time.monotonic() + options['seconds']
            init = ('try intros.\ntry iStartProof.\nzesu_expose_code_lists.\n'
                    'repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].\n'
                    'zesu_reduce_introduced_code_lists.\nrepeat iDestruct select (_ ∗ _)%I as "[? ?]".\n')
            index = 0
            while time.monotonic() < deadline:
                timeout = max(1, int(deadline - time.monotonic()))
                if index == 0:
                    checked = await measured_call(session, 'rocq_check', {
                        'from_state': state['state_id'], 'body': init, 'timeout': timeout},
                        report['steps'], state.get('goals'), 'diagnostic-initialization')
                else:
                    checked = await native_step(session, state, timeout, report['steps'])
                report['calls'].append(checked)
                if not checked.get('success'):
                    report['stop'] = 'diagnostic-step-failed'
                    report['failed_step'] = index
                    report['first_residual'] = state.get('goals')
                    break
                before = goal_size(state.get('goals'))
                state = checked
                report['last_successful_state'] = state
                await export_state(state)
                if state.get('proof_finished'):
                    report['stop'] = 'diagnostic-finished'
                    break
                if index and goal_size(state.get('goals')) == before:
                    report['stop'] = 'diagnostic-no-goal-change'
                    report['first_residual'] = state.get('goals')
                    break
                index += 1
            else:
                report['stop'] = 'diagnostic-budget-expired'
                report['first_residual'] = state.get('goals')
            report['diagnostic'] = data(await session.call_tool('rocq_diag', {}))
    return report


async def diagnose(path, options):
    report = {'label': 'Secondary zesu_liAStep diagnostic; not an outcome classifier',
              'calls': [], 'steps': [], 'last_successful_state': None,
              'initialization': 'intros; iStartProof; existing code exposure and introductions',
              'budget_seconds': options['seconds'],
              'selector_policy': '1: focuses the first active goal; every returned goal remains recorded'}
    try:
        return await _diagnose(path, options, report)
    except Exception as error:
        report['stop'] = 'diagnostic-tooling-failure'
        report['error'] = str(error)
        previous = report.get('last_successful_state') or {}
        report['first_residual'] = previous.get('goals')
        return report
