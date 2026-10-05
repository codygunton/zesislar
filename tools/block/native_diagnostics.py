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
    records.append(timed_result(label or name, started, stamp, before, result))
    return result


def is_primary_timeout(calls):
    return any(value.get('success') is False and value.get('error') == 'Coq: Timeout!'
               and value.get('reason') == 'tactic_failed' for value in calls)


async def _diagnose(path, options, report):
    """Use a fresh session. Never derive a primary outcome from this pass."""
    import os
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client
    from discovery import data
    parameters = StdioServerParameters(command=options['mcp_command'],
        env={**os.environ, 'ROCQ_WORKSPACE': options['workspace'],
             'ROCQ_PET_TIMEOUT': str(options['seconds'])})
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
            report['last_successful_state'] = state
            deadline = time.monotonic() + options['seconds']
            init = ('try intros.\ntry iStartProof.\nzesu_expose_code_lists.\n'
                    'repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].\n'
                    'zesu_reduce_introduced_code_lists.\nrepeat iDestruct select (_ ∗ _)%I as "[? ?]".\n')
            index = 0
            while time.monotonic() < deadline:
                body = init if index == 0 else 'zesu_liAStep.'
                checked = await measured_call(session, 'rocq_check', {
                    'from_state': state['state_id'], 'body': body,
                    'timeout': max(1, int(deadline - time.monotonic()))},
                    report['steps'], state.get('goals'),
                    'diagnostic-initialization' if index == 0 else 'zesu_liAStep')
                report['calls'].append(checked)
                if not checked.get('success'):
                    report['stop'] = 'diagnostic-step-failed'
                    report['failed_step'] = index
                    report['first_residual'] = state.get('goals')
                    break
                before = goal_size(state.get('goals'))
                state = checked
                report['last_successful_state'] = state
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
              'budget_seconds': options['seconds']}
    try:
        return await _diagnose(path, options, report)
    except Exception as error:
        report['stop'] = 'diagnostic-tooling-failure'
        report['error'] = str(error)
        previous = report.get('last_successful_state') or {}
        report['first_residual'] = previous.get('goals')
        return report
