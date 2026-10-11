#!/usr/bin/env python3
"""Extend the pinned MCP server with one read-only goal export."""
import hashlib
import json
import os
from pathlib import Path


PRINTING_DEPTH = 1000000


def goal_groups(value):
    """Keep each group, including both sides of every focus frame."""
    yield value['goals']
    for left, right in value['stack']:
        yield left
        yield right
    yield value['shelf']
    yield value['given_up']


def check_kernel_groups(original, kernel):
    """Check identity and complete terms without comparing print formats."""
    original_groups = list(goal_groups(original))
    kernel_groups = list(goal_groups(kernel))
    if len(original_groups) != len(kernel_groups):
        raise ValueError('The printing branch changed the goal groups')
    for source, full in zip(original_groups, kernel_groups):
        if len(source) != len(full):
            raise ValueError('The printing branch changed a goal group')
        for goal, kernel_goal in zip(source, full):
            if goal.get('info') != kernel_goal.get('info'):
                raise ValueError('The printing branch changed a goal identity')
            if [h['names'] for h in goal['hyps']] != [h['names'] for h in kernel_goal['hyps']]:
                raise ValueError('The printing branch changed the ordered context')
            terms = [kernel_goal['ty']]
            for hyp, kernel_hyp in zip(goal['hyps'], kernel_goal['hyps']):
                body = kernel_hyp.get('def')
                if (hyp.get('def') is None) != (body is None):
                    raise ValueError('The printing branch changed a local definition')
                terms.append(kernel_hyp['ty'])
                if body is not None:
                    if body.strip() == 'HIDDEN':
                        raise ValueError('The kernel export hides a local definition')
                    terms.append(body)
            if any('...' in term for term in terms):
                raise ValueError('The kernel export contains printer ellipsis')


def complete_with_definitions(pet, state):
    """Read full terms on a discarded printing branch. Preserve the state."""
    complete = pet.complete_goals(state, timeout=30)
    if complete is None:
        return complete, None
    original = complete.to_json()
    printing = pet.run(state, f'Set Printing All. Set Printing Depth {PRINTING_DEPTH}.', timeout=30)
    kernel = pet.complete_goals(printing, timeout=30)
    if kernel is None:
        raise ValueError('The printing branch returned no proof scope')
    kernel_value = kernel.to_json()
    check_kernel_groups(original, kernel_value)
    retained = pet.complete_goals(state, timeout=30)
    if retained is None or retained.to_json() != original:
        raise ValueError('The export changed the original proof state')
    return complete, kernel_value


def write_export(complete, directory, state_id, kernel_groups=None):
    if complete is None:
        return {'success': False, 'state_id': state_id, 'reason': 'no-proof-scope',
                'error': 'Pet returned no proof scope. Goal groups are unavailable.'}
    value = complete.to_json()
    if kernel_groups is not None:
        check_kernel_groups(value, kernel_groups)
        value = dict(value, kernel_groups=kernel_groups,
                     local_definition_export={'method': 'discarded-printing-all-branch',
                                              'printing_depth': PRINTING_DEPTH,
                                              'original_state_preserved': True})
    # Keep all active goals, stack entries, shelves and given-up goals.
    payload = (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()
    path = Path(directory) / f'state_{state_id}.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_bytes() != payload:
        raise ValueError('The complete goal export changed for the same state')
    path.write_bytes(payload)
    return {'success': True, 'state_id': state_id, 'path': str(path.resolve()),
            'sha256': hashlib.sha256(payload).hexdigest(), 'bytes': len(payload),
            'active_goals': len(value['goals']), 'stack_entries': len(value['stack']),
            'shelved_goals': len(value['shelf']), 'given_up_goals': len(value['given_up']),
            'stack_frame_goal_counts': [{'left': len(frame[0]), 'right': len(frame[1])}
                                        for frame in value['stack']]}


def main():
    from fastmcp import Context
    from rocq_mcp import server
    from rocq_mcp import interactive
    directory = Path(os.environ['ZESU_COMPLETE_GOAL_DIR']).resolve()
    if os.environ.get('ZESU_FEEDBACK_DIR'):
        from feedback_mcp import install_exporter
        install_exporter(interactive, os.environ['ZESU_FEEDBACK_DIR'])

    @server.mcp.tool
    async def rocq_complete_goals(from_state: int, ctx: Context = None) -> dict:
        """Export all groups and local definitions. Preserve the source state.

        The ordinary groups keep their original printing. kernel_groups keeps
        full typed terms and definition bodies in the same context order.
        Printing commands run only on a discarded branch. No tactic runs.
        An incomplete kernel export fails instead of returning hidden bodies.
        """
        if ctx is None:
            return {'success': False, 'error': 'The export requires a live owned MCP context'}
        def read(pet):
            entry, _, error = interactive._resolve_check_base_state(from_state)
            if error:
                return {'success': False, 'error': error}
            stale = interactive._check_staleness(entry, ctx.lifespan_context)
            if stale:
                return {'success': False, 'error': stale}
            complete, kernel = complete_with_definitions(pet, entry.state)
            return write_export(complete, directory, from_state, kernel)
        return await server._run_with_pet(read, ctx.lifespan_context,
                                           'rocq_complete_goals', timeout=30)

    server.main()


if __name__ == '__main__':
    main()
