#!/usr/bin/env python3
"""Extend the pinned MCP server with one read-only goal export."""
import hashlib
import json
import os
from pathlib import Path


def write_export(complete, directory, state_id):
    value = complete.to_json()
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
            'shelved_goals': len(value['shelf']), 'given_up_goals': len(value['given_up'])}


def main():
    from fastmcp import Context
    from rocq_mcp import server
    from rocq_mcp import interactive
    directory = Path(os.environ['ZESU_COMPLETE_GOAL_DIR']).resolve()

    @server.mcp.tool
    async def rocq_complete_goals(from_state: int, ctx: Context = None) -> dict:
        """Export all returned goal fields without proof commands or truncation."""
        if ctx is None:
            return {'success': False, 'error': 'The export requires a live owned MCP context'}
        def read(pet):
            entry, _, error = interactive._resolve_check_base_state(from_state)
            if error:
                return {'success': False, 'error': error}
            stale = interactive._check_staleness(entry, ctx.lifespan_context)
            if stale:
                return {'success': False, 'error': stale}
            complete = pet.complete_goals(entry.state, timeout=30)
            return write_export(complete, directory, from_state)
        return await server._run_with_pet(read, ctx.lifespan_context,
                                           'rocq_complete_goals', timeout=30)

    server.main()


if __name__ == '__main__':
    main()
