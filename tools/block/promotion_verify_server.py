#!/usr/bin/env python3
"""Identify the owned MCP transport used by native promotion checks."""
import os
from pathlib import Path


def main():
    from rocq_mcp import server

    @server.mcp.tool
    async def rocq_promotion_owner() -> dict:
        pid = os.getpid()
        fields = (Path('/proc') / str(pid) / 'stat').read_text().rsplit(')', 1)[1].split()
        return {'success': True, 'pid': pid, 'start_ticks': int(fields[19])}

    server.main()


if __name__ == '__main__':
    main()
