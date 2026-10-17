"""Retain raw MCP calls before parsing or fallback handling."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path


class ToolJournal:
    def __init__(self, directory):
        self.directory = Path(directory)
        self.directory.mkdir(parents=True, exist_ok=False)
        self.sequence = 0
        self.failed = False

    def _write(self, name, value):
        path = self.directory / name
        try:
            payload = (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()
            temporary = path.with_name('.' + path.name + '.tmp')
            with temporary.open('xb') as stream:
                stream.write(payload)
                stream.flush()
                os.fsync(stream.fileno())
            os.link(temporary, path)
            temporary.unlink()
            descriptor = os.open(self.directory, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
        except BaseException:
            self.failed = True
            raise

    async def _call(self, kind, arguments, operation):
        if self.failed:
            raise RuntimeError('The journal failed. No further MCP call is permitted.')
        self.sequence += 1
        prefix = f'{self.sequence:04d}-{kind}'
        self._write(prefix + '-request.json', {
            'utc': datetime.now(timezone.utc).isoformat(),
            'tool': kind, 'arguments': arguments,
            'status': 'request-prepared; response and acceptance remain unavailable'})
        try:
            raw = await operation()
        except BaseException as error:
            self._write(prefix + '-exception.json', {
                'utc': datetime.now(timezone.utc).isoformat(),
                'type': type(error).__name__, 'error': str(error),
                'status': 'No SDK response returned.'})
            raise
        try:
            payload = raw if isinstance(raw, dict) else raw.model_dump(mode='json')
            self._write(prefix + '-raw.json', payload)
        except BaseException:
            self.failed = True
            raise
        return raw

    async def initialize(self, session):
        return await self._call('initialize', {}, session.initialize)

    async def call_tool(self, session, tool, arguments):
        return await self._call(tool, arguments, lambda: session.call_tool(tool, arguments))

    def snapshot(self):
        rows = []
        for path in sorted(self.directory.iterdir()):
            content = path.read_bytes()
            rows.append({'path': str(path), 'sha256': hashlib.sha256(content).hexdigest(),
                         'bytes': len(content)})
        return {'directory': str(self.directory), 'references': rows,
                'retention_failed': self.failed, 'prepared_requests': self.sequence,
                'scope': 'A prepared request does not establish acceptance or instruction execution.'}
