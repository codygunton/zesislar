"""Stream SDK feedback through the reviewed bounded OCaml writer."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
from trace_block_raw_budget import write_bytes

INLINE_BYTES = 32768
PHYSICAL_BYTES = 2 * 1024 * 1024


def json_parts(value):
    """Yield exact JSON without building a second large escaped string."""
    if isinstance(value, str):
        yield '"'
        for offset in range(0, len(value), 4096):
            yield json.dumps(value[offset:offset + 4096], ensure_ascii=False)[1:-1]
        yield '"'
    elif value is None or type(value) in (bool, int, float):
        yield json.dumps(value, allow_nan=False)
    elif isinstance(value, dict):
        yield '{'
        for index, (key, item) in enumerate(value.items()):
            if not isinstance(key, str):
                raise ValueError('A bounded MCP key is not a string.')
            if index:
                yield ','
            yield from json_parts(key)
            yield ':'
            yield from json_parts(item)
        yield '}'
    elif isinstance(value, (list, tuple)):
        yield '['
        for index, item in enumerate(value):
            if index:
                yield ','
            yield from json_parts(item)
        yield ']'
    else:
        raise ValueError('A bounded MCP value has an unsupported type.')


def is_small(value):
    size = 0
    for part in json_parts(value):
        size += len(part.encode('utf-8'))
        if size > INLINE_BYTES:
            return False
    return True


def write_field(root, logical_event, value, writer):
    relative = 'mcp-chunks/' + logical_event
    process = subprocess.Popen(
        [str(writer), str(root), '/dev/stdin', relative, logical_event],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        close_fds=True)
    try:
        for part in json_parts(value):
            process.stdin.write(part.encode('utf-8'))
        process.stdin.close()
        process.stdin = None
        output, error = process.communicate()
    except BaseException:
        # This child performs serialization only. Never signal a Pet here.
        process.stdin.close() if process.stdin else None
        process.stdin = None
        process.wait()
        raise
    if process.returncode:
        raise RuntimeError('The bounded MCP writer failed: ' + error.decode('utf-8'))
    if len(output) > PHYSICAL_BYTES:
        raise ValueError('The bounded writer returned an oversized descriptor.')
    return json.loads(output)


def store(root, ordinal, value):
    """Keep small metadata inline and retain every large field losslessly."""
    root = Path(root)
    writer = Path(os.environ['ZESU_TRACE_CHUNK_WRITER'])
    result = {}
    for index, (key, item) in enumerate(value.items()):
        result[key] = item if is_small(item) else write_field(
            root, 'capture-%06d-field-%04d' % (ordinal, index), item, writer)
    encoded = (json.dumps(result, ensure_ascii=False, separators=(',', ':')) + '\n').encode()
    if len(encoded) > PHYSICAL_BYTES:
        raise ValueError('The bounded MCP metadata exceeds 2 MiB.')
    path = root / ('capture-%06d.json' % ordinal)
    if path.exists():
        raise FileExistsError(path)
    write_bytes(path, encoded, control=True)
    return {'path': str(path), 'sha256': hashlib.sha256(encoded).hexdigest()}
