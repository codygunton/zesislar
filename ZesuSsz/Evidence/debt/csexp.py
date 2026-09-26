"""Minimal canonical s-expression reader for Dune trace files."""


def parse_all(data):
    """Yield every top-level s-expression in `data` (bytes)."""
    pos = 0
    n = len(data)
    while pos < n:
        if data[pos:pos + 1] in (b"\n", b" "):
            pos += 1
            continue
        value, pos = _parse(data, pos)
        yield value


def _parse(data, pos):
    if data[pos] == 0x28:  # (
        pos += 1
        items = []
        while data[pos] != 0x29:
            item, pos = _parse(data, pos)
            items.append(item)
        return items, pos + 1
    colon = data.index(b":", pos)
    length = int(data[pos:colon])
    start = colon + 1
    return data[start:start + length].decode("utf-8", "replace"), start + length
