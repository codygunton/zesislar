"""Read and render complete text fields with bounded string fragments."""

import json
import re

from trace_block_chunks import ChunkReader, ChunkTextStream
from trace_block_event_identity import _Reader


class StreamText:
    """Provide repeatable decoded text without constructing a complete string."""

    def __init__(self, factory):
        self.factory = factory

    def iter_text(self):
        return iter(self.factory())

    def __deepcopy__(self, memo):
        return self

    def __bool__(self):
        return any(bool(part) for part in self.iter_text())

    def __eq__(self, other):
        if isinstance(other, str):
            other_factory = lambda: iter((other,))
        elif isinstance(other, StreamText):
            other_factory = other.iter_text
        else:
            return False
        with ChunkTextStream(self.iter_text()) as left, ChunkTextStream(other_factory()) as right:
            while True:
                a, b = left.read(65536), right.read(65536)
                if a != b:
                    return False
                if not a:
                    return True

    def __ne__(self, other):
        return not self == other

    def __contains__(self, needle):
        if not isinstance(needle, str):
            raise TypeError("A text search requires a string.")
        if not needle:
            return True
        tail = ''
        for part in self.iter_text():
            text = tail + part
            if needle in text:
                return True
            tail = text[-(len(needle) - 1):] if len(needle) > 1 else ''
        return False

    def complete_text(self):
        """Check truncation markers across fragment boundaries."""
        tail = ""
        short = ""
        long = False
        truncated = False
        for part in self.iter_text():
            if not isinstance(part, str):
                raise ValueError("A text stream contains a non-text fragment.")
            joined = tail + part
            truncated |= "..." in joined or "…" in joined
            tail = joined[-2:]
            if not long:
                short += part
                short = short.lstrip()
                if len(short.rstrip()) > len("HIDDEN"):
                    short, long = "", True
                else:
                    short = short.rstrip() + (" " if short[-1:].isspace() else "")
        return not truncated and (long or short.strip() != "HIDDEN")


def iter_json_string(stream):
    """Decode one JSON string without retaining its complete value."""
    reader = _Reader(stream)
    reader.space()
    if reader.take() != '"':
        raise ValueError("The logical text field is not a JSON string.")
    while reader.peek():
        match = re.search(r'["\\\x00-\x1f]', reader.buffer[reader.offset:])
        end = reader.offset + match.start() if match else len(reader.buffer)
        part = reader.buffer[reader.offset:end]
        reader.offset = end
        if part:
            yield part
        if match is None:
            continue
        char = reader.take()
        if char == '"':
            reader.space()
            if reader.peek():
                raise ValueError("The logical text field contains trailing content.")
            return
        if char != "\\":
            raise ValueError("A logical text field contains a control character.")
        escape = reader.take()
        token = "\\" + escape
        if escape == "u":
            digits = "".join(reader.take() for _ in range(4))
            if re.fullmatch(r"[0-9a-fA-F]{4}", digits) is None:
                raise ValueError("A logical text field contains an invalid Unicode escape.")
            token += digits
            code = int(digits, 16)
            if 0xD800 <= code <= 0xDBFF:
                if reader.take() != "\\" or reader.take() != "u":
                    raise ValueError("A logical text field contains an unpaired surrogate.")
                low = "".join(reader.take() for _ in range(4))
                if re.fullmatch(r"[0-9a-fA-F]{4}", low) is None or not 0xDC00 <= int(low, 16) <= 0xDFFF:
                    raise ValueError("A logical text field contains an unpaired surrogate.")
                token += "\\u" + low
            elif 0xDC00 <= code <= 0xDFFF:
                raise ValueError("A logical text field contains an unpaired surrogate.")
        elif escape not in '"\\/bfnrt':
            raise ValueError("A logical text field contains an invalid escape.")
        yield json.loads('"' + token + '"')
    raise ValueError("A logical text field has no closing quote.")


def chunk_string(evidence_root, envelope, logical_event):
    """Return a repeatable text field backed by a logical JSON string."""
    def fragments():
        with ChunkReader(evidence_root).open_text(envelope, logical_event) as stream:
            yield from iter_json_string(stream)
    return StreamText(fragments)
