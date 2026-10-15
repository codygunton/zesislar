"""Check and read schema2 capture chunks without a complete capture tree."""

import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re

MAX_RECORD_BYTES = 2_097_152
MAX_TEXT_BYTES = 262_144
MAX_CHILDREN = 256
MAX_LEVEL = 32


def _integer(value, minimum=0):
    if type(value) is not int or value < minimum:
        raise ValueError("A chunk integer is invalid.")
    return value


def _fields(value, names):
    if not isinstance(value, dict) or set(value) != set(names.split()):
        raise ValueError("A chunk record has unsupported fields.")


def _digest(value):
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise ValueError("A chunk hash is invalid.")
    return value


def _object(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError("A chunk record contains a duplicate key.")
        value[key] = item
    return value


class ChunkReader:
    """Check every physical record before yielding its logical UTF-8 text."""

    def __init__(self, evidence_root):
        self.root = Path(evidence_root).resolve(strict=True)

    def _path(self, name):
        if not isinstance(name, str) or not name:
            raise ValueError("A chunk path is invalid.")
        path = PurePosixPath(name)
        if path.is_absolute() or any(part in (".", "..") for part in name.split("/")):
            raise ValueError("A chunk path leaves the evidence root.")
        candidate = self.root
        for part in path.parts:
            candidate = candidate / part
            if candidate.is_symlink():
                raise ValueError("A chunk path contains a symlink.")
        if not candidate.is_file():
            raise ValueError("A capture chunk is missing.")
        return candidate

    def _node(self, reference):
        if not isinstance(reference, dict):
            raise ValueError("A chunk reference is invalid.")
        _fields(reference, "path sha256 bytes" + (" logical_bytes" if "logical_bytes" in reference else ""))
        expected = _integer(reference["bytes"], 1)
        if expected > MAX_RECORD_BYTES:
            raise ValueError("A chunk reference exceeds the serialized byte limit.")
        path = self._path(reference["path"])
        with path.open("rb") as stream:
            raw = stream.read(MAX_RECORD_BYTES + 1)
        if len(raw) > MAX_RECORD_BYTES:
            raise ValueError("A chunk record exceeds the serialized byte limit.")
        if len(raw) != expected or hashlib.sha256(raw).hexdigest() != _digest(reference["sha256"]):
            raise ValueError("A chunk record does not match its reference.")
        try:
            node = json.loads(raw.decode("utf-8"), object_pairs_hook=_object)
        except (UnicodeError, json.JSONDecodeError) as error:
            raise ValueError("A chunk record contains invalid UTF-8 JSON.") from error
        if not isinstance(node, dict) or type(node.get("schema")) is not int or node["schema"] != 2:
            raise ValueError("A chunk record has an unsupported schema.")
        return node

    def iter_text(self, envelope, logical_event):
        """Yield complete leaf strings in order after all local checks pass.

        The caller must exhaust the iterator to check totals and all references.
        Output remains provisional until the iterator reaches its end.
        """
        _fields(envelope, "encoding root logical_bytes")
        if envelope["encoding"] != "json-chunks-v1":
            raise ValueError("The capture encoding is unsupported.")
        _fields(envelope["root"], "path sha256 bytes")
        total = _integer(envelope["logical_bytes"])
        if not isinstance(logical_event, str) or not logical_event:
            raise ValueError("The logical event identity is invalid.")
        ordinal = 0
        active = set()

        def visit(reference, expected_level=None):
            nonlocal ordinal
            name = reference["path"]
            if name in active:
                raise ValueError("A capture contains a chunk cycle.")
            active.add(name)
            node = self._node(reference)
            if node.get("logical_event") != logical_event:
                raise ValueError("A chunk belongs to a different logical event.")
            if node.get("kind") == "capture-leaf":
                _fields(node, "schema kind logical_event ordinal encoding text text_bytes payload_sha256")
                if expected_level not in (None, 0):
                    raise ValueError("A chunk index has an incorrect level.")
                if _integer(node["ordinal"]) != ordinal:
                    raise ValueError("Capture leaf ordinals are not consecutive.")
                ordinal += 1
                if node["encoding"] != "utf-8" or not isinstance(node["text"], str):
                    raise ValueError("A capture leaf has an unsupported encoding.")
                try:
                    raw = node["text"].encode("utf-8")
                except UnicodeError as error:
                    raise ValueError("A capture leaf contains an invalid Unicode scalar.") from error
                count = _integer(node["text_bytes"])
                if len(raw) != count or count > MAX_TEXT_BYTES:
                    raise ValueError("A capture leaf exceeds its text byte limit or count.")
                if hashlib.sha256(raw).hexdigest() != _digest(node["payload_sha256"]):
                    raise ValueError("A capture leaf payload hash does not match.")
                yield node["text"]
            elif node.get("kind") == "capture-index":
                _fields(node, "schema kind logical_event level children logical_bytes")
                level = _integer(node["level"], 1)
                if level > MAX_LEVEL or expected_level not in (None, level):
                    raise ValueError("A capture index has an invalid level.")
                children = node["children"]
                if not isinstance(children, list) or not 1 <= len(children) <= MAX_CHILDREN:
                    raise ValueError("A capture index exceeds its child limit.")
                count = 0
                for child in children:
                    _fields(child, "path sha256 bytes logical_bytes")
                    child_count = _integer(child["logical_bytes"])
                    count += child_count
                    yield from visit(child, level - 1)
                if count != _integer(node["logical_bytes"]):
                    raise ValueError("A capture index has an incorrect logical byte count.")
            else:
                raise ValueError("A chunk record has an unsupported kind.")
            if "logical_bytes" in reference and count != reference["logical_bytes"]:
                raise ValueError("A child reference has an incorrect logical byte count.")
            active.remove(name)
            return count

        observed = yield from visit(envelope["root"])
        if observed != total:
            raise ValueError("The capture has an incorrect logical byte total.")

    def open_text(self, envelope, logical_event):
        return ChunkTextStream(self.iter_text(envelope, logical_event))

    def iter_bytes_range(self, envelope, logical_event, start, end):
        """Read an exact byte range after complete capture validation.

        Each visited node must still match its hash. The caller must bind the
        complete validation result before it uses ranges for projection.
        """
        _fields(envelope, "encoding root logical_bytes")
        if envelope["encoding"] != "json-chunks-v1":
            raise ValueError("The capture encoding is unsupported.")
        _integer(start)
        _integer(end)
        if not start <= end <= _integer(envelope["logical_bytes"]):
            raise ValueError("The logical capture byte range is invalid.")
        def visit(reference, offset, size, level=None):
            if offset >= end or offset + size <= start:
                return
            node = self._node(reference)
            if node.get("logical_event") != logical_event:
                raise ValueError("A chunk belongs to a different logical event.")
            if node.get("kind") == "capture-leaf":
                if level not in (None, 0):
                    raise ValueError("A chunk index has an incorrect level.")
                raw = node["text"].encode("utf-8")
                if len(raw) != size or size != node["text_bytes"] or size > MAX_TEXT_BYTES:
                    raise ValueError("A capture leaf has an incorrect byte count.")
                if hashlib.sha256(raw).hexdigest() != _digest(node["payload_sha256"]):
                    raise ValueError("A capture leaf payload hash does not match.")
                yield raw[max(0, start - offset):min(size, end - offset)]
            elif node.get("kind") == "capture-index":
                actual_level = _integer(node["level"], 1)
                if actual_level > MAX_LEVEL or level not in (None, actual_level):
                    raise ValueError("A capture index has an invalid level.")
                children = node["children"]
                if not isinstance(children, list) or not 1 <= len(children) <= MAX_CHILDREN:
                    raise ValueError("A capture index exceeds its child limit.")
                total = 0
                for child in children:
                    _fields(child, "path sha256 bytes logical_bytes")
                    child_size = _integer(child["logical_bytes"])
                    yield from visit(child, offset + total, child_size, actual_level - 1)
                    total += child_size
                if total != size or total != node["logical_bytes"]:
                    raise ValueError("A capture index has an incorrect logical byte count.")
            else:
                raise ValueError("A chunk record has an unsupported kind.")
        yield from visit(envelope["root"], 0, envelope["logical_bytes"])

    def validate(self, envelope, logical_event):
        """Check the full logical JSON syntax with bounded parser buffers."""
        from trace_block_event_identity import _Reader
        with self.open_text(envelope, logical_event) as stream:
            reader = _Reader(stream)
            reader.skip_value()
            reader.space()
            if reader.peek():
                raise ValueError("The logical capture contains trailing JSON content.")


class ChunkTextStream(io.TextIOBase):
    """Expose bounded reads without joining the complete logical capture."""

    def __init__(self, chunks):
        super().__init__()
        self.chunks = iter(chunks)
        self.pending = ""

    def readable(self):
        return True

    def read(self, size=-1):
        if self.closed:
            raise ValueError("The capture stream is closed.")
        if type(size) is not int or size < 0:
            raise ValueError("The capture stream requires a bounded read size.")
        parts = []
        while size:
            if not self.pending:
                self.pending = next(self.chunks, "")
                if not self.pending:
                    # Empty leaves do not terminate the logical stream.
                    for chunk in self.chunks:
                        if chunk:
                            self.pending = chunk
                            break
                    if not self.pending:
                        break
            parts.append(self.pending[:size])
            used = min(size, len(self.pending))
            self.pending = self.pending[used:]
            size -= used
        return "".join(parts)
