"""Index logical JSON structure on disk and load only requested fields."""

from collections.abc import Mapping, Sequence
import hashlib
import json
from pathlib import Path
import sqlite3

from trace_block_chunks import ChunkReader, ChunkTextStream
from trace_block_event_identity import _Reader
from trace_block_text import StreamText, iter_json_string


class _ByteText:
    """Present UTF-8 bytes as Latin-1 characters for exact byte offsets."""

    def __init__(self, chunks):
        self.stream = ChunkTextStream(lambda_part.decode("latin1") for lambda_part in chunks)
        self.position = 0

    def read(self, size):
        text = self.stream.read(size)
        self.position += len(text)
        return text


class LazyCapture:
    """Keep JSON structure in SQLite and retain text in the sealed chunks.

    The index is a disposable projection artifact. The capture chunks remain
    authoritative. The caller must preserve their complete external seal.
    """

    def __init__(self, evidence_root, envelope, logical_event, index_path):
        self.reader = ChunkReader(evidence_root)
        self.envelope = envelope
        self.logical_event = logical_event
        self.index_path = Path(index_path)
        if self.index_path.exists() or self.index_path.is_symlink():
            raise ValueError("The capture index path already exists.")
        self.reader.validate(envelope, logical_event)
        self.index_path.parent.mkdir(parents=True, exist_ok=True)
        # Each new index binds the exact complete capture. An existing index
        # cannot silently substitute cached structure for different inputs.
        self.database = sqlite3.connect(str(self.index_path))
        self.database.execute("PRAGMA cache_size=-2048")
        self.database.execute("PRAGMA temp_store=FILE")
        try:
            self.database.executescript("""
                CREATE TABLE metadata (identity TEXT NOT NULL);
                CREATE TABLE nodes (
                    id INTEGER PRIMARY KEY, parent INTEGER, name TEXT,
                    ordinal INTEGER NOT NULL, kind TEXT NOT NULL,
                    start INTEGER NOT NULL, stop INTEGER,
                    UNIQUE(parent, name), UNIQUE(parent, ordinal));
                CREATE INDEX children ON nodes(parent, ordinal);
            """)
            identity = json.dumps({"envelope": envelope, "logical_event": logical_event}, sort_keys=True)
            self.database.execute("INSERT INTO metadata VALUES (?)", (hashlib.sha256(identity.encode()).hexdigest(),))
            byte_stream = _ByteText(part.encode("utf-8") for part in self.reader.iter_text(envelope, logical_event))
            self.parser = _Reader(byte_stream)
            self.byte_stream = byte_stream
            self.root_id = self._parse(None, None, 0, 0)
            self.parser.space()
            if self.parser.peek():
                raise ValueError("The capture index contains trailing JSON content.")
            self.database.commit()
            del self.parser
            del self.byte_stream
        except BaseException:
            self.database.close()
            raise

    def close(self):
        self.database.close()

    def __enter__(self):
        return self

    def __exit__(self, *arguments):
        self.close()

    def _position(self):
        return self.byte_stream.position - len(self.parser.buffer) + self.parser.offset

    def _parse(self, parent, name, ordinal, depth):
        if depth > 128:
            raise ValueError("The capture metadata exceeds the supported JSON depth.")
        reader = self.parser
        reader.space()
        start = self._position()
        char = reader.peek()
        kind = {"{": "object", "[": "array", '"': "string"}.get(char, "scalar")
        try:
            node_id = self.database.execute(
                "INSERT INTO nodes(parent,name,ordinal,kind,start) VALUES (?,?,?,?,?)",
                (parent, name, ordinal, kind, start)).lastrowid
        except sqlite3.IntegrityError as error:
            raise ValueError("The logical capture contains a duplicate object key.") from error
        if kind in ("object", "array"):
            reader.take()
            closing = "}" if kind == "object" else "]"
            reader.space()
            index = 0
            if reader.peek() != closing:
                while True:
                    child_name = None
                    if kind == "object":
                        reader.space()
                        key_start = self._position()
                        reader.string()
                        key_stop = self._position()
                        if key_stop - key_start > 65536:
                            raise ValueError("A capture metadata key exceeds 65536 bytes.")
                        child_name = json.loads("".join(self._text(key_start, key_stop)))
                        reader.expect(":")
                    self._parse(node_id, child_name, index, depth + 1)
                    index += 1
                    reader.space()
                    if reader.peek() != ",":
                        break
                    reader.take()
            reader.expect(closing)
        elif kind == "string":
            reader.string()
        else:
            reader.scalar()
        self.database.execute("UPDATE nodes SET stop=? WHERE id=?", (self._position(), node_id))
        return node_id

    def _row(self, node_id):
        row = self.database.execute("SELECT kind,start,stop FROM nodes WHERE id=?", (node_id,)).fetchone()
        if row is None:
            raise KeyError(node_id)
        return row

    def _text(self, start, stop):
        # JSON token boundaries use ASCII. The range therefore begins and ends
        # on UTF-8 boundaries. A decoder preserves codepoints across leaves.
        import codecs
        decoder = codecs.getincrementaldecoder("utf-8")()
        for part in self.reader.iter_bytes_range(self.envelope, self.logical_event, start, stop):
            text = decoder.decode(part)
            if text:
                yield text
        final = decoder.decode(b"", final=True)
        if final:
            yield final

    def value(self, node_id):
        kind, start, stop = self._row(node_id)
        if kind == "object":
            return _Object(self, node_id)
        if kind == "array":
            return _Array(self, node_id)
        if kind == "string":
            if stop - start <= 65536:
                return json.loads("".join(self._text(start, stop)))
            def fragments():
                with ChunkTextStream(self._text(start, stop)) as stream:
                    yield from iter_json_string(stream)
            return StreamText(fragments)
        return json.loads("".join(self._text(start, stop)))

    @property
    def root(self):
        return self.value(self.root_id)


class _Object(Mapping):
    def __init__(self, capture, node_id):
        self.capture, self.node_id = capture, node_id

    def __iter__(self):
        for row in self.capture.database.execute("SELECT name FROM nodes WHERE parent=? ORDER BY ordinal", (self.node_id,)):
            yield row[0]

    def __len__(self):
        return self.capture.database.execute("SELECT COUNT(*) FROM nodes WHERE parent=?", (self.node_id,)).fetchone()[0]

    def __bool__(self):
        return bool(len(self))

    def __contains__(self, name):
        return self.capture.database.execute("SELECT 1 FROM nodes WHERE parent=? AND name=?", (self.node_id, name)).fetchone() is not None

    def __getitem__(self, name):
        row = self.capture.database.execute("SELECT id FROM nodes WHERE parent=? AND name=?", (self.node_id, name)).fetchone()
        if row is None:
            raise KeyError(name)
        return self.capture.value(row[0])

    def get(self, name, default=None):
        return self[name] if name in self else default

    def keys(self):
        return iter(self)

    def items(self):
        return ((name, self[name]) for name in self)

    def values(self):
        return (self[name] for name in self)

    def __eq__(self, other):
        return isinstance(other, Mapping) and set(self) == set(other) and all(self[key] == other[key] for key in self)

    def __ne__(self, other):
        return not self == other

    def __deepcopy__(self, memo):
        return self


class _Array(Sequence):
    def __init__(self, capture, node_id):
        self.capture, self.node_id = capture, node_id

    def __iter__(self):
        for row in self.capture.database.execute("SELECT id FROM nodes WHERE parent=? ORDER BY ordinal", (self.node_id,)):
            yield self.capture.value(row[0])

    def __len__(self):
        return self.capture.database.execute("SELECT COUNT(*) FROM nodes WHERE parent=?", (self.node_id,)).fetchone()[0]

    def __bool__(self):
        return bool(len(self))

    def __getitem__(self, index):
        if isinstance(index, slice):
            return _ArraySlice(self, range(len(self))[index])
        if type(index) is not int:
            raise TypeError("The capture array requires an integer or slice index.")
        if index < 0:
            index += len(self)
        if index < 0:
            raise IndexError(index)
        row = self.capture.database.execute("SELECT id FROM nodes WHERE parent=? AND ordinal=?", (self.node_id, index)).fetchone()
        if row is None:
            raise IndexError(index)
        return self.capture.value(row[0])

    def __eq__(self, other):
        return isinstance(other, Sequence) and not isinstance(other, (str, bytes)) and len(self) == len(other) and all(a == b for a, b in zip(self, other))

    def __ne__(self, other):
        return not self == other

    def __deepcopy__(self, memo):
        return self


class _ArraySlice(Sequence):
    def __init__(self, array, indices):
        self.array, self.indices = array, indices

    def __len__(self):
        return len(self.indices)

    def __getitem__(self, index):
        if isinstance(index, slice):
            return _ArraySlice(self.array, self.indices[index])
        return self.array[self.indices[index]]
