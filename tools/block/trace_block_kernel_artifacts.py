"""Read inline or lossless chunked kernel metadata with external lazy indexes."""
from collections.abc import Mapping
from contextlib import ExitStack
import hashlib
from pathlib import Path

from trace_block_chunks import ChunkReader
from trace_block_lazy_capture import LazyCapture
from trace_block_kernel import artifact, _fields, _hash, _json


class ArtifactReader:
    """Keep every lazy view open only within this explicit reader lifetime."""

    def __init__(self, evidence_root, index_dir):
        self.root = Path(evidence_root).resolve(strict=True)
        self.index_dir = Path(index_dir).resolve()
        if self.index_dir.is_relative_to(self.root) or Path(index_dir).is_symlink():
            raise ValueError('Metadata indexes must remain outside immutable evidence.')
        self.index_dir.mkdir(parents=True, exist_ok=True)
        self.stack = ExitStack()
        self.cache = {}
        self.closed = False

    def __enter__(self):
        return self

    def __exit__(self, *arguments):
        self.close()

    def close(self):
        self.closed = True
        self.cache.clear()
        self.stack.close()

    def read(self, reference):
        """Validate all physical and logical bytes before exposing a JSON value."""
        if self.closed:
            raise ValueError('The kernel metadata reader is closed.')
        if not isinstance(reference, Mapping) or set(reference) != {'path', 'sha256', 'bytes'}:
            raise ValueError('The metadata artifact reference has unsupported fields.')
        reference = {key: reference[key] for key in reference}
        path = artifact(self.root, reference)
        identity = (reference['path'], reference['sha256'], reference['bytes'])
        if identity in self.cache:
            return self.cache[identity]
        record = _json(path)
        if isinstance(record, dict) and (record.get('schema') == 2 or record.get('kind') == 'kernel-json-artifact'):
            _fields(record, 'schema kind logical_event logical_sha256 payload')
            if (type(record['schema']) is not int or record['schema'] != 2
                    or record['kind'] != 'kernel-json-artifact'):
                raise ValueError('The metadata artifact wrapper has an unsupported schema or kind.')
            expected_event = 'kernel-json/' + reference['path']
            if record['logical_event'] != expected_event:
                raise ValueError('The metadata logical identity differs from its exact artifact path.')
            _hash(record['logical_sha256'])
            reader = ChunkReader(self.root)
            reader.validate(record['payload'], expected_event)
            digest = hashlib.sha256()
            for text in reader.iter_text(record['payload'], expected_event):
                digest.update(text.encode('utf-8'))
            if digest.hexdigest() != record['logical_sha256']:
                raise ValueError('The complete metadata logical hash differs.')
            index_path = self.index_dir / ('artifact-%08d.sqlite' % len(self.cache))
            document = self.stack.enter_context(LazyCapture(
                self.root, record['payload'], expected_event, index_path))
            value = document.root
        else:
            value = record
        self.cache[identity] = value
        return value
