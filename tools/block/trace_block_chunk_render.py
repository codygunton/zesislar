"""Render one logical capture without constructing its JSON value."""

import hashlib
from pathlib import Path
import tempfile

from trace_block_chunks import ChunkReader


def write_capture_documents(evidence_root, envelope, logical_event, out_dir):
    """Write exact capture JSON and a complete fenced copy for inspection.

    These files describe one capture. They are not a stable TRACE bundle.
    The caller must keep the sealed input files unchanged during rendering.
    """
    from trace_block_stream import fenced_chunks
    reader = ChunkReader(evidence_root)
    reader.validate(envelope, logical_event)
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    names = ("CAPTURE.json", "CAPTURE.md")
    if any((out_dir / name).exists() for name in names):
        raise ValueError("The capture output already exists.")
    result = {}
    with tempfile.TemporaryDirectory(prefix=".capture-", dir=out_dir) as directory:
        staged = Path(directory)
        factories = {
            "CAPTURE.json": lambda: reader.iter_text(envelope, logical_event),
            "CAPTURE.md": lambda: fenced_chunks(lambda: reader.iter_text(envelope, logical_event)),
        }
        for name in names:
            digest = hashlib.sha256()
            count = 0
            with (staged / name).open("xb") as stream:
                for text in factories[name]():
                    raw = text.encode("utf-8")
                    stream.write(raw)
                    digest.update(raw)
                    count += len(raw)
            result[name] = {"path": name, "sha256": digest.hexdigest(), "bytes": count}
        for name in names:
            (staged / name).rename(out_dir / name)
    return result
