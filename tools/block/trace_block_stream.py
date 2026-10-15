"""Validate and write retained traces without materializing the complete bundle.

Each traversal reads one point or snapshot at a time. The emitted bytes match
trace_block's ordinary renderer. This module starts no proof or compiler.
"""

from collections.abc import Mapping, Sequence
import copy
import filecmp
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import shutil
import tempfile

import trace_block
from trace_block_text import StreamText


class ReplayList(list):
    """A repeatable, read-only list whose factory retains no yielded values."""

    def __init__(self, factory):
        self.factory = factory

    def __iter__(self):
        return iter(self.factory())

    def __len__(self):
        return sum(1 for _ in self)

    def __bool__(self):
        return next(iter(self), self) is not self

    def __getitem__(self, index):
        if not isinstance(index, int) or index < 0:
            raise TypeError("The streaming list supports only nonnegative integer indices.")
        marker = object()
        value = next(itertools.islice(self, index, index + 1), marker)
        if value is marker:
            raise IndexError(index)
        return value

    def __eq__(self, other):
        if not isinstance(other, Sequence) or isinstance(other, (str, bytes, bytearray)):
            return False
        marker = object()
        return all(left == right for left, right in itertools.zip_longest(self, other, fillvalue=marker))

    def __ne__(self, other):
        return not self == other

    def __deepcopy__(self, memo):
        return self


class SnapshotMap(dict):
    """Load a snapshot only when a consumer requests that key."""

    def __init__(self, view, session_id):
        self.view = view
        self.session_id = session_id
        self.names = tuple(view.snapshot_keys)
        self.name_set = frozenset(self.names)
        if len(self.names) != len(self.name_set):
            raise ValueError("The projection contains duplicate snapshot keys.")

    def __iter__(self):
        return iter(self.names)

    def __len__(self):
        return len(self.names)

    def __bool__(self):
        return bool(self.names)

    def __contains__(self, key):
        return key in self.name_set

    def __getitem__(self, key):
        if key not in self:
            raise KeyError(key)
        value = self.view.get_snapshot(key)
        if isinstance(value, Mapping):
            value = dict(value)
            value.setdefault("session_id", self.session_id)
        return value

    def get(self, key, default=None):
        return self[key] if key in self else default

    def keys(self):
        return self.names

    def items(self):
        return ((key, self[key]) for key in self)

    def values(self):
        return (self[key] for key in self)

    def __deepcopy__(self, memo):
        return self


def build_stream_trace(request, view):
    """Use the ordinary validator with repeatable, bounded-memory containers."""
    result = copy.deepcopy(view.header)
    visits = ReplayList(view.iter_instruction_visits)
    result.update(points=ReplayList(view.iter_points),
                  snapshots=SnapshotMap(view, trace_block.logical_session_id(request)),
                  instruction_visits=visits, residual=view.residual)
    result.setdefault("coverage", {})["requested_trigger_instruction_list"] = visits
    return trace_block.build_trace(request, result, streaming=True)


def json_chunks(value, level=0):
    """Match json.dumps(sort_keys=True, indent=2, ensure_ascii=False)."""
    if isinstance(value, StreamText):
        yield '"'
        for part in value.iter_text():
            yield json.dumps(part, ensure_ascii=False, allow_nan=False)[1:-1]
        yield '"'
    elif isinstance(value, Mapping):
        names = sorted(value.keys())
        if not names:
            yield "{}"
            return
        yield "{\n"
        for index, key in enumerate(names):
            if not isinstance(key, str):
                raise TypeError("A trace map key must be a string.")
            if index:
                yield ",\n"
            yield "  " * (level + 1)
            yield json.dumps(key, ensure_ascii=False, allow_nan=False)
            yield ": "
            yield from json_chunks(value[key], level + 1)
        yield "\n" + "  " * level + "}"
    elif isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        iterator = iter(value)
        marker = object()
        first = next(iterator, marker)
        if first is marker:
            yield "[]"
            return
        yield "[\n"
        for index, item in enumerate(itertools.chain((first,), iterator)):
            if index:
                yield ",\n"
            yield "  " * (level + 1)
            yield from json_chunks(item, level + 1)
        yield "\n" + "  " * level + "]"
    else:
        yield json.dumps(value, ensure_ascii=False, allow_nan=False)


def json_document(value):
    yield from json_chunks(value)
    yield "\n"


def fenced_chunks(factory):
    """Find the exact fence with one scan, then render the complete field."""
    longest, trailing = 0, 0
    for chunk in factory():
        if not chunk:
            continue
        previous = trailing
        first = last_match = None
        for match in re.finditer(r"`+", chunk):
            first = match if first is None else first
            last_match = match
            longest = max(longest, len(match.group()))
        if first is not None:
            if first.start() == 0:
                longest = max(longest, previous + len(first.group()))
            trailing = (previous + len(chunk) if first.span() == (0, len(chunk))
                        else len(last_match.group()) if last_match.end() == len(chunk) else 0)
        else:
            trailing = 0
    fence = "`" * max(3, longest + 1)
    yield fence + "\n"
    last = ""
    for chunk in factory():
        if chunk:
            last = chunk
        yield chunk
    if not last.endswith("\n"):
        yield "\n"
    yield fence + "\n"


def markdown_chunks(trace):
    """Preserve the ordinary Markdown order and every rendered field."""
    def segments():
        yield "# Native trace\n"
        yield "Trace completeness: " + str(trace["completion"]["trace_complete"]).lower() + ".\n"
        yield "Proof closure: " + str(trace["completion"].get("proof_closed", False)).lower() + ".\n"
        for key in ("identity", "session", "pet_start_tick", "request", "coverage", "instruction_visits", "snapshots", "completion", "verdict"):
            yield "## " + key + "\n"
            yield lambda value=trace[key]: json_document(value)
        records = (("points/" + str(i), point) for i, point in enumerate(trace["points"]))
        if trace["residual"] is not None:
            records = itertools.chain(records, (("residual", trace["residual"]),))
        for location, point in records:
            yield "## " + location + "\n"
            for key in ("id", "session_id") + trace_block.POINT_KEYS + (("show_proof",) if location == "residual" else ()):
                if key not in point:
                    continue
                citation = "TRACE.json#" + trace_block.pointer(*location.split("/"), key)
                yield "### " + key + "\n\n" + citation + "\n"
                value = point[key]
                yield (value.iter_text if isinstance(value, StreamText) else
                       (lambda value=value: iter((value,))) if isinstance(value, str) else
                       (lambda value=value: json_document(value)))
        if trace["residual"] is None:
            yield "## residual\n\nNo residual capture is present. See the completion record.\n"
    for index, segment in enumerate(segments()):
        if index:
            yield "\n"
        if callable(segment):
            yield from fenced_chunks(segment)
        else:
            yield segment


def write_stream_bundle(out_dir, trace):
    """Check both immutable targets before installing either generated file."""
    directory = Path(out_dir)
    directory.mkdir(parents=True, exist_ok=True)
    pending, hashes = {}, {}
    try:
        for name, chunks in (("TRACE.json", json_document(trace)), ("TRACE.md", markdown_chunks(trace))):
            descriptor, path = tempfile.mkstemp(prefix="." + name + "-", dir=directory)
            pending[name] = Path(path)
            digest = hashlib.sha256()
            with os.fdopen(descriptor, "wb") as stream:
                for chunk in chunks:
                    payload = chunk.encode("utf-8")
                    digest.update(payload)
                    stream.write(payload)
            hashes[name] = digest.hexdigest()
        for name, path in pending.items():
            target = directory / name
            if target.exists() and not filecmp.cmp(path, target, shallow=False):
                raise ValueError("The output already contains different bytes: " + name)
        for name, path in pending.items():
            target = directory / name
            if not target.exists():
                # Link prevents concurrent writers from replacing an immutable target.
                os.link(path, target)
        return hashes
    finally:
        for path in pending.values():
            path.unlink(missing_ok=True)


def write_offline_bundle(out_dir, trace, evidence_dir, *, expected_session_sha256,
                         request_path, expected_request_sha256,
                         allow_historical_no_manifest=False,
                         raw_index_path=None, expected_raw_index_sha256=None,
                         raw_seal_path=None, expected_raw_seal_sha256=None, storage_records=None):
    """Seal an offline output with a link to its closed, unchanged raw evidence.

The two TRACE files keep their deterministic bytes. EVIDENCE-MAP.json binds the
runtime directory, session bytes, event seals, and both generated outputs.
"""
    directory = Path(out_dir)
    raw = Path(evidence_dir).resolve(strict=True)
    from trace_block_seal import verify_raw_evidence
    verification = verify_raw_evidence(raw, trace, request_path,
        expected_session_sha256=expected_session_sha256,
        expected_request_sha256=expected_request_sha256,
        allow_historical_no_manifest=allow_historical_no_manifest,
        raw_index_path=raw_index_path, expected_raw_index_sha256=expected_raw_index_sha256,
        raw_seal_path=raw_seal_path, expected_raw_seal_sha256=expected_raw_seal_sha256,
        storage_records=storage_records)
    session_path = raw / "SESSION.json"
    payload = session_path.read_bytes()
    session_hash = hashlib.sha256(payload).hexdigest()
    if session_hash != expected_session_sha256:
        raise ValueError("The raw session differs from its retained input hash.")
    session = json.loads(payload)
    owner = session.get("ownership", {})
    if (owner.get("transport_closed_normally") is not True
            or owner.get("owned_pet_exited") is not True):
        raise ValueError("The raw evidence has no normal owned closure.")
    pet = owner.get("pet")
    if (not isinstance(pet, dict) or type(pet.get("pid")) is not int
            or type(pet.get("start_ticks")) is not int):
        raise ValueError("The raw evidence lacks the actual Pet identity.")
    if trace.get("runtime_evidence") != "evidence/SESSION.json":
        raise ValueError("The trace has an unsupported runtime evidence path.")
    target = directory / "evidence"
    if target.is_symlink():
        if target.resolve(strict=True) != raw:
            raise ValueError("The output evidence link has a different target.")
    elif target.exists():
        raise ValueError("The offline output evidence must use the bound raw-directory link.")
    raw_bindings = {"SESSION.json": session_hash}
    for name in ("EVENT-INDEX.json", "EVENT-SEAL.json"):
        path = raw / name
        if not path.is_file():
            if trace.get("coverage", {}).get("raw_event_index") is None:
                raise ValueError("The raw evidence lacks " + name + ".")
            continue
        raw_bindings[name] = trace_block.sha256(path)
    external = {}
    if trace.get("coverage", {}).get("raw_event_index") is not None:
        external = {"raw/INDEX.json": (Path(raw_index_path), expected_raw_index_sha256),
                    "RAW-SEAL.json": (Path(raw_seal_path), expected_raw_seal_sha256)}
        from trace_block_seal import file_sha256
        for name, (source, digest) in external.items():
            output = directory / name
            if output.exists() and file_sha256(output) != digest:
                raise ValueError("The output contains a different raw sidecar: " + name)
    output_hashes = write_stream_bundle(directory, trace)
    # Check retained inputs again after all streaming reads and writes.
    if any(trace_block.sha256(raw / name) != digest for name, digest in raw_bindings.items()):
        raise ValueError("The raw evidence changed during offline output.")
    final_verification = verify_raw_evidence(raw, trace, request_path,
        expected_session_sha256=expected_session_sha256,
        expected_request_sha256=expected_request_sha256,
        allow_historical_no_manifest=allow_historical_no_manifest,
        raw_index_path=raw_index_path, expected_raw_index_sha256=expected_raw_index_sha256,
        raw_seal_path=raw_seal_path, expected_raw_seal_sha256=expected_raw_seal_sha256,
        storage_records=storage_records)
    if final_verification != verification:
        raise ValueError("The verified raw evidence changed during output.")
    for name, (source, digest) in external.items():
        output = directory / name
        output.parent.mkdir(parents=True, exist_ok=True)
        if not output.exists():
            with source.open("rb") as origin, output.open("xb") as destination:
                shutil.copyfileobj(origin, destination, length=1024 * 1024)
        if file_sha256(output) != digest:
            raise ValueError("The output raw sidecar changed: " + name)
        output_hashes[name] = digest
    mapping = {"schema_version": 1, "session": trace["session"]["id"],
               "raw_verification": verification,
               "link": "evidence", "target": str(raw),
               "runtime_evidence": "evidence/SESSION.json",
               "raw_bindings": raw_bindings, "outputs": output_hashes,
               "ownership": {key: owner[key] for key in
                   ("transport_closed_normally", "owned_pet_exited", "pet")}}
    mapping_bytes = trace_block.json_bytes(mapping)
    mapping_path = directory / "EVIDENCE-MAP.json"
    if mapping_path.exists() and mapping_path.read_bytes() != mapping_bytes:
        raise ValueError("The output already contains a different evidence mapping.")
    if not target.is_symlink():
        target.symlink_to(raw, target_is_directory=True)
    if not mapping_path.exists():
        with mapping_path.open("xb") as stream:
            stream.write(mapping_bytes)
    return {**output_hashes, "EVIDENCE-MAP.json": hashlib.sha256(mapping_bytes).hexdigest()}
