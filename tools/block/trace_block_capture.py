"""Project and seal a closed capture without a materialized BACKEND document."""

import json
from pathlib import Path

import trace_block
from trace_block_seal import checked_reference, file_sha256
from trace_block_stream import build_stream_trace, write_offline_bundle


def validate_capture(request, raw_root, manifest):
    """Check the small API result against its exact retained session."""
    raw_root = Path(raw_root).resolve(strict=True)
    if manifest.get("schema_version") != 1 or manifest.get("projection") != "not-run":
        raise ValueError("The capture API returned an unsupported manifest.")
    paths = {}
    for key, name in (("request", "REQUEST.json"), ("session", "SESSION.json")):
        paths[key] = checked_reference(manifest.get(key))
        if paths[key].resolve() != raw_root / "evidence" / name:
            raise ValueError("The capture reference leaves its owned raw directory: " + key)
    retained = json.loads(paths["request"].read_text())
    if retained != dict(request, writer_id=retained.get("writer_id")):
        raise ValueError("The capture request differs from the prepared request.")
    from trace_block_prepare import writer_identity
    if retained.get("writer_id") != writer_identity(request):
        raise ValueError("The capture request has a different writer identity.")
    session = json.loads(paths["session"].read_text())
    for key, session_key in (("owned_closure", "ownership"),
                              ("source_unchanged", "source_unchanged"), ("error", "error")):
        if key not in manifest or manifest[key] != session.get(session_key):
            raise ValueError("The capture manifest differs from its session: " + key)
    owner = manifest["owned_closure"]
    if (not isinstance(owner, dict) or owner.get("transport_closed_normally") is not True
            or owner.get("owned_pet_exited") is not True):
        raise ValueError("The capture has no normal owned closure.")
    return retained, paths


def write_raw_seal(raw_root, path, session_id):
    """Hash every closed raw file while keeping the seal outside its root."""
    root, path = Path(raw_root).resolve(strict=True), Path(path).absolute()
    if path.is_relative_to(root):
        raise ValueError("The raw seal must remain outside the immutable raw directory.")
    files = []
    for source in sorted(root.rglob("*")):
        if source.is_symlink() and not source.is_file():
            raise ValueError("A raw link is broken or does not target a regular file: " + str(source))
        if source.is_file():
            files.append({"path": source.relative_to(root).as_posix(),
                          "sha256": file_sha256(source), "bytes": source.stat().st_size})
    record = {"schema_version": 1, "root": str(root), "session_id": session_id,
              "files": files}
    payload = trace_block.json_bytes(record)
    if path.exists() and path.read_bytes() != payload:
        raise ValueError("The output contains a different complete raw seal.")
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        with path.open("xb") as stream:
            stream.write(payload)
    return {"path": str(path), "sha256": file_sha256(path)}


def project_capture(request, out_dir, raw_root, manifest, *, view_factory=None,
                    storage_records=None):
    """Validate capture ownership, then stream the selected projection and seal."""
    retained, paths = validate_capture(request, raw_root, manifest)
    runtime = retained.get("observer_runtime")
    if (view_factory is None and isinstance(runtime, dict) and runtime.get("surface_policy") == "bounded-kernel-v1"):
        if storage_records is not None:
            raise ValueError("Bounded capture storage records require an explicit supported adapter.")
        from trace_block_bounded_bundle import write_bundle
        return write_bundle(request, out_dir, raw_root, manifest)
    if view_factory is None:
        if retained.get("observer_runtime") is not None:
            from trace_block_filtered_projection import ProjectionView
            view_factory = lambda request, evidence: ProjectionView(
                request, evidence, index_dir=Path(out_dir) / "projection-index")
        else:
            from trace_block_projection import ProjectionView
            view_factory = ProjectionView
    directory = Path(out_dir)
    directory.mkdir(parents=True, exist_ok=True)
    if directory.resolve().is_relative_to(Path(raw_root).resolve()):
        raise ValueError("The output must remain outside the immutable raw directory.")
    view = view_factory(retained, paths["session"].parent)
    try:
        index_path = directory / "raw" / "INDEX.json"
        index_path.parent.mkdir(parents=True, exist_ok=True)
        view.write_raw_index(index_path)
        index_hash = file_sha256(index_path)
        trace = build_stream_trace(retained, view)
        if manifest.get("admission_exit_status") not in (None, 0):
            trace["completion"]["trace_complete"] = False
            trace["completion"]["reasons"].append(
                "The admitted capture controller exited with status " + str(manifest["admission_exit_status"]))
            trace["verdict"] = trace_block.observed_verdict(trace)
        seal = write_raw_seal(raw_root, directory / "RAW-SEAL.json", trace_block.logical_session_id(retained))
        write_offline_bundle(directory, trace, paths["session"].parent,
            expected_session_sha256=manifest["session"]["sha256"],
            request_path=paths["request"], expected_request_sha256=manifest["request"]["sha256"],
            raw_index_path=index_path, expected_raw_index_sha256=index_hash,
            raw_seal_path=seal["path"], expected_raw_seal_sha256=seal["sha256"],
            storage_records=storage_records)
        # A lazy trace remains valid only while its document indexes stay open.
        # Generated outputs are now immutable. Return their small completion record.
        if retained.get("observer_runtime") is not None:
            return {key: trace[key] for key in ("completion", "verdict", "coverage", "session")}
        return trace
    finally:
        close = getattr(view, "close", None)
        if close is not None:
            close()


def capture_bundle(request, out_dir, backend):
    """Keep raw capture separate from every generated output."""
    raw_root = Path(out_dir) / "raw-capture"
    manifest = backend.run_capture(request, raw_root)
    return project_capture(request, out_dir, raw_root, manifest)
