"""Check streaming byte identity and the retained validation boundary."""

import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import tracemalloc
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
import trace_block
import trace_block_prepare
from trace_block_stream import (ReplayList, SnapshotMap, build_stream_trace,
    fenced_chunks, json_document, markdown_chunks, write_stream_bundle, write_offline_bundle)
from test_trace_block import fixture


class FixtureView:
    def __init__(self, result):
        self.result = result
        self.header = {key: value for key, value in result.items()
                       if key not in ("points", "snapshots", "instruction_visits", "residual")}
        self.header = copy.deepcopy(self.header)
        self.header["coverage"].pop("requested_trigger_instruction_list", None)
        self.snapshot_keys = tuple(result["snapshots"])

    def get_snapshot(self, key):
        return copy.deepcopy(self.result["snapshots"][key])

    def iter_points(self):
        return iter(copy.deepcopy(self.result["points"]))

    def iter_instruction_visits(self):
        return iter(copy.deepcopy(self.result["instruction_visits"]))

    @property
    def residual(self):
        return copy.deepcopy(self.result["residual"])


class StreamingTests(unittest.TestCase):
    def test_all_golden_bytes_match(self):
        for kind in ("introduction", "store", "return"):
            with self.subTest(kind=kind):
                request, result = fixture(kind)
                ordinary = trace_block.build_trace(request, result)
                streamed = build_stream_trace(request, FixtureView(result))
                self.assertTrue(streamed["completion"]["trace_complete"])
                self.assertEqual("".join(json_document(streamed)).encode(), trace_block.json_bytes(ordinary))
                self.assertEqual("".join(markdown_chunks(streamed)), trace_block.render_markdown(ordinary))

    def test_invalid_scope_has_identical_rejection(self):
        request, result = fixture("store")
        result["identity"]["source_sha256"] = "d" * 64
        ordinary = trace_block.build_trace(request, result)
        streamed = build_stream_trace(request, FixtureView(result))
        self.assertFalse(streamed["completion"]["trace_complete"])
        self.assertEqual(json.loads("".join(json_document(streamed))), ordinary)

    def test_bad_command_pointer_has_identical_rejection(self):
        request, result = fixture("store")
        result["points"][0]["hand_call"][0]["commands"][0]["before"] = "#/snapshots/trial"
        ordinary = trace_block.build_trace(request, result)
        streamed = build_stream_trace(request, FixtureView(result))
        self.assertFalse(streamed["completion"]["trace_complete"])
        self.assertEqual(json.loads("".join(json_document(streamed))), ordinary)

    def test_missing_snapshot_rejects(self):
        request, result = fixture("store")
        del result["snapshots"]["trial"]
        streamed = build_stream_trace(request, FixtureView(result))
        self.assertFalse(streamed["completion"]["trace_complete"])

    def test_supplied_refutation_rejects(self):
        request, result = fixture("return")
        result["verdict"] = {"status": "established-unsatisfiable"}
        streamed = build_stream_trace(request, FixtureView(result))
        self.assertFalse(streamed["completion"]["trace_complete"])

    def test_nested_unicode_and_fences_match(self):
        value = {"z": [None, True, 3, "∀x\n````", {}], "a": {"β": []}}
        self.assertEqual("".join(json_document(value)).encode(), trace_block.json_bytes(value))
        text = "a`````b\n"
        self.assertEqual("".join(fenced_chunks(lambda: iter(("a``", "```b", "\n")))), trace_block._fence(text))

    def test_empty_fence_matches(self):
        self.assertEqual("".join(fenced_chunks(lambda: iter(("",)))), trace_block._fence(""))

    def test_replay_list_is_repeatable(self):
        sequence = ReplayList(lambda: iter((1, 2)))
        self.assertTrue(sequence)
        self.assertEqual(sequence, [1, 2])
        self.assertEqual(list(sequence), [1, 2])
        self.assertEqual(sequence[1], 2)
        self.assertFalse(sequence == [1])
        self.assertIs(copy.deepcopy(sequence), sequence)

    def test_snapshot_map_is_lazy(self):
        request, result = fixture("store")
        view = FixtureView(result)
        with patch.object(view, "get_snapshot", wraps=view.get_snapshot) as getter:
            snapshots = SnapshotMap(view, trace_block.logical_session_id(request))
            self.assertEqual(getter.call_count, 0)
            self.assertIn("entry", snapshots)
            self.assertEqual(getter.call_count, 0)
            self.assertEqual(snapshots["entry"]["session_id"], trace_block.logical_session_id(request))
            self.assertEqual(getter.call_count, 1)
            self.assertIs(copy.deepcopy(snapshots), snapshots)

    def test_streaming_writer_matches_immutable_writer(self):
        request, result = fixture("return")
        trace = build_stream_trace(request, FixtureView(result))
        ordinary = trace_block.build_trace(request, result)
        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            expected = trace_block.write_bundle(first, ordinary)
            actual = write_stream_bundle(second, trace)
            self.assertEqual(actual, expected)
            self.assertEqual(write_stream_bundle(second, trace), expected)
            for name in expected:
                self.assertEqual((Path(first) / name).read_bytes(), (Path(second) / name).read_bytes())
            self.assertFalse(list(Path(second).glob(".TRACE*")))

    def test_conflict_installs_neither_output(self):
        request, result = fixture("return")
        trace = build_stream_trace(request, FixtureView(result))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / "TRACE.md").write_text("existing")
            with self.assertRaises(ValueError):
                write_stream_bundle(path, trace)
            self.assertFalse((path / "TRACE.json").exists())
            self.assertEqual((path / "TRACE.md").read_text(), "existing")
            self.assertFalse(list(path.glob(".TRACE*")))

    def test_write_failure_removes_temporary_files(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(ValueError):
                write_stream_bundle(directory, {"not-finite": float("nan")})
            self.assertFalse(list(Path(directory).iterdir()))

    def test_large_lazy_json_does_not_retain_all_rows(self):
        sequence = ReplayList(lambda: ({"text": str(i) + "x" * 10000} for i in range(1000)))
        tracemalloc.start()
        try:
            count = sum(len(chunk) for chunk in json_document({"rows": sequence}))
            _, peak = tracemalloc.get_traced_memory()
        finally:
            tracemalloc.stop()
        self.assertGreater(count, 10_000_000)
        self.assertLess(peak, 1_000_000)

    def test_explicit_invalid_owner_does_not_use_environment(self):
        with patch.dict("os.environ", {"ZESU_WRITER_ID": "worker2-b"}):
            for value in ("", False, None, 0, [], {}):
                with self.subTest(value=value), self.assertRaises(ValueError):
                    trace_block_prepare.writer_identity({"writer_id": value})
            self.assertEqual(trace_block_prepare.writer_identity({}), "worker2-b")

    def test_cli_omits_unspecified_owner(self):
        class Backend:
            def prepare_request(backend, request, out):
                backend.request = request
                raise ValueError("Stop before startup.")
        backend = Backend()
        with tempfile.TemporaryDirectory() as directory, patch.object(trace_block, "resolve_request", side_effect=lambda request: request), patch("sys.stderr"):
            result = trace_block.main(["--block", "0x1000", "--rules", "ReturnRoute=on", "--stop", "jalr", "--out", directory], backend=backend)
        self.assertEqual(result, 1)
        self.assertNotIn("writer_id", backend.request)

    def test_cli_preserves_explicit_owner(self):
        class Backend:
            def prepare_request(backend, request, out):
                backend.request = request
                raise ValueError("Stop before startup.")
        backend = Backend()
        with tempfile.TemporaryDirectory() as directory, patch.object(trace_block, "resolve_request", side_effect=lambda request: request), patch("sys.stderr"):
            result = trace_block.main(["--block", "0x1000", "--rules", "ReturnRoute=on", "--stop", "jalr", "--out", directory, "--writer", "worker2-b"], backend=backend)
        self.assertEqual(result, 1)
        self.assertEqual(backend.request["writer_id"], "worker2-b")


class EvidenceMappingTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.raw = self.directory / "raw"
        self.raw.mkdir()
        self.owner = {"transport_closed_normally": True, "owned_pet_exited": True,
                      "pet": {"pid": 42, "start_ticks": 73}}
        request, result = fixture("return")
        request.update(workspace=str(self.directory), source=str(self.directory / "Fixture.v"),
                       theorem="fixture")
        self.request_path = self.raw / "REQUEST.json"
        self.request_path.write_bytes(trace_block.json_bytes(request))
        self.request_hash = hashlib.sha256(self.request_path.read_bytes()).hexdigest()
        start_path = self.raw / "start.json"
        start_path.write_bytes(trace_block.json_bytes({"structuredContent": {
            "success": True, "file": request["source"], "theorem": request["theorem"]}}))
        self.operations = [{"tool": "rocq_trace_start", "path": str(start_path),
            "sha256": hashlib.sha256(start_path.read_bytes()).hexdigest(),
            "arguments": {"workspace": request["workspace"], "file": request["source"],
                          "theorem": request["theorem"]}}]
        self.instrumentation = {"fixture": True}
        request["instrumentation"] = self.instrumentation
        self.request_path.write_bytes(trace_block.json_bytes(request))
        self.request_hash = hashlib.sha256(self.request_path.read_bytes()).hexdigest()
        (self.raw / "RUN-MANIFEST.json").write_bytes(trace_block.json_bytes({
            "revisions": {}, "prepared_instrumentation": self.instrumentation}))
        self.update_session()
        event = self.raw / "events/process-42/event-00000001.json"
        event.parent.mkdir(parents=True)
        event.write_text("{}\n")
        (self.raw / "EVENT-SEAL.json").write_bytes(trace_block.json_bytes({"streams": [
            {"path": "events/process-42/event-00000001.json",
             "sha256": hashlib.sha256(event.read_bytes()).hexdigest()}]}))
        (self.raw / "EVENT-INDEX.json").write_bytes(trace_block.json_bytes({"process": self.owner["pet"]}))
        self.trace = trace_block.build_trace(request, result)
        self.out = self.directory / "output"

    def update_session(self):
        payload = trace_block.json_bytes({"ownership": self.owner, "operations": self.operations, "revisions": {}})
        (self.raw / "SESSION.json").write_bytes(payload)
        self.expected = hashlib.sha256(payload).hexdigest()

    def write(self):
        return write_offline_bundle(self.out, self.trace, self.raw,
                                    expected_session_sha256=self.expected, request_path=self.request_path,
                                    expected_request_sha256=self.request_hash)

    def test_closed_evidence_link_and_hashes(self):
        result = self.write()
        self.assertEqual((self.out / "evidence").resolve(), self.raw.resolve())
        mapping = json.loads((self.out / "EVIDENCE-MAP.json").read_text())
        self.assertEqual(mapping["raw_bindings"]["SESSION.json"], self.expected)
        self.assertEqual(mapping["target"], str(self.raw.resolve()))
        self.assertEqual(mapping["ownership"]["pet"]["start_ticks"], 73)
        self.assertEqual((self.out / "evidence/SESSION.json").read_bytes(), (self.raw / "SESSION.json").read_bytes())
        self.assertEqual(self.write(), result)

    def test_unclosed_raw_capture_rejects_before_output(self):
        self.owner["owned_pet_exited"] = False
        self.update_session()
        with self.assertRaisesRegex(ValueError, "normal owned closure"):
            self.write()
        self.assertFalse(self.out.exists())

    def test_wrong_expected_session_hash_rejects(self):
        self.expected = "0" * 64
        with self.assertRaisesRegex(ValueError, "raw evidence reference changed"):
            self.write()
        self.assertFalse(self.out.exists())

    def test_missing_event_seal_rejects(self):
        (self.raw / "EVENT-SEAL.json").unlink()
        with self.assertRaisesRegex(ValueError, "EVENT-SEAL"):
            self.write()
        self.assertFalse(self.out.exists())

    def test_wrong_existing_link_rejects(self):
        self.out.mkdir()
        (self.out / "evidence").symlink_to(self.directory)
        with self.assertRaisesRegex(ValueError, "different target"):
            self.write()
        self.assertFalse((self.out / "TRACE.json").exists())

    def test_changed_raw_evidence_cannot_receive_seal(self):
        from trace_block_stream import write_stream_bundle as original
        def change_after_output(*args):
            result = original(*args)
            (self.raw / "EVENT-SEAL.json").write_text("changed")
            return result
        with patch("trace_block_stream.write_stream_bundle", side_effect=change_after_output):
            with self.assertRaisesRegex(ValueError, "changed during offline output"):
                self.write()
        self.assertFalse((self.out / "EVIDENCE-MAP.json").exists())
        self.assertFalse((self.out / "evidence").exists())

    def test_changed_event_without_changed_seal_rejects(self):
        (self.raw / "events/process-42/event-00000001.json").write_text("changed")
        with self.assertRaisesRegex(ValueError, "raw evidence reference changed"):
            self.write()
        self.assertFalse(self.out.exists())

    def test_unsealed_owned_event_rejects(self):
        (self.raw / "events/process-42/event-00000002.json").write_text("{}")
        with self.assertRaisesRegex(ValueError, "differs from its event seal"):
            self.write()

    def test_trace_session_association_rejects(self):
        self.trace["session"]["id"] = "trace-session-wrong"
        with self.assertRaisesRegex(ValueError, "differs from the retained request"):
            self.write()

    def test_request_source_differs_from_actual_start(self):
        request = json.loads(self.request_path.read_text())
        request["source"] = "another-file.v"
        self.request_path.write_bytes(trace_block.json_bytes(request))
        self.request_hash = hashlib.sha256(self.request_path.read_bytes()).hexdigest()
        with self.assertRaisesRegex(ValueError, "proof start differs"):
            self.write()

    def test_changed_operation_rejects(self):
        (self.raw / "start.json").write_text("changed")
        with self.assertRaisesRegex(ValueError, "raw evidence reference changed"):
            self.write()

    def test_native_missing_manifest_rejects(self):
        (self.raw / "RUN-MANIFEST.json").unlink()
        with self.assertRaisesRegex(ValueError, "lacks its run manifest"):
            self.write()

    def test_manifest_instrumentation_mismatch_rejects(self):
        (self.raw / "RUN-MANIFEST.json").write_text("{}")
        with self.assertRaisesRegex(ValueError, "run manifest differs"):
            self.write()


if __name__ == "__main__":
    unittest.main()
