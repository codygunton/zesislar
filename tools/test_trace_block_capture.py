"""Test capture API associations. These controls use no proof process."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / "block"))
import trace_block
import trace_block_capture as capture


class CaptureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.raw = self.base / "raw-capture"
        self.evidence = self.raw / "evidence"
        self.evidence.mkdir(parents=True)
        self.request = {"writer_id": "worker2-b", "scope": {"source": "Control.v"}}
        self.session = {"ownership": {"transport_closed_normally": True,
                                      "owned_pet_exited": True},
                        "source_unchanged": True, "error": None}
        self.manifest = {"schema_version": 1, "projection": "not-run",
                         "owned_closure": self.session["ownership"],
                         "source_unchanged": True, "error": None}
        self.refresh()

    def refresh(self):
        for key, value in (("request", self.request), ("session", self.session)):
            path = self.evidence / (key.upper() + ".json")
            path.write_bytes(trace_block.json_bytes(value))
            self.manifest[key] = {"path": str(path), "sha256": trace_block.sha256(path)}

    def test_exact_manifest_and_session_match(self):
        retained, paths = capture.validate_capture(self.request, self.raw, self.manifest)
        self.assertEqual(retained, self.request)
        self.assertEqual(paths["session"], self.evidence / "SESSION.json")

    def test_changed_session_hash_rejects(self):
        (self.evidence / "SESSION.json").write_text("{}")
        with self.assertRaisesRegex(ValueError, "changed"):
            capture.validate_capture(self.request, self.raw, self.manifest)

    def test_external_reference_rejects_even_with_matching_hash(self):
        path = self.base / "SESSION.json"
        path.write_bytes((self.evidence / "SESSION.json").read_bytes())
        self.manifest["session"]["path"] = str(path)
        with self.assertRaisesRegex(ValueError, "leaves"):
            capture.validate_capture(self.request, self.raw, self.manifest)

    def test_different_prepared_source_rejects(self):
        request = dict(self.request, source="different.v")
        with self.assertRaisesRegex(ValueError, "prepared request"):
            capture.validate_capture(request, self.raw, self.manifest)

    def test_different_writer_rejects(self):
        request = dict(self.request, writer_id="worker2-a")
        with self.assertRaisesRegex(ValueError, "writer identity"):
            capture.validate_capture(request, self.raw, self.manifest)

    def test_false_closure_rejects(self):
        self.session["ownership"]["owned_pet_exited"] = False
        self.refresh()
        with self.assertRaisesRegex(ValueError, "normal owned closure"):
            capture.validate_capture(self.request, self.raw, self.manifest)

    def test_manifest_cannot_replace_actual_error(self):
        self.manifest["error"] = "different"
        with self.assertRaisesRegex(ValueError, "differs from its session"):
            capture.validate_capture(self.request, self.raw, self.manifest)

    def test_missing_manifest_field_rejects(self):
        del self.manifest["error"]
        with self.assertRaisesRegex(ValueError, "differs from its session"):
            capture.validate_capture(self.request, self.raw, self.manifest)

    def test_raw_seal_covers_all_files_and_rejects_changed_output(self):
        extra = self.raw / "compiler-event.json"
        extra.write_text("{}")
        path = self.base / "RAW-SEAL.json"
        capture.write_raw_seal(self.raw, path, "logical-id")
        record = json.loads(path.read_text())
        self.assertEqual({row["path"] for row in record["files"]},
                         {"compiler-event.json", "evidence/REQUEST.json", "evidence/SESSION.json"})
        extra.write_text('{"changed":true}')
        with self.assertRaisesRegex(ValueError, "different complete raw seal"):
            capture.write_raw_seal(self.raw, path, "logical-id")

    def test_raw_seal_cannot_enter_raw_root(self):
        with self.assertRaisesRegex(ValueError, "outside"):
            capture.write_raw_seal(self.raw, self.raw / "RAW-SEAL.json", "logical-id")

    def test_capture_uses_separate_root_without_legacy_run(self):
        backend = unittest.mock.Mock()
        backend.run_capture.return_value = self.manifest
        with patch.object(capture, "project_capture", return_value="trace") as project:
            self.assertEqual(capture.capture_bundle(self.request, self.base, backend), "trace")
        backend.run_capture.assert_called_once_with(self.request, self.raw)
        backend.run.assert_not_called()
        project.assert_called_once_with(self.request, self.base, self.raw, self.manifest)

    def test_admission_failure_marks_projection_incomplete_and_passes_storage(self):
        trace = {"completion": {"trace_complete": True, "reasons": []},
                 "session": {"id": "synthetic"}}
        class View:
            def __init__(self, request, evidence):
                pass
            def write_raw_index(self, path):
                path.write_text("{}")
        self.manifest["admission_exit_status"] = 3
        records = {"synthetic": "record"}
        with patch.object(capture, "build_stream_trace", return_value=trace), patch.object(
                capture.trace_block, "logical_session_id", return_value="synthetic"), patch.object(
                capture.trace_block, "observed_verdict", return_value={"status": "unresolved"}), patch.object(
                capture, "write_offline_bundle") as writer:
            actual = capture.project_capture(self.request, self.base, self.raw, self.manifest,
                                             view_factory=View, storage_records=records)
        self.assertFalse(actual["completion"]["trace_complete"])
        self.assertIn("status 3", actual["completion"]["reasons"][0])
        self.assertEqual(actual["verdict"], {"status": "unresolved"})
        self.assertIs(writer.call_args.kwargs["storage_records"], records)

    def test_projection_cannot_write_inside_raw_root(self):
        with self.assertRaisesRegex(ValueError, "outside"):
            capture.project_capture(self.request, self.raw / "output", self.raw, self.manifest)

    def test_raw_seal_rejects_broken_links(self):
        (self.raw / "broken.json").symlink_to(self.base / "missing.json")
        with self.assertRaisesRegex(ValueError, "broken or"):
            capture.write_raw_seal(self.raw, self.base / "RAW-SEAL.json", "logical-id")

    def test_raw_seal_rejects_directory_links(self):
        (self.raw / "directory").symlink_to(self.base, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "broken or"):
            capture.write_raw_seal(self.raw, self.base / "RAW-SEAL.json", "logical-id")


if __name__ == "__main__":
    unittest.main()
