"""Reject the stale paths that redirected a frozen native comparison."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / "block"))
from frozen_attempt import load_inputs


class FrozenAttemptTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.old = self.root / "attempt-001"
        self.current = self.root / "attempt-002"
        for directory in (self.old, self.current):
            directory.mkdir()
            (directory / "native-inputs.json").write_text(json.dumps({
                "attempt_directory": str(directory), "root": "frozen-root"}))
            (directory / "run.py").write_text("# launcher\n")
        self.original = (self.old / "native-inputs.json").read_bytes()
        self.summary = self.old / "result-summary.json"
        self.summary.write_text('{"outcome": "retained"}\n')
        self.summary_bytes = self.summary.read_bytes()

    def test_current_paths_load(self):
        result = load_inputs(self.current / "run.py",
                             self.current / "native-inputs.json", self.current)
        self.assertEqual(result["root"], "frozen-root")

    def test_stale_relative_index_is_rejected_before_old_summary_changes(self):
        index = self.current / ".." / "attempt-001" / "native-inputs.json"
        with self.assertRaisesRegex(ValueError, "input index belongs"):
            load_inputs(self.current / "run.py", index, self.current)
        self.assertEqual((self.old / "native-inputs.json").read_bytes(), self.original)
        self.assertEqual(self.summary.read_bytes(), self.summary_bytes)

    def test_stale_absolute_output_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "output directory belongs"):
            load_inputs(self.current / "run.py",
                        self.current / "native-inputs.json", self.old)
        self.assertEqual(self.summary.read_bytes(), self.summary_bytes)

    def test_copied_stale_index_binding_is_rejected(self):
        (self.current / "native-inputs.json").write_bytes(self.original)
        with self.assertRaisesRegex(ValueError, "binds another attempt"):
            load_inputs(self.current / "run.py",
                        self.current / "native-inputs.json", self.current)


if __name__ == "__main__":
    unittest.main()
