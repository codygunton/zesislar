"""Check trace exclusion at the shared build and package boundaries."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from coqc_recipe import compiler_recipe, trace_events
from dune_trace_guard import reject_environment_header
from test_coqc_recipe import csexp

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
from archive_discovery import store


class DuneTraceGuardTests(unittest.TestCase):
    def trace(self):
        header = csexp(["config", "init", "1", ["env", ["TEST_KEY=private-value"]]])
        compiler = csexp(["process", "start", "2", ["prog", "/switch/bin/coqc"],
                          ["process_args", ["ZesuSsz/Test.v"]], ["dir", "/build/default"]])
        return header, compiler

    def test_wrapper_scrubs_failed_build_before_packaging(self):
        header, compiler = self.trace()
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory)
            writer = build / "writer.py"
            writer.write_text("import pathlib,sys\n"
                              f"pathlib.Path(sys.argv[2]).mkdir(exist_ok=True)\n"
                              f"(pathlib.Path(sys.argv[2])/'trace.csexp').write_bytes({header + compiler!r})\n"
                              "raise SystemExit(7)\n")
            result = subprocess.run([sys.executable, str(Path(__file__).with_name("dune_trace_guard.py")),
                                     "--", sys.executable, str(writer), "--build-dir", str(build)],
                                    capture_output=True)
            self.assertEqual(result.returncode, 7)
            data = (build / "trace.csexp").read_bytes()
            self.assertEqual(data, compiler)
            self.assertEqual(compiler_recipe(data), compiler_recipe(header + compiler))
            record = store(build / "package", data)
            self.assertEqual(Path(record["archive_path"]).read_bytes(), compiler)
            self.assertNotIn(b"private-value", result.stdout + result.stderr + data)

    def test_package_rejects_raw_header_without_writing(self):
        header, compiler = self.trace()
        with tempfile.TemporaryDirectory() as directory:
            package = Path(directory) / "package"
            with self.assertRaisesRegex(ValueError, "environment header"):
                store(package, header + compiler)
            self.assertFalse(package.exists())

    def test_package_rejects_incomplete_header(self):
        header, _ = self.trace()
        with self.assertRaisesRegex(ValueError, "environment header"):
            reject_environment_header(header[:-4])

    def test_shared_parser_excludes_headers(self):
        header, compiler = self.trace()
        self.assertEqual(list(trace_events(header + compiler)), list(trace_events(compiler)))

    def test_package_keeps_proof_capture(self):
        data = (json.dumps({"environment": "iris", "goal": "envs_entails E P"}) + "\n").encode()
        with tempfile.TemporaryDirectory() as directory:
            record = store(directory, data)
            self.assertEqual(Path(record["archive_path"]).read_bytes(), data)


if __name__ == "__main__":
    unittest.main()
