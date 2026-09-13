"""Check bounded compiler diagnostics and excluded environment records."""

import unittest

from dune_diagnostics import failed_compilers
from test_coqc_recipe import csexp


class DuneDiagnosticsTests(unittest.TestCase):
    def test_excludes_environment_and_command(self):
        data = csexp(["config", "init", "1", ["env", ["KEY=secret"]]])
        data += csexp(["process", "finish", "2", ["prog", "/switch/bin/coqc"],
                       ["process_args", ["secret-argument"]], ["exit", "1"],
                       ["target_files", ["/private/Test.vo"]],
                       ["stdout", "Error: first\nsecond\nthird"]])
        result = list(failed_compilers(data, 2))
        self.assertEqual(result, [{"exit": "1", "targets": ["/private/Test.vo"],
                                   "diagnostic": "Error: first\nsecond"}])
        self.assertNotIn("secret", str(result))

    def test_ignores_success_and_noncompiler(self):
        events = [["process", "finish", "1", ["prog", "/bin/echo"], ["exit", "1"]],
                  ["process", "finish", "2", ["prog", "/switch/bin/coqc"], ["exit", "0"]]]
        self.assertEqual(list(failed_compilers(b"".join(map(csexp, events)))), [])

    def test_accepts_incomplete_running_trace(self):
        event = ["process", "finish", "1", ["prog", "/switch/bin/coqc"],
                 ["exit", "1"], ["stdout", "Error: first"]]
        self.assertEqual(list(failed_compilers(csexp(event) + b"(7:partial")),
                         list(failed_compilers(csexp(event))))

    def test_keeps_error_after_large_goal(self):
        event = ["process", "finish", "1", ["prog", "/switch/bin/coqc"],
                 ["exit", "1"], ["stdout", "goal\n" * 100 +
                                  "File Test.v\nError: proof incomplete\ndetail"]]
        result = list(failed_compilers(csexp(event), 3))
        self.assertEqual(result[0]["diagnostic"],
                         "File Test.v\nError: proof incomplete\ndetail")

    def test_includes_compiler_stderr(self):
        event = ["process", "finish", "1", ["prog", "/switch/bin/coqc"],
                 ["exit", "1"], ["stdout", "timing\n"],
                 ["stderr", "File Test.v\nError: proof incomplete"]]
        result = list(failed_compilers(csexp(event), 2))
        self.assertEqual(result[0]["diagnostic"],
                         "File Test.v\nError: proof incomplete")
