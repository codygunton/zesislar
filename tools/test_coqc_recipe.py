"""Check compiler recipes after a cached build."""

import tempfile
import unittest
from pathlib import Path

from coqc_recipe import compiler_recipe, remember_recipe


def csexp(value):
    if isinstance(value, list):
        return b"(" + b"".join(map(csexp, value)) + b")"
    atom = value.encode()
    return str(len(atom)).encode() + b":" + atom


class CompilerRecipeTests(unittest.TestCase):
    def test_preserves_recipe_after_cached_build(self):
        event = ["process", "start", "1", ["prog", "/switch/bin/coqc"],
                 ["process_args", ["-q", "-Q", "ZesuSsz", "ZesuSsz", "Test.v"]],
                 ["dir", "/private/default"]]
        with tempfile.TemporaryDirectory() as directory:
            build_dir = Path(directory)
            trace = build_dir / "trace.csexp"
            trace.write_bytes(csexp(event))
            expected = remember_recipe(build_dir)
            trace.write_bytes(csexp(["build", "cached"]))
            self.assertEqual(remember_recipe(build_dir), expected)
            self.assertEqual(expected["command"][-1], "Test.v")
            self.assertEqual(expected["working_dir"], "/private/default")

    def test_rejects_noncompiler_process(self):
        event = ["process", "start", "1", ["prog", "/bin/echo"],
                 ["process_args", ["coqc", "Test.v"]]]
        self.assertIsNone(compiler_recipe(csexp(event)))

    def test_missing_recipe(self):
        with tempfile.TemporaryDirectory() as directory:
            self.assertIsNone(remember_recipe(Path(directory)))

    def test_incomplete_event(self):
        event = ["process", "start", "1", ["prog", "/switch/bin/coqc"],
                 ["process_args", ["-q", "Test.v"]]]
        data = csexp(event)
        self.assertEqual(compiler_recipe(data + b"(7:partial"), compiler_recipe(data))
        self.assertIsNone(compiler_recipe(data[:-1]))
