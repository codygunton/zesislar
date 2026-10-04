"""Retained tests for the platform link boundary."""
import importlib.util
from pathlib import Path
import unittest
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("platform_build", HERE / "build.py")
build = importlib.util.module_from_spec(spec); spec.loader.exec_module(build)
spec = importlib.util.spec_from_file_location("platform_traces", HERE / "traces.py")
traces = importlib.util.module_from_spec(spec); spec.loader.exec_module(traces)

class TraceCoverageTests(unittest.TestCase):
    def test_instruction_modules_match_selected_pcs(self):
        with tempfile.TemporaryDirectory() as directory:
            out=Path(directory)
            for name in ["a800d6960.v", "a800d6964.v", "instrs.v"]:
                (out/name).touch()
            self.assertEqual(traces.validate_instruction_modules(out,[0x800d6960,0x800d6964]),2)
            (out/"a800d6964.v").unlink()
            with self.assertRaisesRegex(ValueError,"missing=.*a800d6964"):
                traces.validate_instruction_modules(out,[0x800d6960,0x800d6964])
            (out/"a800d6964.v").touch(); (out/"a800d6968.v").touch()
            with self.assertRaisesRegex(ValueError,"extra=.*a800d6968"):
                traces.validate_instruction_modules(out,[0x800d6960,0x800d6964])

class LinkTests(unittest.TestCase):
    def setUp(self):
        self.base = Path("/home/cody/isla-snapshots/riscv64.ir").read_text()
        self.adapter = Path("build/stock-zisk/platform/adapter.ir").read_text()
    def test_only_platform_bodies_change(self):
        result, report = build.link(self.base, self.adapter)
        self.assertTrue(report["non_platform_declarations_byte_identical"])
        before, after = build.functions(self.base), build.functions(result)
        self.assertEqual(set(after) - set(before), set(build.ADDED))
        for name in before.keys() - set(build.HOOKS):
            self.assertEqual(before[name], after[name])
    def test_modified_instruction_model_fails(self):
        with self.assertRaisesRegex(ValueError, "base snapshot hash"):
            build.link(self.base.replace("fn zexecute(", "fn zexecute_changed(", 1), self.adapter)
    def test_missing_hook_fails(self):
        with self.assertRaisesRegex(ValueError, "Missing platform hook"):
            build.link(self.base, self.adapter.replace("fn zchecked_mem_read(", "fn zchanged(", 1))

if __name__ == "__main__": unittest.main()
