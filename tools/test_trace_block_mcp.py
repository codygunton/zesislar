import asyncio
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools/block"))
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module
helper = load("owner_helper", ROOT / "tools/block/trace_block_prepare.py")
backend = load("owner_backend", ROOT / "tools/block/trace_block_mcp.py")

class OwnerTests(unittest.TestCase):
    def invoke(self, requested, environment, expected):
        with tempfile.TemporaryDirectory() as tmp:
            calls = []
            def admitted(command, env, cwd):
                calls.append((command, env, cwd))
                backend.save_json(Path(command[-1]), {"completion": {"trace_complete": True}})
                return type("Result", (), {"returncode": 0})()
            supplied = {"workspace": tmp, **requested}
            environment = {"ZESU_MCP_PYTHON": sys.executable, **environment}
            with patch.dict(sys.modules, {"trace_block_prepare": helper}), patch.dict(os.environ, environment, clear=True), patch.object(backend.subprocess, "run", side_effect=admitted):
                result = backend.run(supplied, Path(tmp) / "capture")
            self.assertTrue(result["completion"]["trace_complete"])
            self.assertEqual(len(calls), 1)
            command, env, cwd = calls[0]
            self.assertEqual(command[2], expected)
            self.assertEqual(env["ZESU_WRITER_ID"], expected)
            self.assertEqual(cwd, Path(tmp))
            request = json.loads((Path(tmp) / "capture/evidence/REQUEST.json").read_text())
            self.assertEqual(request["writer_id"], expected)
    def test_explicit_owner(self):
        self.invoke({"writer_id": "worker2-other"}, {"ZESU_WRITER_ID": "ignored"}, "worker2-other")
    def test_declared_environment_owner(self):
        self.invoke({}, {"ZESU_WRITER_ID": "owner-a", "COORD_AGENT": "ignored"}, "owner-a")
    def test_coordinator_owner(self):
        self.invoke({}, {"COORD_AGENT": "owner-b"}, "owner-b")
    def test_missing_owner_refuses_before_admission(self):
        with patch.dict(sys.modules, {"trace_block_prepare": helper}), patch.dict(os.environ, {}, clear=True), patch.object(backend.subprocess, "run") as command:
            with self.assertRaisesRegex(ValueError, "writer identity"):
                backend.run({"workspace": str(ROOT)}, ROOT / "_build/unused-owner-test")
            command.assert_not_called()
    def test_invalid_owner_refuses_before_admission(self):
        with patch.dict(sys.modules, {"trace_block_prepare": helper}), patch.object(backend.subprocess, "run") as command:
            with self.assertRaisesRegex(ValueError, "writer identity"):
                backend.run({"workspace": str(ROOT), "writer_id": "owner bad"}, ROOT / "_build/unused-owner-test")
            command.assert_not_called()
    def test_admitted_owner_mismatch_refuses(self):
        with patch.dict(sys.modules, {"trace_block_prepare": helper}), patch.dict(os.environ, {"ZESU_WRITER_ID": "owner-b"}):
            with self.assertRaisesRegex(ValueError, "admitted writer"):
                asyncio.run(backend._run({"writer_id": "owner-a"}, ROOT / "_build/unused-owner-test"))

if __name__ == "__main__":
    unittest.main()
