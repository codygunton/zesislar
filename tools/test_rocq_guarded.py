#!/usr/bin/env python3
"""Check the MCP launch fence and guarded compiler routing without proofs."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from test_guard import fixture_environment


TOOLS = Path(__file__).resolve().parent


class RocqGuardedTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.environment = fixture_environment( PATH=f"{self.root}:{os.environ['PATH']}",
                                TEST_RECORD=str(self.root / "record.jsonl"))
        for name in ("rocq_mcp_guarded.sh", "rocq_coqc_guarded.sh", "coqc_findlib.py"):
            shutil.copy2(TOOLS / name, self.root / name)

    def executable(self, name, body):
        path = self.root / name
        path.write_text("#!/usr/bin/env python3\n" + body)
        path.chmod(0o755)
        return str(path)

    def records(self):
        return [json.loads(line) for line in (self.root / "record.jsonl").read_text().splitlines()]

    def test_server_fence_and_supported_settings(self):
        self.executable("resource_guard.sh", "print('zesuworkloads.slice')\n")
        self.executable("systemd-run", "import json,os,sys\n"
                        "print(json.dumps({'args':sys.argv[1:], 'compiler':os.environ['ROCQ_COQC_BINARY'],"
                        "'pet_limit':os.environ['ROCQ_MAX_PET_RSS_MB'],'hold':os.environ['ZESU_HOLD_GIB'],'guard':os.environ['ZESU_RESOURCE_GUARD']}))\n")
        result = subprocess.run([str(self.root / "rocq_mcp_guarded.sh"), "argument"],
                                env=dict(self.environment, ZESU_ROCQ_MCP_BINARY="/test/mcp"),
                                check=True, capture_output=True, text=True)
        record = json.loads(result.stdout)
        self.assertIn("--slice=zesuworkloads.slice", record["args"])
        self.assertIn("parent-exec", record["args"])
        self.assertEqual(record["guard"], str(self.root / "resource_guard.sh"))
        self.assertIn("MemoryMax=16G", record["args"])
        self.assertIn("MemorySwapMax=0", record["args"])
        self.assertTrue(any(value.startswith("--unit=rocq-writer-") for value in record["args"]))
        self.assertEqual(record["args"][-2:], ["/test/mcp", "argument"])
        self.assertEqual(record["compiler"], str(self.root / "rocq_coqc_guarded.sh"))
        self.assertEqual(record["pet_limit"], "16384")
        self.assertEqual(record["hold"], "180")

    def test_parent_setup_failure_prevents_server(self):
        self.executable("resource_guard.sh", "raise SystemExit(2)\n")
        self.executable("systemd-run", "raise RuntimeError('must not launch')\n")
        result = subprocess.run([str(self.root / "rocq_mcp_guarded.sh")],
                                env=dict(self.environment, ZESU_ROCQ_MCP_BINARY="/test/mcp"),
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertNotIn("must not launch", result.stderr)

    def test_old_guard_override_refuses_before_server(self):
        old = self.executable("old-guard", "print('app.slice')\n")
        self.executable("systemd-run", "raise RuntimeError('must not launch')\n")
        result = subprocess.run([str(self.root / "rocq_mcp_guarded.sh")],
                                env=dict(self.environment, ZESU_RESOURCE_GUARD=old,
                                         ZESU_ROCQ_MCP_BINARY="/test/mcp"),
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("lacks the shared memory parent", result.stderr)
        self.assertNotIn("must not launch", result.stderr)

    def test_compiler_enters_registered_scope_without_duplicate_wait(self):
        self.executable("resource_guard.sh", "import json,os,sys\n"
                        "with open(os.environ['TEST_RECORD'],'a') as f: f.write(json.dumps(sys.argv[1:])+'\\n')\n")
        subprocess.run([str(self.root / "rocq_coqc_guarded.sh"), "-Q", "a", "b", "proof.v"],
                       env=dict(self.environment, ZESU_ROCQ_COQC_BINARY="/test/coqc"), check=True,
                       cwd=self.root)
        self.assertEqual(self.records(), [["scope", "rocq-mcp-coqc", "--",
                          "/test/coqc", "-Q", "a", "b", "proof.v"]])

    def test_health_does_not_reserve_a_slot(self):
        compiler = self.executable("fake-coqc", "import sys\nprint(' '.join(sys.argv[1:]))\n")
        result = subprocess.run([str(self.root / "rocq_coqc_guarded.sh"), "--version"],
                                env=dict(self.environment, ZESU_ROCQ_COQC_BINARY=compiler),
                                check=True, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), "--version")
        self.assertFalse((self.root / "record.jsonl").exists())


if __name__ == "__main__":
    unittest.main()
