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
        for name in ("rocq_mcp_guarded.sh", "rocq_coqc_guarded.sh"):
            shutil.copy2(TOOLS / name, self.root / name)

    def executable(self, name, body):
        path = self.root / name
        path.write_text("#!/usr/bin/env python3\n" + body)
        path.chmod(0o755)
        return str(path)

    def records(self):
        return [json.loads(line) for line in (self.root / "record.jsonl").read_text().splitlines()]

    def test_server_fence_and_supported_settings(self):
        self.executable("systemd-run", "import json,os,sys\n"
                        "print(json.dumps({'args':sys.argv[1:], 'compiler':os.environ['ROCQ_COQC_BINARY'],"
                        "'pet_limit':os.environ['ROCQ_MAX_PET_RSS_MB'],'hold':os.environ['ZESU_HOLD_GIB']}))\n")
        result = subprocess.run([str(self.root / "rocq_mcp_guarded.sh"), "argument"],
                                env=dict(self.environment, ZESU_ROCQ_MCP_BINARY="/test/mcp"),
                                check=True, capture_output=True, text=True)
        record = json.loads(result.stdout)
        self.assertIn("MemoryMax=6G", record["args"])
        self.assertIn("MemorySwapMax=0", record["args"])
        self.assertTrue(any(value.startswith("--unit=rocq-writer-") for value in record["args"]))
        self.assertEqual(record["args"][-2:], ["/test/mcp", "argument"])
        self.assertEqual(record["compiler"], str(self.root / "rocq_coqc_guarded.sh"))
        self.assertEqual(record["pet_limit"], "6144")
        self.assertEqual(record["hold"], "180")

    def test_compiler_waits_before_registered_scope(self):
        self.executable("resource_guard.sh", "import json,os,sys\n"
                        "with open(os.environ['TEST_RECORD'],'a') as f: f.write(json.dumps(sys.argv[1:])+'\\n')\n")
        subprocess.run([str(self.root / "rocq_coqc_guarded.sh"), "-Q", "a", "b", "proof.v"],
                       env=dict(self.environment, ZESU_ROCQ_COQC_BINARY="/test/coqc"), check=True)
        self.assertEqual(self.records(), [["wait"], ["scope", "rocq-mcp-coqc", "--",
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
