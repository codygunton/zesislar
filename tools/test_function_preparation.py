"""Check the selected-function preparation order and Makefile path overrides."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class FunctionPreparationTests(unittest.TestCase):
    def test_free_binding_follows_native_restore_with_the_configured_paths(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            python = root / "record-python"
            log = root / "calls.jsonl"
            python.write_text(
                "#!/usr/bin/python3\nimport json,sys\n"
                f"with open({str(log)!r}, 'a') as stream:\n"
                " stream.write(json.dumps(sys.argv[1:]) + '\\n')\n")
            python.chmod(0o755)
            guard = root / "record-guard"
            guard.write_text(
                "#!/usr/bin/python3\nimport os,sys\n"
                "if sys.argv[1:4] != ['batch', 'eql-traces', '--']: sys.exit(2)\n"
                "os.execv(sys.argv[4], sys.argv[4:])\n")
            guard.chmod(0o755)
            command = ["make", "--no-print-directory", "-f", str(ROOT / "Makefile"),
                       "stock-native-indexes", f"PYTHON={python}", f"GUARD={guard}",
                       "STOCK_DECODE_TRACE_DIR=custom/decode",
                       "STOCK_CLOSURE_TRACE_DIR=custom/closure",
                       "STOCK_TRACE_MANIFEST=custom/recipe.json",
                       "STOCK_NATIVE_TRACE_CACHE_DIR=custom/cache",
                       "GATE_SOURCE_WORKSPACE=custom/source",
                       "DUMP=custom/program.raw.dump", "TRACE_JOBS=3"]
            result = subprocess.run(command, cwd=root, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            calls = [json.loads(line) for line in log.read_text().splitlines()]
            self.assertEqual(len(calls), 5)
            self.assertEqual(calls[0], ["tools/gate_workspace.py", "--workspace", ".",
                                      "--source-workspace", "custom/source"])
            self.assertEqual(calls[1], ["tools/stock_zisk/platform/traces.py",
                                      "--ensure-native-indexes",
                                      "--manifest", "custom/recipe.json",
                                      "--cache-dir", "custom/cache",
                                      "--decode-out", "custom/decode",
                                      "--closure-out", "custom/closure",
                                      "--dump", "custom/program.raw.dump", "--jobs", "3"])
            self.assertEqual(calls[2], ["tools/stock_zisk/selected/bind_traces.py",
                                      "--out", "custom/closure", "--function",
                                      "alt_fl_alloc.free", "--trace-name", "free"])


            self.assertEqual(calls[3], ["tools/stock_zisk/platform/traces.py",
                "--trace-only", "--manifest", "build/stock-zisk/eql-trace-input.json",
                "--dump", "build/stock-zisk/eql-policy/eql.raw.dump",
                "--out", "generated/isla-traces/stock-zisk/eql",
                "--coqdir", "ZesuSsz.Stock.Eql", "--jobs", "3",
                "--per-load-regions", "build/stock-zisk/eql-policy/regions.json.gz",
                "--per-load-regions-sha256", "3e79c1525180f95d48d65823a69394c89ba7d7e70bc778dae19b89004885cfeb",
                "--region-source-map", "build/stock-zisk/eql-policy/PATH-MAP.json",
                "--region-source-map-sha256", "a5afd3146de5a937cbebe3c0b18fbebc7927e73ca27302ae490afd749721afde"])
            self.assertEqual(calls[4], ["tools/stock_zisk/platform/bind_traces.py",
                "--out", "generated/isla-traces/stock-zisk/eql", "--trace-name", "eql",
                "--check-manifest", "custom/recipe.json"])


if __name__ == "__main__":
    unittest.main()
