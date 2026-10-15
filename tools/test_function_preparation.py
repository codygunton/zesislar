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
            command = ["make", "--no-print-directory", "-f", str(ROOT / "Makefile"),
                       "stock-native-indexes", f"PYTHON={python}",
                       "STOCK_DECODE_TRACE_DIR=custom/decode",
                       "STOCK_CLOSURE_TRACE_DIR=custom/closure",
                       "STOCK_TRACE_MANIFEST=custom/recipe.json",
                       "STOCK_NATIVE_TRACE_CACHE_DIR=custom/cache"]
            result = subprocess.run(command, cwd=root, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            calls = [json.loads(line) for line in log.read_text().splitlines()]
            self.assertEqual(len(calls), 2)
            self.assertEqual(calls[0][0], "tools/stock_zisk/platform/traces.py")
            self.assertIn("--ensure-native-indexes", calls[0])
            for flag, value in [("--decode-out", "custom/decode"),
                                ("--closure-out", "custom/closure"),
                                ("--manifest", "custom/recipe.json"),
                                ("--cache-dir", "custom/cache")]:
                self.assertEqual(calls[0][calls[0].index(flag) + 1], value)
            self.assertEqual(calls[1], ["tools/stock_zisk/selected/bind_traces.py",
                                      "--out", "custom/closure", "--function",
                                      "alt_fl_alloc.free", "--trace-name", "free"])


if __name__ == "__main__":
    unittest.main()
