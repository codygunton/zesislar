"""Check block boundaries, source generation, and result classification."""
import json
import sys
import tempfile
import os
import subprocess
import time
import unittest
from unittest.mock import patch
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools/block"))
import entries
import blockrun
import analyze
import runner


class BlockTests(unittest.TestCase):
    def test_scanner_keeps_selected_pre_entry(self):
        candidates = entries.scan(ROOT / "ZesuSsz/Proofs/WriteSuccess")
        selected = json.loads((ROOT / "ZesuSsz/Evidence/det/block_entries.json").read_text())
        self.assertEqual(len(selected), 87)
        for leader, entry in selected.items():
            self.assertIn(entry, candidates[leader])
        self.assertEqual(selected["0x15190"]["lemma"], "transactions_recipient_output_value_continuation")

    def test_interior_premise_removal(self):
        lines = ["  instr_pre 0x1004 (", "    P) -∗", "  instr_pre 0x1008 Q -∗",
                 "  instr_body 0x1000 R."]
        self.assertEqual(blockrun.drop_premises(lines, {0x1004}), lines[2:])

    def test_variant_a_keeps_successor(self):
        block = dict(leader="0x14e28", last="0x14e34", succ=["0x14e38"])
        source, metadata = blockrun.source(block, "write_success_header_chunk_14e28", "WriteSuccessHeaderChunk14e28")
        self.assertIn("instr_body 0x14e38", source)
        self.assertIn("0x14e38", metadata["kept_succ"])
        self.assertIn("Abort.", source)

    def test_runner_measures_descendant_compiler(self):
        with tempfile.TemporaryDirectory() as directory:
            program = Path(directory) / "coqc"
            # Linux reports the task name from the executable, so use a copy of sleep.
            import shutil
            shutil.copyfile("/usr/bin/sleep", program)
            program.chmod(0o755)
            process = subprocess.Popen([str(program), "5"])
            try:
                deadline = time.monotonic() + 2
                rss = 0
                while rss == 0 and time.monotonic() < deadline:
                    _, rss = runner.compiler_stats(os.getpid())
                    time.sleep(0.01)
                self.assertGreater(rss, 0)
            finally:
                process.terminate()
                process.wait()

    def test_runner_timeout_stops_the_compiler(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tools").mkdir()
            guard = root / "tools/resource_guard.sh"
            guard.write_text("#!/usr/bin/env python3\nimport os,sys\n"
                             "args=sys.argv[sys.argv.index('--')+1:]\nos.execv(args[0],args)\n")
            compiler = root / "coqc"
            compiler.write_text("#!/usr/bin/env python3\nimport ctypes,os,time\n"
                                "ctypes.CDLL(None).prctl(15,b'coqc',0,0,0)\n"
                                "print(os.getpid(),flush=True)\ntime.sleep(30)\n")
            guard.chmod(0o755)
            compiler.chmod(0o755)
            source = root / "probe.v"
            source.write_text("Goal True. Abort.\n")
            recipe = dict(command=[str(compiler), "old.v"], working_dir=str(root))
            with patch.object(runner, "ROOT", root), patch.object(runner, "remember_recipe", return_value=recipe):
                result = runner.run(source, root, 1)
            self.assertEqual(result["limit"], "time")
            self.assertGreater(result["peak_mib"], 0)
            pid = int(source.with_suffix(".out").read_text().strip())
            with self.assertRaises(ProcessLookupError):
                os.kill(pid, 0)

    def test_absent_call_set_skips_the_arm(self):
        if (ROOT / "ZesuSsz/Automation/Sets/call.v").exists():
            self.skipTest("The call set exists at this revision.")
        result = subprocess.run([sys.executable, str(ROOT / "tools/block/blockrun.py")],
                                env={**os.environ, "RULES": "call"}, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("call set unavailable", result.stdout)

    def test_partial_handoff(self):
        result = analyze.classify(dict(leader="0x15930", last="0x1593c", n=4, outcome="closed-all"))
        self.assertEqual(result["result"], "partial")
        self.assertEqual(result["stall_pc"], "0x1593c")

    def test_comparison_reports_missing_and_changed_outcomes(self):
        with tempfile.TemporaryDirectory() as directory:
            actual, expected = [Path(directory) / name for name in ("actual.csv", "expected.csv")]
            actual.write_text("leader,result,wall_s\n0x1000,closed,4\n0x1004,timeout,10\n")
            expected.write_text("leader,result,wall_s\n0x1000,closed,9\n0x1004,stalled,1\n0x1008,no-entry,0\n")
            self.assertEqual(analyze.compare_table(actual, expected), [
                dict(leader="0x1004", expected="stalled", actual="timeout"),
                dict(leader="0x1008", expected="no-entry", actual=None)])

    def test_timeout_preserves_last_pc(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "probe.out"
            output.write_text("BLK-PC (bv_to_bvn (Z_to_bv 64 4100))")
            result = analyze.classify(dict(leader="0x1000", last="0x100c", n=4,
                                          outcome="timeout", raw_path=str(output)))
            self.assertEqual(result["k"], 2)
            self.assertEqual(result["stall_pc"], "0x1004")

    def test_abstract_stop_is_reached(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "probe.out"
            output.write_text("BOUNDARY-ALL-GOALS-END\n----------∗\nBLK_STOP_1008")
            result = analyze.classify(dict(leader="0x1000", last="0x1004", n=2, outcome="probe", raw_path=str(output)))
            self.assertEqual(result["result"], "reached")


if __name__ == "__main__":
    unittest.main()
