"""Tests for the one-command native scratch helper."""

import contextlib
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
import scratch_block


SOURCE = """Require Import ZesuSsz.Automation.All.
Definition LocalEntry := True.
Lemma DesignedBoundary_800d6b08 (n : nat) :
  n = n.
Proof.
  exact eq_refl.
Qed.
Print Assumptions DesignedBoundary_800d6b08.
"""


class ScratchBlockTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.workspace = Path(self.temporary.name)
        self.hand = self.workspace / "ZesuSsz/Proofs/DecodeItem/Hand"
        self.hand.mkdir(parents=True)
        self.module = self.hand / "Block800d6b08.v"
        self.module.write_text(SOURCE)

    def test_full_pc_and_unique_suffix_select_same_source(self):
        for pc in ("0x800d6b08", "800D6B08", "6b08"):
            self.assertEqual(scratch_block.find_hand_block(self.workspace, pc), self.module)

    def test_missing_ambiguous_and_invalid_pc_are_rejected(self):
        (self.hand / "Block900d6b08.v").write_text(SOURCE)
        for pc in ("6b08", "missing", "0x1234", "../6b08"):
            with self.subTest(pc=pc), self.assertRaises(ValueError):
                scratch_block.find_hand_block(self.workspace, pc)
        self.assertEqual(scratch_block.find_hand_block(self.workspace, "800d6b08"), self.module)

    def test_exact_statement_and_prefix_survive_body_replacement(self):
        generated = scratch_block.scratch_source(self.module)
        self.assertEqual(generated.split("Proof.")[0], SOURCE.split("Proof.")[0])
        self.assertIn("  Time all: zesu_block.\n  Show.\nAbort.\n", generated)
        self.assertIn("Set Printing Depth 30.", generated)
        self.assertNotIn("exact eq_refl", generated)
        self.assertNotIn("Print Assumptions", generated)
        self.assertNotIn("Qed.", generated)
        self.assertEqual(self.module.read_text(), SOURCE)

    def test_local_additions_precede_exact_statement(self):
        extra = "Require Import LocalHints.\nLocal Hint Resolve foo : core.\n"
        generated = scratch_block.scratch_source(self.module, extra)
        statement = SOURCE[SOURCE.index("Lemma "):SOURCE.index("Proof.")]
        self.assertIn(extra + "\n" + statement + "Proof.", generated)
        self.assertEqual(self.module.read_text(), SOURCE)

    def test_inline_proof_is_rejected(self):
        self.module.write_text(SOURCE.replace("Proof.\n  exact eq_refl.\nQed.", "Proof. exact eq_refl. Qed."))
        with self.assertRaisesRegex(ValueError, "separate Proof"):
            scratch_block.scratch_source(self.module)

    def test_command_uses_existing_compiler_cpu_and_probe_policy(self):
        build = self.workspace / "_build/agents/test"
        build.mkdir(parents=True)
        extra = self.workspace / "extra.v"
        extra.write_text("Local Hint Resolve foo : core.")
        received = []
        def compile_source(source, output, private_build, *, policy):
            received.append((source, output, private_build, policy))
            self.assertIn(extra.read_text(), source.read_text())
            return (subprocess.CompletedProcess([], 0), "residual\n", output / "compiler.log",
                    {"measurement_complete": True, "cpu_seconds": 12.75,
                     "peak_rss_kib": 2 * 1024**2}, None)
        output = io.StringIO()
        with patch.object(scratch_block, "__file__", str(self.workspace / "tools/block/scratch_block.py")), \
                patch.object(scratch_block.coqc_primary, "compile_source", side_effect=compile_source), \
                contextlib.redirect_stdout(output):
            self.assertEqual(scratch_block.main(["6b08", str(extra), "--build-dir", str(build)]), 0)
        self.assertIn("compiler_cpu_seconds=12.750000 peak_rss_gib=2.000000", output.getvalue())
        self.assertIn("residual", output.getvalue())
        self.assertEqual(received[0][2], build)
        self.assertEqual(received[0][3], scratch_block.coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True))

    def test_compiler_failure_and_unavailable_measurement_are_reported(self):
        build = self.workspace / "build"
        build.mkdir()
        result = (subprocess.CompletedProcess([], 3), "compile error", build / "compiler.log", None, None)
        output, errors = io.StringIO(), io.StringIO()
        with patch.object(scratch_block, "__file__", str(self.workspace / "tools/block/scratch_block.py")), \
                patch.object(scratch_block.coqc_primary, "compile_source", return_value=result), \
                contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
            self.assertEqual(scratch_block.main(["6b08", "--build-dir", str(build)]), 3)
        self.assertIn("Compiler CPU is unavailable.", errors.getvalue())
        self.assertNotIn("compiler_cpu_seconds=", output.getvalue())


if __name__ == "__main__":
    unittest.main()
