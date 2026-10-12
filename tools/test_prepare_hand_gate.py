"""Check Hand gate preparation without a proof process or project build."""
import json
import tempfile
import unittest
from pathlib import Path

from block.prepare_hand_gate import gate_environment, prepare


class HandGateTests(unittest.TestCase):
    def fixture(self, body_lines):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        name = "ZesuSsz/Proofs/DecodeItem/Hand/Block800d698c.v"
        path = root / name
        path.parent.mkdir(parents=True)
        path.write_text("Require Import ZesuSsz.Automation.All.\n"
                        "Lemma block : instr_body 0x1 entry.\nProof.\n" +
                        "iFrame.\n" * body_lines + "Qed.\n")
        baseline = root / "ZesuSsz/Evidence/proof_size_baseline.json"
        baseline.parent.mkdir(parents=True)
        baseline.write_text(json.dumps({"files": {"existing.v": {"max_proof_lines": 49}}}))
        return root, name, baseline

    def test_missing_baseline_requires_explicit_record(self):
        root, name, baseline = self.fixture(78)
        before = baseline.read_bytes()
        with self.assertRaisesRegex(ValueError, "Missing measured"):
            prepare(root, name)
        self.assertEqual(baseline.read_bytes(), before)

    def test_exact_eighty_lines_records_only_its_metrics(self):
        root, name, baseline = self.fixture(78)
        report = prepare(root, name, record_size=True)
        self.assertEqual(report["proof_lines"], [80])
        data = json.loads(baseline.read_text())["files"]
        self.assertEqual(data["existing.v"], {"max_proof_lines": 49})
        self.assertEqual(data[name], {"long_proofs": 1, "max_proof_lines": 78})
        self.assertFalse(report["proof_verification_performed"])

    def test_eighty_one_lines_cannot_record_an_allowance(self):
        root, name, baseline = self.fixture(79)
        before = baseline.read_bytes()
        with self.assertRaisesRegex(ValueError, "exceeds 80"):
            prepare(root, name, record_size=True)
        self.assertEqual(baseline.read_bytes(), before)

    def test_gate_does_not_inherit_writer_or_probe(self):
        environment = {"ZESU_WRITER_ID": "spec-a", "ZESU_DIAGNOSTIC_PROBE": "1",
                       "ZESU_MODULE_LIMIT_GIB": "64", "ZESU_SCOPE_CPU": "unlimited",
                       "PATH": "/pinned/bin", "CHECK_AGENT": "spec-a"}
        actual = gate_environment(environment)
        self.assertEqual(actual, {"PATH": "/pinned/bin", "CHECK_AGENT": "spec-a"})
        self.assertEqual(environment["ZESU_WRITER_ID"], "spec-a")
