#!/usr/bin/env python3
"""Python-only tests for the A6 proof rewrite and assumption audit parsers."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "det"))

import closed_cleanup_assumptions as audit  # noqa: E402
import closed_cleanup_rewrite as rewrite  # noqa: E402

# P0-B removed the writeSuccess proof tree. These tests read its modules,
# so they run only in a checkout that still has it.
NEEDS_WRITE_SUCCESS = unittest.skipUnless(
    (Path(__file__).resolve().parents[1] / "ZesuSsz/Proofs/WriteSuccess").is_dir(),
    "reads ZesuSsz/Proofs/WriteSuccess, removed in P0-B")


class RewriteTests(unittest.TestCase):
    def test_exact_proof_span(self) -> None:
        source = ("Lemma first : True.\nProof. exact I. Qed.\n"
                  "Lemma second : True.\nProof.\n  exact I.\nQed.\n")
        start, end = rewrite.proof_span(source, "second")
        changed = source[:start] + rewrite.PROOF + source[end:]
        self.assertEqual(changed,
                         "Lemma first : True.\nProof. exact I. Qed.\n"
                         "Lemma second : True.\n" + rewrite.PROOF + "\n")

    def test_missing_and_unclosed_proofs_fail(self) -> None:
        with self.assertRaises(ValueError):
            rewrite.proof_span("Lemma first : True.\nAdmitted.\n", "first")
        with self.assertRaises(ValueError):
            rewrite.proof_span("Lemma first : True.\nProof.\nAdmitted.\n", "first")

    def test_list_rejects_duplicate(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "list.txt"
            path.write_text("M.v f 2 1.0\nM.v f 2 1.0\n")
            with self.assertRaises(ValueError):
                rewrite.listed_rows(path)


class AssumptionTests(unittest.TestCase):
    @NEEDS_WRITE_SUCCESS
    def test_scratch_uses_qualified_lemma(self) -> None:
        source = audit.scratch_text("WriteSuccessEncoderOptionalNoneBoolean.v",
                                    ["encoder_optional_none_boolean"])
        qualified = ("ZesuSsz.Proofs.WriteSuccess."
                     "WriteSuccessEncoderOptionalNoneBoolean")
        self.assertIn(f"Require Import {qualified}.\n", source)
        self.assertIn(
            f"Print Assumptions {qualified}.encoder_optional_none_boolean.\n",
            source,
        )
        self.assertNotIn("Print Assumptions encoder_optional_none_boolean.", source)

    def test_capture_normalizes_whitespace(self) -> None:
        content = ("A6_BEGIN_0000\nClosed   under the global context\n"
                   "A6_END_0000\nA6_BEGIN_0001\nAxioms:\n x :   True\n"
                   "A6_END_0001\nexit=0 ms=44 rss_kb=1234\n")
        self.assertEqual(audit.parse_log(content, ["first", "second"]),
                         [["Closed under the global context"],
                          ["Axioms:", "x : True"]])

    def test_missing_marker_and_failed_exit_fail(self) -> None:
        with self.assertRaises(ValueError):
            audit.parse_log("A6_BEGIN_0000\nx\nexit=0 ms=1 rss_kb=1\n", ["f"])
        with self.assertRaises(ValueError):
            audit.parse_log("A6_BEGIN_0000\nx\nA6_END_0000\n"
                            "exit=1 ms=1 rss_kb=1\n", ["f"])

    def test_duplicate_and_out_of_order_markers_fail(self) -> None:
        with self.assertRaises(ValueError):
            audit.parse_log("A6_BEGIN_0001\nx\nA6_END_0001\n"
                            "exit=0 ms=1 rss_kb=1\n", ["f", "g"])
        with self.assertRaises(ValueError):
            audit.parse_log("A6_BEGIN_0000\nx\nA6_END_0000\n"
                            "A6_BEGIN_0000\nx\nA6_END_0000\n"
                            "exit=0 ms=1 rss_kb=1\n", ["f"])

    def test_compare_fails_on_changed_assumption(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            before = Path(directory) / "before.json"
            after = Path(directory) / "after.json"
            row = {"module": "M.v", "lemma": "f", "assumptions": ["closed"]}
            before.write_text(json.dumps({"schema": 1, "entries": [row]}))
            after.write_text(before.read_text())
            self.assertEqual(audit.compare(before, after), 0)
            row["assumptions"] = ["new axiom"]
            after.write_text(json.dumps({"schema": 1, "entries": [row]}))
            self.assertEqual(audit.compare(before, after), 1)


if __name__ == "__main__":
    unittest.main()
