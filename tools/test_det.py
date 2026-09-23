"""Tests for the determinism branch's segment tools."""

import sys
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import importlib.util

DET = Path(__file__).resolve().parent / "det"
sys.path.insert(0, str(DET))


def _load(name: str):
    """Load a `tools/det` module by path.

    `tools/residual` has a `report.py` too, and whichever directory a
    sibling test inserted first wins the bare name.
    """
    spec = importlib.util.spec_from_file_location(f"det_{name}", DET / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


gen_boundary = _load("gen_boundary")
report = _load("report")
infer_trace = _load("infer_trace")
call_sites = _load("call_sites")
segment = _load("segment")


GOAL_BLOCK = """
  Sigma : gFunctors
  islaG0 : islaG Sigma
  H : threadG
  witness : writeSuccessNativeWitness Decoded
  b : bv 64
  Hbound : 0 <= bv_unsigned b
  ============================
  _ : instr_lookup_resources lookup
  _ : instr_pre 89360 encoderIntEntryBoundary
  --------------------------------------□
  _ : "x2" ↦ᵣ RVal_Bits (writeSuccessFrameSp witness)
  _ : (bv_unsigned (writeSuccessFrameSp witness) + 1032)
      ↦ₘ∗ take 69 (writeSuccessValues witness)
  _ : spec_trace (writeSuccessTraceTail witness)
  --------------------------------------∗
  instr_pre 87876 whatever
"""


class Sections(unittest.TestCase):
    def test_splits_the_three_parts(self):
        coq, persistent, spatial = gen_boundary.sections(GOAL_BLOCK)
        self.assertEqual([name for name, _ in coq],
                         ["Sigma", "islaG0", "H", "witness", "b", "Hbound"])
        self.assertEqual(len(persistent), 2)
        self.assertEqual(len(spatial), 3)

    def test_joins_a_wrapped_hypothesis(self):
        _coq, _persistent, spatial = gen_boundary.sections(GOAL_BLOCK)
        self.assertIn("↦ₘ∗ take 69 (writeSuccessValues witness)", spatial[1])
        self.assertTrue(spatial[1].startswith("(bv_unsigned"))

    def test_the_conclusion_is_not_a_hypothesis(self):
        _coq, _persistent, spatial = gen_boundary.sections(GOAL_BLOCK)
        self.assertNotIn("instr_pre 87876 whatever", spatial)


class FreeLocals(unittest.TestCase):
    def test_keeps_the_segments_own_binders_as_parameters(self):
        coq, _persistent, _spatial = gen_boundary.sections(GOAL_BLOCK)
        free = gen_boundary.free_locals(coq, "(witness : writeSuccessNativeWitness Decoded)")
        self.assertEqual([name for name, _ in free], ["b", "Hbound"])

    def test_closes_what_the_automation_introduced(self):
        coq, _persistent, _spatial = gen_boundary.sections(GOAL_BLOCK)
        source = gen_boundary.boundary_source(
            "TestBoundary", "(witness : writeSuccessNativeWitness Decoded)",
            coq, _spatial, seal=False)
        self.assertIn("∃ b : bv 64,", source)
        self.assertIn("LithiumUnfold (@TestBoundary)", source)

    def test_a_wide_boundary_is_sealed(self):
        coq, _persistent, _spatial = gen_boundary.sections(GOAL_BLOCK)
        wide = [f"P{index}" for index in range(20)]
        source = gen_boundary.boundary_source("WideBoundary", "", coq, wide,
                                              seal=True)
        self.assertIn("Global Opaque WideBoundary.", source)
        self.assertIn("WideBoundary_unfold", source)


class ExplicitArguments(unittest.TestCase):
    def test_takes_the_explicit_groups_only(self):
        binders = ("`{!islaG Sigma} `{!threadG} (sp data size : bv 64) "
                   "(hashBase : Z) (tail : spec) (P : iProp Sigma)")
        self.assertEqual(gen_boundary.explicit_arguments(binders),
                         "sp data size hashBase tail P")

    def test_skips_implicit_and_instance_groups(self):
        binders = ("`{!islaG Sigma} `{!threadG} {Decoded} "
                   "`{!WriteSuccessMemoryRepresentation Decoded} "
                   "(args : WriteSuccessArgs Decoded) (P : iProp Sigma)")
        self.assertEqual(gen_boundary.explicit_arguments(binders),
                         "args P")


class Report(unittest.TestCase):
    def test_orders_the_classes_by_segments_blocked(self):
        by_lemma = {
            "a": {"outcome": "stalled", "pred_class": "C1"},
            "b": {"outcome": "stalled", "pred_class": "C2"},
            "c": {"outcome": "stalled", "pred_class": "C2"},
            "d": {"outcome": "reached"},
        }
        table = report.class_table(by_lemma, ["a", "b", "c", "d"])
        self.assertIn("| C2 | 2 |", table[2])
        self.assertIn("| C1 | 1 |", table[3])

    def test_newest_record_wins(self):
        rows = [(1.0, {"lemma": "x", "frame": 5}),
                (2.0, {"lemma": "x", "frame": 9})]
        self.assertEqual(report.newest_by_lemma(rows)["x"]["frame"], 9)


class DefiningLookup(unittest.TestCase):
    """A loaded word, written in terms the boundary can state.

    Post-withdrawals' first event mentions `vmem`, which the segment
    does not bind, and the same context says which element of which
    list it is. Everything on the left of that hypothesis is bound, so
    the boundary can state the value the way
    `WriteSuccessExactTailWithdrawalCountEntry.v` already states
    indices 11 and 12 of the same list.
    """

    CONTEXT = (
        "  vmem : bv 64\n"
        "  H2 : -1 < bv_unsigned vmem < bv_modulus 64\n"
        "  Hlookup : take 69 (writeSuccessValues witness) "
        "!! Z.to_nat (13) = Some vmem"
    )

    def test_reads_the_defining_hypothesis(self):
        self.assertEqual(
            infer_trace.defining_lookup(self.CONTEXT, "vmem"),
            "default (BV 64 0) "
            "(take 69 (writeSuccessValues witness) !! Z.to_nat (13))")

    def test_no_hypothesis_is_not_a_guess(self):
        self.assertIsNone(infer_trace.defining_lookup(self.CONTEXT, "other"))
        self.assertIsNone(infer_trace.defining_lookup("", "vmem"))


class CallSites(unittest.TestCase):
    def test_checked_in_index_supplies_calls_without_ignored_dumps(self):
        with tempfile.TemporaryDirectory() as directory:
            missing = Path(directory) / "missing"
            lines, modules, unknown = call_sites.premises(
                0x15744, 0x15754, dumps=missing)
        self.assertEqual(lines,
                         ["  □ instr_pre 0x15d10 encoderIntEntryBoundary -∗"])
        self.assertEqual(modules, ["ZesuSsz.Proofs.WriteSuccess.Interfaces"])
        self.assertEqual(unknown, [])

    def test_existing_dump_takes_precedence_over_index(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "block_1.dump").write_text(
                "   1574c: 5c8080e7 jalr 1480(ra) # 15d10 <encoder_int>\n")
            (root / "index.json").write_text(json.dumps({"calls": []}))
            found = call_sites.call_sites(root, root / "index.json")
        self.assertEqual(found[0x1574c], (0x15d10, "encoder_int"))


class ExistingSegment(unittest.TestCase):
    def test_exact_range_finds_the_suffix_module(self):
        path, lemma = segment.existing_segment(0x15744, 0x15754)
        self.assertEqual(path.name, "WriteSuccessExactSuffixEntrySegment.v")
        self.assertEqual(lemma, "write_success_exact_suffix_entry_segment")
        self.assertIsNone(segment.existing_segment(0x15748, 0x15754))

    def test_generation_reports_probe_outcome_and_class(self):
        path, lemma = segment.existing_segment(0x15744, 0x15754)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            result = {"seconds": 3.8, "outcome": "stalled",
                      "pred_class": "C3", "signature": "subsume (…) (…)"}
            with patch.object(segment, "infer", return_value=result) as probe:
                record = segment.generate_existing(
                    path, lemma, 0x15754, root / "generated",
                    root / "probe.jsonl", root / "build", 30)
            source = Path(record["generated"]).read_text()
            self.assertIn("Require Import ZesuSsz.Automation.Sets.v2.", source)
            self.assertEqual(probe.call_args.kwargs["extra_imports"],
                             ("ZesuSsz.Automation.Sets.v2",))
            self.assertIn("Proof. move => *. zesu_block. Qed.", source)
            self.assertEqual(json.loads((root / "probe.jsonl").read_text())
                             ["pred_class"], "C3")


if __name__ == "__main__":
    unittest.main()
