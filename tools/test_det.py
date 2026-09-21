"""Tests for the determinism branch's segment tools."""

import sys
import unittest
from pathlib import Path

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


if __name__ == "__main__":
    unittest.main()
