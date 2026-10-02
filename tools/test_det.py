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
infer_boundary = _load("infer_boundary")


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

    def test_grouped_locals_keep_their_common_type(self):
        coq, _, _ = gen_boundary.sections(GOAL_BLOCK.replace("b : bv 64", "b, c : bv 64"))
        self.assertEqual(dict(coq)["b"], "bv 64")
        self.assertEqual(dict(coq)["c"], "bv 64")

    def test_spatial_context_without_persistent_separator(self):
        goal = "  b : bv 64\n  ============================\n  _ : reg_col sys_regs\n  --------------------------------------∗\n  False\n"
        coq, persistent, spatial = gen_boundary.sections(goal)
        self.assertEqual(coq, [("b", "bv 64")])
        self.assertEqual(persistent, [])
        self.assertEqual(spatial, ["reg_col sys_regs"])

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

    def test_unknown_resources_do_not_enter_a_memory_seal(self):
        coq, _persistent, _spatial = gen_boundary.sections(GOAL_BLOCK)
        wide = [f"P{index}" for index in range(20)]
        source = gen_boundary.boundary_source("WideBoundary", "", coq, wide,
                                              seal=True)
        self.assertNotIn("Global Opaque", source)
        self.assertIn("LithiumUnfold (@WideBoundary)", source)


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

    def test_post_transactions_memcpy_has_closed_entry_boundary(self):
        _lines, modules, unknown = call_sites.premises(0x15668, 0x156e8)
        self.assertIn("ZesuSsz.Proofs.WriteSuccess.Interfaces", modules)
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

    def test_exit_premise_before_entry_finds_the_third_tail_module(self):
        path, lemma = segment.existing_segment(0x159b8, 0x159d8)
        self.assertEqual(path.name, "WriteSuccessExactTailFieldsThirdSegment.v")
        self.assertEqual(lemma, "write_success_exact_tail_fields_third_segment")

    def test_open_probe_uses_requested_build_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(sys, "argv", ["segment.py", "--entry", "0x156e8",
                                            "--exit", "0x15744", "--spec", "True",
                                            "--binders", "(P : iProp Sigma)",
                                            "--probe", "--build-dir", str(root / "build"),
                                            "--spec-out", str(root / "spec.json"),
                                            "--out", str(root / "result.jsonl")]), \
                 patch.object(segment, "call_premises", return_value=([], [], [])), \
                 patch.object(segment.subprocess, "run") as probe:
                probe.return_value.returncode = 0
                self.assertEqual(segment.main(), 0)
            command = probe.call_args.args[0]
            self.assertEqual(command[command.index("--build-dir") + 1],
                             str(root / "build"))

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


class ProbeGoals(unittest.TestCase):
    def test_existing_probe_shelves_term_goals_before_show(self):
        path, lemma = segment.existing_segment(0x159b8, 0x159d8)
        source = infer_boundary.probe_source(path, lemma, "0x159d8", [])
        self.assertIn(infer_boundary.SHELVE_TERM_GOALS, source)
        self.assertIn(f'all: idtac "{infer_boundary.RAW_BEGIN}".', source)
        self.assertIn(f'all: idtac "{infer_boundary.RAW_END}".', source)
        self.assertLess(source.index(infer_boundary.SHELVE_TERM_GOALS),
                        source.rindex("\nShow."))

    def test_closed_probe_needs_no_goal_for_raw_markers(self):
        path, lemma = segment.existing_segment(0x159b8, 0x159d8)
        source = infer_boundary.probe_source(path, lemma, "0x159d8", [])
        self.assertNotIn('1: idtac "BOUNDARY-ALL-GOALS', source)
        output = (infer_boundary.probes.BEGIN + "No more goals.\n"
                  + infer_boundary.probes.END)
        with patch.object(infer_boundary, "run", return_value=output):
            record = infer_boundary.infer(path, lemma, "0x159d8", Path("unused"), [], 30)
        self.assertNotEqual(record["outcome"], "error")
        self.assertEqual(record["raw_goals"], "No more goals.\n")

    def test_shelving_keeps_term_and_prop_goals_in_raw_record(self):
        raw = "2 goals\n=====\nspec\ngoal 2 is:\nsubsume left right"
        text = (infer_boundary.RAW_BEGIN + infer_boundary.RAW_BEGIN + raw
                + infer_boundary.RAW_END + infer_boundary.RAW_END
                + "1 goal\n=====\nsubsume left right")
        selected, record = infer_boundary.goal_record(text)
        self.assertEqual(record["raw_goals"], text)
        self.assertEqual([g["conclusion"] for g in record["goals"]],
                         ["spec", "subsume left right"])
        self.assertEqual(infer_boundary.conclusion_text(selected)[1],
                         "subsume left right")

    def test_record_preserves_second_goal(self):
        path, lemma = segment.existing_segment(0x159b8, 0x159d8)
        text = GOAL_BLOCK + "\ngoal 2 is:\n  subsume left right\n"
        output = infer_boundary.probes.BEGIN + text + infer_boundary.probes.END
        with patch.object(infer_boundary, "run", return_value=output):
            record = infer_boundary.infer(path, lemma, "0x159d8", Path("unused"), [], 30)
        self.assertEqual(record["raw_goals"], text)
        self.assertEqual(len(record["goals"]), 2)
        self.assertEqual(record["goals"][0]["conclusion"], "instr_pre 87876 whatever")
        self.assertEqual(record["goals"][1]["conclusion"], "subsume left right")


if __name__ == "__main__":
    unittest.main()
