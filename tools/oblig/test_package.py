"""Goal packaging: address class, prover tasks within the byte bound, answers, spatial diagnosis."""
import io
import json
from contextlib import redirect_stdout
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import package  # noqa: E402

HEADER = "Require Import ZesuSsz.Automation2.All.\nFrom Coq Require Import ZArith.ZArith.\nLocal Open Scope Z_scope."
SLOT = "(* PROOF-SLOT: replace this line and the Admitted below with the proof script and Qed. *)\nAdmitted.\n"
# Code addresses are built at run time, so that this file names none (plan A9).
CODE = (1 << 31) + 0xc4
TEXT_ADDRESS = "%#x" % ((1 << 31) + 0xd6960)
DECIMAL = 2148 * 10 ** 6 + 123


def positive(value):
    if value == 1:
        return "xH"
    return "(%s %s)" % ("xI" if value % 2 else "xO", positive(value // 2))


def make_run(root, goals):
    run = Path(root) / "run"
    manifest = dict(block="00c4", bank="/nonexistent", caller="/nonexistent", rounds=1, goals=[], skipped=[],
                    exports=[], reruns=[])
    for n, statement in enumerate(goals, 1):
        gid = "00c4-%d" % n
        name = "residual_txAccessList_00c4_%016x" % n
        d = run / "goals" / gid
        d.mkdir(parents=True)
        (d / "goal.v").write_text("%s\n\nLemma %s :\n  %s.\nProof.\n%s" % (HEADER, name, statement, SLOT))
        (d / "STATUS.json").write_text(json.dumps(dict(attempts=[], result="OPEN")))
        manifest["goals"].append(dict(id=gid, name=name, statement=statement, reparse="exact", source="final",
                                      binders=["x"], readable="x : Z\n============================\nx < x + 1",
                                      counts=dict(kept=1, props=3, small=2)))
    (run / "MANIFEST.json").write_text(json.dumps(manifest))
    return run, manifest


INDEX = dict(entries=[dict(name="residual_x_1", statement="forall (x : Z), Z.lt x (Z.add x 1)", proof="intros. lia.\nQed.",
                           source="t", head="Z.lt", names=["Z", "Z.add", "Z.lt"], statement_sha256="0" * 64)])


class AddressTests(unittest.TestCase):
    def test_text_and_literal_addresses_are_found(self):
        self.assertEqual(package.address_matches("pc = " + TEXT_ADDRESS)[0]["match"], TEXT_ADDRESS)
        hits = package.address_matches("forall (x : Z), x = Zpos %s" % positive(CODE))
        self.assertEqual(hits, [dict(match=str(CODE), source="literal", hex="%#x" % CODE)])
        self.assertEqual(package.address_matches("forall (x : Z), x = Zpos %s" % positive(0xa0000000)), [])
        self.assertEqual(package.address_matches("x = %d" % DECIMAL),
                         [dict(match=str(DECIMAL), source="text"),
                          dict(match=str(DECIMAL), source="literal", hex="%#x" % DECIMAL)])


class GoalTaskTests(unittest.TestCase):
    def test_tasks_carry_the_loop_text_the_answer_form_and_fitting_context(self):
        with tempfile.TemporaryDirectory() as root:
            run, manifest = make_run(root, ["forall (x : Z), Z.lt x (Z.add x 1)",
                                            "forall (x : Z), x <> Zpos %s" % positive(CODE)])
            hints = Path(root) / "hints.py"
            hints.write_text("import sys\nprint('# Hint slice at ' + ' '.join(sys.argv[sys.argv.index('--pcs') + 1:"
                             "sys.argv.index('--pcs') + 2]))\n")
            saved, package.HINTS = package.HINTS, hints
            try:
                records = [package.package_goal(run, manifest, g, "txAccessList", "haiku-low", 12000, INDEX, root)
                           for g in package.open_goals(run, manifest)]
                text = Path(records[0]["task"]).read_text()
                tight = package.package_goal(run, manifest, manifest["goals"][0], "txAccessList", "haiku-low",
                                             records[0]["prompt_bytes"] - 1, INDEX, root)
            finally:
                package.HINTS = saved
            self.assertEqual(records[0]["next"], "prover")
            self.assertEqual(records[0]["id"], package.obligation_id("txAccessList", "00c4", manifest["goals"][0]["statement"]))
            self.assertTrue(records[0]["id"].startswith("txAccessList/goal/00c4-"))
            self.assertIn("# Residual goal 00c4-1 (block 00c4)", text)
            self.assertIn('"verdict": "proved" | "false" | "need_context" | "give_up"', text)
            self.assertIn("residual_x_1", text)
            self.assertIn("# Hint slice at +0x00c4", text)
            self.assertEqual(records[0]["context_supplied"], ["similar", "hints"])
            self.assertEqual(records[0]["prompt_bytes"], len(text.encode()))
            self.assertEqual(records[1]["class"], "ADDRESS")
            self.assertEqual(records[1]["next"], "decision")
            self.assertFalse((run / "package" / "00c4-2" / "TASK-haiku-low.md").exists())
            self.assertEqual(len(tight["context_supplied"]), 1)
            self.assertLessEqual(tight["prompt_bytes"], records[0]["prompt_bytes"] - 1)
            too_small = package.package_goal(run, manifest, manifest["goals"][0], "txAccessList", "haiku-low", 100,
                                             INDEX, None)
            self.assertEqual(too_small["next"], "too-large")

    def test_a_history_premise_brings_the_history_hint(self):
        hist = ("(forall (x : Z), (forall (H11 : (@ZesuSsz.Automation2.Hist.zesu_hist "
                "(@ZesuSsz.Generated.K.FP301.Pilot0170Entries.fp_machineAt0170_ForwardA0N0_Hist x))), "
                "(@Coq.ZArith.BinInt.Z.lt x (@Coq.ZArith.BinInt.Z.add x (1)%Z))))")
        with tempfile.TemporaryDirectory() as root:
            run, manifest = make_run(root, [hist, "forall (x : Z), Z.lt x (Z.add x 1)"])
            records = [package.package_goal(run, manifest, g, "keys", "haiku-low", 12000, None, None)
                       for g in manifest["goals"]]
            text = Path(records[0]["task"]).read_text()
        self.assertEqual(records[0]["context_supplied"], ["hist"])
        self.assertIn("## History hint", text)
        self.assertIn("unfold fp_machineAt0170_ForwardA0N0_Hist in H11; rewrite zesu_hist_eq in H11;", text)
        self.assertIn("destruct H11 as [_ H11]", text)
        self.assertEqual(records[1]["context_supplied"], [])
        self.assertNotIn("range", records[0]["context_supplied"])

    def test_premises_omitted_for_size_reach_the_record_and_the_task(self):
        log = ("1.0 @@X begin final\n1.1 @@X binders x\n1.2 @@X dropped-fact H7 3021 and\n"
               "1.3 @@X dropped-fact H9 2600 ZesuSsz.Contracts.AltFlAllocPremises.altFlBlock\n"
               "1.4 @@X counts props=9 small=7 kept=1\n1.5 @@X stmt forall (x : Z), Z.lt x (Z.add x 1)\n1.6 @@X end\n")
        rl = package.rl
        goals, _, _ = rl.select_goals(rl.parse_export(log.split("\n")), "00c4", False, "txAccessList")
        dropped = [dict(name="H7", nodes=3021, head="and"),
                   dict(name="H9", nodes=2600, head="ZesuSsz.Contracts.AltFlAllocPremises.altFlBlock")]
        self.assertEqual(goals[0]["dropped_facts"], dropped)
        with tempfile.TemporaryDirectory() as root:
            run, manifest = make_run(root, ["forall (x : Z), Z.lt x (Z.add x 1)", "forall (y : Z), y = y"])
            manifest["goals"][0]["dropped_facts"] = dropped
            records = [package.package_goal(run, manifest, g, "keys", "haiku-low", 12000, None, None)
                       for g in manifest["goals"]]
            text = Path(records[0]["task"]).read_text()
            other = Path(records[1]["task"]).read_text()
            stored = json.loads((run / "package" / "00c4-1" / "PACKAGE.json").read_text())
        self.assertEqual(stored["dropped_facts"], dropped)
        self.assertIn("premises omitted for size: H7 (3021 nodes, head and), H9 (2600 nodes, head "
                      "ZesuSsz.Contracts.AltFlAllocPremises.altFlBlock)", text)
        self.assertEqual(records[1]["dropped_facts"], [])
        self.assertNotIn("premises omitted for size", other)


class AnswerTests(unittest.TestCase):
    def test_answers_become_collect_files(self):
        with tempfile.TemporaryDirectory() as root:
            run, _ = make_run(root, ["forall (x : Z), Z.lt x (Z.add x 1)"])
            raw = json.dumps(dict(verdict="proved", proof="intros. lia.\nQed."))
            self.assertEqual(package.write_answer(run, "00c4-1", json.loads(raw), raw, "haiku-low", 100, 20),
                             ("proved", None))
            self.assertEqual((run / "answers" / "00c4-1.v").read_text(), "intros. lia.\nQed.\n")
            meta = json.loads((run / "answers" / "00c4-1.json").read_text())
            self.assertEqual((meta["tokens"], meta["tier"], meta["verdict"]), (120, "haiku-low", "proved"))
            raw = json.dumps(dict(verdict="proved", proof="admit.\nQed."))
            self.assertEqual(package.write_answer(run, "00c4-1", json.loads(raw), raw)[1],
                             "the answer uses a forbidden command")
            for bad in ({"verdict": "maybe"}, {"verdict": "proved"}, {"verdict": "need_context"},
                        {"verdict": "false"}, {"verdict": "give_up", "needs": "x"}):
                with self.subTest(bad=bad), self.assertRaises(package.PackageError):
                    package.write_answer(run, "00c4-1", bad, json.dumps(bad))
            with self.assertRaises(package.PackageError):
                package.write_answer(run, "00c4-9", {"verdict": "give_up"}, "{}")
            raw = json.dumps(dict(verdict="give_up"))
            package.write_answer(run, "00c4-1", json.loads(raw), raw)
            self.assertEqual(json.loads((run / "answers" / "00c4-1.json").read_text())["verdict"], "give_up")


SPATIAL_LOG = """12.0 @@X skip final spatial
12.1 @@S begin final
12.1 @@S head lithium.definitions.find_in_context isla.automation.FindRegMapsTo
12.1 @@S seek reg "x10"
12.1 @@S seek-vars b18
12.2 @@S res s "Hx11" full "x11" ↦ᵣ RVal_Bits b18
12.2 @@S res p ~3 full instr_table
12.2 @@S fact H4 full bv_unsigned b18 < 56
12.2 @@S counts persistent=1 spatial=1 facts=3 shared=1
12.2 @@S end
12.3 @@S skip final error
"""


class DiagnosisTests(unittest.TestCase):
    def test_records_parse_into_typed_tasks(self):
        records = package.spatial_records(SPATIAL_LOG)
        self.assertEqual(len(records), 2)
        record = records[0]
        self.assertEqual(record["seek"], dict(sort="reg", text='"x10"'))
        self.assertEqual(len(record["res"]), 2)
        self.assertEqual(record["counts"]["spatial"], "1")
        self.assertEqual(records[1], dict(skip="final error"))
        with tempfile.TemporaryDirectory() as root:
            log = Path(root) / "export.log"
            log.write_text(SPATIAL_LOG)
            disasm = Path(root) / "disasm.txt"
            disasm.write_text("+0x00c4: ld a0, 8(sp)")
            with redirect_stdout(io.StringIO()):
                package.main(["diagnose", "--log", str(log), "--run", root, "--function", "txAccessList",
                              "--block", "00c4", "--disasm", str(disasm)])
            task = (Path(root) / "diagnose" / "00c4-1" / "TASK.md").read_text()
            request = json.loads((Path(root) / "diagnose" / "00c4-1" / "REQUEST.json").read_text())
            self.assertIn('seeks (reg): `"x10"`', task)
            self.assertIn("+0x00c4: ld a0, 8(sp)", task)
            for kind in package.DIAGNOSIS_KINDS:
                self.assertIn('"kind": "%s"' % kind, task)
            self.assertEqual(request["id"], "txAccessList/diagnosis/00c4-1")
            self.assertEqual(json.loads((Path(root) / "diagnose" / "00c4-2" / "REQUEST.json").read_text())["next"],
                             "skip")
            answer = Path(root) / "answer.json"
            answer.write_text(json.dumps(dict(kind="pure_goal", statement="forall (b : bv 64), bv_unsigned b < 56")))
            with redirect_stdout(io.StringIO()):
                package.main(["diagnosis-answer", "--task", str(Path(root) / "diagnose" / "00c4-1"),
                              "--answer", str(answer)])
            self.assertTrue((Path(root) / "diagnose" / "00c4-1" / "pure_goal.txt").exists())
        for bad in ({"kind": "proof"}, {"kind": "false", "statement": "s"}, {"kind": "annotation", "annotation": "x"},
                    {"kind": "rule_gap", "entailment": "pc %s ⊢ ..." % TEXT_ADDRESS}):
            with self.subTest(bad=bad), self.assertRaises(package.PackageError):
                package.parse_diagnosis(bad)


class StrictSliceTests(unittest.TestCase):
    def test_unrelated_repeated_and_conjunct_premises_drop(self):
        statement = ("forall (x y z : Z), (0 <= x) -> (z = 3) -> (0 <= x) -> (y = x /\\ 0 <= y) -> (y = x) -> "
                     "(x + 1 > 0)")
        sliced, dropped = package.strict_slice(statement)
        self.assertEqual(dropped, ["(z = 3)", "(0 <= x)", "(y = x)"])
        self.assertEqual(sliced, "forall (x y z : Z),\n  (0 <= x) ->\n  (y = x /\\ 0 <= y) ->\n  (x + 1 > 0)")

    def test_nothing_dropped_keeps_the_statement(self):
        statement = "forall (x : Z), (0 <= x) -> (x + 1 > 0)"
        self.assertEqual(package.strict_slice(statement), (statement, []))

    def test_named_premise_binders_of_the_exporter(self):
        statement = ("forall (x : Z) (w : bv 8) (H0 : 0 <= x) (H1 : bv_unsigned w = 3) (H2 : 0 <= x), "
                     "(x + 1 > 0)")
        sliced, dropped = package.strict_slice(statement)
        self.assertEqual(dropped, ["(H1 : bv_unsigned w = 3)", "(H2 : 0 <= x)"])
        self.assertEqual(sliced, "forall (x : Z) (w : bv 8) (H0 : 0 <= x),\n  (x + 1 > 0)")
        self.assertEqual(package.premise_count(statement), 3)


if __name__ == "__main__":
    unittest.main()
