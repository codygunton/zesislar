"""The residual loop: export records, goal files, answers, registration, RESULT lines."""
from contextlib import redirect_stdout
from pathlib import Path
import io
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import residual_loop as loop  # noqa: E402
import render_residual_module as rrm  # noqa: E402

CALLER = """Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Automation2.DiagnosticsOn.
Local Open Scope Z_scope.

Definition DesignedEntry_800d1234 (x : Z) : Prop := True.

Lemma DesignedBoundary_800d1234 (x : Z) : True.
Proof.
  zesu_block2.
Qed.
"""

STATEMENT = "(forall (x : @Coq.Numbers.BinNums.Z) (Hx : (@Coq.ZArith.BinInt.Z.le (0)%Z x)), " \
            "(@Coq.ZArith.BinInt.Z.le (0)%Z (@Coq.ZArith.BinInt.Z.add x (1)%Z)))"
OTHER = STATEMENT.replace("(1)%Z", "(2)%Z")

# A stopped run: two split records (one wrapped over two lines), a split skip,
# then no final record.
SPLIT_LOG = """12.000 Warning: something
167.100 @@X begin split
167.101 @@X binders x Hx
167.102 @@X conclusion-definitions
167.103 @@X counts props=146 small=120 kept=1
167.104 @@X stmt %s
167.105 @@X end
167.200 @@X skip split evar in goal
167.300 @@X begin split
167.301 @@X binders x Hx
167.302 @@X conclusion-definitions LET0
167.303 @@X counts props=146 small=120 kept=1
167.304 @@X stmt %s
167.304 %s
167.305 @@X end
""" % (STATEMENT, OTHER[:OTHER.index(" ", 40)], OTHER[OTHER.index(" ", 40) + 1:])

FINAL_LOG = SPLIT_LOG + """900.000 @@X skip final spatial
900.100 @@X begin final
900.101 @@X binders x Hx
900.102 @@X conclusion-definitions
900.103 @@X counts props=146 small=120 kept=1
900.104 @@X stmt %s
900.105 @@X end
""" % STATEMENT

ANSWER = "intros.\n  (* unique-proof-token *) lia.\nQed.\n"


class ExportRecordTests(unittest.TestCase):
    def test_records_join_wrapped_lines_and_keep_skips(self):
        found = loop.parse_export(SPLIT_LOG.split("\n"))
        self.assertEqual([(r["kind"], r["status"]) for r in found],
                         [("split", "pure"), ("split", "skip"), ("split", "pure")])
        self.assertEqual(found[0]["statement"], STATEMENT)
        self.assertEqual(found[2]["statement"], OTHER)
        self.assertEqual(found[0]["binders"], ["x", "Hx"])
        self.assertEqual(found[2]["conclusion_definitions"], ["LET0"])
        self.assertEqual(found[0]["counts"], dict(props=146, small=120, kept=1))
        self.assertEqual(found[1]["reason"], "evar in goal")

    def test_stopped_run_takes_split_records(self):
        goals, source, _ = loop.select_goals(loop.parse_export(SPLIT_LOG.split("\n")), "1234", closed=False)
        self.assertEqual(source, "split")
        self.assertEqual(len(goals), 2)
        self.assertTrue(goals[0]["name"].startswith("residual_1234_"))
        self.assertEqual(goals[0]["name"], "residual_1234_" + loop.sha(STATEMENT)[:16])

    def test_finished_run_takes_final_records(self):
        goals, source, split_only = loop.select_goals(loop.parse_export(FINAL_LOG.split("\n")), "1234",
                                                      closed=False)
        self.assertEqual(source, "final")
        self.assertEqual([g["statement"] for g in goals], [STATEMENT])
        self.assertEqual(split_only, 1)  # the second split goal closed after the split

    def test_closed_run_has_no_goals(self):
        goals, source, split_only = loop.select_goals(loop.parse_export(SPLIT_LOG.split("\n")), "1234",
                                                      closed=True)
        self.assertEqual((goals, source, split_only), ([], "final", 2))

    def test_a_later_line_is_not_part_of_the_last_record(self):
        log = SPLIT_LOG + "2433.115 resource_guard.sh: line 1801: 2304756 Killed\n"
        found = loop.parse_export(log.split("\n"))
        self.assertEqual([r["status"] for r in found], ["pure", "skip", "pure"])

    def test_equal_statements_merge(self):
        final = FINAL_LOG[FINAL_LOG.index("900.100"):]
        goals, _, _ = loop.select_goals(loop.parse_export((FINAL_LOG + final).split("\n")), "1234", False)
        self.assertEqual([g["copies"] for g in goals], [2])

    def test_quiet_watch_stops_only_after_a_split_record(self):
        watch = loop.QuietWatch(60)
        self.assertFalse(watch("@@X skip final spatial", 10.0))
        self.assertFalse(watch(None, 100.0))
        self.assertFalse(watch("@@X begin split", 167.0))
        self.assertFalse(watch("@@X end", 168.0))
        self.assertFalse(watch(None, 200.0))
        # The compiler prints nothing while the finisher runs; idle ticks stop it.
        self.assertTrue(watch(None, 228.5))


class CallerTests(unittest.TestCase):
    def test_export_caller_imports_the_switch_last(self):
        text = loop.export_caller(CALLER)
        lines = text.split("\n")
        self.assertNotIn("Require Import ZesuSsz.Automation2.DiagnosticsOn.", lines)
        self.assertEqual(lines[lines.index(loop.SWITCH) - 1], "Require Import ZesuSsz.Automation2.All.")
        self.assertEqual(lines[lines.index(loop.SWITCH) + 1], "Local Open Scope Z_scope.")

    def test_rerun_caller_replaces_the_block_module_import(self):
        source = CALLER.replace("Require Import ZesuSsz.Automation2.DiagnosticsOn.",
                                "Require Import ZesuSsz.Residuals.Block800d1234.")
        text = loop.export_caller(source, "Require Import ResidualLoop.Block800d1234.")
        self.assertNotIn("ZesuSsz.Residuals.Block800d1234", text)
        self.assertLess(text.index("ResidualLoop.Block800d1234"), text.index(loop.SWITCH))

    def test_header_drops_switches_and_the_block_module(self):
        source = CALLER.replace("Require Import ZesuSsz.Automation2.DiagnosticsOn.",
                                "Require Import ZesuSsz.Residuals.Block800d1234.")
        header = loop.caller_header(source, "1234")
        self.assertEqual(header[-1], "Local Open Scope Z_scope.")
        self.assertFalse(any("Residuals.Block800d1234" in line or "DiagnosticsOn" in line for line in header))
        self.assertIn("From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.", header)


def goal_dir(root, gid, statement=STATEMENT, answer=ANSWER):
    header = loop.caller_header(CALLER, "1234")
    d = Path(root) / gid
    d.mkdir(parents=True)
    name = "residual_1234_" + loop.sha(statement)[:16]
    goal = loop.goal_text(header, name, statement)
    (d / "goal.v").write_text(goal)
    (d / "proof.v").write_text(loop.goal_head(goal) + answer.strip() + "\n")
    return d, name


class GoalFileTests(unittest.TestCase):
    def test_goal_and_proof_files_are_renderer_input(self):
        with tempfile.TemporaryDirectory() as root:
            d, name = goal_dir(root, "1234-1")
            imports, lemma, _, _ = rrm.read_goal(d)
            self.assertTrue(lemma.startswith("Lemma %s :\n  %s.\nProof.\n" % (name, STATEMENT)))
            self.assertIn("Local Open Scope Z_scope.", imports)

    def test_answers_are_proof_scripts_with_one_qed(self):
        self.assertIsNone(loop.answer_problems(ANSWER))
        for bad in ["intros. admit.\nQed.\n", "Admitted.\n", "lia.\nQed.\nQed.\n", "intros. lia.\n",
                    "timeout 5 lia.\nQed.\n", "Lemma x : True.\nProof.\nexact I.\nQed.\n"]:
            with self.subTest(answer=bad):
                self.assertIsNotNone(loop.answer_problems(bad))

    def test_minimize_file_makes_the_proof_transparent(self):
        text = loop.minimize_text(["Local Open Scope Z_scope."], "residual_1234_ab", STATEMENT, ANSWER)
        self.assertIn("lia.\nDefined.\n", text)
        self.assertNotIn("Qed.", text)
        self.assertIn("Goal %s.\nintros.\n" % STATEMENT, text)
        self.assertIn("zesu_export_minimized_of '(@residual_1234_ab)", text)

    def test_roundtrip_log_gives_readable_statement_and_reprint(self):
        log = ("0.1 @@X roundtrip %s\n0.2 1 goal\n0.2   \n0.2   x : Z\n0.2   Hx : 0 <= x\n"
               "0.2   ============================\n0.2   0 <= x + 1\n0.3 Warning: something\n" % STATEMENT)
        self.assertEqual(loop.readable(log), "x : Z\nHx : 0 <= x\n============================\n0 <= x + 1")
        self.assertEqual(loop.last_record(log, "@@X roundtrip "), STATEMENT)
        self.assertIsNone(loop.first_difference(STATEMENT, STATEMENT))
        self.assertEqual(loop.first_difference("abcd", "abxd"), 2)


class RegisterTests(unittest.TestCase):
    def test_new_module_then_added_lemma_keeps_old_lemmas(self):
        with tempfile.TemporaryDirectory() as root:
            first, name1 = goal_dir(Path(root) / "a", "1234-1")
            text, added = loop.module_text("1234", None, [first])
            self.assertEqual(added, [name1])
            block, _, rows = rrm.parse_module(text)
            self.assertEqual((block, [r["name"] for r in rows]), ("1234", [name1]))
            # A later run numbers its goals from 1 again; the label is renumbered.
            second, name2 = goal_dir(Path(root) / "b", "1234-1", statement=OTHER)
            again, added = loop.module_text("1234", text, [second, first])
            self.assertEqual(added, [name2])
            _, _, rows = rrm.parse_module(again)
            self.assertEqual([(r["goal"], r["name"]) for r in rows], [("1234-1", name1), ("1234-2", name2)])

    def test_register_writes_module_and_caller_import(self):
        with tempfile.TemporaryDirectory() as root:
            run = Path(root) / "run"
            d, name = goal_dir(run / "goals", "1234-1")
            loop.write_json(d / "STATUS.json", dict(result="PASS", attempts=[]))
            caller = Path(root) / "Caller1234.v"
            caller.write_text(CALLER)
            loop.write_json(run / "MANIFEST.json", dict(block="1234", caller=str(caller), goals=[
                dict(id="1234-1", name=name, statement=STATEMENT, source="split", binders=["x", "Hx"],
                     reparse="exact")], reruns=[]))
            residuals = Path(root) / "Residuals"
            with redirect_stdout(io.StringIO()):
                loop.main(["register", "--run", str(run), "--residuals", str(residuals)])
            module = (residuals / "Block800d1234.v").read_text()
            self.assertEqual(rrm.parse_module(module)[0], "1234")
            self.assertIn("unique-proof-token", module)
            lines = caller.read_text().split("\n")
            self.assertEqual(lines.count("Require Import ZesuSsz.Residuals.Block800d1234."), 1)


class TaskTests(unittest.TestCase):
    def test_task_file_and_index_hold_the_exact_statement_and_rules(self):
        with tempfile.TemporaryDirectory() as root:
            run = Path(root)
            header = loop.caller_header(CALLER, "1234")
            goal = dict(id="1234-1", name="residual_1234_ab", statement=STATEMENT, readable="forall x : Z, ...",
                        counts=dict(kept=1, props=146, small=120), reparse="exact", round=1)
            loop.write_task(run, "1234", goal, header)
            loop.write_task_index(run, dict(block="1234", goals=[goal]))
            task = (run / "tasks" / "1234-1.md").read_text()
            index = (run / "tasks" / "README.md").read_text()
        self.assertIn(STATEMENT, task)
        self.assertIn("residual_1234_ab", task)
        self.assertIn("Never use Admitted", task)
        self.assertIn(str(run / "answers" / "1234-1.v"), task)
        self.assertIn("`1234-1.md`", index)


class ResultTests(unittest.TestCase):
    def test_result_lines_hold_no_proof_text(self):
        with tempfile.TemporaryDirectory() as root:
            run = Path(root)
            d, name = goal_dir(run / "goals", "1234-1")
            loop.write_json(d / "STATUS.json", dict(result="PASS", attempts=[
                dict(sha256="a", result="FAIL", seconds=3.0, tokens=1000),
                dict(sha256="b", result="PASS", seconds=4.0, tokens=2000)],
                minimized=dict(state="kept", binders_after=2)))
            (run / "answers").mkdir()
            (run / "answers" / "1234-1.v").write_text(ANSWER)
            loop.write_json(run / "MANIFEST.json", dict(block="1234", goals=[
                dict(id="1234-1", name=name, statement=STATEMENT, source="split", binders=["x", "Hx", "y"],
                     reparse="exact", conclusion_definitions=[])],
                reruns=[dict(round=2, closed=False, seconds=50.0, open_again=["1234-1"], new_goals=[]),
                        dict(round=3, closed=True, seconds=99.0)]))
            lines = loop.result_lines(run)
        self.assertEqual(lines[0], "RESULT 1234-1 PASS source=split reparse=exact binders=3 minimized=2 "
                                   "attempts=2 tokens=3000 tier=matchable")
        self.assertEqual(lines[1], "RESULT 1234 rerun round=2 open open_again=1234-1 new=- seconds=50.0")
        self.assertEqual(lines[2], "RESULT 1234 rerun round=3 closed seconds=99.0")
        self.assertFalse(any("unique-proof-token" in line or "lia" in line for line in lines))


if __name__ == "__main__":
    unittest.main()
