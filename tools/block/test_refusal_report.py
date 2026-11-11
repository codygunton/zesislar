"""The refusal report: step, pc, instruction, head, last stage and fact order."""
from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from refusal_report import analyze, instructions, parse, render, render_unfinished, unfinished

OBJDUMP = """
800d6974:	00058683          	lb	a3,0(a1)
800d6978:	00b505b3          	add	a1,a0,a1
"""

# Two steps (the second raises the side condition), a finisher stage that
# runs without Hlate, a later stage where Hlate first appears, then the final
# refusal of the side condition with Hx and Hlate relevant.
LOG = """0.100 @@D step
0.101 @@D pc 2148362612
0.102 @@D head instr_body 2148362612 __
0.103 @@D names Hx
0.200 @@D step
0.201 @@D pc 2148362616
0.202 @@D sidecond bv_unsigned __ < 5
0.203 @@D head ⌜bv_unsigned __ < 5⌝ ∗ __
0.204 @@D names Hx Hlate
0.300 @@D stage "finish_v1.solvers"
0.301 @@D head bv_unsigned x < 5
0.302 @@D fact Hx : bv_unsigned x < 10
0.303 @@D facts-end 1
0.400 @@D stage "final_pure"
0.401 @@D head bv_unsigned x < 5
0.402 @@D fact Hx : bv_unsigned x < 10
0.403 @@D fact Hlate : bv_unsigned x =
0.403 3
0.404 @@D facts-end 2
0.500 @@D refuse "final"
0.501 @@D head bv_unsigned x < 5
0.502 @@D sidecond bv_unsigned __ < 5
0.503 @@D relevant Hx Hlate
0.504 @@D fact Hx : bv_unsigned x < 10
0.505 @@D fact Hlate : bv_unsigned x = 3
0.506 @@D facts-end 2
0.507 @@GOAL-BEGIN
0.508 @@HYP Hlate : bv_unsigned x = 3
0.509 @@HYP Hx : bv_unsigned x < 10
0.510 @@CONCL bv_unsigned x < 5
0.511 @@GOAL-END
"""


class RefusalReport(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / "disassembly.objdump"
        path.write_text(OBJDUMP)
        self.table = instructions(path)

    def message(self, log, **options):
        messages = analyze(parse(log.splitlines()), self.table, **options)
        self.assertEqual(len(messages), 1)
        return messages[0]

    def test_step_pc_instruction_head_and_last_stage(self):
        message = self.message(LOG)
        self.assertEqual(message["step"], 2)
        self.assertTrue(message["raised_at_step"])
        self.assertEqual(message["pc"], 0x800d6978)
        self.assertEqual(message["instruction"], "add a1,a0,a1")
        self.assertEqual(message["head"], "bv_unsigned x < 5")
        self.assertEqual(message["last_stage"], "final_pure")

    def test_a_fact_that_first_appears_after_the_finisher(self):
        message = self.message(LOG)
        stages = {fact["name"]: fact["stage"] for fact in message["facts"]}
        self.assertEqual(stages, {"Hx": "finish_v1.solvers", "Hlate": "final_pure"})
        steps = {fact["name"]: (fact["step"], fact["pc"]) for fact in message["facts"]}
        self.assertEqual(steps, {"Hx": (1, 0x800d6974), "Hlate": (2, 0x800d6978)})
        self.assertEqual(message["verdict"], "fact-after-finisher")
        text = render(message)
        self.assertIn('insn="add a1,a0,a1"', text)
        self.assertIn("Hlate@step 2/stage final_pure#1", text)

    def test_facts_present_before_the_finisher(self):
        log = LOG.replace("0.302 @@D fact Hx : bv_unsigned x < 10\n",
                          "0.302 @@D fact Hx : bv_unsigned x < 10\n0.302 @@D fact Hlate : bv_unsigned x = 3\n")
        self.assertEqual(self.message(log)["verdict"], "facts-before-finisher")

    def test_expected_fact_absent_here_and_found_in_a_control_run(self):
        refused = LOG.replace("Hlate", "Hother").replace("bv_unsigned x = 3", "0 <= 1")
        control = parse(LOG.splitlines())
        message = self.message(refused, expect=re.compile(r"bv_unsigned x = 3"), control=control)
        self.assertEqual(message["expect"]["present"], [])
        self.assertEqual(message["expect"]["control"]["stage"], "final_pure")
        self.assertEqual(message["expect"]["control"]["pc"], 0x800d6978)
        self.assertEqual(message["expect"]["control"]["step"], 2)
        self.assertIn("absent in this run", render(message))

    def test_a_log_without_refusals_reports_where_the_run_was(self):
        log = "\n".join(line for line in LOG.splitlines() if "0.5" not in line.split()[0])
        parsed = parse(log.splitlines())
        self.assertEqual(analyze(parsed, self.table), [])
        state = unfinished(parsed, self.table, re.compile(r"bv_unsigned x = 3"), parse(LOG.splitlines()))
        self.assertEqual((state["steps"], state["pc"], state["last_stage"]), (2, 0x800d6978, "final_pure"))
        self.assertEqual(state["head"], "bv_unsigned x < 5")
        self.assertEqual(state["expect"]["present"], ["Hlate"])
        self.assertEqual(state["expect"]["control"]["step"], 2)
        self.assertIn("NO REFUSAL", render_unfinished(state))


if __name__ == "__main__":
    unittest.main()
