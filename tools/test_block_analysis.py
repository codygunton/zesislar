"""Check that a reached branch cannot hide another residual goal."""
import importlib.util
from pathlib import Path
import unittest

path = Path(__file__).resolve().parent / "block" / "analyze.py"
spec = importlib.util.spec_from_file_location("block_analysis", path)
analyze = importlib.util.module_from_spec(spec)
spec.loader.exec_module(analyze)


class ResidualGoals(unittest.TestCase):
    def test_pure_goal_before_reached_branch_remains_visible(self):
        output = """BOUNDARY-ALL-GOALS-END
2 goals
  value : bv 64
  ============================
  value = 0%bv

goal 2 is:
  _ : P
  --------------------------------------∗
  BLK_STOP_15694
PROBE-END
"""
        self.assertEqual(analyze.final_conclusions(output),
                         ["value = 0%bv", "BLK_STOP_15694"])

    def test_both_successor_goals_are_checked(self):
        output = """BOUNDARY-ALL-GOALS-END
2 goals
  ============================
  _ : P
  --------------------------------------∗
  BLK_STOP_1513c

goal 2 is:
  _ : Q
  --------------------------------------∗
  BLK_STOP_1511c
PROBE-END
"""
        self.assertEqual(analyze.final_conclusions(output),
                         ["BLK_STOP_1513c", "BLK_STOP_1511c"])
