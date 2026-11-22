"""One alternative per edge and state (`forward_design._disjoined_conditions`): alternatives that
differ only in memory-map guards merge as before (the guards held alone are dropped); alternatives
that differ in value guards (a byte load's input-past-end arm reads 0, a compare branches on it)
merge into the shared conditions plus the disjunction of what each holds alone. Measured cause:
set C's compare chain held 4^k such alternatives at its k-th block (FORWARD.json 9 GB)."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from forward_design import _disjoined_conditions
from symbolic_state import bits, input_expr, operation

ADDRESS = input_expr('address128', 128)
REGION = operation('bvult', ADDRESS, bits(0xc0000000, 128))
LEFT, RIGHT = input_expr('leftByte', 64), input_expr('rightByte', 64)
EQUAL = operation('=', LEFT, RIGHT)
LEFT_ZERO = operation('=', LEFT, bits(0, 64))
RIGHT_ZERO = operation('=', RIGHT, bits(0, 64))
MSTATUS = operation('=', input_expr('mstatus', 64), bits(0, 64))


class DisjoinedConditions(unittest.TestCase):
    def test_memory_map_guards_alone_merge_as_before(self):
        self.assertEqual(_disjoined_conditions([MSTATUS, REGION, EQUAL], [MSTATUS, operation('not', REGION), EQUAL]),
                         [MSTATUS, EQUAL])

    def test_value_guards_become_one_disjunction(self):
        merged = _disjoined_conditions([MSTATUS, REGION, EQUAL], [MSTATUS, operation('not', REGION), LEFT_ZERO])
        self.assertEqual(merged, [MSTATUS, operation('or', EQUAL, LEFT_ZERO)])

    def test_repeated_merges_stay_flat(self):
        merged = [MSTATUS, EQUAL]
        for other in ([MSTATUS, LEFT_ZERO], [MSTATUS, RIGHT_ZERO, LEFT_ZERO]):
            merged = _disjoined_conditions(merged, other)
        self.assertEqual(merged, [MSTATUS, operation('or', operation('or', EQUAL, LEFT_ZERO),
                                                     operation('and', RIGHT_ZERO, LEFT_ZERO))])

    def test_a_side_with_nothing_alone_gives_the_shared_conditions(self):
        # (MSTATUS) ∨ (MSTATUS ∧ EQUAL) is MSTATUS.
        self.assertEqual(_disjoined_conditions([MSTATUS], [MSTATUS, EQUAL]), [MSTATUS])

    def test_each_side_implies_the_merge(self):
        # Truth table over the atoms: whenever one side's conditions all hold, so do the merged ones.
        from itertools import product
        atoms = [MSTATUS, EQUAL, LEFT_ZERO, RIGHT_ZERO]
        sides = ([MSTATUS, EQUAL], [MSTATUS, LEFT_ZERO, RIGHT_ZERO])
        merged = _disjoined_conditions(*sides)

        def holds(condition, values):
            if condition.op == 'or':
                return any(holds(arg, values) for arg in condition.args)
            if condition.op == 'and':
                return all(holds(arg, values) for arg in condition.args)
            return values[atoms.index(condition)]
        for values in product([False, True], repeat=len(atoms)):
            for side in sides:
                if all(holds(c, values) for c in side):
                    self.assertTrue(all(holds(c, values) for c in merged))


if __name__ == '__main__':
    unittest.main()
