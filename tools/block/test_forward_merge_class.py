"""The merge candidates of the forward pass are keyed by their conditions that are not memory-map
guards (`forward_design._merge_class`): two alternatives can merge exactly when those sets agree,
so a new alternative is compared only with the earlier ones it can merge with."""
from itertools import product
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from forward_design import _merge_class, _merged_conditions
from symbolic_state import bits, input_expr, operation

ADDRESS = input_expr('address128', 128)
REGION = operation('bvult', ADDRESS, bits(0xc0000000, 128))      # memory-map guard
INPUT_END = operation('bvule', ADDRESS, input_expr('inputEnd', 128))  # memory-map guard
LEFT, RIGHT = input_expr('leftByte', 64), input_expr('rightByte', 64)
EQUAL = operation('=', LEFT, RIGHT)                                # value guard
LEFT_ZERO = operation('=', LEFT, bits(0, 64))                      # value guard (zero arm)


class MergeClass(unittest.TestCase):
    def test_class_equality_is_mergeability(self):
        atoms = [REGION, operation('not', REGION), INPUT_END, EQUAL, operation('not', EQUAL), LEFT_ZERO]
        sets = [[atom for atom, keep in zip(atoms, mask) if keep] for mask in product([0, 1], repeat=len(atoms))]
        for kept in sets:
            for other in sets:
                self.assertEqual(_merged_conditions(kept, other) is not None,
                                 _merge_class(kept) == _merge_class(other), (kept, other))

    def test_shared_conditions_keep_their_order(self):
        kept = [EQUAL, REGION, LEFT_ZERO]
        self.assertEqual(_merged_conditions(kept, [LEFT_ZERO, operation('not', REGION), EQUAL]), [EQUAL, LEFT_ZERO])

    def test_a_value_guard_separates_classes(self):
        self.assertNotEqual(_merge_class([REGION, EQUAL]), _merge_class([REGION, LEFT_ZERO]))
        self.assertEqual(_merge_class([REGION, EQUAL]), _merge_class([operation('not', REGION), EQUAL]))


if __name__ == '__main__':
    unittest.main()
