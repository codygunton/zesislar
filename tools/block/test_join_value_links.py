"""A join keeps the link between a generalized register and its contract-level value on each edge
(`join_generalize.linked_guard_disjunction`, the default `join_guard_form: factored`)."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from join_generalize import generalize_registers, join_guard_fact, linked_guard_disjunction
from symbolic_state import Expr, bits, input_expr, operation
import entry_hist

OUTER = ('args', 'returnAddress')
LENGTH = input_expr('(Z_to_bv 64%N (lenOf args))', 64)
POINTER = input_expr('(Z_to_bv 64%N (ptrOf args))', 64)
EMPTY = operation('=', LENGTH, bits(0, 64))
MSTATUS = operation('=', input_expr('fp_seed_mstatus_bits', 64), bits(0, 64))
CURSOR = input_expr('machine_x9', 64)


def alternative(predecessor, seed, registers, conditions):
    return {'predecessor_pc': predecessor, 'seed_pc': seed,
            'state': {'registers': {key: value.to_dict() for key, value in registers.items()},
                      'conditions': [value.to_dict() for value in conditions]}}


def linked(alternatives, registers):
    plan = generalize_registers(alternatives, register_order=registers)
    return plan, linked_guard_disjunction(alternatives, [MSTATUS], plan, OUTER)


class JoinValueLinks(unittest.TestCase):
    def setUp(self):
        entry_hist.configure({'entry_hist': 'wrap'})

    def test_zero_length_slice_pointer(self):
        # mem.eql 63d4: a zero-length slice's pointer is set to 1, else it is the argument pointer.
        edges = [alternative(0x58, 0xc8, {'x14': bits(1, 64)}, [MSTATUS, EMPTY]),
                 alternative(0xd0, 0xc8, {'x14': POINTER}, [MSTATUS, operation('not', EMPTY)])]
        plan, fact = linked(edges, ['x14'])
        word = input_expr('machine_x14', 64)
        self.assertEqual([binder['name'] for binder in plan['binders']], ['machine_x14'])
        self.assertEqual(fact, operation('or', operation('and', EMPTY, operation('=', word, bits(1, 64))),
                                         operation('and', operation('not', EMPTY), operation('=', word, POINTER))))
        # The flat guard of the same join says only `len = 0 \/ len <> 0`: no link.
        entry_hist.configure({'entry_hist': 'wrap', 'join_guard_form': 'both'})
        self.assertNotIn('machine_x14', join_guard_fact(edges, [MSTATUS], plan, OUTER).coq())

    def test_edges_from_different_seeds_keep_contract_guards_only(self):
        # mem.eql 63d8: the two edges leave different seeds (two earlier joins); a guard on a seed
        # binder means something else on each edge and is not kept; the contract-level guard is.
        local = operation('bvult', CURSOR, LENGTH)
        edges = [alternative(0xd4, 0xd4, {'x12': POINTER}, [MSTATUS, local, operation('not', EMPTY)]),
                 alternative(0x60, 0x60, {'x12': bits(1, 64)}, [MSTATUS, local, EMPTY])]
        plan, fact = linked(edges, ['x12'])
        word = input_expr('machine_x12', 64)
        self.assertEqual(fact, operation('or', operation('and', operation('not', EMPTY), operation('=', word, POINTER)),
                                         operation('and', EMPTY, operation('=', word, bits(1, 64)))))
        self.assertNotIn('machine_x9', fact.coq())

    def test_many_alternatives_one_predecessor(self):
        # utils::lt 0230: alternatives from one predecessor whose register is a byte word on the
        # RAM case and a constant on the ROM case; each disjunct pins it under its own guard.
        word_value = input_expr('(bytesWord (leftBytes args))', 64)
        ram = operation('bvult', input_expr('(Z_to_bv 64%N (leftPtr args))', 64), bits(0xa0000000, 64))
        edges = [alternative(0x2c, 0x00, {'x13': word_value}, [MSTATUS, ram]),
                 alternative(0x2c, 0x00, {'x13': bits(7, 64)}, [MSTATUS, operation('not', ram)])]
        plan, fact = linked(edges, ['x13'])
        word = input_expr('machine_x13', 64)
        self.assertEqual(fact, operation('or', operation('and', ram, operation('=', word, word_value)),
                                         operation('and', operation('not', ram), operation('=', word, bits(7, 64)))))

    def test_a_seed_binder_value_is_not_linked(self):
        edges = [alternative(0x10, 0x00, {'x13': CURSOR}, [MSTATUS, EMPTY]),
                 alternative(0x20, 0x00, {'x13': POINTER}, [MSTATUS, operation('not', EMPTY)])]
        _, fact = linked(edges, ['x13'])
        self.assertEqual(fact, operation('or', EMPTY, operation('not', EMPTY)))

    def test_no_fact_when_an_edge_has_nothing_to_state(self):
        edges = [alternative(0x10, 0x00, {'x13': CURSOR}, [MSTATUS]),
                 alternative(0x10, 0x04, {'x13': POINTER}, [MSTATUS, EMPTY])]
        _, fact = linked(edges, ['x13'])
        self.assertIsNone(fact)

    def test_the_default_renders_it_as_its_proposition(self):
        edges = [alternative(0x58, 0xc8, {'x14': bits(1, 64)}, [MSTATUS, EMPTY]),
                 alternative(0xd0, 0xc8, {'x14': POINTER}, [MSTATUS, operation('not', EMPTY)])]
        plan = generalize_registers(edges, register_order=['x14'])
        fact = join_guard_fact(edges, [MSTATUS], plan, OUTER)
        self.assertEqual(fact.value, entry_hist.PROP_ONLY_GUARD)
        self.assertIsInstance(fact, Expr)

    def test_a_dead_register_is_not_linked(self):
        # A compare chain's last loaded bytes differ per edge but the join's successor never reads them.
        edges = [alternative(0x58, 0xc8, {'x14': bits(1, 64)}, [MSTATUS, EMPTY]),
                 alternative(0xd0, 0xc8, {'x14': POINTER}, [MSTATUS, operation('not', EMPTY)])]
        plan = generalize_registers(edges, register_order=['x14'])
        self.assertEqual(linked_guard_disjunction(edges, [MSTATUS], plan, OUTER, live_registers=['x10']),
                         operation('or', EMPTY, operation('not', EMPTY)))
        self.assertIn('machine_x14', linked_guard_disjunction(edges, [MSTATUS], plan, OUTER,
                                                              live_registers=['x14']).coq())


if __name__ == '__main__':
    unittest.main()
