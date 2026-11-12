"""Inherited join binders without a holder, and per-site function-return packages."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from join_generalize import _register_definition, drop_unheld_binders
from symbolic_state import SymbolicState, bits, input_expr, operation
from render_function_callers import return_site


def state_with(registers, conditions):
    state = SymbolicState(registers=dict(registers))
    state.conditions = list(conditions)
    return state


class UnheldBinders(unittest.TestCase):
    b = input_expr('machine_x10', 64)

    def run_rules(self, state, live, components=()):
        plan = {'binders': []}
        drop_unheld_binders(state, list(components), {}, [{'name': 'machine_x10'}], plan, live,
                            lambda key, writes: '')
        return plan

    def test_a_defining_equation_is_substituted(self):
        entry = input_expr('(Z_to_bv 64%N (n args))', 64)
        state = state_with({'x13': operation('bvadd', self.b, bits(1, 64))},
                           [operation('=', self.b, entry)])
        plan = self.run_rules(state, live=['x13'])
        self.assertEqual(state.registers['x13'], operation('bvadd', entry, bits(1, 64)))
        self.assertEqual(state.conditions, [])
        self.assertEqual(plan['dropped_binders'][0]['rule'], 'definition')

    def test_a_dead_register_gets_a_fresh_binder_and_its_conditions_go(self):
        guard = operation('bvult', self.b, bits(8, 64))
        state = state_with({'x13': operation('bvadd', self.b, bits(1, 64)), 'x1': input_expr('ra', 64)}, [guard])
        plan = self.run_rules(state, live=['x1', 'x2'])
        self.assertEqual(state.registers['x13'], input_expr('machine_x13_1', 64))
        self.assertEqual(state.conditions, [])
        self.assertEqual(plan['binders'], [{'name': 'machine_x13_1', 'type': 'bv 64', 'value_key': 'x13'}])
        self.assertEqual(plan['dropped_binders'][0]['registers'], ['x13'])

    def test_a_live_register_needs_the_binder(self):
        state = state_with({'x13': operation('bvadd', self.b, bits(1, 64))}, [])
        with self.assertRaisesRegex(ValueError, 'a successor needs it: machine_x10'):
            self.run_rules(state, live=['x13'])
        # Without liveness every register counts as live.
        with self.assertRaisesRegex(ValueError, 'a successor needs it'):
            self.run_rules(state_with({'x13': operation('bvadd', self.b, bits(1, 64))}, []),
                           live=None)

    def test_a_held_binder_stays(self):
        state = state_with({'x10': self.b, 'x13': operation('bvadd', self.b, bits(1, 64))}, [])
        plan = self.run_rules(state, live=['x1'])
        self.assertEqual(state.registers['x13'], operation('bvadd', self.b, bits(1, 64)))
        self.assertNotIn('dropped_binders', plan)


class RegisterDefinition(unittest.TestCase):
    b = input_expr('machine_x15', 64)
    out = input_expr('(Z_to_bv 64%N (outPointer args))', 64)

    def state(self, ranged=True):
        cursor = operation('bvadd', operation('bvadd', self.b, self.out), bits(1, 64))
        flag = operation('bvor', self.b, input_expr('(Z_to_bv 64%N (n args))', 64))
        state = state_with({'x13': cursor, 'x15': flag},
                           [operation('bvuge', self.b, bits(0, 64)), operation('bvule', self.b, bits(1, 64))]
                           if ranged else [])
        state.source_intervals = [{'expression': self.out.to_dict(), 'minimum': 0xa0000000,
                                   'maximum': 0xa0400000, 'origin': {'source': 'test'}}]
        return state

    def test_a_live_register_determines_the_binder(self):
        register, width, rest = _register_definition(self.state(), 'machine_x15')
        self.assertEqual((register, width), ('x13', 64))
        self.assertEqual(rest, operation('bvadd', self.out, bits(1, 64)))

    def test_no_range_no_definition(self):
        self.assertIsNone(_register_definition(self.state(ranged=False), 'machine_x15'))

    def test_the_definition_replaces_the_binder_everywhere(self):
        state = self.state()
        plan = {'binders': []}
        drop_unheld_binders(state, [], {}, [{'name': 'machine_x15'}], plan, ['x13', 'x15'], lambda key, writes: '')
        fresh = input_expr('machine_x13_1', 64)
        self.assertEqual(state.registers['x13'], fresh)
        definition = operation('bvsub', fresh, operation('bvadd', self.out, bits(1, 64)))
        self.assertEqual(state.registers['x15'], operation('bvor', definition, input_expr('(Z_to_bv 64%N (n args))', 64)))
        self.assertEqual(state.conditions[1], operation('bvule', definition, bits(1, 64)))
        self.assertEqual(plan['dropped_binders'][0]['rule'], 'register_definition')


class ReturnSites(unittest.TestCase):
    def test_each_return_block_names_its_site(self):
        sites = [('3ed8', {'return_instruction_pc': '0x800d3ed8'}),
                 ('3f10', {'return_instruction_pc': '0x800d3f10'})]
        self.assertEqual(return_site(sites, 0x800d3ec8, 0x800d3edc), '3ed8')
        self.assertEqual(return_site(sites, 0x800d3f04, 0x800d3f14), '3f10')
        self.assertIsNone(return_site(sites, 0x800d3f00, 0x800d3f04))
        self.assertEqual(return_site([('', {'return_instruction_pc': '0x10'})], 0x40, 0x44), '')
        self.assertEqual(return_site([], 0x40, None), '')


if __name__ == '__main__':
    unittest.main()
